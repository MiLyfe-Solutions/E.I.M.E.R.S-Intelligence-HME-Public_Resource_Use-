import V185TrunkScan23Chunk1382

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8191433 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 5, 1, 5]
def baseStart_8191433 : Nat := 118140960795 + 8191433 * 2 ^ 59
def prefixEnd_8191433 : Nat := 4983230072969 + 3 ^ 40 * 8191433 * 2
def baseEnd_8191433 : Nat := 4206142378100954714415791

theorem tailTrace_8191433 : CollatzResearch.WordTrace tailWord_8191433 prefixEnd_8191433 4206142378100954714415791 := by
  unfold tailWord_8191433
  simp only [CollatzResearch.WordTrace]
  refine ⟨298766106132844701222594953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199177404088563134148396635 298766106132844701222594953)
  ·
    refine ⟨224074579599633525916946215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298766106132844701222594953 224074579599633525916946215)
    ·
      refine ⟨336111869399450288875419323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224074579599633525916946215 336111869399450288875419323)
      ·
        refine ⟨504167804099175433313128985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336111869399450288875419323 504167804099175433313128985)
        ·
          refine ⟨378125853074381574984846739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 504167804099175433313128985 378125853074381574984846739)
          ·
            refine ⟨567188779611572362477270109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378125853074381574984846739 567188779611572362477270109)
            ·
              refine ⟨212695792354339635928976291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 567188779611572362477270109 212695792354339635928976291)
              ·
                refine ⟨319043688531509453893464437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212695792354339635928976291 319043688531509453893464437)
                ·
                  refine ⟨29910345799829011302512291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 319043688531509453893464437 29910345799829011302512291)
                  ·
                    refine ⟨44865518699743516953768437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29910345799829011302512291 44865518699743516953768437)
                    ·
                      refine ⟨4206142378100954714415791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44865518699743516953768437 4206142378100954714415791)
                      ·
                        rfl

theorem cell23_8191433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 1, 5].length) (baseStart_8191433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8191433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8191433 prefixEnd_8191433 := by exact prefixLift 8191433
  have htrace : WordTrace (prefixWord ++ tailWord_8191433) baseStart_8191433 baseEnd_8191433 := by
    simpa [prefixWord, tailWord_8191433, baseEnd_8191433] using wordTrace_append hprefix tailTrace_8191433
  have hstable : (prefixWord ++ tailWord_8191433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8191433).length < 2 ^ (prefixWord ++ tailWord_8191433).sum := by decide
  have hdescent : baseEnd_8191433 < baseStart_8191433 := by decide
  rcases family_descends (prefixWord ++ tailWord_8191433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8191447 : List Nat := [1, 1, 3, 2, 1, 1, 1, 4, 5, 2, 2]
def baseStart_8191447 : Nat := 118140960795 + 8191447 * 2 ^ 59
def prefixEnd_8191447 : Nat := 4983230072969 + 3 ^ 40 * 8191447 * 2
def baseEnd_8191447 : Nat := 4206149566830117659640727

theorem tailTrace_8191447 : CollatzResearch.WordTrace tailWord_8191447 prefixEnd_8191447 4206149566830117659640727 := by
  unfold tailWord_8191447
  simp only [CollatzResearch.WordTrace]
  refine ⟨298766616754793981613604595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199177744503195987742403063 298766616754793981613604595)
  ·
    refine ⟨448149925132190972420406893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298766616754793981613604595 448149925132190972420406893)
    ·
      refine ⟨168056221924571614657652585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 448149925132190972420406893 168056221924571614657652585)
      ·
        refine ⟨126042166443428710993239439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168056221924571614657652585 126042166443428710993239439)
        ·
          refine ⟨189063249665143066489859159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126042166443428710993239439 189063249665143066489859159)
          ·
            refine ⟨283594874497714599734788739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189063249665143066489859159 283594874497714599734788739)
            ·
              refine ⟨425392311746571899602183109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283594874497714599734788739 425392311746571899602183109)
              ·
                refine ⟨79761058452482231175409333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 425392311746571899602183109 79761058452482231175409333)
                ·
                  refine ⟨7477599229920209172694625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79761058452482231175409333 7477599229920209172694625)
                  ·
                    refine ⟨5608199422440156879520969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7477599229920209172694625 5608199422440156879520969)
                    ·
                      refine ⟨4206149566830117659640727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5608199422440156879520969 4206149566830117659640727)
                      ·
                        rfl

theorem cell23_8191447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 5, 2, 2].length) (baseStart_8191447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8191447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8191447 prefixEnd_8191447 := by exact prefixLift 8191447
  have htrace : WordTrace (prefixWord ++ tailWord_8191447) baseStart_8191447 baseEnd_8191447 := by
    simpa [prefixWord, tailWord_8191447, baseEnd_8191447] using wordTrace_append hprefix tailTrace_8191447
  have hstable : (prefixWord ++ tailWord_8191447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8191447).length < 2 ^ (prefixWord ++ tailWord_8191447).sum := by decide
  have hdescent : baseEnd_8191447 < baseStart_8191447 := by decide
  rcases family_descends (prefixWord ++ tailWord_8191447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8191450 : List Nat := [3, 1, 1, 2, 3, 2, 1, 3, 1, 1, 5]
def baseStart_8191450 : Nat := 118140960795 + 8191450 * 2 ^ 59
def prefixEnd_8191450 : Nat := 4983230072969 + 3 ^ 40 * 8191450 * 2
def baseEnd_8191450 : Nat := 4206151107272081147903213

theorem tailTrace_8191450 : CollatzResearch.WordTrace tailWord_8191450 prefixEnd_8191450 4206151107272081147903213 := by
  unfold tailWord_8191450
  simp only [CollatzResearch.WordTrace]
  refine ⟨74691681543445778281490951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199177817449188742083975869 74691681543445778281490951)
  ·
    refine ⟨112037522315168667422236427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74691681543445778281490951 112037522315168667422236427)
    ·
      refine ⟨168056283472753001133354641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112037522315168667422236427 168056283472753001133354641)
      ·
        refine ⟨126042212604564750850015981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168056283472753001133354641 126042212604564750850015981)
        ·
          refine ⟨47265829726711781568755993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126042212604564750850015981 47265829726711781568755993)
          ·
            refine ⟨35449372295033836176566995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47265829726711781568755993 35449372295033836176566995)
            ·
              refine ⟨53174058442550754264850493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35449372295033836176566995 53174058442550754264850493)
              ·
                refine ⟨19940271915956532849318935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53174058442550754264850493 19940271915956532849318935)
                ·
                  refine ⟨29910407873934799273978403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19940271915956532849318935 29910407873934799273978403)
                  ·
                    refine ⟨44865611810902198910967605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29910407873934799273978403 44865611810902198910967605)
                    ·
                      refine ⟨4206151107272081147903213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44865611810902198910967605 4206151107272081147903213)
                      ·
                        rfl

theorem cell23_8191450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_8191450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8191450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8191450 prefixEnd_8191450 := by exact prefixLift 8191450
  have htrace : WordTrace (prefixWord ++ tailWord_8191450) baseStart_8191450 baseEnd_8191450 := by
    simpa [prefixWord, tailWord_8191450, baseEnd_8191450] using wordTrace_append hprefix tailTrace_8191450
  have hstable : (prefixWord ++ tailWord_8191450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8191450).length < 2 ^ (prefixWord ++ tailWord_8191450).sum := by decide
  have hdescent : baseEnd_8191450 < baseStart_8191450 := by decide
  rcases family_descends (prefixWord ++ tailWord_8191450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8191470 : List Nat := [4, 1, 2, 1, 2, 1, 4, 8]
def baseStart_8191470 : Nat := 118140960795 + 8191470 * 2 ^ 59
def prefixEnd_8191470 : Nat := 4983230072969 + 3 ^ 40 * 8191470 * 2
def baseEnd_8191470 : Nat := 155783754699450780357523

theorem tailTrace_8191470 : CollatzResearch.WordTrace tailWord_8191470 prefixEnd_8191470 155783754699450780357523 := by
  unfold tailWord_8191470
  simp only [CollatzResearch.WordTrace]
  refine ⟨37345931954213832067711483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199178303755807104361127909 37345931954213832067711483)
  ·
    refine ⟨56018897931320748101567225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37345931954213832067711483 56018897931320748101567225)
    ·
      refine ⟨42014173448490561076175419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56018897931320748101567225 42014173448490561076175419)
      ·
        refine ⟨63021260172735841614263129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42014173448490561076175419 63021260172735841614263129)
        ·
          refine ⟨47265945129551881210697347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63021260172735841614263129 47265945129551881210697347)
          ·
            refine ⟨70898917694327821816046021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47265945129551881210697347 70898917694327821816046021)
            ·
              refine ⟨13293547067686466590508629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70898917694327821816046021 13293547067686466590508629)
              ·
                refine ⟨155783754699450780357523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13293547067686466590508629 155783754699450780357523)
                ·
                  rfl

theorem cell23_8191470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 8].length) (baseStart_8191470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8191470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8191470 prefixEnd_8191470 := by exact prefixLift 8191470
  have htrace : WordTrace (prefixWord ++ tailWord_8191470) baseStart_8191470 baseEnd_8191470 := by
    simpa [prefixWord, tailWord_8191470, baseEnd_8191470] using wordTrace_append hprefix tailTrace_8191470
  have hstable : (prefixWord ++ tailWord_8191470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8191470).length < 2 ^ (prefixWord ++ tailWord_8191470).sum := by decide
  have hdescent : baseEnd_8191470 < baseStart_8191470 := by decide
  rcases family_descends (prefixWord ++ tailWord_8191470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8191474 : List Nat := [3, 2, 1, 4, 1, 2, 1, 3, 2, 4]
def baseStart_8191474 : Nat := 118140960795 + 8191474 * 2 ^ 59
def prefixEnd_8191474 : Nat := 4983230072969 + 3 ^ 40 * 8191474 * 2
def baseEnd_8191474 : Nat := 1402054476935929684667701

theorem tailTrace_8191474 : CollatzResearch.WordTrace tailWord_8191474 prefixEnd_8191474 1402054476935929684667701 := by
  unfold tailWord_8191474
  simp only [CollatzResearch.WordTrace]
  refine ⟨74691900381424041306209369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199178401017130776816558317 74691900381424041306209369)
  ·
    refine ⟨56018925286068030979657027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74691900381424041306209369 56018925286068030979657027)
    ·
      refine ⟨84028387929102046469485541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56018925286068030979657027 84028387929102046469485541)
      ·
        refine ⟨15755322736706633713028539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84028387929102046469485541 15755322736706633713028539)
        ·
          refine ⟨23632984105059950569542809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15755322736706633713028539 23632984105059950569542809)
          ·
            refine ⟨17724738078794962927157107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23632984105059950569542809 17724738078794962927157107)
            ·
              refine ⟨26587107118192444390735661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17724738078794962927157107 26587107118192444390735661)
              ·
                refine ⟨9970165169322166646525873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26587107118192444390735661 9970165169322166646525873)
                ·
                  refine ⟨7477623876991624984894405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9970165169322166646525873 7477623876991624984894405)
                  ·
                    refine ⟨1402054476935929684667701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7477623876991624984894405 1402054476935929684667701)
                    ·
                      rfl

theorem cell23_8191474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 3, 2, 4].length) (baseStart_8191474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8191474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8191474 prefixEnd_8191474 := by exact prefixLift 8191474
  have htrace : WordTrace (prefixWord ++ tailWord_8191474) baseStart_8191474 baseEnd_8191474 := by
    simpa [prefixWord, tailWord_8191474, baseEnd_8191474] using wordTrace_append hprefix tailTrace_8191474
  have hstable : (prefixWord ++ tailWord_8191474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8191474).length < 2 ^ (prefixWord ++ tailWord_8191474).sum := by decide
  have hdescent : baseEnd_8191474 < baseStart_8191474 := by decide
  rcases family_descends (prefixWord ++ tailWord_8191474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8191477 : List Nat := [1, 3, 5, 1, 1, 1, 2, 1, 1, 1, 6]
def baseStart_8191477 : Nat := 118140960795 + 8191477 * 2 ^ 59
def prefixEnd_8191477 : Nat := 4983230072969 + 3 ^ 40 * 8191477 * 2
def baseEnd_8191477 : Nat := 4206164971249752542265589

theorem tailTrace_8191477 : CollatzResearch.WordTrace tailWord_8191477 prefixEnd_8191477 4206164971249752542265589 := by
  unfold tailWord_8191477
  simp only [CollatzResearch.WordTrace]
  refine ⟨298767710944685296737196685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199178473963123531158131123 298767710944685296737196685)
  ·
    refine ⟨112037891604256986276448757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298767710944685296737196685 112037891604256986276448757)
    ·
      refine ⟨10503552337899092463417071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 112037891604256986276448757 10503552337899092463417071)
      ·
        refine ⟨15755328506848638695125607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10503552337899092463417071 15755328506848638695125607)
        ·
          refine ⟨23632992760272958042688411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15755328506848638695125607 23632992760272958042688411)
          ·
            refine ⟨35449489140409437064032617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23632992760272958042688411 35449489140409437064032617)
            ·
              refine ⟨26587116855307077798024463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35449489140409437064032617 26587116855307077798024463)
              ·
                refine ⟨39880675282960616697036695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26587116855307077798024463 39880675282960616697036695)
                ·
                  refine ⟨59821012924440925045555043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39880675282960616697036695 59821012924440925045555043)
                  ·
                    refine ⟨89731519386661387568332565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59821012924440925045555043 89731519386661387568332565)
                    ·
                      refine ⟨4206164971249752542265589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89731519386661387568332565 4206164971249752542265589)
                      ·
                        rfl

theorem cell23_8191477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_8191477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8191477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8191477 prefixEnd_8191477 := by exact prefixLift 8191477
  have htrace : WordTrace (prefixWord ++ tailWord_8191477) baseStart_8191477 baseEnd_8191477 := by
    simpa [prefixWord, tailWord_8191477, baseEnd_8191477] using wordTrace_append hprefix tailTrace_8191477
  have hstable : (prefixWord ++ tailWord_8191477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8191477).length < 2 ^ (prefixWord ++ tailWord_8191477).sum := by decide
  have hdescent : baseEnd_8191477 < baseStart_8191477 := by decide
  rcases family_descends (prefixWord ++ tailWord_8191477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8191483 : List Nat := [1, 1, 1, 1, 1, 3, 2, 4, 2, 7]
def baseStart_8191483 : Nat := 118140960795 + 8191483 * 2 ^ 59
def prefixEnd_8191483 : Nat := 4983230072969 + 3 ^ 40 * 8191483 * 2
def baseEnd_8191483 : Nat := 1402056017377893172930187

theorem tailTrace_8191483 : CollatzResearch.WordTrace tailWord_8191483 prefixEnd_8191483 1402056017377893172930187 := by
  unfold tailWord_8191483
  simp only [CollatzResearch.WordTrace]
  refine ⟨298767929782663559761915103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199178619855109039841276735 298767929782663559761915103)
  ·
    refine ⟨448151894673995339642872655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298767929782663559761915103 448151894673995339642872655)
    ·
      refine ⟨672227842010993009464308983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448151894673995339642872655 672227842010993009464308983)
      ·
        refine ⟨1008341763016489514196463475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 672227842010993009464308983 1008341763016489514196463475)
        ·
          refine ⟨1512512644524734271294695213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1008341763016489514196463475 1512512644524734271294695213)
          ·
            refine ⟨567192241696775351735510705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1512512644524734271294695213 567192241696775351735510705)
            ·
              refine ⟨425394181272581513801633029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 567192241696775351735510705 425394181272581513801633029)
              ·
                refine ⟨79761408988609033837806193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 425394181272581513801633029 79761408988609033837806193)
                ·
                  refine ⟨59821056741456775378354645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79761408988609033837806193 59821056741456775378354645)
                  ·
                    refine ⟨1402056017377893172930187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59821056741456775378354645 1402056017377893172930187)
                    ·
                      rfl

theorem cell23_8191483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 7].length) (baseStart_8191483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8191483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8191483 prefixEnd_8191483 := by exact prefixLift 8191483
  have htrace : WordTrace (prefixWord ++ tailWord_8191483) baseStart_8191483 baseEnd_8191483 := by
    simpa [prefixWord, tailWord_8191483, baseEnd_8191483] using wordTrace_append hprefix tailTrace_8191483
  have hstable : (prefixWord ++ tailWord_8191483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8191483).length < 2 ^ (prefixWord ++ tailWord_8191483).sum := by decide
  have hdescent : baseEnd_8191483 < baseStart_8191483 := by decide
  rcases family_descends (prefixWord ++ tailWord_8191483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8191565 : List Nat := [1, 6, 1, 1, 4, 1, 1, 2, 2, 1, 3]
def baseStart_8191565 : Nat := 118140960795 + 8191565 * 2 ^ 59
def prefixEnd_8191565 : Nat := 4983230072969 + 3 ^ 40 * 8191565 * 2
def baseEnd_8191565 : Nat := 4206210157547348197965185

theorem tailTrace_8191565 : CollatzResearch.WordTrace tailWord_8191565 prefixEnd_8191565 4206210157547348197965185 := by
  unfold tailWord_8191565
  simp only [CollatzResearch.WordTrace]
  refine ⟨298770920568366487766400149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199180613712244325177600099 298770920568366487766400149)
  ·
    refine ⟨14004886901642179114050007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 298770920568366487766400149 14004886901642179114050007)
    ·
      refine ⟨21007330352463268671075011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14004886901642179114050007 21007330352463268671075011)
      ·
        refine ⟨31510995528694903006612517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21007330352463268671075011 31510995528694903006612517)
        ·
          refine ⟨5908311661630294313739847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31510995528694903006612517 5908311661630294313739847)
          ·
            refine ⟨8862467492445441470609771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5908311661630294313739847 8862467492445441470609771)
            ·
              refine ⟨13293701238668162205914657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8862467492445441470609771 13293701238668162205914657)
              ·
                refine ⟨9970275929001121654435993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13293701238668162205914657 9970275929001121654435993)
                ·
                  refine ⟨7477706946750841240826995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9970275929001121654435993 7477706946750841240826995)
                  ·
                    refine ⟨11216560420126261861240493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7477706946750841240826995 11216560420126261861240493)
                    ·
                      refine ⟨4206210157547348197965185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11216560420126261861240493 4206210157547348197965185)
                      ·
                        rfl

theorem cell23_8191565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_8191565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8191565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8191565 prefixEnd_8191565 := by exact prefixLift 8191565
  have htrace : WordTrace (prefixWord ++ tailWord_8191565) baseStart_8191565 baseEnd_8191565 := by
    simpa [prefixWord, tailWord_8191565, baseEnd_8191565] using wordTrace_append hprefix tailTrace_8191565
  have hstable : (prefixWord ++ tailWord_8191565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8191565).length < 2 ^ (prefixWord ++ tailWord_8191565).sum := by decide
  have hdescent : baseEnd_8191565 < baseStart_8191565 := by decide
  rcases family_descends (prefixWord ++ tailWord_8191565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8191587 : List Nat := [1, 1, 1, 5, 1, 3, 2, 1, 2, 3, 3]
def baseStart_8191587 : Nat := 118140960795 + 8191587 * 2 ^ 59
def prefixEnd_8191587 : Nat := 4983230072969 + 3 ^ 40 * 8191587 * 2
def baseEnd_8191587 : Nat := 4206221454121747111890083

theorem tailTrace_8191587 : CollatzResearch.WordTrace tailWord_8191587 prefixEnd_8191587 4206221454121747111890083 := by
  unfold tailWord_8191587
  simp only [CollatzResearch.WordTrace]
  refine ⟨298771722974286785523701015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199181148649524523682467343 298771722974286785523701015)
  ·
    refine ⟨448157584461430178285551523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298771722974286785523701015 448157584461430178285551523)
    ·
      refine ⟨672236376692145267428327285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448157584461430178285551523 672236376692145267428327285)
      ·
        refine ⟨63022160314888618821405683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 672236376692145267428327285 63022160314888618821405683)
        ·
          refine ⟨94533240472332928232108525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63022160314888618821405683 94533240472332928232108525)
          ·
            refine ⟨35449965177124848087040697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94533240472332928232108525 35449965177124848087040697)
            ·
              refine ⟨26587473882843636065280523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35449965177124848087040697 26587473882843636065280523)
              ·
                refine ⟨39881210824265454097920785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26587473882843636065280523 39881210824265454097920785)
                ·
                  refine ⟨29910908118199090573440589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39881210824265454097920785 29910908118199090573440589)
                  ·
                    refine ⟨11216590544324658965040221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29910908118199090573440589 11216590544324658965040221)
                    ·
                      refine ⟨4206221454121747111890083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11216590544324658965040221 4206221454121747111890083)
                      ·
                        rfl

theorem cell23_8191587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_8191587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8191587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8191587 prefixEnd_8191587 := by exact prefixLift 8191587
  have htrace : WordTrace (prefixWord ++ tailWord_8191587) baseStart_8191587 baseEnd_8191587 := by
    simpa [prefixWord, tailWord_8191587, baseEnd_8191587] using wordTrace_append hprefix tailTrace_8191587
  have hstable : (prefixWord ++ tailWord_8191587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8191587).length < 2 ^ (prefixWord ++ tailWord_8191587).sum := by decide
  have hdescent : baseEnd_8191587 < baseStart_8191587 := by decide
  rcases family_descends (prefixWord ++ tailWord_8191587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8191588 : List Nat := [2, 3, 1, 1, 2, 4, 3, 1, 2, 2, 2]
def baseStart_8191588 : Nat := 118140960795 + 8191588 * 2 ^ 59
def prefixEnd_8191588 : Nat := 4983230072969 + 3 ^ 40 * 8191588 * 2
def baseEnd_8191588 : Nat := 4206221967602401607977579

theorem tailTrace_8191588 : CollatzResearch.WordTrace tailWord_8191588 prefixEnd_8191588 4206221967602401607977579 := by
  unfold tailWord_8191588
  simp only [CollatzResearch.WordTrace]
  refine ⟨149385879723641581347243709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199181172964855441796324945 149385879723641581347243709)
  ·
    refine ⟨56019704896365593005216391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149385879723641581347243709 56019704896365593005216391)
    ·
      refine ⟨84029557344548389507824587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56019704896365593005216391 84029557344548389507824587)
      ·
        refine ⟨126044336016822584261736881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84029557344548389507824587 126044336016822584261736881)
        ·
          refine ⟨94533252012616938196302661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126044336016822584261736881 94533252012616938196302661)
          ·
            refine ⟨17724984752365675911806749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94533252012616938196302661 17724984752365675911806749)
            ·
              refine ⟨6646869282137128466927531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17724984752365675911806749 6646869282137128466927531)
              ·
                refine ⟨9970303923205692700391297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6646869282137128466927531 9970303923205692700391297)
                ·
                  refine ⟨7477727942404269525293473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9970303923205692700391297 7477727942404269525293473)
                  ·
                    refine ⟨5608295956803202143970105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7477727942404269525293473 5608295956803202143970105)
                    ·
                      refine ⟨4206221967602401607977579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5608295956803202143970105 4206221967602401607977579)
                      ·
                        rfl

theorem cell23_8191588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 1, 2, 2, 2].length) (baseStart_8191588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8191588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8191588 prefixEnd_8191588 := by exact prefixLift 8191588
  have htrace : WordTrace (prefixWord ++ tailWord_8191588) baseStart_8191588 baseEnd_8191588 := by
    simpa [prefixWord, tailWord_8191588, baseEnd_8191588] using wordTrace_append hprefix tailTrace_8191588
  have hstable : (prefixWord ++ tailWord_8191588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8191588).length < 2 ^ (prefixWord ++ tailWord_8191588).sum := by decide
  have hdescent : baseEnd_8191588 < baseStart_8191588 := by decide
  rcases family_descends (prefixWord ++ tailWord_8191588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8191627 : List Nat := [1, 1, 1, 1, 4, 1, 5, 2, 2, 1, 4]
def baseStart_8191627 : Nat := 118140960795 + 8191627 * 2 ^ 59
def prefixEnd_8191627 : Nat := 4983230072969 + 3 ^ 40 * 8191627 * 2
def baseEnd_8191627 : Nat := 4206241993347926955389899

theorem tailTrace_8191627 : CollatzResearch.WordTrace tailWord_8191627 prefixEnd_8191627 4206241993347926955389899 := by
  unfold tailWord_8191627
  simp only [CollatzResearch.WordTrace]
  refine ⟨298773181894141872355157135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199182121262761248236771423 298773181894141872355157135)
  ·
    refine ⟨448159772841212808532735703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298773181894141872355157135 448159772841212808532735703)
    ·
      refine ⟨672239659261819212799103555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448159772841212808532735703 672239659261819212799103555)
      ·
        refine ⟨1008359488892728819198655333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 672239659261819212799103555 1008359488892728819198655333)
        ·
          refine ⟨189067404167386653599747875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1008359488892728819198655333 189067404167386653599747875)
          ·
            refine ⟨283601106251079980399621813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189067404167386653599747875 283601106251079980399621813)
            ·
              refine ⟨26587603711038748162464545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 283601106251079980399621813 26587603711038748162464545)
              ·
                refine ⟨19940702783279061121848409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26587603711038748162464545 19940702783279061121848409)
                ·
                  refine ⟨14955527087459295841386307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19940702783279061121848409 14955527087459295841386307)
                  ·
                    refine ⟨22433290631188943762079461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14955527087459295841386307 22433290631188943762079461)
                    ·
                      refine ⟨4206241993347926955389899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22433290631188943762079461 4206241993347926955389899)
                      ·
                        rfl

theorem cell23_8191627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 2, 1, 4].length) (baseStart_8191627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8191627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8191627 prefixEnd_8191627 := by exact prefixLift 8191627
  have htrace : WordTrace (prefixWord ++ tailWord_8191627) baseStart_8191627 baseEnd_8191627 := by
    simpa [prefixWord, tailWord_8191627, baseEnd_8191627] using wordTrace_append hprefix tailTrace_8191627
  have hstable : (prefixWord ++ tailWord_8191627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8191627).length < 2 ^ (prefixWord ++ tailWord_8191627).sum := by decide
  have hdescent : baseEnd_8191627 < baseStart_8191627 := by decide
  rcases family_descends (prefixWord ++ tailWord_8191627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8191634 : List Nat := [3, 2, 3, 1, 3, 1, 1, 1, 1, 2, 5]
def baseStart_8191634 : Nat := 118140960795 + 8191634 * 2 ^ 59
def prefixEnd_8191634 : Nat := 4983230072969 + 3 ^ 40 * 8191634 * 2
def baseEnd_8191634 : Nat := 4206245587712508428002367

theorem tailTrace_8191634 : CollatzResearch.WordTrace tailWord_8191634 prefixEnd_8191634 4206245587712508428002367 := by
  unfold tailWord_8191634
  simp only [CollatzResearch.WordTrace]
  refine ⟨74693359301279128137665489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199182291470077675033774637 74693359301279128137665489)
  ·
    refine ⟨56020019475959346103249117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74693359301279128137665489 56020019475959346103249117)
    ·
      refine ⟨21007507303484754788718419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56020019475959346103249117 21007507303484754788718419)
      ·
        refine ⟨31511260955227132183077629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21007507303484754788718419 31511260955227132183077629)
        ·
          refine ⟨11816722858210174568654111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31511260955227132183077629 11816722858210174568654111)
          ·
            refine ⟨17725084287315261852981167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11816722858210174568654111 17725084287315261852981167)
            ·
              refine ⟨26587626430972892779471751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17725084287315261852981167 26587626430972892779471751)
              ·
                refine ⟨39881439646459339169207627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26587626430972892779471751 39881439646459339169207627)
                ·
                  refine ⟨59822159469689008753811441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39881439646459339169207627 59822159469689008753811441)
                  ·
                    refine ⟨44866619602266756565358581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59822159469689008753811441 44866619602266756565358581)
                    ·
                      refine ⟨4206245587712508428002367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44866619602266756565358581 4206245587712508428002367)
                      ·
                        rfl

theorem cell23_8191634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_8191634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8191634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8191634 prefixEnd_8191634 := by exact prefixLift 8191634
  have htrace : WordTrace (prefixWord ++ tailWord_8191634) baseStart_8191634 baseEnd_8191634 := by
    simpa [prefixWord, tailWord_8191634, baseEnd_8191634] using wordTrace_append hprefix tailTrace_8191634
  have hstable : (prefixWord ++ tailWord_8191634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8191634).length < 2 ^ (prefixWord ++ tailWord_8191634).sum := by decide
  have hdescent : baseEnd_8191634 < baseStart_8191634 := by decide
  rcases family_descends (prefixWord ++ tailWord_8191634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8191684 : List Nat := [2, 3, 3, 1, 1, 1, 4, 2, 6]
def baseStart_8191684 : Nat := 118140960795 + 8191684 * 2 ^ 59
def prefixEnd_8191684 : Nat := 4983230072969 + 3 ^ 40 * 8191684 * 2
def baseEnd_8191684 : Nat := 467363473527248136930793

theorem tailTrace_8191684 : CollatzResearch.WordTrace tailWord_8191684 prefixEnd_8191684 467363473527248136930793 := by
  unfold tailWord_8191684
  simp only [CollatzResearch.WordTrace]
  refine ⟨149387630427467685544991053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199183507236623580726654737 149387630427467685544991053)
  ·
    refine ⟨56020361410300382079371645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149387630427467685544991053 56020361410300382079371645)
    ·
      refine ⟨21007635528862643279764367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56020361410300382079371645 21007635528862643279764367)
      ·
        refine ⟨31511453293293964919646551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21007635528862643279764367 31511453293293964919646551)
        ·
          refine ⟨47267179939940947379469827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31511453293293964919646551 47267179939940947379469827)
          ·
            refine ⟨70900769909911421069204741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47267179939940947379469827 70900769909911421069204741)
            ·
              refine ⟨13293894358108391450475889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70900769909911421069204741 13293894358108391450475889)
              ·
                refine ⟨9970420768581293587856917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13293894358108391450475889 9970420768581293587856917)
                ·
                  refine ⟨467363473527248136930793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9970420768581293587856917 467363473527248136930793)
                  ·
                    rfl

theorem cell23_8191684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 2, 6].length) (baseStart_8191684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8191684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8191684 prefixEnd_8191684 := by exact prefixLift 8191684
  have htrace : WordTrace (prefixWord ++ tailWord_8191684) baseStart_8191684 baseEnd_8191684 := by
    simpa [prefixWord, tailWord_8191684, baseEnd_8191684] using wordTrace_append hprefix tailTrace_8191684
  have hstable : (prefixWord ++ tailWord_8191684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8191684).length < 2 ^ (prefixWord ++ tailWord_8191684).sum := by decide
  have hdescent : baseEnd_8191684 < baseStart_8191684 := by decide
  rcases family_descends (prefixWord ++ tailWord_8191684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8191697 : List Nat := [1, 2, 2, 1, 2, 4, 1, 2, 3, 5]
def baseStart_8191697 : Nat := 118140960795 + 8191697 * 2 ^ 59
def prefixEnd_8191697 : Nat := 4983230072969 + 3 ^ 40 * 8191697 * 2
def baseEnd_8191697 : Nat := 1402092645664580560504859

theorem tailTrace_8191697 : CollatzResearch.WordTrace tailWord_8191697 prefixEnd_8191697 1402092645664580560504859 := by
  unfold tailWord_8191697
  simp only [CollatzResearch.WordTrace]
  refine ⟨298775735003888274310205345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199183823335925516206803563 298775735003888274310205345)
  ·
    refine ⟨224081801252916205732654009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298775735003888274310205345 224081801252916205732654009)
    ·
      refine ⟨168061350939687154299490507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224081801252916205732654009 168061350939687154299490507)
      ·
        refine ⟨252092026409530731449235761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168061350939687154299490507 252092026409530731449235761)
        ·
          refine ⟨189069019807148048586926821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252092026409530731449235761 189069019807148048586926821)
          ·
            refine ⟨35450441213840259110048779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189069019807148048586926821 35450441213840259110048779)
            ·
              refine ⟨53175661820760388665073169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35450441213840259110048779 53175661820760388665073169)
              ·
                refine ⟨39881746365570291498804877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53175661820760388665073169 39881746365570291498804877)
                ·
                  refine ⟨14955654887088859312051829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39881746365570291498804877 14955654887088859312051829)
                  ·
                    refine ⟨1402092645664580560504859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14955654887088859312051829 1402092645664580560504859)
                    ·
                      rfl

theorem cell23_8191697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 3, 5].length) (baseStart_8191697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8191697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8191697 prefixEnd_8191697 := by exact prefixLift 8191697
  have htrace : WordTrace (prefixWord ++ tailWord_8191697) baseStart_8191697 baseEnd_8191697 := by
    simpa [prefixWord, tailWord_8191697, baseEnd_8191697] using wordTrace_append hprefix tailTrace_8191697
  have hstable : (prefixWord ++ tailWord_8191697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8191697).length < 2 ^ (prefixWord ++ tailWord_8191697).sum := by decide
  have hdescent : baseEnd_8191697 < baseStart_8191697 := by decide
  rcases family_descends (prefixWord ++ tailWord_8191697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8191704 : List Nat := [2, 1, 2, 2, 3, 1, 2, 2, 1, 5, 2]
def baseStart_8191704 : Nat := 118140960795 + 8191704 * 2 ^ 59
def prefixEnd_8191704 : Nat := 4983230072969 + 3 ^ 40 * 8191704 * 2
def baseEnd_8191704 : Nat := 4206281531358323154127045

theorem tailTrace_8191704 : CollatzResearch.WordTrace tailWord_8191704 prefixEnd_8191704 4206281531358323154127045 := by
  unfold tailWord_8191704
  simp only [CollatzResearch.WordTrace]
  refine ⟨149387995157431457252855083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199183993543241943003806777 149387995157431457252855083)
  ·
    refine ⟨224081992736147185879282625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149387995157431457252855083 224081992736147185879282625)
    ·
      refine ⟨168061494552110389409461969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224081992736147185879282625 168061494552110389409461969)
      ·
        refine ⟨126046120914082792057096477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168061494552110389409461969 126046120914082792057096477)
        ·
          refine ⟨47267295342781047021411179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126046120914082792057096477 47267295342781047021411179)
          ·
            refine ⟨70900943014171570532116769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47267295342781047021411179 70900943014171570532116769)
            ·
              refine ⟨53175707260628677899087577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70900943014171570532116769 53175707260628677899087577)
              ·
                refine ⟨39881780445471508424315683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53175707260628677899087577 39881780445471508424315683)
                ·
                  refine ⟨59822670668207262636473525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39881780445471508424315683 59822670668207262636473525)
                  ·
                    refine ⟨5608375375144430872169393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59822670668207262636473525 5608375375144430872169393)
                    ·
                      refine ⟨4206281531358323154127045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5608375375144430872169393 4206281531358323154127045)
                      ·
                        rfl

theorem cell23_8191704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 1, 5, 2].length) (baseStart_8191704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8191704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8191704 prefixEnd_8191704 := by exact prefixLift 8191704
  have htrace : WordTrace (prefixWord ++ tailWord_8191704) baseStart_8191704 baseEnd_8191704 := by
    simpa [prefixWord, tailWord_8191704, baseEnd_8191704] using wordTrace_append hprefix tailTrace_8191704
  have hstable : (prefixWord ++ tailWord_8191704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8191704).length < 2 ^ (prefixWord ++ tailWord_8191704).sum := by decide
  have hdescent : baseEnd_8191704 < baseStart_8191704 := by decide
  rcases family_descends (prefixWord ++ tailWord_8191704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8191727 : List Nat := [1, 1, 2, 1, 5, 1, 1, 4, 1, 6]
def baseStart_8191727 : Nat := 118140960795 + 8191727 * 2 ^ 59
def prefixEnd_8191727 : Nat := 4983230072969 + 3 ^ 40 * 8191727 * 2
def baseEnd_8191727 : Nat := 1402097780471125521379813

theorem tailTrace_8191727 : CollatzResearch.WordTrace tailWord_8191727 prefixEnd_8191727 1402097780471125521379813 := by
  unfold tailWord_8191727
  simp only [CollatzResearch.WordTrace]
  refine ⟨298776829193779589433797435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199184552795853059622531623 298776829193779589433797435)
  ·
    refine ⟨448165243790669384150696153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298776829193779589433797435 448165243790669384150696153)
    ·
      refine ⟨336123932843002038113022115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 448165243790669384150696153 336123932843002038113022115)
      ·
        refine ⟨504185899264503057169533173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336123932843002038113022115 504185899264503057169533173)
        ·
          refine ⟨47267428056047161609643735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 504185899264503057169533173 47267428056047161609643735)
          ·
            refine ⟨70901142084070742414465603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47267428056047161609643735 70901142084070742414465603)
            ·
              refine ⟨106351713126106113621698405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70901142084070742414465603 106351713126106113621698405)
              ·
                refine ⟨19940946211144896304068451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106351713126106113621698405 19940946211144896304068451)
                ·
                  refine ⟨29911419316717344456102677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19940946211144896304068451 29911419316717344456102677)
                  ·
                    refine ⟨1402097780471125521379813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29911419316717344456102677 1402097780471125521379813)
                    ·
                      rfl

theorem cell23_8191727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 6].length) (baseStart_8191727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8191727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8191727 prefixEnd_8191727 := by exact prefixLift 8191727
  have htrace : WordTrace (prefixWord ++ tailWord_8191727) baseStart_8191727 baseEnd_8191727 := by
    simpa [prefixWord, tailWord_8191727, baseEnd_8191727] using wordTrace_append hprefix tailTrace_8191727
  have hstable : (prefixWord ++ tailWord_8191727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8191727).length < 2 ^ (prefixWord ++ tailWord_8191727).sum := by decide
  have hdescent : baseEnd_8191727 < baseStart_8191727 := by decide
  rcases family_descends (prefixWord ++ tailWord_8191727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8191747 : List Nat := [1, 1, 1, 3, 2, 2, 2, 2, 3, 2, 4]
def baseStart_8191747 : Nat := 118140960795 + 8191747 * 2 ^ 59
def prefixEnd_8191747 : Nat := 4983230072969 + 3 ^ 40 * 8191747 * 2
def baseEnd_8191747 : Nat := 4206303611026466485889347

theorem tailTrace_8191747 : CollatzResearch.WordTrace tailWord_8191747 prefixEnd_8191747 4206303611026466485889347 := by
  unfold tailWord_8191747
  simp only [CollatzResearch.WordTrace]
  refine ⟨298777558653707132849525495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199185039102471421899683663 298777558653707132849525495)
  ·
    refine ⟨448166337980560699274288243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298777558653707132849525495 448166337980560699274288243)
    ·
      refine ⟨672249506970841048911432365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448166337980560699274288243 672249506970841048911432365)
      ·
        refine ⟨252093565114065393341787137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 672249506970841048911432365 252093565114065393341787137)
        ·
          refine ⟨189070173835549045006340353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252093565114065393341787137 189070173835549045006340353)
          ·
            refine ⟨141802630376661783754755265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189070173835549045006340353 141802630376661783754755265)
            ·
              refine ⟨106351972782496337816066449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141802630376661783754755265 106351972782496337816066449)
              ·
                refine ⟨79763979586872253362049837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106351972782496337816066449 79763979586872253362049837)
                ·
                  refine ⟨29911492345077095010768689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79763979586872253362049837 29911492345077095010768689)
                  ·
                    refine ⟨22433619258807821258076517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29911492345077095010768689 22433619258807821258076517)
                    ·
                      refine ⟨4206303611026466485889347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22433619258807821258076517 4206303611026466485889347)
                      ·
                        rfl

theorem cell23_8191747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 2, 4].length) (baseStart_8191747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8191747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8191747 prefixEnd_8191747 := by exact prefixLift 8191747
  have htrace : WordTrace (prefixWord ++ tailWord_8191747) baseStart_8191747 baseEnd_8191747 := by
    simpa [prefixWord, tailWord_8191747, baseEnd_8191747] using wordTrace_append hprefix tailTrace_8191747
  have hstable : (prefixWord ++ tailWord_8191747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8191747).length < 2 ^ (prefixWord ++ tailWord_8191747).sum := by decide
  have hdescent : baseEnd_8191747 < baseStart_8191747 := by decide
  rcases family_descends (prefixWord ++ tailWord_8191747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8191754 : List Nat := [3, 1, 2, 2, 1, 4, 1, 2, 1, 1, 5]
def baseStart_8191754 : Nat := 118140960795 + 8191754 * 2 ^ 59
def prefixEnd_8191754 : Nat := 4983230072969 + 3 ^ 40 * 8191754 * 2
def baseEnd_8191754 : Nat := 4206307205391047958501815

theorem tailTrace_8191754 : CollatzResearch.WordTrace tailWord_8191754 prefixEnd_8191754 4206307205391047958501815 := by
  unfold tailWord_8191754
  simp only [CollatzResearch.WordTrace]
  refine ⟨74694453491170443261257579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199185209309787848696686877 74694453491170443261257579)
  ·
    refine ⟨112041680236755664891886369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74694453491170443261257579 112041680236755664891886369)
    ·
      refine ⟨84031260177566748668914777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112041680236755664891886369 84031260177566748668914777)
      ·
        refine ⟨63023445133175061501686083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84031260177566748668914777 63023445133175061501686083)
        ·
          refine ⟨94535167699762592252529125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63023445133175061501686083 94535167699762592252529125)
          ·
            refine ⟨17725343943705486047349211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94535167699762592252529125 17725343943705486047349211)
            ·
              refine ⟨26588015915558229071023817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17725343943705486047349211 26588015915558229071023817)
              ·
                refine ⟨19941011936668671803267863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26588015915558229071023817 19941011936668671803267863)
                ·
                  refine ⟨29911517905003007704901795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19941011936668671803267863 29911517905003007704901795)
                  ·
                    refine ⟨44867276857504511557352693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29911517905003007704901795 44867276857504511557352693)
                    ·
                      refine ⟨4206307205391047958501815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44867276857504511557352693 4206307205391047958501815)
                      ·
                        rfl

theorem cell23_8191754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_8191754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8191754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8191754 prefixEnd_8191754 := by exact prefixLift 8191754
  have htrace : WordTrace (prefixWord ++ tailWord_8191754) baseStart_8191754 baseEnd_8191754 := by
    simpa [prefixWord, tailWord_8191754, baseEnd_8191754] using wordTrace_append hprefix tailTrace_8191754
  have hstable : (prefixWord ++ tailWord_8191754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8191754).length < 2 ^ (prefixWord ++ tailWord_8191754).sum := by decide
  have hdescent : baseEnd_8191754 < baseStart_8191754 := by decide
  rcases family_descends (prefixWord ++ tailWord_8191754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8191802 : List Nat := [3, 1, 1, 1, 5, 2, 3, 2, 1, 2, 2]
def baseStart_8191802 : Nat := 118140960795 + 8191802 * 2 ^ 59
def prefixEnd_8191802 : Nat := 4983230072969 + 3 ^ 40 * 8191802 * 2
def baseEnd_8191802 : Nat := 4206331852462463770701595

theorem tailTrace_8191802 : CollatzResearch.WordTrace tailWord_8191802 prefixEnd_8191802 4206331852462463770701595 := by
  unfold tailWord_8191802
  simp only [CollatzResearch.WordTrace]
  refine ⟨74694891167126969310694415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199186376445671918161851773 74694891167126969310694415)
  ·
    refine ⟨112042336750690453966041623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74694891167126969310694415 112042336750690453966041623)
    ·
      refine ⟨168063505126035680949062435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112042336750690453966041623 168063505126035680949062435)
      ·
        refine ⟨252095257689053521423593653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168063505126035680949062435 252095257689053521423593653)
        ·
          refine ⟨23633930408348767633461905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 252095257689053521423593653 23633930408348767633461905)
          ·
            refine ⟨17725447806261575725096429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23633930408348767633461905 17725447806261575725096429)
            ·
              refine ⟨6647042927348090896911161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17725447806261575725096429 6647042927348090896911161)
              ·
                refine ⟨4985282195511068172683371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6647042927348090896911161 4985282195511068172683371)
                ·
                  refine ⟨7477923293266602259025057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4985282195511068172683371 7477923293266602259025057)
                  ·
                    refine ⟨5608442469949951694268793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7477923293266602259025057 5608442469949951694268793)
                    ·
                      refine ⟨4206331852462463770701595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5608442469949951694268793 4206331852462463770701595)
                      ·
                        rfl

theorem cell23_8191802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 2, 1, 2, 2].length) (baseStart_8191802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8191802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8191802 prefixEnd_8191802 := by exact prefixLift 8191802
  have htrace : WordTrace (prefixWord ++ tailWord_8191802) baseStart_8191802 baseEnd_8191802 := by
    simpa [prefixWord, tailWord_8191802, baseEnd_8191802] using wordTrace_append hprefix tailTrace_8191802
  have hstable : (prefixWord ++ tailWord_8191802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8191802).length < 2 ^ (prefixWord ++ tailWord_8191802).sum := by decide
  have hdescent : baseEnd_8191802 < baseStart_8191802 := by decide
  rcases family_descends (prefixWord ++ tailWord_8191802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8191817 : List Nat := [1, 2, 1, 1, 2, 4, 2, 1, 1, 8]
def baseStart_8191817 : Nat := 118140960795 + 8191817 * 2 ^ 59
def prefixEnd_8191817 : Nat := 4983230072969 + 3 ^ 40 * 8191817 * 2
def baseEnd_8191817 : Nat := 1402113184890760404004675

theorem tailTrace_8191817 : CollatzResearch.WordTrace tailWord_8191817 prefixEnd_8191817 1402113184890760404004675 := by
  unfold tailWord_8191817
  simp only [CollatzResearch.WordTrace]
  refine ⟨298780111763453534804573705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199186741175635689869715803 298780111763453534804573705)
  ·
    refine ⟨224085083822590151103430279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298780111763453534804573705 224085083822590151103430279)
    ·
      refine ⟨336127625733885226655145419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224085083822590151103430279 336127625733885226655145419)
      ·
        refine ⟨504191438600827839982718129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336127625733885226655145419 504191438600827839982718129)
        ·
          refine ⟨378143578950620879987038597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 504191438600827839982718129 378143578950620879987038597)
          ·
            refine ⟨70901921053241414997569737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 378143578950620879987038597 70901921053241414997569737)
            ·
              refine ⟨53176440789931061248177303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70901921053241414997569737 53176440789931061248177303)
              ·
                refine ⟨79764661184896591872265955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53176440789931061248177303 79764661184896591872265955)
                ·
                  refine ⟨119646991777344887808398933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79764661184896591872265955 119646991777344887808398933)
                  ·
                    refine ⟨1402113184890760404004675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 119646991777344887808398933 1402113184890760404004675)
                    ·
                      rfl

theorem cell23_8191817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 8].length) (baseStart_8191817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8191817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8191817 prefixEnd_8191817 := by exact prefixLift 8191817
  have htrace : WordTrace (prefixWord ++ tailWord_8191817) baseStart_8191817 baseEnd_8191817 := by
    simpa [prefixWord, tailWord_8191817, baseEnd_8191817] using wordTrace_append hprefix tailTrace_8191817
  have hstable : (prefixWord ++ tailWord_8191817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8191817).length < 2 ^ (prefixWord ++ tailWord_8191817).sum := by decide
  have hdescent : baseEnd_8191817 < baseStart_8191817 := by decide
  rcases family_descends (prefixWord ++ tailWord_8191817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8191828 : List Nat := [2, 4, 1, 1, 3, 2, 1, 1, 3, 3, 2]
def baseStart_8191828 : Nat := 118140960795 + 8191828 * 2 ^ 59
def prefixEnd_8191828 : Nat := 4983230072969 + 3 ^ 40 * 8191828 * 2
def baseEnd_8191828 : Nat := 4206345202959480668976475

theorem tailTrace_8191828 : CollatzResearch.WordTrace tailWord_8191828 prefixEnd_8191828 4206345202959480668976475 := by
  unfold tailWord_8191828
  simp only [CollatzResearch.WordTrace]
  refine ⟨149390256483206841841612069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199187008644275789122149425 149390256483206841841612069)
  ·
    refine ⟨28010673090601282845302263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149390256483206841841612069 28010673090601282845302263)
    ·
      refine ⟨42016009635901924267953395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28010673090601282845302263 42016009635901924267953395)
      ·
        refine ⟨63024014453852886401930093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42016009635901924267953395 63024014453852886401930093)
        ·
          refine ⟨23634005420194832400723785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63024014453852886401930093 23634005420194832400723785)
          ·
            refine ⟨17725504065146124300542839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23634005420194832400723785 17725504065146124300542839)
            ·
              refine ⟨26588256097719186450814259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17725504065146124300542839 26588256097719186450814259)
              ·
                refine ⟨39882384146578779676221389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26588256097719186450814259 39882384146578779676221389)
                ·
                  refine ⟨14955894054967042378583021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39882384146578779676221389 14955894054967042378583021)
                  ·
                    refine ⟨5608460270612640891968633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14955894054967042378583021 5608460270612640891968633)
                    ·
                      refine ⟨4206345202959480668976475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5608460270612640891968633 4206345202959480668976475)
                      ·
                        rfl

theorem cell23_8191828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 3, 3, 2].length) (baseStart_8191828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8191828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8191828 prefixEnd_8191828 := by exact prefixLift 8191828
  have htrace : WordTrace (prefixWord ++ tailWord_8191828) baseStart_8191828 baseEnd_8191828 := by
    simpa [prefixWord, tailWord_8191828, baseEnd_8191828] using wordTrace_append hprefix tailTrace_8191828
  have hstable : (prefixWord ++ tailWord_8191828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8191828).length < 2 ^ (prefixWord ++ tailWord_8191828).sum := by decide
  have hdescent : baseEnd_8191828 < baseStart_8191828 := by decide
  rcases family_descends (prefixWord ++ tailWord_8191828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8191841 : List Nat := [1, 2, 3, 1, 1, 1, 5, 2, 1, 4, 2]
def baseStart_8191841 : Nat := 118140960795 + 8191841 * 2 ^ 59
def prefixEnd_8191841 : Nat := 4983230072969 + 3 ^ 40 * 8191841 * 2
def baseEnd_8191841 : Nat := 4206351878207989118113915

theorem tailTrace_8191841 : CollatzResearch.WordTrace tailWord_8191841 prefixEnd_8191841 4206351878207989118113915 := by
  unfold tailWord_8191841
  simp only [CollatzResearch.WordTrace]
  refine ⟨298780987115366586903447377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199187324743577724602298251 298780987115366586903447377)
  ·
    refine ⟨224085740336524940177585533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298780987115366586903447377 224085740336524940177585533)
    ·
      refine ⟨84032152626196852566594575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224085740336524940177585533 84032152626196852566594575)
      ·
        refine ⟨126048228939295278849891863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84032152626196852566594575 126048228939295278849891863)
        ·
          refine ⟨189072343408942918274837795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126048228939295278849891863 189072343408942918274837795)
          ·
            refine ⟨283608515113414377412256693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189072343408942918274837795 283608515113414377412256693)
            ·
              refine ⟨26588298291882597882399065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 283608515113414377412256693 26588298291882597882399065)
              ·
                refine ⟨19941223718911948411799299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26588298291882597882399065 19941223718911948411799299)
                ·
                  refine ⟨29911835578367922617698949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19941223718911948411799299 29911835578367922617698949)
                  ·
                    refine ⟨5608469170943985490818553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29911835578367922617698949 5608469170943985490818553)
                    ·
                      refine ⟨4206351878207989118113915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5608469170943985490818553 4206351878207989118113915)
                      ·
                        rfl

theorem cell23_8191841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 4, 2].length) (baseStart_8191841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8191841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8191841 prefixEnd_8191841 := by exact prefixLift 8191841
  have htrace : WordTrace (prefixWord ++ tailWord_8191841) baseStart_8191841 baseEnd_8191841 := by
    simpa [prefixWord, tailWord_8191841, baseEnd_8191841] using wordTrace_append hprefix tailTrace_8191841
  have hstable : (prefixWord ++ tailWord_8191841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8191841).length < 2 ^ (prefixWord ++ tailWord_8191841).sum := by decide
  have hdescent : baseEnd_8191841 < baseStart_8191841 := by decide
  rcases family_descends (prefixWord ++ tailWord_8191841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8191867 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 8]
def baseStart_8191867 : Nat := 118140960795 + 8191867 * 2 ^ 59
def prefixEnd_8191867 : Nat := 4983230072969 + 3 ^ 40 * 8191867 * 2
def baseEnd_8191867 : Nat := 4206365228705006016388795

theorem tailTrace_8191867 : CollatzResearch.WordTrace tailWord_8191867 prefixEnd_8191867 4206365228705006016388795 := by
  unfold tailWord_8191867
  simp only [CollatzResearch.WordTrace]
  refine ⟨298781935413272393343893855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199187956942181595562595903 298781935413272393343893855)
  ·
    refine ⟨448172903119908590015840783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298781935413272393343893855 448172903119908590015840783)
    ·
      refine ⟨672259354679862885023761175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448172903119908590015840783 672259354679862885023761175)
      ·
        refine ⟨1008389032019794327535641763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 672259354679862885023761175 1008389032019794327535641763)
        ·
          refine ⟨1512583548029691491303462645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1008389032019794327535641763 1512583548029691491303462645)
          ·
            refine ⟨141804707627783577309699623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1512583548029691491303462645 141804707627783577309699623)
            ·
              refine ⟨212707061441675365964549435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141804707627783577309699623 212707061441675365964549435)
              ·
                refine ⟨319060592162513048946824153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212707061441675365964549435 319060592162513048946824153)
                ·
                  refine ⟨239295444121884786710118115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 319060592162513048946824153 239295444121884786710118115)
                  ·
                    refine ⟨358943166182827180065177173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 239295444121884786710118115 358943166182827180065177173)
                    ·
                      refine ⟨4206365228705006016388795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 358943166182827180065177173 4206365228705006016388795)
                      ·
                        rfl

theorem cell23_8191867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 8].length) (baseStart_8191867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8191867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8191867 prefixEnd_8191867 := by exact prefixLift 8191867
  have htrace : WordTrace (prefixWord ++ tailWord_8191867) baseStart_8191867 baseEnd_8191867 := by
    simpa [prefixWord, tailWord_8191867, baseEnd_8191867] using wordTrace_append hprefix tailTrace_8191867
  have hstable : (prefixWord ++ tailWord_8191867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8191867).length < 2 ^ (prefixWord ++ tailWord_8191867).sum := by decide
  have hdescent : baseEnd_8191867 < baseStart_8191867 := by decide
  rcases family_descends (prefixWord ++ tailWord_8191867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8191898 : List Nat := [3, 1, 1, 4, 2, 2, 2, 3, 5]
def baseStart_8191898 : Nat := 118140960795 + 8191898 * 2 ^ 59
def prefixEnd_8191898 : Nat := 4983230072969 + 3 ^ 40 * 8191898 * 2
def baseEnd_8191898 : Nat := 467375682956143932789017

theorem tailTrace_8191898 : CollatzResearch.WordTrace tailWord_8191898 prefixEnd_8191898 467375682956143932789017 := by
  unfold tailWord_8191898
  simp only [CollatzResearch.WordTrace]
  refine ⟨74695766519040021409568087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199188710717440057092181565 74695766519040021409568087)
  ·
    refine ⟨112043649778560032114352131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74695766519040021409568087 112043649778560032114352131)
    ·
      refine ⟨168065474667840048171528197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112043649778560032114352131 168065474667840048171528197)
      ·
        refine ⟨31512276500220009032161537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168065474667840048171528197 31512276500220009032161537)
        ·
          refine ⟨23634207375165006774121153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31512276500220009032161537 23634207375165006774121153)
          ·
            refine ⟨17725655531373755080590865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23634207375165006774121153 17725655531373755080590865)
            ·
              refine ⟨13294241648530316310443149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17725655531373755080590865 13294241648530316310443149)
              ·
                refine ⟨4985340618198868616416181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13294241648530316310443149 4985340618198868616416181)
                ·
                  refine ⟨467375682956143932789017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4985340618198868616416181 467375682956143932789017)
                  ·
                    rfl

theorem cell23_8191898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 3, 5].length) (baseStart_8191898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8191898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8191898 prefixEnd_8191898 := by exact prefixLift 8191898
  have htrace : WordTrace (prefixWord ++ tailWord_8191898) baseStart_8191898 baseEnd_8191898 := by
    simpa [prefixWord, tailWord_8191898, baseEnd_8191898] using wordTrace_append hprefix tailTrace_8191898
  have hstable : (prefixWord ++ tailWord_8191898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8191898).length < 2 ^ (prefixWord ++ tailWord_8191898).sum := by decide
  have hdescent : baseEnd_8191898 < baseStart_8191898 := by decide
  rcases family_descends (prefixWord ++ tailWord_8191898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8191951 : List Nat := [1, 1, 2, 1, 1, 5, 2, 3, 2, 2, 3]
def baseStart_8191951 : Nat := 118140960795 + 8191951 * 2 ^ 59
def prefixEnd_8191951 : Nat := 4983230072969 + 3 ^ 40 * 8191951 * 2
def baseEnd_8191951 : Nat := 4206408361079983687738409

theorem tailTrace_8191951 : CollatzResearch.WordTrace tailWord_8191951 prefixEnd_8191951 4206408361079983687738409 := by
  unfold tailWord_8191951
  simp only [CollatzResearch.WordTrace]
  refine ⟨298784999144968075689951707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199189999429978717126634471 298784999144968075689951707)
  ·
    refine ⟨448177498717452113534927561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298784999144968075689951707 448177498717452113534927561)
    ·
      refine ⟨336133124038089085151195671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 448177498717452113534927561 336133124038089085151195671)
      ·
        refine ⟨504199686057133627726793507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336133124038089085151195671 504199686057133627726793507)
        ·
          refine ⟨756299529085700441590190261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504199686057133627726793507 756299529085700441590190261)
          ·
            refine ⟨70903080851784416399080337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 756299529085700441590190261 70903080851784416399080337)
            ·
              refine ⟨53177310638838312299310253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70903080851784416399080337 53177310638838312299310253)
              ·
                refine ⟨19941491489564367112241345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53177310638838312299310253 19941491489564367112241345)
                ·
                  refine ⟨14956118617173275334181009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19941491489564367112241345 14956118617173275334181009)
                  ·
                    refine ⟨11217088962879956500635757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14956118617173275334181009 11217088962879956500635757)
                    ·
                      refine ⟨4206408361079983687738409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11217088962879956500635757 4206408361079983687738409)
                      ·
                        rfl

theorem cell23_8191951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 2, 2, 3].length) (baseStart_8191951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8191951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8191951 prefixEnd_8191951 := by exact prefixLift 8191951
  have htrace : WordTrace (prefixWord ++ tailWord_8191951) baseStart_8191951 baseEnd_8191951 := by
    simpa [prefixWord, tailWord_8191951, baseEnd_8191951] using wordTrace_append hprefix tailTrace_8191951
  have hstable : (prefixWord ++ tailWord_8191951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8191951).length < 2 ^ (prefixWord ++ tailWord_8191951).sum := by decide
  have hdescent : baseEnd_8191951 < baseStart_8191951 := by decide
  rcases family_descends (prefixWord ++ tailWord_8191951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8191975 : List Nat := [1, 1, 5, 2, 3, 2, 1, 1, 3, 4]
def baseStart_8191975 : Nat := 118140960795 + 8191975 * 2 ^ 59
def prefixEnd_8191975 : Nat := 4983230072969 + 3 ^ 40 * 8191975 * 2
def baseEnd_8191975 : Nat := 1402140228205230531279433

theorem tailTrace_8191975 : CollatzResearch.WordTrace tailWord_8191975 prefixEnd_8191975 1402140228205230531279433 := by
  unfold tailWord_8191975
  simp only [CollatzResearch.WordTrace]
  refine ⟨298785874496881127788825379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199190582997920751859216919 298785874496881127788825379)
  ·
    refine ⟨448178811745321691683238069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298785874496881127788825379 448178811745321691683238069)
    ·
      refine ⟨42016763601123908595303569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 448178811745321691683238069 42016763601123908595303569)
      ·
        refine ⟨31512572700842931446477677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42016763601123908595303569 31512572700842931446477677)
        ·
          refine ⟨11817214762816099292429129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31512572700842931446477677 11817214762816099292429129)
          ·
            refine ⟨8862911072112074469321847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11817214762816099292429129 8862911072112074469321847)
            ·
              refine ⟨13294366608168111703982771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8862911072112074469321847 13294366608168111703982771)
              ·
                refine ⟨19941549912252167555974157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13294366608168111703982771 19941549912252167555974157)
                ·
                  refine ⟨7478081217094562833490309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19941549912252167555974157 7478081217094562833490309)
                  ·
                    refine ⟨1402140228205230531279433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7478081217094562833490309 1402140228205230531279433)
                    ·
                      rfl

theorem cell23_8191975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_8191975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8191975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8191975 prefixEnd_8191975 := by exact prefixLift 8191975
  have htrace : WordTrace (prefixWord ++ tailWord_8191975) baseStart_8191975 baseEnd_8191975 := by
    simpa [prefixWord, tailWord_8191975, baseEnd_8191975] using wordTrace_append hprefix tailTrace_8191975
  have hstable : (prefixWord ++ tailWord_8191975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8191975).length < 2 ^ (prefixWord ++ tailWord_8191975).sum := by decide
  have hdescent : baseEnd_8191975 < baseStart_8191975 := by decide
  rcases family_descends (prefixWord ++ tailWord_8191975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8192001 : List Nat := [1, 2, 4, 1, 2, 1, 3, 1, 3, 5]
def baseStart_8192001 : Nat := 118140960795 + 8192001 * 2 ^ 59
def prefixEnd_8192001 : Nat := 4983230072969 + 3 ^ 40 * 8192001 * 2
def baseEnd_8192001 : Nat := 1402144678370902830704393

theorem tailTrace_8192001 : CollatzResearch.WordTrace tailWord_8192001 prefixEnd_8192001 1402144678370902830704393 := by
  unfold tailWord_8192001
  simp only [CollatzResearch.WordTrace]
  refine ⟨298786822794786934229271857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199191215196524622819514571 298786822794786934229271857)
  ·
    refine ⟨224090117096090200671953893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298786822794786934229271857 224090117096090200671953893)
    ·
      refine ⟨42016896955516912625991355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224090117096090200671953893 42016896955516912625991355)
      ·
        refine ⟨63025345433275368938987033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42016896955516912625991355 63025345433275368938987033)
        ·
          refine ⟨47269009074956526704240275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63025345433275368938987033 47269009074956526704240275)
          ·
            refine ⟨70903513612434790056360413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47269009074956526704240275 70903513612434790056360413)
            ·
              refine ⟨26588817604663046271135155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70903513612434790056360413 26588817604663046271135155)
              ·
                refine ⟨39883226406994569406702733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26588817604663046271135155 39883226406994569406702733)
                ·
                  refine ⟨14956209902622963527513525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39883226406994569406702733 14956209902622963527513525)
                  ·
                    refine ⟨1402144678370902830704393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14956209902622963527513525 1402144678370902830704393)
                    ·
                      rfl

theorem cell23_8192001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_8192001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8192001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8192001 prefixEnd_8192001 := by exact prefixLift 8192001
  have htrace : WordTrace (prefixWord ++ tailWord_8192001) baseStart_8192001 baseEnd_8192001 := by
    simpa [prefixWord, tailWord_8192001, baseEnd_8192001] using wordTrace_append hprefix tailTrace_8192001
  have hstable : (prefixWord ++ tailWord_8192001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8192001).length < 2 ^ (prefixWord ++ tailWord_8192001).sum := by decide
  have hdescent : baseEnd_8192001 < baseStart_8192001 := by decide
  rcases family_descends (prefixWord ++ tailWord_8192001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8192044 : List Nat := [2, 2, 1, 1, 1, 2, 2, 12]
def baseStart_8192044 : Nat := 118140960795 + 8192044 * 2 ^ 59
def prefixEnd_8192044 : Nat := 4983230072969 + 3 ^ 40 * 8192044 * 2
def baseEnd_8192044 : Nat := 155794670917809326810203

theorem tailTrace_8192044 : CollatzResearch.WordTrace tailWord_8192044 prefixEnd_8192044 155794670917809326810203 := by
  unfold tailWord_8192044
  simp only [CollatzResearch.WordTrace]
  refine ⟨149394195566815576286543593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199192260755754101715391457 149394195566815576286543593)
  ·
    refine ⟨112045646675111682214907695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149394195566815576286543593 112045646675111682214907695)
    ·
      refine ⟨168068470012667523322361543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112045646675111682214907695 168068470012667523322361543)
      ·
        refine ⟨252102705019001284983542315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168068470012667523322361543 252102705019001284983542315)
        ·
          refine ⟨378154057528501927475313473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252102705019001284983542315 378154057528501927475313473)
          ·
            refine ⟨283615543146376445606485105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 378154057528501927475313473 283615543146376445606485105)
            ·
              refine ⟨212711657359782334204863829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283615543146376445606485105 212711657359782334204863829)
              ·
                refine ⟨155794670917809326810203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 212711657359782334204863829 155794670917809326810203)
                ·
                  rfl

theorem cell23_8192044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 12].length) (baseStart_8192044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8192044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8192044 prefixEnd_8192044 := by exact prefixLift 8192044
  have htrace : WordTrace (prefixWord ++ tailWord_8192044) baseStart_8192044 baseEnd_8192044 := by
    simpa [prefixWord, tailWord_8192044, baseEnd_8192044] using wordTrace_append hprefix tailTrace_8192044
  have hstable : (prefixWord ++ tailWord_8192044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8192044).length < 2 ^ (prefixWord ++ tailWord_8192044).sum := by decide
  have hdescent : baseEnd_8192044 < baseStart_8192044 := by decide
  rcases family_descends (prefixWord ++ tailWord_8192044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8192048 : List Nat := [2, 1, 1, 1, 2, 5, 2, 3, 2, 4]
def baseStart_8192048 : Nat := 118140960795 + 8192048 * 2 ^ 59
def prefixEnd_8192048 : Nat := 4983230072969 + 3 ^ 40 * 8192048 * 2
def baseEnd_8192048 : Nat := 1402152722901156602741821

theorem tailTrace_8192048 : CollatzResearch.WordTrace tailWord_8192048 prefixEnd_8192048 1402152722901156602741821 := by
  unfold tailWord_8192048
  simp only [CollatzResearch.WordTrace]
  refine ⟨149394268512808330628116399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199192358017077774170821865 149394268512808330628116399)
  ·
    refine ⟨224091402769212495942174599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149394268512808330628116399 224091402769212495942174599)
    ·
      refine ⟨336137104153818743913261899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224091402769212495942174599 336137104153818743913261899)
      ·
        refine ⟨504205656230728115869892849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336137104153818743913261899 504205656230728115869892849)
        ·
          refine ⟨378154242173046086902419637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 504205656230728115869892849 378154242173046086902419637)
          ·
            refine ⟨35451960203723070647101841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 378154242173046086902419637 35451960203723070647101841)
            ·
              refine ⟨26588970152792302985326381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35451960203723070647101841 26588970152792302985326381)
              ·
                refine ⟨9970863807297113619497393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26588970152792302985326381 9970863807297113619497393)
                ·
                  refine ⟨7478147855472835214623045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9970863807297113619497393 7478147855472835214623045)
                  ·
                    refine ⟨1402152722901156602741821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7478147855472835214623045 1402152722901156602741821)
                    ·
                      rfl

theorem cell23_8192048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 3, 2, 4].length) (baseStart_8192048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8192048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8192048 prefixEnd_8192048 := by exact prefixLift 8192048
  have htrace : WordTrace (prefixWord ++ tailWord_8192048) baseStart_8192048 baseEnd_8192048 := by
    simpa [prefixWord, tailWord_8192048, baseEnd_8192048] using wordTrace_append hprefix tailTrace_8192048
  have hstable : (prefixWord ++ tailWord_8192048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8192048).length < 2 ^ (prefixWord ++ tailWord_8192048).sum := by decide
  have hdescent : baseEnd_8192048 < baseStart_8192048 := by decide
  rcases family_descends (prefixWord ++ tailWord_8192048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8192051 : List Nat := [1, 1, 1, 2, 4, 1, 3, 3, 1, 2, 4]
def baseStart_8192051 : Nat := 118140960795 + 8192051 * 2 ^ 59
def prefixEnd_8192051 : Nat := 4983230072969 + 3 ^ 40 * 8192051 * 2
def baseEnd_8192051 : Nat := 4206459709145433296487949

theorem tailTrace_8192051 : CollatzResearch.WordTrace tailWord_8192051 prefixEnd_8192051 4206459709145433296487949 := by
  unfold tailWord_8192051
  simp only [CollatzResearch.WordTrace]
  refine ⟨298788646444605792768592007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199192430963070528512394671 298788646444605792768592007)
  ·
    refine ⟨448182969666908689152888011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298788646444605792768592007 448182969666908689152888011)
    ·
      refine ⟨672274454500363033729332017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448182969666908689152888011 672274454500363033729332017)
      ·
        refine ⟨504205840875272275296999013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 672274454500363033729332017 504205840875272275296999013)
        ·
          refine ⟨94538595164113551618187315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 504205840875272275296999013 94538595164113551618187315)
          ·
            refine ⟨141807892746170327427280973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94538595164113551618187315 141807892746170327427280973)
            ·
              refine ⟨53177959779813872785230365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141807892746170327427280973 53177959779813872785230365)
              ·
                refine ⟨19941734917430202294461387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53177959779813872785230365 19941734917430202294461387)
                ·
                  refine ⟨29912602376145303441692081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19941734917430202294461387 29912602376145303441692081)
                  ·
                    refine ⟨22434451782108977581269061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29912602376145303441692081 22434451782108977581269061)
                    ·
                      refine ⟨4206459709145433296487949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22434451782108977581269061 4206459709145433296487949)
                      ·
                        rfl

theorem cell23_8192051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 2, 4].length) (baseStart_8192051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8192051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8192051 prefixEnd_8192051 := by exact prefixLift 8192051
  have htrace : WordTrace (prefixWord ++ tailWord_8192051) baseStart_8192051 baseEnd_8192051 := by
    simpa [prefixWord, tailWord_8192051, baseEnd_8192051] using wordTrace_append hprefix tailTrace_8192051
  have hstable : (prefixWord ++ tailWord_8192051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8192051).length < 2 ^ (prefixWord ++ tailWord_8192051).sum := by decide
  have hdescent : baseEnd_8192051 < baseStart_8192051 := by decide
  rcases family_descends (prefixWord ++ tailWord_8192051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8192058 : List Nat := [3, 1, 1, 1, 3, 1, 1, 6, 1, 2, 3]
def baseStart_8192058 : Nat := 118140960795 + 8192058 * 2 ^ 59
def prefixEnd_8192058 : Nat := 4983230072969 + 3 ^ 40 * 8192058 * 2
def baseEnd_8192058 : Nat := 4206463303510014769100417

theorem tailTrace_8192058 : CollatzResearch.WordTrace tailWord_8192058 prefixEnd_8192058 4206463303510014769100417 := by
  unfold tailWord_8192058
  simp only [CollatzResearch.WordTrace]
  refine ⟨74697225438895108241024207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199192601170386955309397885 74697225438895108241024207)
  ·
    refine ⟨112045838158342662361536311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74697225438895108241024207 112045838158342662361536311)
    ·
      refine ⟨168068757237513993542304467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112045838158342662361536311 168068757237513993542304467)
      ·
        refine ⟨252103135856270990313456701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168068757237513993542304467 252103135856270990313456701)
        ·
          refine ⟨94538675946101621367546263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252103135856270990313456701 94538675946101621367546263)
          ·
            refine ⟨141808013919152432051319395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94538675946101621367546263 141808013919152432051319395)
            ·
              refine ⟨212712020878728648076979093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141808013919152432051319395 212712020878728648076979093)
              ·
                refine ⟨9970875978690405378608395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 212712020878728648076979093 9970875978690405378608395)
                ·
                  refine ⟨14956313968035608067912593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9970875978690405378608395 14956313968035608067912593)
                  ·
                    refine ⟨11217235476026706050934445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14956313968035608067912593 11217235476026706050934445)
                    ·
                      refine ⟨4206463303510014769100417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11217235476026706050934445 4206463303510014769100417)
                      ·
                        rfl

theorem cell23_8192058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 6, 1, 2, 3].length) (baseStart_8192058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8192058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8192058 prefixEnd_8192058 := by exact prefixLift 8192058
  have htrace : WordTrace (prefixWord ++ tailWord_8192058) baseStart_8192058 baseEnd_8192058 := by
    simpa [prefixWord, tailWord_8192058, baseEnd_8192058] using wordTrace_append hprefix tailTrace_8192058
  have hstable : (prefixWord ++ tailWord_8192058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8192058).length < 2 ^ (prefixWord ++ tailWord_8192058).sum := by decide
  have hdescent : baseEnd_8192058 < baseStart_8192058 := by decide
  rcases family_descends (prefixWord ++ tailWord_8192058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8192082 : List Nat := [3, 2, 2, 1, 4, 2, 1, 2, 2, 4]
def baseStart_8192082 : Nat := 118140960795 + 8192082 * 2 ^ 59
def prefixEnd_8192082 : Nat := 4983230072969 + 3 ^ 40 * 8192082 * 2
def baseEnd_8192082 : Nat := 1402158542348574225066769

theorem tailTrace_8192082 : CollatzResearch.WordTrace tailWord_8192082 prefixEnd_8192082 1402158542348574225066769 := by
  unfold tailWord_8192082
  simp only [CollatzResearch.WordTrace]
  refine ⟨74697444276873371265742625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199193184738328990041980333 74697444276873371265742625)
  ·
    refine ⟨56023083207655028449306969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74697444276873371265742625 56023083207655028449306969)
    ·
      refine ⟨42017312405741271336980227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56023083207655028449306969 42017312405741271336980227)
      ·
        refine ⟨63025968608611907005470341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42017312405741271336980227 63025968608611907005470341)
        ·
          refine ⟨11817369114114732563525689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63025968608611907005470341 11817369114114732563525689)
          ·
            refine ⟨8863026835586049422644267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11817369114114732563525689 8863026835586049422644267)
            ·
              refine ⟨13294540253379074133966401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8863026835586049422644267 13294540253379074133966401)
              ·
                refine ⟨9970905190034305600474801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13294540253379074133966401 9970905190034305600474801)
                ·
                  refine ⟨7478178892525729200356101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9970905190034305600474801 7478178892525729200356101)
                  ·
                    refine ⟨1402158542348574225066769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7478178892525729200356101 1402158542348574225066769)
                    ·
                      rfl

theorem cell23_8192082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_8192082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8192082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8192082 prefixEnd_8192082 := by exact prefixLift 8192082
  have htrace : WordTrace (prefixWord ++ tailWord_8192082) baseStart_8192082 baseEnd_8192082 := by
    simpa [prefixWord, tailWord_8192082, baseEnd_8192082] using wordTrace_append hprefix tailTrace_8192082
  have hstable : (prefixWord ++ tailWord_8192082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8192082).length < 2 ^ (prefixWord ++ tailWord_8192082).sum := by decide
  have hdescent : baseEnd_8192082 < baseStart_8192082 := by decide
  rcases family_descends (prefixWord ++ tailWord_8192082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8192118 : List Nat := [5, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5]
def baseStart_8192118 : Nat := 118140960795 + 8192118 * 2 ^ 59
def prefixEnd_8192118 : Nat := 4983230072969 + 3 ^ 40 * 8192118 * 2
def baseEnd_8192118 : Nat := 4206494112349284534350141

theorem tailTrace_8192118 : CollatzResearch.WordTrace tailWord_8192118 prefixEnd_8192118 4206494112349284534350141 := by
  unfold tailWord_8192118
  simp only [CollatzResearch.WordTrace]
  refine ⟨18674443133460191450705063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199194060090242042140854005 18674443133460191450705063)
  ·
    refine ⟨28011664700190287176057595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18674443133460191450705063 28011664700190287176057595)
    ·
      refine ⟨42017497050285430764086393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28011664700190287176057595 42017497050285430764086393)
      ·
        refine ⟨31513122787714073073064795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42017497050285430764086393 31513122787714073073064795)
        ·
          refine ⟨47269684181571109609597193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31513122787714073073064795 47269684181571109609597193)
          ·
            refine ⟨35452263136178332207197895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47269684181571109609597193 35452263136178332207197895)
            ·
              refine ⟨53178394704267498310796843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35452263136178332207197895 53178394704267498310796843)
              ·
                refine ⟨79767592056401247466195265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53178394704267498310796843 79767592056401247466195265)
                ·
                  refine ⟨59825694042300935599646449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79767592056401247466195265 59825694042300935599646449)
                  ·
                    refine ⟨44869270531725701699734837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59825694042300935599646449 44869270531725701699734837)
                    ·
                      refine ⟨4206494112349284534350141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44869270531725701699734837 4206494112349284534350141)
                      ·
                        rfl

theorem cell23_8192118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_8192118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8192118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8192118 prefixEnd_8192118 := by exact prefixLift 8192118
  have htrace : WordTrace (prefixWord ++ tailWord_8192118) baseStart_8192118 baseEnd_8192118 := by
    simpa [prefixWord, tailWord_8192118, baseEnd_8192118] using wordTrace_append hprefix tailTrace_8192118
  have hstable : (prefixWord ++ tailWord_8192118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8192118).length < 2 ^ (prefixWord ++ tailWord_8192118).sum := by decide
  have hdescent : baseEnd_8192118 < baseStart_8192118 := by decide
  rcases family_descends (prefixWord ++ tailWord_8192118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8192128 : List Nat := [2, 1, 1, 2, 1, 3, 1, 3, 3, 4, 2]
def baseStart_8192128 : Nat := 118140960795 + 8192128 * 2 ^ 59
def prefixEnd_8192128 : Nat := 4983230072969 + 3 ^ 40 * 8192128 * 2
def baseEnd_8192128 : Nat := 4206499247155829495225095

theorem tailTrace_8192128 : CollatzResearch.WordTrace tailWord_8192128 prefixEnd_8192128 4206499247155829495225095 := by
  unfold tailWord_8192128
  simp only [CollatzResearch.WordTrace]
  refine ⟨149395727432663417459572519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199194303243551223279430025 149395727432663417459572519)
  ·
    refine ⟨224093591148995126189358779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149395727432663417459572519 224093591148995126189358779)
    ·
      refine ⟨336140386723492689284038169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224093591148995126189358779 336140386723492689284038169)
      ·
        refine ⟨252105290042619516963028627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336140386723492689284038169 252105290042619516963028627)
        ·
          refine ⟨378157935063929275444542941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252105290042619516963028627 378157935063929275444542941)
          ·
            refine ⟨141809225648973478291703603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 378157935063929275444542941 141809225648973478291703603)
            ·
              refine ⟨212713838473460217437555405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141809225648973478291703603 212713838473460217437555405)
              ·
                refine ⟨79767689427547581539083277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 212713838473460217437555405 79767689427547581539083277)
                ·
                  refine ⟨29912883535330343077156229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79767689427547581539083277 29912883535330343077156229)
                  ·
                    refine ⟨5608665662874439326966793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29912883535330343077156229 5608665662874439326966793)
                    ·
                      refine ⟨4206499247155829495225095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5608665662874439326966793 4206499247155829495225095)
                      ·
                        rfl

theorem cell23_8192128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 3, 4, 2].length) (baseStart_8192128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8192128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8192128 prefixEnd_8192128 := by exact prefixLift 8192128
  have htrace : WordTrace (prefixWord ++ tailWord_8192128) baseStart_8192128 baseEnd_8192128 := by
    simpa [prefixWord, tailWord_8192128, baseEnd_8192128] using wordTrace_append hprefix tailTrace_8192128
  have hstable : (prefixWord ++ tailWord_8192128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8192128).length < 2 ^ (prefixWord ++ tailWord_8192128).sum := by decide
  have hdescent : baseEnd_8192128 < baseStart_8192128 := by decide
  rcases family_descends (prefixWord ++ tailWord_8192128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8192131 : List Nat := [1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 5]
def baseStart_8192131 : Nat := 118140960795 + 8192131 * 2 ^ 59
def prefixEnd_8192131 : Nat := 4983230072969 + 3 ^ 40 * 8192131 * 2
def baseEnd_8192131 : Nat := 4206500787597792983487581

theorem tailTrace_8192131 : CollatzResearch.WordTrace tailWord_8192131 prefixEnd_8192131 4206500787597792983487581 := by
  unfold tailWord_8192131
  simp only [CollatzResearch.WordTrace]
  refine ⟨298791564284315966431504247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199194376189543977621002831 298791564284315966431504247)
  ·
    refine ⟨448187346426473949647256371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298791564284315966431504247 448187346426473949647256371)
    ·
      refine ⟨672281019639710924470884557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448187346426473949647256371 672281019639710924470884557)
      ·
        refine ⟨252105382364891596676581709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 672281019639710924470884557 252105382364891596676581709)
        ·
          refine ⟨94539518386834348753718141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252105382364891596676581709 94539518386834348753718141)
          ·
            refine ⟨35452319395062880782644303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94539518386834348753718141 35452319395062880782644303)
            ·
              refine ⟨53178479092594321173966455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35452319395062880782644303 53178479092594321173966455)
              ·
                refine ⟨79767718638891481760949683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53178479092594321173966455 79767718638891481760949683)
                ·
                  refine ⟨119651577958337222641424525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79767718638891481760949683 119651577958337222641424525)
                  ·
                    refine ⟨44869341734376458490534197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 119651577958337222641424525 44869341734376458490534197)
                    ·
                      refine ⟨4206500787597792983487581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44869341734376458490534197 4206500787597792983487581)
                      ·
                        rfl

theorem cell23_8192131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 5].length) (baseStart_8192131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8192131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8192131 prefixEnd_8192131 := by exact prefixLift 8192131
  have htrace : WordTrace (prefixWord ++ tailWord_8192131) baseStart_8192131 baseEnd_8192131 := by
    simpa [prefixWord, tailWord_8192131, baseEnd_8192131] using wordTrace_append hprefix tailTrace_8192131
  have hstable : (prefixWord ++ tailWord_8192131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8192131).length < 2 ^ (prefixWord ++ tailWord_8192131).sum := by decide
  have hdescent : baseEnd_8192131 < baseStart_8192131 := by decide
  rcases family_descends (prefixWord ++ tailWord_8192131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8192150 : List Nat := [5, 3, 2, 1, 1, 2, 2, 1, 2, 4]
def baseStart_8192150 : Nat := 118140960795 + 8192150 * 2 ^ 59
def prefixEnd_8192150 : Nat := 4983230072969 + 3 ^ 40 * 8192150 * 2
def baseEnd_8192150 : Nat := 1402170181243409469716665

theorem tailTrace_8192150 : CollatzResearch.WordTrace tailWord_8192150 prefixEnd_8192150 1402170181243409469716665 := by
  unfold tailWord_8192150
  simp only [CollatzResearch.WordTrace]
  refine ⟨18674516079452945792277869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199194838180831421784297269 18674516079452945792277869)
  ·
    refine ⟨7002943529794854672104201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18674516079452945792277869 7002943529794854672104201)
    ·
      refine ⟨5252207647346141004078151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7002943529794854672104201 5252207647346141004078151)
      ·
        refine ⟨7878311471019211506117227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5252207647346141004078151 7878311471019211506117227)
        ·
          refine ⟨11817467206528817259175841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7878311471019211506117227 11817467206528817259175841)
          ·
            refine ⟨8863100404896612944381881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11817467206528817259175841 8863100404896612944381881)
            ·
              refine ⟨6647325303672459708286411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8863100404896612944381881 6647325303672459708286411)
              ·
                refine ⟨9970987955508689562429617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6647325303672459708286411 9970987955508689562429617)
                ·
                  refine ⟨7478240966631517171822213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9970987955508689562429617 7478240966631517171822213)
                  ·
                    refine ⟨1402170181243409469716665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7478240966631517171822213 1402170181243409469716665)
                    ·
                      rfl

theorem cell23_8192150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_8192150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8192150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8192150 prefixEnd_8192150 := by exact prefixLift 8192150
  have htrace : WordTrace (prefixWord ++ tailWord_8192150) baseStart_8192150 baseEnd_8192150 := by
    simpa [prefixWord, tailWord_8192150, baseEnd_8192150] using wordTrace_append hprefix tailTrace_8192150
  have hstable : (prefixWord ++ tailWord_8192150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8192150).length < 2 ^ (prefixWord ++ tailWord_8192150).sum := by decide
  have hdescent : baseEnd_8192150 < baseStart_8192150 := by decide
  rcases family_descends (prefixWord ++ tailWord_8192150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8192218 : List Nat := [3, 1, 1, 2, 2, 1, 2, 2, 4, 1, 4]
def baseStart_8192218 : Nat := 118140960795 + 8192218 * 2 ^ 59
def prefixEnd_8192218 : Nat := 4983230072969 + 3 ^ 40 * 8192218 * 2
def baseEnd_8192218 : Nat := 4206545460414734143099681

theorem tailTrace_8192218 : CollatzResearch.WordTrace tailWord_8192218 prefixEnd_8192218 4206545460414734143099681 := by
  unfold tailWord_8192218
  simp only [CollatzResearch.WordTrace]
  refine ⟨74698684358750195072480327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199196491623333853526614205 74698684358750195072480327)
  ·
    refine ⟨112048026538125292608720491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74698684358750195072480327 112048026538125292608720491)
    ·
      refine ⟨168072039807187938913080737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112048026538125292608720491 168072039807187938913080737)
      ·
        refine ⟨126054029855390954184810553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168072039807187938913080737 126054029855390954184810553)
        ·
          refine ⟨94540522391543215638607915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126054029855390954184810553 94540522391543215638607915)
          ·
            refine ⟨141810783587314823457911873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94540522391543215638607915 141810783587314823457911873)
            ·
              refine ⟨106358087690486117593433905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141810783587314823457911873 106358087690486117593433905)
              ·
                refine ⟨79768565767864588195075429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106358087690486117593433905 79768565767864588195075429)
                ·
                  refine ⟨14956606081474610286576643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79768565767864588195075429 14956606081474610286576643)
                  ·
                    refine ⟨22434909122211915429864965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14956606081474610286576643 22434909122211915429864965)
                    ·
                      refine ⟨4206545460414734143099681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22434909122211915429864965 4206545460414734143099681)
                      ·
                        rfl

theorem cell23_8192218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_8192218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8192218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8192218 prefixEnd_8192218 := by exact prefixLift 8192218
  have htrace : WordTrace (prefixWord ++ tailWord_8192218) baseStart_8192218 baseEnd_8192218 := by
    simpa [prefixWord, tailWord_8192218, baseEnd_8192218] using wordTrace_append hprefix tailTrace_8192218
  have hstable : (prefixWord ++ tailWord_8192218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8192218).length < 2 ^ (prefixWord ++ tailWord_8192218).sum := by decide
  have hdescent : baseEnd_8192218 < baseStart_8192218 := by decide
  rcases family_descends (prefixWord ++ tailWord_8192218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8192251 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 7]
def baseStart_8192251 : Nat := 118140960795 + 8192251 * 2 ^ 59
def prefixEnd_8192251 : Nat := 4983230072969 + 3 ^ 40 * 8192251 * 2
def baseEnd_8192251 : Nat := 4206562405276332513987029

theorem tailTrace_8192251 : CollatzResearch.WordTrace tailWord_8192251 prefixEnd_8192251 4206562405276332513987029 := by
  unfold tailWord_8192251
  simp only [CollatzResearch.WordTrace]
  refine ⟨298795941043881226925872607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199197294029254151283915071 298795941043881226925872607)
  ·
    refine ⟨448193911565821840388808911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298795941043881226925872607 448193911565821840388808911)
    ·
      refine ⟨672290867348732760583213367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448193911565821840388808911 672290867348732760583213367)
      ·
        refine ⟨1008436301023099140874820051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 672290867348732760583213367 1008436301023099140874820051)
        ·
          refine ⟨1512654451534648711312230077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1008436301023099140874820051 1512654451534648711312230077)
          ·
            refine ⟨567245419325493266742086279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1512654451534648711312230077 567245419325493266742086279)
            ·
              refine ⟨850868128988239900113129419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 567245419325493266742086279 850868128988239900113129419)
              ·
                refine ⟨1276302193482359850169694129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 850868128988239900113129419 1276302193482359850169694129)
                ·
                  refine ⟨957226645111769887627270597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1276302193482359850169694129 957226645111769887627270597)
                  ·
                    refine ⟨179479995958456853930113237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 957226645111769887627270597 179479995958456853930113237)
                    ·
                      refine ⟨4206562405276332513987029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 179479995958456853930113237 4206562405276332513987029)
                      ·
                        rfl

theorem cell23_8192251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 7].length) (baseStart_8192251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8192251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8192251 prefixEnd_8192251 := by exact prefixLift 8192251
  have htrace : WordTrace (prefixWord ++ tailWord_8192251) baseStart_8192251 baseEnd_8192251 := by
    simpa [prefixWord, tailWord_8192251, baseEnd_8192251] using wordTrace_append hprefix tailTrace_8192251
  have hstable : (prefixWord ++ tailWord_8192251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8192251).length < 2 ^ (prefixWord ++ tailWord_8192251).sum := by decide
  have hdescent : baseEnd_8192251 < baseStart_8192251 := by decide
  rcases family_descends (prefixWord ++ tailWord_8192251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8192296 : List Nat := [2, 1, 5, 1, 3, 2, 1, 3, 1, 4]
def baseStart_8192296 : Nat := 118140960795 + 8192296 * 2 ^ 59
def prefixEnd_8192296 : Nat := 4983230072969 + 3 ^ 40 * 8192296 * 2
def baseEnd_8192296 : Nat := 1402195170635261612641441

theorem tailTrace_8192296 : CollatzResearch.WordTrace tailWord_8192296 prefixEnd_8192296 1402195170635261612641441 := by
  unfold tailWord_8192296
  simp only [CollatzResearch.WordTrace]
  refine ⟨149398791164359099805630371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199198388219145466407507161 149398791164359099805630371)
  ·
    refine ⟨224098186746538649708445557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149398791164359099805630371 224098186746538649708445557)
    ·
      refine ⟨21009205007487998410166771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 224098186746538649708445557 21009205007487998410166771)
      ·
        refine ⟨31513807511231997615250157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21009205007487998410166771 31513807511231997615250157)
        ·
          refine ⟨11817677816711999105718809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31513807511231997615250157 11817677816711999105718809)
          ·
            refine ⟨8863258362533999329289107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11817677816711999105718809 8863258362533999329289107)
            ·
              refine ⟨13294887543800998993933661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8863258362533999329289107 13294887543800998993933661)
              ·
                refine ⟨4985582828925374622725123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13294887543800998993933661 4985582828925374622725123)
                ·
                  refine ⟨7478374243388061934087685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4985582828925374622725123 7478374243388061934087685)
                  ·
                    refine ⟨1402195170635261612641441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7478374243388061934087685 1402195170635261612641441)
                    ·
                      rfl

theorem cell23_8192296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_8192296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8192296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8192296 prefixEnd_8192296 := by exact prefixLift 8192296
  have htrace : WordTrace (prefixWord ++ tailWord_8192296) baseStart_8192296 baseEnd_8192296 := by
    simpa [prefixWord, tailWord_8192296, baseEnd_8192296] using wordTrace_append hprefix tailTrace_8192296
  have hstable : (prefixWord ++ tailWord_8192296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8192296).length < 2 ^ (prefixWord ++ tailWord_8192296).sum := by decide
  have hdescent : baseEnd_8192296 < baseStart_8192296 := by decide
  rcases family_descends (prefixWord ++ tailWord_8192296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8192355 : List Nat := [1, 1, 1, 5, 2, 1, 3, 2, 1, 2, 4]
def baseStart_8192355 : Nat := 118140960795 + 8192355 * 2 ^ 59
def prefixEnd_8192355 : Nat := 4983230072969 + 3 ^ 40 * 8192355 * 2
def baseEnd_8192355 : Nat := 4206615807264400107086551

theorem tailTrace_8192355 : CollatzResearch.WordTrace tailWord_8192355 prefixEnd_8192355 4206615807264400107086551 := by
  unfold tailWord_8192355
  simp only [CollatzResearch.WordTrace]
  refine ⟨298799734235504452687658519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199199822823669635125105679 298799734235504452687658519)
  ·
    refine ⟨448199601353256679031487779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298799734235504452687658519 448199601353256679031487779)
    ·
      refine ⟨672299402029885018547231669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448199601353256679031487779 672299402029885018547231669)
      ·
        refine ⟨63028068940301720488802969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 672299402029885018547231669 63028068940301720488802969)
        ·
          refine ⟨47271051705226290366602227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63028068940301720488802969 47271051705226290366602227)
          ·
            refine ⟨70906577557839435549903341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47271051705226290366602227 70906577557839435549903341)
            ·
              refine ⟨26589966584189788331213753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70906577557839435549903341 26589966584189788331213753)
              ·
                refine ⟨19942474938142341248410315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26589966584189788331213753 19942474938142341248410315)
                ·
                  refine ⟨29913712407213511872615473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19942474938142341248410315 29913712407213511872615473)
                  ·
                    refine ⟨22435284305410133904461605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29913712407213511872615473 22435284305410133904461605)
                    ·
                      refine ⟨4206615807264400107086551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22435284305410133904461605 4206615807264400107086551)
                      ·
                        rfl

theorem cell23_8192355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_8192355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8192355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8192355 prefixEnd_8192355 := by exact prefixLift 8192355
  have htrace : WordTrace (prefixWord ++ tailWord_8192355) baseStart_8192355 baseEnd_8192355 := by
    simpa [prefixWord, tailWord_8192355, baseEnd_8192355] using wordTrace_append hprefix tailTrace_8192355
  have hstable : (prefixWord ++ tailWord_8192355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8192355).length < 2 ^ (prefixWord ++ tailWord_8192355).sum := by decide
  have hdescent : baseEnd_8192355 < baseStart_8192355 := by decide
  rcases family_descends (prefixWord ++ tailWord_8192355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8192359 : List Nat := [1, 1, 5, 1, 3, 2, 3, 1, 1, 1, 4]
def baseStart_8192359 : Nat := 118140960795 + 8192359 * 2 ^ 59
def prefixEnd_8192359 : Nat := 4983230072969 + 3 ^ 40 * 8192359 * 2
def baseEnd_8192359 : Nat := 4206617861187018091436533

theorem tailTrace_8192359 : CollatzResearch.WordTrace tailWord_8192359 prefixEnd_8192359 4206617861187018091436533 := by
  unfold tailWord_8192359
  simp only [CollatzResearch.WordTrace]
  refine ⟨298799880127489961370804131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199199920084993307580536087 298799880127489961370804131)
  ·
    refine ⟨448199820191234942056206197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298799880127489961370804131 448199820191234942056206197)
    ·
      refine ⟨42018733142928275817769331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 448199820191234942056206197 42018733142928275817769331)
      ·
        refine ⟨63028099714392413726653997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42018733142928275817769331 63028099714392413726653997)
        ·
          refine ⟨23635537392897155147495249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63028099714392413726653997 23635537392897155147495249)
          ·
            refine ⟨17726653044672866360621437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23635537392897155147495249 17726653044672866360621437)
            ·
              refine ⟨6647494891752324885233039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17726653044672866360621437 6647494891752324885233039)
              ·
                refine ⟨9971242337628487327849559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6647494891752324885233039 9971242337628487327849559)
                ·
                  refine ⟨14956863506442730991774339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9971242337628487327849559 14956863506442730991774339)
                  ·
                    refine ⟨22435295259664096487661509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14956863506442730991774339 22435295259664096487661509)
                    ·
                      refine ⟨4206617861187018091436533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22435295259664096487661509 4206617861187018091436533)
                      ·
                        rfl

theorem cell23_8192359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 3, 1, 1, 1, 4].length) (baseStart_8192359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8192359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8192359 prefixEnd_8192359 := by exact prefixLift 8192359
  have htrace : WordTrace (prefixWord ++ tailWord_8192359) baseStart_8192359 baseEnd_8192359 := by
    simpa [prefixWord, tailWord_8192359, baseEnd_8192359] using wordTrace_append hprefix tailTrace_8192359
  have hstable : (prefixWord ++ tailWord_8192359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8192359).length < 2 ^ (prefixWord ++ tailWord_8192359).sum := by decide
  have hdescent : baseEnd_8192359 < baseStart_8192359 := by decide
  rcases family_descends (prefixWord ++ tailWord_8192359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8192362 : List Nat := [3, 1, 3, 3, 1, 1, 3, 1, 1, 1, 5]
def baseStart_8192362 : Nat := 118140960795 + 8192362 * 2 ^ 59
def prefixEnd_8192362 : Nat := 4983230072969 + 3 ^ 40 * 8192362 * 2
def baseEnd_8192362 : Nat := 4206619401628981579699019

theorem tailTrace_8192362 : CollatzResearch.WordTrace tailWord_8192362 prefixEnd_8192362 4206619401628981579699019 := by
  unfold tailWord_8192362
  simp only [CollatzResearch.WordTrace]
  refine ⟨74699997386619773220790835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199199993030986061922108893 74699997386619773220790835)
  ·
    refine ⟨112049996079929659831186253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74699997386619773220790835 112049996079929659831186253)
    ·
      refine ⟨42018748529973622436694845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112049996079929659831186253 42018748529973622436694845)
      ·
        refine ⟨15757030698740108413760567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42018748529973622436694845 15757030698740108413760567)
        ·
          refine ⟨23635546048110162620640851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15757030698740108413760567 23635546048110162620640851)
          ·
            refine ⟨35453319072165243930961277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23635546048110162620640851 35453319072165243930961277)
            ·
              refine ⟨13294994652061966474110479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35453319072165243930961277 13294994652061966474110479)
              ·
                refine ⟨19942491978092949711165719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13294994652061966474110479 19942491978092949711165719)
                ·
                  refine ⟨29913737967139424566748579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19942491978092949711165719 29913737967139424566748579)
                  ·
                    refine ⟨44870606950709136850122869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29913737967139424566748579 44870606950709136850122869)
                    ·
                      refine ⟨4206619401628981579699019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44870606950709136850122869 4206619401628981579699019)
                      ·
                        rfl

theorem cell23_8192362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_8192362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8192362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8192362 prefixEnd_8192362 := by exact prefixLift 8192362
  have htrace : WordTrace (prefixWord ++ tailWord_8192362) baseStart_8192362 baseEnd_8192362 := by
    simpa [prefixWord, tailWord_8192362, baseEnd_8192362] using wordTrace_append hprefix tailTrace_8192362
  have hstable : (prefixWord ++ tailWord_8192362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8192362).length < 2 ^ (prefixWord ++ tailWord_8192362).sum := by decide
  have hdescent : baseEnd_8192362 < baseStart_8192362 := by decide
  rcases family_descends (prefixWord ++ tailWord_8192362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8192392 : List Nat := [2, 1, 3, 3, 1, 1, 4, 1, 1, 3, 3]
def baseStart_8192392 : Nat := 118140960795 + 8192392 * 2 ^ 59
def prefixEnd_8192392 : Nat := 4983230072969 + 3 ^ 40 * 8192392 * 2
def baseEnd_8192392 : Nat := 4206634806048616462323881

theorem tailTrace_8192392 : CollatzResearch.WordTrace tailWord_8192392 prefixEnd_8192392 4206634806048616462323881 := by
  unfold tailWord_8192392
  simp only [CollatzResearch.WordTrace]
  refine ⟨149400541868185204003377715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199200722490913605337836953 149400541868185204003377715)
  ·
    refine ⟨224100812802277806005066573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149400541868185204003377715 224100812802277806005066573)
    ·
      refine ⟨84037804800854177251899965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224100812802277806005066573 84037804800854177251899965)
      ·
        refine ⟨31514176800320316469462487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84037804800854177251899965 31514176800320316469462487)
        ·
          refine ⟨47271265200480474704193731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31514176800320316469462487 47271265200480474704193731)
          ·
            refine ⟨70906897800720712056290597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47271265200480474704193731 70906897800720712056290597)
            ·
              refine ⟨13295043337635133510554487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70906897800720712056290597 13295043337635133510554487)
              ·
                refine ⟨19942565006452700265831731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13295043337635133510554487 19942565006452700265831731)
                ·
                  refine ⟨29913847509679050398747597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19942565006452700265831731 29913847509679050398747597)
                  ·
                    refine ⟨11217692816129643899530349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29913847509679050398747597 11217692816129643899530349)
                    ·
                      refine ⟨4206634806048616462323881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11217692816129643899530349 4206634806048616462323881)
                      ·
                        rfl

theorem cell23_8192392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_8192392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8192392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8192392 prefixEnd_8192392 := by exact prefixLift 8192392
  have htrace : WordTrace (prefixWord ++ tailWord_8192392) baseStart_8192392 baseEnd_8192392 := by
    simpa [prefixWord, tailWord_8192392, baseEnd_8192392] using wordTrace_append hprefix tailTrace_8192392
  have hstable : (prefixWord ++ tailWord_8192392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8192392).length < 2 ^ (prefixWord ++ tailWord_8192392).sum := by decide
  have hdescent : baseEnd_8192392 < baseStart_8192392 := by decide
  rcases family_descends (prefixWord ++ tailWord_8192392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8192413 : List Nat := [1, 4, 2, 1, 5, 1, 2, 1, 1, 2, 3]
def baseStart_8192413 : Nat := 118140960795 + 8192413 * 2 ^ 59
def prefixEnd_8192413 : Nat := 4983230072969 + 3 ^ 40 * 8192413 * 2
def baseEnd_8192413 : Nat := 4206645589142360880161285

theorem tailTrace_8192413 : CollatzResearch.WordTrace tailWord_8192413 prefixEnd_8192413 4206645589142360880161285 := by
  unfold tailWord_8192413
  simp only [CollatzResearch.WordTrace]
  refine ⟨298801849669294328593269893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199201233112862885728846595 298801849669294328593269893)
  ·
    refine ⟨56025346812992686611238105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 298801849669294328593269893 56025346812992686611238105)
    ·
      refine ⟨42019010109744514958428579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56025346812992686611238105 42019010109744514958428579)
      ·
        refine ⟨63028515164616772437642869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42019010109744514958428579 63028515164616772437642869)
        ·
          refine ⟨5908923296682822416029019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63028515164616772437642869 5908923296682822416029019)
          ·
            refine ⟨8863384945024233624043529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5908923296682822416029019 8863384945024233624043529)
            ·
              refine ⟨6647538708768175218032647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8863384945024233624043529 6647538708768175218032647)
              ·
                refine ⟨9971308063152262827048971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6647538708768175218032647 9971308063152262827048971)
                ·
                  refine ⟨14956962094728394240573457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9971308063152262827048971 14956962094728394240573457)
                  ·
                    refine ⟨11217721571046295680430093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14956962094728394240573457 11217721571046295680430093)
                    ·
                      refine ⟨4206645589142360880161285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11217721571046295680430093 4206645589142360880161285)
                      ·
                        rfl

theorem cell23_8192413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 1, 1, 2, 3].length) (baseStart_8192413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8192413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8192413 prefixEnd_8192413 := by exact prefixLift 8192413
  have htrace : WordTrace (prefixWord ++ tailWord_8192413) baseStart_8192413 baseEnd_8192413 := by
    simpa [prefixWord, tailWord_8192413, baseEnd_8192413] using wordTrace_append hprefix tailTrace_8192413
  have hstable : (prefixWord ++ tailWord_8192413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8192413).length < 2 ^ (prefixWord ++ tailWord_8192413).sum := by decide
  have hdescent : baseEnd_8192413 < baseStart_8192413 := by decide
  rcases family_descends (prefixWord ++ tailWord_8192413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8192419 : List Nat := [1, 1, 1, 4, 1, 5, 1, 3, 1, 3, 2]
def baseStart_8192419 : Nat := 118140960795 + 8192419 * 2 ^ 59
def prefixEnd_8192419 : Nat := 4983230072969 + 3 ^ 40 * 8192419 * 2
def baseEnd_8192419 : Nat := 4206648670026287856686257

theorem tailTrace_8192419 : CollatzResearch.WordTrace tailWord_8192419 prefixEnd_8192419 4206648670026287856686257 := by
  unfold tailWord_8192419
  simp only [CollatzResearch.WordTrace]
  refine ⟨298802068507272591617988311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199201379004848394411992207 298802068507272591617988311)
  ·
    refine ⟨448203102760908887426982467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298802068507272591617988311 448203102760908887426982467)
    ·
      refine ⟨672304654141363331140473701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448203102760908887426982467 672304654141363331140473701)
      ·
        refine ⟨126057122651505624588838819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 672304654141363331140473701 126057122651505624588838819)
        ·
          refine ⟨189085683977258436883258229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126057122651505624588838819 189085683977258436883258229)
          ·
            refine ⟨17726782872867978457805459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 189085683977258436883258229 17726782872867978457805459)
            ·
              refine ⟨26590174309301967686708189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17726782872867978457805459 26590174309301967686708189)
              ·
                refine ⟨9971315365988237882515571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26590174309301967686708189 9971315365988237882515571)
                ·
                  refine ⟨14956973048982356823773357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9971315365988237882515571 14956973048982356823773357)
                  ·
                    refine ⟨5608864893368383808915009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14956973048982356823773357 5608864893368383808915009)
                    ·
                      refine ⟨4206648670026287856686257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5608864893368383808915009 4206648670026287856686257)
                      ·
                        rfl

theorem cell23_8192419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 3, 1, 3, 2].length) (baseStart_8192419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8192419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8192419 prefixEnd_8192419 := by exact prefixLift 8192419
  have htrace : WordTrace (prefixWord ++ tailWord_8192419) baseStart_8192419 baseEnd_8192419 := by
    simpa [prefixWord, tailWord_8192419, baseEnd_8192419] using wordTrace_append hprefix tailTrace_8192419
  have hstable : (prefixWord ++ tailWord_8192419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8192419).length < 2 ^ (prefixWord ++ tailWord_8192419).sum := by decide
  have hdescent : baseEnd_8192419 < baseStart_8192419 := by decide
  rcases family_descends (prefixWord ++ tailWord_8192419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8192455 : List Nat := [1, 1, 4, 1, 1, 4, 2, 2, 7]
def baseStart_8192455 : Nat := 118140960795 + 8192455 * 2 ^ 59
def prefixEnd_8192455 : Nat := 4983230072969 + 3 ^ 40 * 8192455 * 2
def baseEnd_8192455 : Nat := 467407461703316635092899

theorem tailTrace_8192455 : CollatzResearch.WordTrace tailWord_8192455 prefixEnd_8192455 467407461703316635092899 := by
  unfold tailWord_8192455
  simp only [CollatzResearch.WordTrace]
  refine ⟨298803381535142169766298819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199202254356761446510865879 298803381535142169766298819)
  ·
    refine ⟨448205072302713254649448229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298803381535142169766298819 448205072302713254649448229)
    ·
      refine ⟨84038451056758735246771543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 448205072302713254649448229 84038451056758735246771543)
      ·
        refine ⟨126057676585138102870157315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84038451056758735246771543 126057676585138102870157315)
        ·
          refine ⟨189086514877707154305235973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126057676585138102870157315 189086514877707154305235973)
          ·
            refine ⟨35453721539570091432231745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189086514877707154305235973 35453721539570091432231745)
            ·
              refine ⟨26590291154677568574173809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35453721539570091432231745 26590291154677568574173809)
              ·
                refine ⟨19942718366008176430630357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26590291154677568574173809 19942718366008176430630357)
                ·
                  refine ⟨467407461703316635092899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19942718366008176430630357 467407461703316635092899)
                  ·
                    rfl

theorem cell23_8192455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 7].length) (baseStart_8192455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8192455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8192455 prefixEnd_8192455 := by exact prefixLift 8192455
  have htrace : WordTrace (prefixWord ++ tailWord_8192455) baseStart_8192455 baseEnd_8192455 := by
    simpa [prefixWord, tailWord_8192455, baseEnd_8192455] using wordTrace_append hprefix tailTrace_8192455
  have hstable : (prefixWord ++ tailWord_8192455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8192455).length < 2 ^ (prefixWord ++ tailWord_8192455).sum := by decide
  have hdescent : baseEnd_8192455 < baseStart_8192455 := by decide
  rcases family_descends (prefixWord ++ tailWord_8192455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8192465 : List Nat := [1, 2, 2, 1, 2, 1, 1, 4, 1, 5, 3]
def baseStart_8192465 : Nat := 118140960795 + 8192465 * 2 ^ 59
def prefixEnd_8192465 : Nat := 4983230072969 + 3 ^ 40 * 8192465 * 2
def baseEnd_8192465 : Nat := 4206672290136394676711045

theorem tailTrace_8192465 : CollatzResearch.WordTrace tailWord_8192465 prefixEnd_8192465 4206672290136394676711045 := by
  unfold tailWord_8192465
  simp only [CollatzResearch.WordTrace]
  refine ⟨298803746265105941474162849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199202497510070627649441899 298803746265105941474162849)
  ·
    refine ⟨224102809698829456105622137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298803746265105941474162849 224102809698829456105622137)
    ·
      refine ⟨168077107274122092079216603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224102809698829456105622137 168077107274122092079216603)
      ·
        refine ⟨252115660911183138118824905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168077107274122092079216603 252115660911183138118824905)
        ·
          refine ⟨189086745683387353589118679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252115660911183138118824905 189086745683387353589118679)
          ·
            refine ⟨283630118525081030383678019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189086745683387353589118679 283630118525081030383678019)
            ·
              refine ⟨425445177787621545575517029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283630118525081030383678019 425445177787621545575517029)
              ·
                refine ⟨79770970835179039795409443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 425445177787621545575517029 79770970835179039795409443)
                ·
                  refine ⟨119656456252768559693114165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79770970835179039795409443 119656456252768559693114165)
                  ·
                    refine ⟨11217792773697052471229453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 119656456252768559693114165 11217792773697052471229453)
                    ·
                      refine ⟨4206672290136394676711045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11217792773697052471229453 4206672290136394676711045)
                      ·
                        rfl

theorem cell23_8192465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 5, 3].length) (baseStart_8192465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8192465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8192465 prefixEnd_8192465 := by exact prefixLift 8192465
  have htrace : WordTrace (prefixWord ++ tailWord_8192465) baseStart_8192465 baseEnd_8192465 := by
    simpa [prefixWord, tailWord_8192465, baseEnd_8192465] using wordTrace_append hprefix tailTrace_8192465
  have hstable : (prefixWord ++ tailWord_8192465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8192465).length < 2 ^ (prefixWord ++ tailWord_8192465).sum := by decide
  have hdescent : baseEnd_8192465 < baseStart_8192465 := by decide
  rcases family_descends (prefixWord ++ tailWord_8192465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8192492 : List Nat := [2, 2, 1, 1, 2, 1, 4, 1, 2, 5, 2]
def baseStart_8192492 : Nat := 118140960795 + 8192492 * 2 ^ 59
def prefixEnd_8192492 : Nat := 4983230072969 + 3 ^ 40 * 8192492 * 2
def baseEnd_8192492 : Nat := 4206686154114066071073421

theorem tailTrace_8192492 : CollatzResearch.WordTrace tailWord_8192492 prefixEnd_8192492 4206686154114066071073421 := by
  unfold tailWord_8192492
  simp only [CollatzResearch.WordTrace]
  refine ⟨149402365518004062542697865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199203154024005416723597153 149402365518004062542697865)
  ·
    refine ⟨112051774138503046907023399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149402365518004062542697865 112051774138503046907023399)
    ·
      refine ⟨168077661207754570360535099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112051774138503046907023399 168077661207754570360535099)
      ·
        refine ⟨252116491811631855540802649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168077661207754570360535099 252116491811631855540802649)
        ·
          refine ⟨189087368858723891655601987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252116491811631855540802649 189087368858723891655601987)
          ·
            refine ⟨283631053288085837483402981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189087368858723891655601987 283631053288085837483402981)
            ·
              refine ⟨53180822491516094528138059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 283631053288085837483402981 53180822491516094528138059)
              ·
                refine ⟨79771233737274141792207089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53180822491516094528138059 79771233737274141792207089)
                ·
                  refine ⟨59828425302955606344155317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79771233737274141792207089 59828425302955606344155317)
                  ·
                    refine ⟨5608914872152088094764561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59828425302955606344155317 5608914872152088094764561)
                    ·
                      refine ⟨4206686154114066071073421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5608914872152088094764561 4206686154114066071073421)
                      ·
                        rfl

theorem cell23_8192492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 5, 2].length) (baseStart_8192492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8192492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8192492 prefixEnd_8192492 := by exact prefixLift 8192492
  have htrace : WordTrace (prefixWord ++ tailWord_8192492) baseStart_8192492 baseEnd_8192492 := by
    simpa [prefixWord, tailWord_8192492, baseEnd_8192492] using wordTrace_append hprefix tailTrace_8192492
  have hstable : (prefixWord ++ tailWord_8192492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8192492).length < 2 ^ (prefixWord ++ tailWord_8192492).sum := by decide
  have hdescent : baseEnd_8192492 < baseStart_8192492 := by decide
  rcases family_descends (prefixWord ++ tailWord_8192492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8192502 : List Nat := [5, 1, 1, 1, 2, 1, 1, 2, 4, 5]
def baseStart_8192502 : Nat := 118140960795 + 8192502 * 2 ^ 59
def prefixEnd_8192502 : Nat := 4983230072969 + 3 ^ 40 * 8192502 * 2
def baseEnd_8192502 : Nat := 1402230429640203677316125

theorem tailTrace_8192502 : CollatzResearch.WordTrace tailWord_8192502 prefixEnd_8192502 1402230429640203677316125 := by
  unfold tailWord_8192502
  simp only [CollatzResearch.WordTrace]
  refine ⟨18675318485373243549578735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199203397177314597862173173 18675318485373243549578735)
  ·
    refine ⟨28012977728059865324368103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18675318485373243549578735 28012977728059865324368103)
    ·
      refine ⟨42019466592089797986552155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28012977728059865324368103 42019466592089797986552155)
      ·
        refine ⟨63029199888134696979828233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42019466592089797986552155 63029199888134696979828233)
        ·
          refine ⟨47271899916101022734871175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63029199888134696979828233 47271899916101022734871175)
          ·
            refine ⟨70907849874151534102306763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47271899916101022734871175 70907849874151534102306763)
            ·
              refine ⟨106361774811227301153460145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70907849874151534102306763 106361774811227301153460145)
              ·
                refine ⟨79771331108420475865095109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106361774811227301153460145 79771331108420475865095109)
                ·
                  refine ⟨14957124582828839224705333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79771331108420475865095109 14957124582828839224705333)
                  ·
                    refine ⟨1402230429640203677316125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14957124582828839224705333 1402230429640203677316125)
                    ·
                      rfl

theorem cell23_8192502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_8192502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8192502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8192502 prefixEnd_8192502 := by exact prefixLift 8192502
  have htrace : WordTrace (prefixWord ++ tailWord_8192502) baseStart_8192502 baseEnd_8192502 := by
    simpa [prefixWord, tailWord_8192502, baseEnd_8192502] using wordTrace_append hprefix tailTrace_8192502
  have hstable : (prefixWord ++ tailWord_8192502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8192502).length < 2 ^ (prefixWord ++ tailWord_8192502).sum := by decide
  have hdescent : baseEnd_8192502 < baseStart_8192502 := by decide
  rcases family_descends (prefixWord ++ tailWord_8192502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8192505 : List Nat := [1, 2, 1, 3, 1, 2, 2, 1, 3, 3, 4]
def baseStart_8192505 : Nat := 118140960795 + 8192505 * 2 ^ 59
def prefixEnd_8192505 : Nat := 4983230072969 + 3 ^ 40 * 8192505 * 2
def baseEnd_8192505 : Nat := 4206692829362574520210861

theorem tailTrace_8192505 : CollatzResearch.WordTrace tailWord_8192505 prefixEnd_8192505 4206692829362574520210861 := by
  unfold tailWord_8192505
  simp only [CollatzResearch.WordTrace]
  refine ⟨298805205184961028305618969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199203470123307352203745979 298805205184961028305618969)
  ·
    refine ⟨224103903888720771229214227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298805205184961028305618969 224103903888720771229214227)
    ·
      refine ⟨336155855833081156843821341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224103903888720771229214227 336155855833081156843821341)
      ·
        refine ⟨126058445937405433816433003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 336155855833081156843821341 126058445937405433816433003)
        ·
          refine ⟨189087668906108150724649505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126058445937405433816433003 189087668906108150724649505)
          ·
            refine ⟨141815751679581113043487129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189087668906108150724649505 141815751679581113043487129)
            ·
              refine ⟨106361813759685834782615347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141815751679581113043487129 106361813759685834782615347)
              ·
                refine ⟨159542720639528752173923021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106361813759685834782615347 159542720639528752173923021)
                ·
                  refine ⟨59828520239823282065221133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159542720639528752173923021 59828520239823282065221133)
                  ·
                    refine ⟨22435695089933730774457925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59828520239823282065221133 22435695089933730774457925)
                    ·
                      refine ⟨4206692829362574520210861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22435695089933730774457925 4206692829362574520210861)
                      ·
                        rfl

theorem cell23_8192505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_8192505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8192505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8192505 prefixEnd_8192505 := by exact prefixLift 8192505
  have htrace : WordTrace (prefixWord ++ tailWord_8192505) baseStart_8192505 baseEnd_8192505 := by
    simpa [prefixWord, tailWord_8192505, baseEnd_8192505] using wordTrace_append hprefix tailTrace_8192505
  have hstable : (prefixWord ++ tailWord_8192505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8192505).length < 2 ^ (prefixWord ++ tailWord_8192505).sum := by decide
  have hdescent : baseEnd_8192505 < baseStart_8192505 := by decide
  rcases family_descends (prefixWord ++ tailWord_8192505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8192519 : List Nat := [1, 1, 4, 3, 3, 1, 2, 1, 2, 5]
def baseStart_8192519 : Nat := 118140960795 + 8192519 * 2 ^ 59
def prefixEnd_8192519 : Nat := 4983230072969 + 3 ^ 40 * 8192519 * 2
def baseEnd_8192519 : Nat := 1402233339363912488478599

theorem tailTrace_8192519 : CollatzResearch.WordTrace tailWord_8192519 prefixEnd_8192519 1402233339363912488478599 := by
  unfold tailWord_8192519
  simp only [CollatzResearch.WordTrace]
  refine ⟨298805715806910308696628611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199203810537940205797752407 298805715806910308696628611)
  ·
    refine ⟨448208573710365463044942917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298805715806910308696628611 448208573710365463044942917)
    ·
      refine ⟨84039107570693524320926797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 448208573710365463044942917 84039107570693524320926797)
      ·
        refine ⟨31514665339010071620347549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84039107570693524320926797 31514665339010071620347549)
        ·
          refine ⟨11817999502128776857630331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31514665339010071620347549 11817999502128776857630331)
          ·
            refine ⟨17726999253193165286445497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11817999502128776857630331 17726999253193165286445497)
            ·
              refine ⟨13295249439894873964834123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17726999253193165286445497 13295249439894873964834123)
              ·
                refine ⟨19942874159842310947251185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13295249439894873964834123 19942874159842310947251185)
                ·
                  refine ⟨14957155619881733210438389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19942874159842310947251185 14957155619881733210438389)
                  ·
                    refine ⟨1402233339363912488478599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14957155619881733210438389 1402233339363912488478599)
                    ·
                      rfl

theorem cell23_8192519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 2, 5].length) (baseStart_8192519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8192519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8192519 prefixEnd_8192519 := by exact prefixLift 8192519
  have htrace : WordTrace (prefixWord ++ tailWord_8192519) baseStart_8192519 baseEnd_8192519 := by
    simpa [prefixWord, tailWord_8192519, baseEnd_8192519] using wordTrace_append hprefix tailTrace_8192519
  have hstable : (prefixWord ++ tailWord_8192519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8192519).length < 2 ^ (prefixWord ++ tailWord_8192519).sum := by decide
  have hdescent : baseEnd_8192519 < baseStart_8192519 := by decide
  rcases family_descends (prefixWord ++ tailWord_8192519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8192562 : List Nat := [3, 2, 1, 1, 2, 1, 4, 3, 6]
def baseStart_8192562 : Nat := 118140960795 + 8192562 * 2 ^ 59
def prefixEnd_8192562 : Nat := 4983230072969 + 3 ^ 40 * 8192562 * 2
def baseEnd_8192562 : Nat := 467413566417764533022011

theorem tailTrace_8192562 : CollatzResearch.WordTrace tailWord_8192562 prefixEnd_8192562 467413566417764533022011 := by
  unfold tailWord_8192562
  simp only [CollatzResearch.WordTrace]
  refine ⟨74701821036438631760110985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199204856097169684693629293 74701821036438631760110985)
  ·
    refine ⟨56026365777328973820083239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74701821036438631760110985 56026365777328973820083239)
    ·
      refine ⟨84039548665993460730124859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56026365777328973820083239 84039548665993460730124859)
      ·
        refine ⟨126059322998990191095187289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84039548665993460730124859 126059322998990191095187289)
        ·
          refine ⟨94544492249242643321390467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126059322998990191095187289 94544492249242643321390467)
          ·
            refine ⟨141816738373863964982085701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94544492249242643321390467 141816738373863964982085701)
            ·
              refine ⟨26590638445099493434141069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141816738373863964982085701 26590638445099493434141069)
              ·
                refine ⟨9971489416912310037802901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26590638445099493434141069 9971489416912310037802901)
                ·
                  refine ⟨467413566417764533022011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9971489416912310037802901 467413566417764533022011)
                  ·
                    rfl

theorem cell23_8192562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 3, 6].length) (baseStart_8192562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8192562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8192562 prefixEnd_8192562 := by exact prefixLift 8192562
  have htrace : WordTrace (prefixWord ++ tailWord_8192562) baseStart_8192562 baseEnd_8192562 := by
    simpa [prefixWord, tailWord_8192562, baseEnd_8192562] using wordTrace_append hprefix tailTrace_8192562
  have hstable : (prefixWord ++ tailWord_8192562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8192562).length < 2 ^ (prefixWord ++ tailWord_8192562).sum := by decide
  have hdescent : baseEnd_8192562 < baseStart_8192562 := by decide
  rcases family_descends (prefixWord ++ tailWord_8192562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8192566 : List Nat := [5, 1, 2, 1, 2, 2, 1, 2, 3, 4]
def baseStart_8192566 : Nat := 118140960795 + 8192566 * 2 ^ 59
def prefixEnd_8192566 : Nat := 4983230072969 + 3 ^ 40 * 8192566 * 2
def baseEnd_8192566 : Nat := 1402241383894166260516027

theorem tailTrace_8192566 : CollatzResearch.WordTrace tailWord_8192566 prefixEnd_8192566 1402241383894166260516027 := by
  unfold tailWord_8192566
  simp only [CollatzResearch.WordTrace]
  refine ⟨18675464377358752232724347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199204953358493357149059701 18675464377358752232724347)
  ·
    refine ⟨28013196566038128349086521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18675464377358752232724347 28013196566038128349086521)
    ·
      refine ⟨21009897424528596261814891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28013196566038128349086521 21009897424528596261814891)
      ·
        refine ⟨31514846136792894392722337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21009897424528596261814891 31514846136792894392722337)
        ·
          refine ⟨23636134602594670794541753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31514846136792894392722337 23636134602594670794541753)
          ·
            refine ⟨17727100951946003095906315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23636134602594670794541753 17727100951946003095906315)
            ·
              refine ⟨26590651427919004643859473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17727100951946003095906315 26590651427919004643859473)
              ·
                refine ⟨19942988570939253482894605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26590651427919004643859473 19942988570939253482894605)
                ·
                  refine ⟨7478620714102220056085477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19942988570939253482894605 7478620714102220056085477)
                  ·
                    refine ⟨1402241383894166260516027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7478620714102220056085477 1402241383894166260516027)
                    ·
                      rfl

theorem cell23_8192566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_8192566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8192566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8192566 prefixEnd_8192566 := by exact prefixLift 8192566
  have htrace : WordTrace (prefixWord ++ tailWord_8192566) baseStart_8192566 baseEnd_8192566 := by
    simpa [prefixWord, tailWord_8192566, baseEnd_8192566] using wordTrace_append hprefix tailTrace_8192566
  have hstable : (prefixWord ++ tailWord_8192566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8192566).length < 2 ^ (prefixWord ++ tailWord_8192566).sum := by decide
  have hdescent : baseEnd_8192566 < baseStart_8192566 := by decide
  rcases family_descends (prefixWord ++ tailWord_8192566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8192585 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 1, 6, 5]
def baseStart_8192585 : Nat := 118140960795 + 8192585 * 2 ^ 59
def prefixEnd_8192585 : Nat := 4983230072969 + 3 ^ 40 * 8192585 * 2
def baseEnd_8192585 : Nat := 4206733907814934207210493

theorem tailTrace_8192585 : CollatzResearch.WordTrace tailWord_8192585 prefixEnd_8192585 4206733907814934207210493 := by
  unfold tailWord_8192585
  simp only [CollatzResearch.WordTrace]
  refine ⟨298808123024671201968531209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199205415349780801312354139 298808123024671201968531209)
  ·
    refine ⟨224106092268503401476398407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298808123024671201968531209 224106092268503401476398407)
    ·
      refine ⟨336159138402755102214597611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224106092268503401476398407 336159138402755102214597611)
      ·
        refine ⟨504238707604132653321896417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336159138402755102214597611 504238707604132653321896417)
        ·
          refine ⟨378179030703099489991422313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 504238707604132653321896417 378179030703099489991422313)
          ·
            refine ⟨283634273027324617493566735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 378179030703099489991422313 283634273027324617493566735)
            ·
              refine ⟨425451409540986926240350103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283634273027324617493566735 425451409540986926240350103)
              ·
                refine ⟨638177114311480389360525155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 425451409540986926240350103 638177114311480389360525155)
                ·
                  refine ⟨957265671467220584040787733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 638177114311480389360525155 957265671467220584040787733)
                  ·
                    refine ⟨44871828350025964876911925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 957265671467220584040787733 44871828350025964876911925)
                    ·
                      refine ⟨4206733907814934207210493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44871828350025964876911925 4206733907814934207210493)
                      ·
                        rfl

theorem cell23_8192585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 6, 5].length) (baseStart_8192585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8192585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8192585 prefixEnd_8192585 := by exact prefixLift 8192585
  have htrace : WordTrace (prefixWord ++ tailWord_8192585) baseStart_8192585 baseEnd_8192585 := by
    simpa [prefixWord, tailWord_8192585, baseEnd_8192585] using wordTrace_append hprefix tailTrace_8192585
  have hstable : (prefixWord ++ tailWord_8192585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8192585).length < 2 ^ (prefixWord ++ tailWord_8192585).sum := by decide
  have hdescent : baseEnd_8192585 < baseStart_8192585 := by decide
  rcases family_descends (prefixWord ++ tailWord_8192585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8192599 : List Nat := [1, 1, 3, 2, 2, 2, 2, 1, 4, 3, 2]
def baseStart_8192599 : Nat := 118140960795 + 8192599 * 2 ^ 59
def prefixEnd_8192599 : Nat := 4983230072969 + 3 ^ 40 * 8192599 * 2
def baseEnd_8192599 : Nat := 4206741096544097152435429

theorem tailTrace_8192599 : CollatzResearch.WordTrace tailWord_8192599 prefixEnd_8192599 4206741096544097152435429 := by
  unfold tailWord_8192599
  simp only [CollatzResearch.WordTrace]
  refine ⟨298808633646620482359540851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199205755764413654906360567 298808633646620482359540851)
  ·
    refine ⟨448212950469930723539311277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298808633646620482359540851 448212950469930723539311277)
    ·
      refine ⟨168079856426224021327241729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 448212950469930723539311277 168079856426224021327241729)
      ·
        refine ⟨126059892319668015995431297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168079856426224021327241729 126059892319668015995431297)
        ·
          refine ⟨94544919239751011996573473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126059892319668015995431297 94544919239751011996573473)
          ·
            refine ⟨70908689429813258997430105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94544919239751011996573473 70908689429813258997430105)
            ·
              refine ⟨53181517072359944248072579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70908689429813258997430105 53181517072359944248072579)
              ·
                refine ⟨79772275608539916372108869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53181517072359944248072579 79772275608539916372108869)
                ·
                  refine ⟨14957301676601234319770413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79772275608539916372108869 14957301676601234319770413)
                  ·
                    refine ⟨5608988128725462869913905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14957301676601234319770413 5608988128725462869913905)
                    ·
                      refine ⟨4206741096544097152435429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5608988128725462869913905 4206741096544097152435429)
                      ·
                        rfl

theorem cell23_8192599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 4, 3, 2].length) (baseStart_8192599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8192599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8192599 prefixEnd_8192599 := by exact prefixLift 8192599
  have htrace : WordTrace (prefixWord ++ tailWord_8192599) baseStart_8192599 baseEnd_8192599 := by
    simpa [prefixWord, tailWord_8192599, baseEnd_8192599] using wordTrace_append hprefix tailTrace_8192599
  have hstable : (prefixWord ++ tailWord_8192599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8192599).length < 2 ^ (prefixWord ++ tailWord_8192599).sum := by decide
  have hdescent : baseEnd_8192599 < baseStart_8192599 := by decide
  rcases family_descends (prefixWord ++ tailWord_8192599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8192626 : List Nat := [3, 2, 1, 2, 4, 1, 2, 2, 1, 5]
def baseStart_8192626 : Nat := 118140960795 + 8192626 * 2 ^ 59
def prefixEnd_8192626 : Nat := 4983230072969 + 3 ^ 40 * 8192626 * 2
def baseEnd_8192626 : Nat := 1402251653507256182265935

theorem tailTrace_8192626 : CollatzResearch.WordTrace tailWord_8192626 prefixEnd_8192626 1402251653507256182265935 := by
  unfold tailWord_8192626
  simp only [CollatzResearch.WordTrace]
  refine ⟨74702404604380666492693433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199206412278348443980515821 74702404604380666492693433)
  ·
    refine ⟨56026803453285499869520075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74702404604380666492693433 56026803453285499869520075)
    ·
      refine ⟨84040205179928249804280113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56026803453285499869520075 84040205179928249804280113)
      ·
        refine ⟨63030153884946187353210085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84040205179928249804280113 63030153884946187353210085)
        ·
          refine ⟨11818153853427410128726891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63030153884946187353210085 11818153853427410128726891)
          ·
            refine ⟨17727230780141115193090337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11818153853427410128726891 17727230780141115193090337)
            ·
              refine ⟨13295423085105836394817753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17727230780141115193090337 13295423085105836394817753)
              ·
                refine ⟨9971567313829377296113315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13295423085105836394817753 9971567313829377296113315)
                ·
                  refine ⟨14957350970744065944169973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9971567313829377296113315 14957350970744065944169973)
                  ·
                    refine ⟨1402251653507256182265935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14957350970744065944169973 1402251653507256182265935)
                    ·
                      rfl

theorem cell23_8192626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 2, 1, 5].length) (baseStart_8192626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8192626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8192626 prefixEnd_8192626 := by exact prefixLift 8192626
  have htrace : WordTrace (prefixWord ++ tailWord_8192626) baseStart_8192626 baseEnd_8192626 := by
    simpa [prefixWord, tailWord_8192626, baseEnd_8192626] using wordTrace_append hprefix tailTrace_8192626
  have hstable : (prefixWord ++ tailWord_8192626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8192626).length < 2 ^ (prefixWord ++ tailWord_8192626).sum := by decide
  have hdescent : baseEnd_8192626 < baseStart_8192626 := by decide
  rcases family_descends (prefixWord ++ tailWord_8192626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8192736 : List Nat := [2, 1, 1, 3, 1, 2, 1, 2, 6, 2, 2]
def baseStart_8192736 : Nat := 118140960795 + 8192736 * 2 ^ 59
def prefixEnd_8192736 : Nat := 4983230072969 + 3 ^ 40 * 8192736 * 2
def baseEnd_8192736 : Nat := 4206811443393763116422299

theorem tailTrace_8192736 : CollatzResearch.WordTrace tailWord_8192736 prefixEnd_8192736 4206811443393763116422299 := by
  unfold tailWord_8192736
  simp only [CollatzResearch.WordTrace]
  refine ⟨149406815223562077378639031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199209086964749436504852041 149406815223562077378639031)
  ·
    refine ⟨224110222835343116067958547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149406815223562077378639031 224110222835343116067958547)
    ·
      refine ⟨336165334253014674101937821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224110222835343116067958547 336165334253014674101937821)
      ·
        refine ⟨126062000344880502788226683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 336165334253014674101937821 126062000344880502788226683)
        ·
          refine ⟨189093000517320754182340025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126062000344880502788226683 189093000517320754182340025)
          ·
            refine ⟨141819750387990565636755019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189093000517320754182340025 141819750387990565636755019)
            ·
              refine ⟨212729625581985848455132529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141819750387990565636755019 212729625581985848455132529)
              ·
                refine ⟨159547219186489386341349397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212729625581985848455132529 159547219186489386341349397)
                ·
                  refine ⟨7478775899366689984750753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 159547219186489386341349397 7478775899366689984750753)
                  ·
                    refine ⟨5609081924525017488563065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7478775899366689984750753 5609081924525017488563065)
                    ·
                      refine ⟨4206811443393763116422299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5609081924525017488563065 4206811443393763116422299)
                      ·
                        rfl

theorem cell23_8192736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 6, 2, 2].length) (baseStart_8192736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8192736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8192736 prefixEnd_8192736 := by exact prefixLift 8192736
  have htrace : WordTrace (prefixWord ++ tailWord_8192736) baseStart_8192736 baseEnd_8192736 := by
    simpa [prefixWord, tailWord_8192736, baseEnd_8192736] using wordTrace_append hprefix tailTrace_8192736
  have hstable : (prefixWord ++ tailWord_8192736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8192736).length < 2 ^ (prefixWord ++ tailWord_8192736).sum := by decide
  have hdescent : baseEnd_8192736 < baseStart_8192736 := by decide
  rcases family_descends (prefixWord ++ tailWord_8192736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8192749 : List Nat := [1, 5, 1, 2, 1, 1, 1, 2, 1, 4, 4]
def baseStart_8192749 : Nat := 118140960795 + 8192749 * 2 ^ 59
def prefixEnd_8192749 : Nat := 4983230072969 + 3 ^ 40 * 8192749 * 2
def baseEnd_8192749 : Nat := 4206818118642271565559739

theorem tailTrace_8192749 : CollatzResearch.WordTrace tailWord_8192749 prefixEnd_8192749 4206818118642271565559739 := by
  unfold tailWord_8192749
  simp only [CollatzResearch.WordTrace]
  refine ⟨298814104596077057977501301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199209403064051371985000867 298814104596077057977501301)
  ·
    refine ⟨28013822305882224185390747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 298814104596077057977501301 28013822305882224185390747)
    ·
      refine ⟨42020733458823336278086121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28013822305882224185390747 42020733458823336278086121)
      ·
        refine ⟨31515550094117502208564591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42020733458823336278086121 31515550094117502208564591)
        ·
          refine ⟨47273325141176253312846887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31515550094117502208564591 47273325141176253312846887)
          ·
            refine ⟨70909987711764379969270331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47273325141176253312846887 70909987711764379969270331)
            ·
              refine ⟨106364981567646569953905497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70909987711764379969270331 106364981567646569953905497)
              ·
                refine ⟨79773736175734927465429123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106364981567646569953905497 79773736175734927465429123)
                ·
                  refine ⟨119660604263602391198143685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79773736175734927465429123 119660604263602391198143685)
                  ·
                    refine ⟨22436363299425448349651941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 119660604263602391198143685 22436363299425448349651941)
                    ·
                      refine ⟨4206818118642271565559739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22436363299425448349651941 4206818118642271565559739)
                      ·
                        rfl

theorem cell23_8192749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_8192749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8192749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8192749 prefixEnd_8192749 := by exact prefixLift 8192749
  have htrace : WordTrace (prefixWord ++ tailWord_8192749) baseStart_8192749 baseEnd_8192749 := by
    simpa [prefixWord, tailWord_8192749, baseEnd_8192749] using wordTrace_append hprefix tailTrace_8192749
  have hstable : (prefixWord ++ tailWord_8192749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8192749).length < 2 ^ (prefixWord ++ tailWord_8192749).sum := by decide
  have hdescent : baseEnd_8192749 < baseStart_8192749 := by decide
  rcases family_descends (prefixWord ++ tailWord_8192749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8192766 : List Nat := [4, 2, 2, 1, 2, 1, 1, 2, 2, 2, 4]
def baseStart_8192766 : Nat := 118140960795 + 8192766 * 2 ^ 59
def prefixEnd_8192766 : Nat := 4983230072969 + 3 ^ 40 * 8192766 * 2
def baseEnd_8192766 : Nat := 4206826847813397999047161

theorem tailTrace_8192766 : CollatzResearch.WordTrace tailWord_8192766 prefixEnd_8192766 4206826847813397999047161 := by
  unfold tailWord_8192766
  simp only [CollatzResearch.WordTrace]
  refine ⟨37351840579626933735108769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199209816424676979920580101 37351840579626933735108769)
  ·
    refine ⟨28013880434720200301331577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37351840579626933735108769 28013880434720200301331577)
    ·
      refine ⟨21010410326040150225998683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28013880434720200301331577 21010410326040150225998683)
      ·
        refine ⟨31515615489060225338998025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21010410326040150225998683 31515615489060225338998025)
        ·
          refine ⟨23636711616795169004248519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31515615489060225338998025 23636711616795169004248519)
          ·
            refine ⟨35455067425192753506372779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23636711616795169004248519 35455067425192753506372779)
            ·
              refine ⟨53182601137789130259559169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35455067425192753506372779 53182601137789130259559169)
              ·
                refine ⟨39886950853341847694669377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53182601137789130259559169 39886950853341847694669377)
                ·
                  refine ⟨29915213140006385771002033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39886950853341847694669377 29915213140006385771002033)
                  ·
                    refine ⟨22436409855004789328251525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29915213140006385771002033 22436409855004789328251525)
                    ·
                      refine ⟨4206826847813397999047161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22436409855004789328251525 4206826847813397999047161)
                      ·
                        rfl

theorem cell23_8192766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_8192766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8192766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8192766 prefixEnd_8192766 := by exact prefixLift 8192766
  have htrace : WordTrace (prefixWord ++ tailWord_8192766) baseStart_8192766 baseEnd_8192766 := by
    simpa [prefixWord, tailWord_8192766, baseEnd_8192766] using wordTrace_append hprefix tailTrace_8192766
  have hstable : (prefixWord ++ tailWord_8192766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8192766).length < 2 ^ (prefixWord ++ tailWord_8192766).sum := by decide
  have hdescent : baseEnd_8192766 < baseStart_8192766 := by decide
  rcases family_descends (prefixWord ++ tailWord_8192766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8192770 : List Nat := [3, 4, 1, 1, 1, 3, 1, 1, 4, 2, 2]
def baseStart_8192770 : Nat := 118140960795 + 8192770 * 2 ^ 59
def prefixEnd_8192770 : Nat := 4983230072969 + 3 ^ 40 * 8192770 * 2
def baseEnd_8192770 : Nat := 4206828901736015983397143

theorem tailTrace_8192770 : CollatzResearch.WordTrace tailWord_8192770 prefixEnd_8192770 4206828901736015983397143 := by
  unfold tailWord_8192770
  simp only [CollatzResearch.WordTrace]
  refine ⟨74703717632250244641003941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199209913686000652376010509 74703717632250244641003941)
  ·
    refine ⟨14006947056046920870188239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74703717632250244641003941 14006947056046920870188239)
    ·
      refine ⟨21010420584070381305282359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14006947056046920870188239 21010420584070381305282359)
      ·
        refine ⟨31515630876105571957923539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21010420584070381305282359 31515630876105571957923539)
        ·
          refine ⟨47273446314158357936885309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31515630876105571957923539 47273446314158357936885309)
          ·
            refine ⟨17727542367809384226331991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47273446314158357936885309 17727542367809384226331991)
            ·
              refine ⟨26591313551714076339497987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17727542367809384226331991 26591313551714076339497987)
              ·
                refine ⟨39886970327571114509246981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26591313551714076339497987 39886970327571114509246981)
                ·
                  refine ⟨7478806936419583970483809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39886970327571114509246981 7478806936419583970483809)
                  ·
                    refine ⟨5609105202314687977862857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7478806936419583970483809 5609105202314687977862857)
                    ·
                      refine ⟨4206828901736015983397143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5609105202314687977862857 4206828901736015983397143)
                      ·
                        rfl

theorem cell23_8192770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_8192770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8192770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8192770 prefixEnd_8192770 := by exact prefixLift 8192770
  have htrace : WordTrace (prefixWord ++ tailWord_8192770) baseStart_8192770 baseEnd_8192770 := by
    simpa [prefixWord, tailWord_8192770, baseEnd_8192770] using wordTrace_append hprefix tailTrace_8192770
  have hstable : (prefixWord ++ tailWord_8192770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8192770).length < 2 ^ (prefixWord ++ tailWord_8192770).sum := by decide
  have hdescent : baseEnd_8192770 < baseStart_8192770 := by decide
  rcases family_descends (prefixWord ++ tailWord_8192770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8192776 : List Nat := [2, 1, 3, 2, 2, 2, 2, 4, 5]
def baseStart_8192776 : Nat := 118140960795 + 8192776 * 2 ^ 59
def prefixEnd_8192776 : Nat := 4983230072969 + 3 ^ 40 * 8192776 * 2
def baseEnd_8192776 : Nat := 467425775846660328880235

theorem tailTrace_8192776 : CollatzResearch.WordTrace tailWord_8192776 prefixEnd_8192776 467425775846660328880235 := by
  unfold tailWord_8192776
  simp only [CollatzResearch.WordTrace]
  refine ⟨149407544683489620794367091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199210059577986161059156121 149407544683489620794367091)
  ·
    refine ⟨224111317025234431191550637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149407544683489620794367091 224111317025234431191550637)
    ·
      refine ⟨84041743884462911696831489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224111317025234431191550637 84041743884462911696831489)
      ·
        refine ⟨63031307913347183772623617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84041743884462911696831489 63031307913347183772623617)
        ·
          refine ⟨47273480935010387829467713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63031307913347183772623617 47273480935010387829467713)
          ·
            refine ⟨35455110701257790872100785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47273480935010387829467713 35455110701257790872100785)
            ·
              refine ⟨26591333025943343154075589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35455110701257790872100785 26591333025943343154075589)
              ·
                refine ⟨4985874942364376841389173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26591333025943343154075589 4985874942364376841389173)
                ·
                  refine ⟨467425775846660328880235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4985874942364376841389173 467425775846660328880235)
                  ·
                    rfl

theorem cell23_8192776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 4, 5].length) (baseStart_8192776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8192776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8192776 prefixEnd_8192776 := by exact prefixLift 8192776
  have htrace : WordTrace (prefixWord ++ tailWord_8192776) baseStart_8192776 baseEnd_8192776 := by
    simpa [prefixWord, tailWord_8192776, baseEnd_8192776] using wordTrace_append hprefix tailTrace_8192776
  have hstable : (prefixWord ++ tailWord_8192776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8192776).length < 2 ^ (prefixWord ++ tailWord_8192776).sum := by decide
  have hdescent : baseEnd_8192776 < baseStart_8192776 := by decide
  rcases family_descends (prefixWord ++ tailWord_8192776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8192833 : List Nat := [1, 2, 5, 3, 1, 1, 1, 1, 1, 2, 5]
def baseStart_8192833 : Nat := 118140960795 + 8192833 * 2 ^ 59
def prefixEnd_8192833 : Nat := 4983230072969 + 3 ^ 40 * 8192833 * 2
def baseEnd_8192833 : Nat := 4206861251017249236909353

theorem tailTrace_8192833 : CollatzResearch.WordTrace tailWord_8192833 prefixEnd_8192833 4206861251017249236909353 := by
  unfold tailWord_8192833
  simp only [CollatzResearch.WordTrace]
  refine ⟨298817168327772740323559153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199211445551848493549039435 298817168327772740323559153)
  ·
    refine ⟨224112876245829555242669365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298817168327772740323559153 224112876245829555242669365)
    ·
      refine ⟨21010582148046520804000253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 224112876245829555242669365 21010582148046520804000253)
      ·
        refine ⟨7878968305517445301500095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21010582148046520804000253 7878968305517445301500095)
        ·
          refine ⟨11818452458276167952250143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7878968305517445301500095 11818452458276167952250143)
          ·
            refine ⟨17727678687414251928375215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11818452458276167952250143 17727678687414251928375215)
            ·
              refine ⟨26591518031121377892562823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17727678687414251928375215 26591518031121377892562823)
              ·
                refine ⟨39887277046682066838844235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26591518031121377892562823 39887277046682066838844235)
                ·
                  refine ⟨59830915570023100258266353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39887277046682066838844235 59830915570023100258266353)
                  ·
                    refine ⟨44873186677517325193699765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59830915570023100258266353 44873186677517325193699765)
                    ·
                      refine ⟨4206861251017249236909353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44873186677517325193699765 4206861251017249236909353)
                      ·
                        rfl

theorem cell23_8192833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_8192833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8192833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8192833 prefixEnd_8192833 := by exact prefixLift 8192833
  have htrace : WordTrace (prefixWord ++ tailWord_8192833) baseStart_8192833 baseEnd_8192833 := by
    simpa [prefixWord, tailWord_8192833, baseEnd_8192833] using wordTrace_append hprefix tailTrace_8192833
  have hstable : (prefixWord ++ tailWord_8192833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8192833).length < 2 ^ (prefixWord ++ tailWord_8192833).sum := by decide
  have hdescent : baseEnd_8192833 < baseStart_8192833 := by decide
  rcases family_descends (prefixWord ++ tailWord_8192833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8192838 : List Nat := [6, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2]
def baseStart_8192838 : Nat := 118140960795 + 8192838 * 2 ^ 59
def prefixEnd_8192838 : Nat := 4983230072969 + 3 ^ 40 * 8192838 * 2
def baseEnd_8192838 : Nat := 4206863818420521717346831

theorem tailTrace_8192838 : CollatzResearch.WordTrace tailWord_8192838 prefixEnd_8192838 4206863818420521717346831 := by
  unfold tailWord_8192838
  simp only [CollatzResearch.WordTrace]
  refine ⟨9338042209148582068046599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 199211567128503084118327445 9338042209148582068046599)
  ·
    refine ⟨14007063313722873102069899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9338042209148582068046599 14007063313722873102069899)
    ·
      refine ⟨21010594970584309653104849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14007063313722873102069899 21010594970584309653104849)
      ·
        refine ⟨15757946227938232239828637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21010594970584309653104849 15757946227938232239828637)
        ·
          refine ⟨5909229835476837089935739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15757946227938232239828637 5909229835476837089935739)
          ·
            refine ⟨8863844753215255634903609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5909229835476837089935739 8863844753215255634903609)
            ·
              refine ⟨6647883564911441726177707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8863844753215255634903609 6647883564911441726177707)
              ·
                refine ⟨9971825347367162589266561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6647883564911441726177707 9971825347367162589266561)
                ·
                  refine ⟨7478869010525371941949921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9971825347367162589266561 7478869010525371941949921)
                  ·
                    refine ⟨5609151757894028956462441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7478869010525371941949921 5609151757894028956462441)
                    ·
                      refine ⟨4206863818420521717346831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5609151757894028956462441 4206863818420521717346831)
                      ·
                        rfl

theorem cell23_8192838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_8192838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8192838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8192838 prefixEnd_8192838 := by exact prefixLift 8192838
  have htrace : WordTrace (prefixWord ++ tailWord_8192838) baseStart_8192838 baseEnd_8192838 := by
    simpa [prefixWord, tailWord_8192838, baseEnd_8192838] using wordTrace_append hprefix tailTrace_8192838
  have hstable : (prefixWord ++ tailWord_8192838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8192838).length < 2 ^ (prefixWord ++ tailWord_8192838).sum := by decide
  have hdescent : baseEnd_8192838 < baseStart_8192838 := by decide
  rcases family_descends (prefixWord ++ tailWord_8192838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8192927 : List Nat := [1, 1, 2, 5, 2, 2, 2, 3, 1, 1, 3]
def baseStart_8192927 : Nat := 118140960795 + 8192927 * 2 ^ 59
def prefixEnd_8192927 : Nat := 4983230072969 + 3 ^ 40 * 8192927 * 2
def baseEnd_8192927 : Nat := 4206909518198771869133921

theorem tailTrace_8192927 : CollatzResearch.WordTrace tailWord_8192927 prefixEnd_8192927 4206909518198771869133921 := by
  unfold tailWord_8192927
  simp only [CollatzResearch.WordTrace]
  refine ⟨298820596789432194377481035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199213731192954796251654023 298820596789432194377481035)
  ·
    refine ⟨448230895184148291566221553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298820596789432194377481035 448230895184148291566221553)
    ·
      refine ⟨336173171388111218674666165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 448230895184148291566221553 336173171388111218674666165)
      ·
        refine ⟨31516234817635426750749953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 336173171388111218674666165 31516234817635426750749953)
        ·
          refine ⟨23637176113226570063062465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31516234817635426750749953 23637176113226570063062465)
          ·
            refine ⟨17727882084919927547296849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23637176113226570063062465 17727882084919927547296849)
            ·
              refine ⟨13295911563689945660472637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17727882084919927547296849 13295911563689945660472637)
              ·
                refine ⟨4985966836383729622677239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13295911563689945660472637 4985966836383729622677239)
                ·
                  refine ⟨7478950254575594434015859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4985966836383729622677239 7478950254575594434015859)
                  ·
                    refine ⟨11218425381863391651023789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7478950254575594434015859 11218425381863391651023789)
                    ·
                      refine ⟨4206909518198771869133921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11218425381863391651023789 4206909518198771869133921)
                      ·
                        rfl

theorem cell23_8192927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_8192927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8192927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8192927 prefixEnd_8192927 := by exact prefixLift 8192927
  have htrace : WordTrace (prefixWord ++ tailWord_8192927) baseStart_8192927 baseEnd_8192927 := by
    simpa [prefixWord, tailWord_8192927, baseEnd_8192927] using wordTrace_append hprefix tailTrace_8192927
  have hstable : (prefixWord ++ tailWord_8192927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8192927).length < 2 ^ (prefixWord ++ tailWord_8192927).sum := by decide
  have hdescent : baseEnd_8192927 < baseStart_8192927 := by decide
  rcases family_descends (prefixWord ++ tailWord_8192927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8192930 : List Nat := [3, 3, 1, 2, 2, 1, 4, 1, 1, 5]
def baseStart_8192930 : Nat := 118140960795 + 8192930 * 2 ^ 59
def prefixEnd_8192930 : Nat := 4983230072969 + 3 ^ 40 * 8192930 * 2
def baseEnd_8192930 : Nat := 1402303686213578452465469

theorem tailTrace_8192930 : CollatzResearch.WordTrace tailWord_8192930 prefixEnd_8192930 1402303686213578452465469 := by
  unfold tailWord_8192930
  simp only [CollatzResearch.WordTrace]
  refine ⟨74705176552105331472460061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199213804138947550593226829 74705176552105331472460061)
  ·
    refine ⟨28014441207039499302172523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74705176552105331472460061 28014441207039499302172523)
    ·
      refine ⟨42021661810559248953258785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28014441207039499302172523 42021661810559248953258785)
      ·
        refine ⟨31516246357919436714944089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42021661810559248953258785 31516246357919436714944089)
        ·
          refine ⟨23637184768439577536208067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31516246357919436714944089 23637184768439577536208067)
          ·
            refine ⟨35455777152659366304312101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23637184768439577536208067 35455777152659366304312101)
            ·
              refine ⟨6647958216123631182058519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35455777152659366304312101 6647958216123631182058519)
              ·
                refine ⟨9971937324185446773087779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6647958216123631182058519 9971937324185446773087779)
                ·
                  refine ⟨14957905986278170159631669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9971937324185446773087779 14957905986278170159631669)
                  ·
                    refine ⟨1402303686213578452465469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14957905986278170159631669 1402303686213578452465469)
                    ·
                      rfl

theorem cell23_8192930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_8192930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8192930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8192930 prefixEnd_8192930 := by exact prefixLift 8192930
  have htrace : WordTrace (prefixWord ++ tailWord_8192930) baseStart_8192930 baseEnd_8192930 := by
    simpa [prefixWord, tailWord_8192930, baseEnd_8192930] using wordTrace_append hprefix tailTrace_8192930
  have hstable : (prefixWord ++ tailWord_8192930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8192930).length < 2 ^ (prefixWord ++ tailWord_8192930).sum := by decide
  have hdescent : baseEnd_8192930 < baseStart_8192930 := by decide
  rcases family_descends (prefixWord ++ tailWord_8192930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8192959 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 6]
def baseStart_8192959 : Nat := 118140960795 + 8192959 * 2 ^ 59
def prefixEnd_8192959 : Nat := 4983230072969 + 3 ^ 40 * 8192959 * 2
def baseEnd_8192959 : Nat := 4206925949579715743933773

theorem tailTrace_8192959 : CollatzResearch.WordTrace tailWord_8192959 prefixEnd_8192959 4206925949579715743933773 := by
  unfold tailWord_8192959
  simp only [CollatzResearch.WordTrace]
  refine ⟨298821763925316263842645931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199214509283544175895097287 298821763925316263842645931)
  ·
    refine ⟨448232645887974395763968897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298821763925316263842645931 448232645887974395763968897)
    ·
      refine ⟨336174484415980796822976673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 448232645887974395763968897 336174484415980796822976673)
      ·
        refine ⟨252130863311985597617232505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336174484415980796822976673 252130863311985597617232505)
        ·
          refine ⟨189098147483989198212924379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252130863311985597617232505 189098147483989198212924379)
          ·
            refine ⟨283647221225983797319386569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189098147483989198212924379 283647221225983797319386569)
            ·
              refine ⟨212735415919487847989539927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283647221225983797319386569 212735415919487847989539927)
              ·
                refine ⟨319103123879231771984309891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212735415919487847989539927 319103123879231771984309891)
                ·
                  refine ⟨478654685818847657976464837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 319103123879231771984309891 478654685818847657976464837)
                  ·
                    refine ⟨89747753591033935870587157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 478654685818847657976464837 89747753591033935870587157)
                    ·
                      refine ⟨4206925949579715743933773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89747753591033935870587157 4206925949579715743933773)
                      ·
                        rfl

theorem cell23_8192959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 6].length) (baseStart_8192959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8192959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8192959 prefixEnd_8192959 := by exact prefixLift 8192959
  have htrace : WordTrace (prefixWord ++ tailWord_8192959) baseStart_8192959 baseEnd_8192959 := by
    simpa [prefixWord, tailWord_8192959, baseEnd_8192959] using wordTrace_append hprefix tailTrace_8192959
  have hstable : (prefixWord ++ tailWord_8192959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8192959).length < 2 ^ (prefixWord ++ tailWord_8192959).sum := by decide
  have hdescent : baseEnd_8192959 < baseStart_8192959 := by decide
  rcases family_descends (prefixWord ++ tailWord_8192959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8192960 : List Nat := [2, 1, 1, 2, 3, 4, 3, 1, 2, 4]
def baseStart_8192960 : Nat := 118140960795 + 8192960 * 2 ^ 59
def prefixEnd_8192960 : Nat := 4983230072969 + 3 ^ 40 * 8192960 * 2
def baseEnd_8192960 : Nat := 1402308821020123413340423

theorem tailTrace_8192960 : CollatzResearch.WordTrace tailWord_8192960 prefixEnd_8192960 1402308821020123413340423 := by
  unfold tailWord_8192960
  simp only [CollatzResearch.WordTrace]
  refine ⟨149410900199156320506716167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199214533598875094008954889 149410900199156320506716167)
  ·
    refine ⟨224116350298734480760074251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149410900199156320506716167 224116350298734480760074251)
    ·
      refine ⟨336174525448101721140111377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224116350298734480760074251 336174525448101721140111377)
      ·
        refine ⟨252130894086076290855083533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336174525448101721140111377 252130894086076290855083533)
        ·
          refine ⟨94549085282278609070656325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252130894086076290855083533 94549085282278609070656325)
          ·
            refine ⟨17727953490427239200748061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94549085282278609070656325 17727953490427239200748061)
            ·
              refine ⟨6647982558910214700280523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17727953490427239200748061 6647982558910214700280523)
              ·
                refine ⟨9971973838365322050420785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6647982558910214700280523 9971973838365322050420785)
                ·
                  refine ⟨7478980378773991537815589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9971973838365322050420785 7478980378773991537815589)
                  ·
                    refine ⟨1402308821020123413340423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7478980378773991537815589 1402308821020123413340423)
                    ·
                      rfl

theorem cell23_8192960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 1, 2, 4].length) (baseStart_8192960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8192960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8192960 prefixEnd_8192960 := by exact prefixLift 8192960
  have htrace : WordTrace (prefixWord ++ tailWord_8192960) baseStart_8192960 baseEnd_8192960 := by
    simpa [prefixWord, tailWord_8192960, baseEnd_8192960] using wordTrace_append hprefix tailTrace_8192960
  have hstable : (prefixWord ++ tailWord_8192960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8192960).length < 2 ^ (prefixWord ++ tailWord_8192960).sum := by decide
  have hdescent : baseEnd_8192960 < baseStart_8192960 := by decide
  rcases family_descends (prefixWord ++ tailWord_8192960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8192984 : List Nat := [2, 1, 2, 2, 2, 5, 1, 3, 1, 2, 2]
def baseStart_8192984 : Nat := 118140960795 + 8192984 * 2 ^ 59
def prefixEnd_8192984 : Nat := 4983230072969 + 3 ^ 40 * 8192984 * 2
def baseEnd_8192984 : Nat := 4206938786596078146121159

theorem tailTrace_8192984 : CollatzResearch.WordTrace tailWord_8192984 prefixEnd_8192984 4206938786596078146121159 := by
  unfold tailWord_8192984
  simp only [CollatzResearch.WordTrace]
  refine ⟨149411337875112846556153003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199215117166817128741537337 149411337875112846556153003)
  ·
    refine ⟨224117006812669269834229505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149411337875112846556153003 224117006812669269834229505)
    ·
      refine ⟨168087755109501952375672129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224117006812669269834229505 168087755109501952375672129)
      ·
        refine ⟨126065816332126464281754097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168087755109501952375672129 126065816332126464281754097)
        ·
          refine ⟨94549362249094848211315573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126065816332126464281754097 94549362249094848211315573)
          ·
            refine ⟨8864002710852642019810835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94549362249094848211315573 8864002710852642019810835)
            ·
              refine ⟨13296004066278963029716253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8864002710852642019810835 13296004066278963029716253)
              ·
                refine ⟨4986001524854611136143595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13296004066278963029716253 4986001524854611136143595)
                ·
                  refine ⟨7479002287281916704215393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4986001524854611136143595 7479002287281916704215393)
                  ·
                    refine ⟨5609251715461437528161545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7479002287281916704215393 5609251715461437528161545)
                    ·
                      refine ⟨4206938786596078146121159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5609251715461437528161545 4206938786596078146121159)
                      ·
                        rfl

theorem cell23_8192984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 3, 1, 2, 2].length) (baseStart_8192984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8192984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8192984 prefixEnd_8192984 := by exact prefixLift 8192984
  have htrace : WordTrace (prefixWord ++ tailWord_8192984) baseStart_8192984 baseEnd_8192984 := by
    simpa [prefixWord, tailWord_8192984, baseEnd_8192984] using wordTrace_append hprefix tailTrace_8192984
  have hstable : (prefixWord ++ tailWord_8192984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8192984).length < 2 ^ (prefixWord ++ tailWord_8192984).sum := by decide
  have hdescent : baseEnd_8192984 < baseStart_8192984 := by decide
  rcases family_descends (prefixWord ++ tailWord_8192984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8192993 : List Nat := [1, 2, 3, 1, 2, 1, 1, 2, 5, 3, 2]
def baseStart_8192993 : Nat := 118140960795 + 8192993 * 2 ^ 59
def prefixEnd_8192993 : Nat := 4983230072969 + 3 ^ 40 * 8192993 * 2
def baseEnd_8192993 : Nat := 4206943407921968610908617

theorem tailTrace_8192993 : CollatzResearch.WordTrace tailWord_8192993 prefixEnd_8192993 4206943407921968610908617 := by
  unfold tailWord_8192993
  simp only [CollatzResearch.WordTrace]
  refine ⟨298823004007193087649383633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199215336004795391766255755 298823004007193087649383633)
  ·
    refine ⟨224117253005394815737037725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298823004007193087649383633 224117253005394815737037725)
    ·
      refine ⟨84043969877023055901389147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224117253005394815737037725 84043969877023055901389147)
      ·
        refine ⟨126065954815534583852083721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84043969877023055901389147 126065954815534583852083721)
        ·
          refine ⟨94549466111650937889062791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126065954815534583852083721 94549466111650937889062791)
          ·
            refine ⟨141824199167476406833594187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94549466111650937889062791 141824199167476406833594187)
            ·
              refine ⟨212736298751214610250391281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141824199167476406833594187 212736298751214610250391281)
              ·
                refine ⟨159552224063410957687793461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212736298751214610250391281 159552224063410957687793461)
                ·
                  refine ⟨14958021005944777283230637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 159552224063410957687793461 14958021005944777283230637)
                  ·
                    refine ⟨5609257877229291481211489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14958021005944777283230637 5609257877229291481211489)
                    ·
                      refine ⟨4206943407921968610908617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5609257877229291481211489 4206943407921968610908617)
                      ·
                        rfl

theorem cell23_8192993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 5, 3, 2].length) (baseStart_8192993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8192993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8192993 prefixEnd_8192993 := by exact prefixLift 8192993
  have htrace : WordTrace (prefixWord ++ tailWord_8192993) baseStart_8192993 baseEnd_8192993 := by
    simpa [prefixWord, tailWord_8192993, baseEnd_8192993] using wordTrace_append hprefix tailTrace_8192993
  have hstable : (prefixWord ++ tailWord_8192993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8192993).length < 2 ^ (prefixWord ++ tailWord_8192993).sum := by decide
  have hdescent : baseEnd_8192993 < baseStart_8192993 := by decide
  rcases family_descends (prefixWord ++ tailWord_8192993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8193057 : List Nat := [1, 2, 3, 2, 3, 1, 1, 4, 2, 2, 2]
def baseStart_8193057 : Nat := 118140960795 + 8193057 * 2 ^ 59
def prefixEnd_8193057 : Nat := 4983230072969 + 3 ^ 40 * 8193057 * 2
def baseEnd_8193057 : Nat := 4206976270683856360508323

theorem tailTrace_8193057 : CollatzResearch.WordTrace tailWord_8193057 prefixEnd_8193057 4206976270683856360508323 := by
  unfold tailWord_8193057
  simp only [CollatzResearch.WordTrace]
  refine ⟨298825338278961226579713425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199216892185974151053142283 298825338278961226579713425)
  ·
    refine ⟨224119003709220919934785069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298825338278961226579713425 224119003709220919934785069)
    ·
      refine ⟨84044626390957844975544401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224119003709220919934785069 84044626390957844975544401)
      ·
        refine ⟨63033469793218383731658301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84044626390957844975544401 63033469793218383731658301)
        ·
          refine ⟨23637551172456893899371863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63033469793218383731658301 23637551172456893899371863)
          ·
            refine ⟨35456326758685340849057795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23637551172456893899371863 35456326758685340849057795)
            ·
              refine ⟨53184490138028011273586693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35456326758685340849057795 53184490138028011273586693)
              ·
                refine ⟨9972091900880252113797505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53184490138028011273586693 9972091900880252113797505)
                ·
                  refine ⟨7479068925660189085348129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9972091900880252113797505 7479068925660189085348129)
                  ·
                    refine ⟨5609301694245141814011097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7479068925660189085348129 5609301694245141814011097)
                    ·
                      refine ⟨4206976270683856360508323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5609301694245141814011097 4206976270683856360508323)
                      ·
                        rfl

theorem cell23_8193057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 4, 2, 2, 2].length) (baseStart_8193057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8193057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8193057 prefixEnd_8193057 := by exact prefixLift 8193057
  have htrace : WordTrace (prefixWord ++ tailWord_8193057) baseStart_8193057 baseEnd_8193057 := by
    simpa [prefixWord, tailWord_8193057, baseEnd_8193057] using wordTrace_append hprefix tailTrace_8193057
  have hstable : (prefixWord ++ tailWord_8193057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8193057).length < 2 ^ (prefixWord ++ tailWord_8193057).sum := by decide
  have hdescent : baseEnd_8193057 < baseStart_8193057 := by decide
  rcases family_descends (prefixWord ++ tailWord_8193057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8193073 : List Nat := [1, 2, 2, 3, 1, 2, 3, 1, 2, 3, 3]
def baseStart_8193073 : Nat := 118140960795 + 8193073 * 2 ^ 59
def prefixEnd_8193073 : Nat := 4983230072969 + 3 ^ 40 * 8193073 * 2
def baseEnd_8193073 : Nat := 4206984486374328297908249

theorem tailTrace_8193073 : CollatzResearch.WordTrace tailWord_8193073 prefixEnd_8193073 4206984486374328297908249 := by
  unfold tailWord_8193073
  simp only [CollatzResearch.WordTrace]
  refine ⟨298825921846903261312295873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199217281231268840874863915 298825921846903261312295873)
  ·
    refine ⟨224119441385177445984221905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298825921846903261312295873 224119441385177445984221905)
    ·
      refine ⟨168089581038883084488166429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224119441385177445984221905 168089581038883084488166429)
      ·
        refine ⟨63033592889581156683062411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168089581038883084488166429 63033592889581156683062411)
        ·
          refine ⟨94550389334371735024593617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63033592889581156683062411 94550389334371735024593617)
          ·
            refine ⟨70912792000778801268445213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94550389334371735024593617 70912792000778801268445213)
            ·
              refine ⟨26592297000292050475666955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70912792000778801268445213 26592297000292050475666955)
              ·
                refine ⟨39888445500438075713500433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26592297000292050475666955 39888445500438075713500433)
                ·
                  refine ⟨29916334125328556785125325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39888445500438075713500433 29916334125328556785125325)
                  ·
                    refine ⟨11218625296998208794421997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29916334125328556785125325 11218625296998208794421997)
                    ·
                      refine ⟨4206984486374328297908249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11218625296998208794421997 4206984486374328297908249)
                      ·
                        rfl

theorem cell23_8193073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_8193073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8193073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8193073 prefixEnd_8193073 := by exact prefixLift 8193073
  have htrace : WordTrace (prefixWord ++ tailWord_8193073) baseStart_8193073 baseEnd_8193073 := by
    simpa [prefixWord, tailWord_8193073, baseEnd_8193073] using wordTrace_append hprefix tailTrace_8193073
  have hstable : (prefixWord ++ tailWord_8193073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8193073).length < 2 ^ (prefixWord ++ tailWord_8193073).sum := by decide
  have hdescent : baseEnd_8193073 < baseStart_8193073 := by decide
  rcases family_descends (prefixWord ++ tailWord_8193073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8193093 : List Nat := [1, 3, 1, 1, 1, 3, 5, 1, 2, 5]
def baseStart_8193093 : Nat := 118140960795 + 8193093 * 2 ^ 59
def prefixEnd_8193093 : Nat := 4983230072969 + 3 ^ 40 * 8193093 * 2
def baseEnd_8193093 : Nat := 1402331585329139406552719

theorem tailTrace_8193093 : CollatzResearch.WordTrace tailWord_8193093 prefixEnd_8193093 1402331585329139406552719 := by
  unfold tailWord_8193093
  simp only [CollatzResearch.WordTrace]
  refine ⟨298826651306830804728023933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199217767537887203152015955 298826651306830804728023933)
  ·
    refine ⟨112059994240061551773008975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298826651306830804728023933 112059994240061551773008975)
    ·
      refine ⟨168089991360092327659513463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112059994240061551773008975 168089991360092327659513463)
      ·
        refine ⟨252134987040138491489270195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168089991360092327659513463 252134987040138491489270195)
        ·
          refine ⟨378202480560207737233905293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252134987040138491489270195 378202480560207737233905293)
          ·
            refine ⟨141825930210077901462714485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 378202480560207737233905293 141825930210077901462714485)
            ·
              refine ⟨13296180957194803262129483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 141825930210077901462714485 13296180957194803262129483)
              ·
                refine ⟨19944271435792204893194225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13296180957194803262129483 19944271435792204893194225)
                ·
                  refine ⟨14958203576844153669895669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19944271435792204893194225 14958203576844153669895669)
                  ·
                    refine ⟨1402331585329139406552719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14958203576844153669895669 1402331585329139406552719)
                    ·
                      rfl

theorem cell23_8193093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 2, 5].length) (baseStart_8193093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8193093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8193093 prefixEnd_8193093 := by exact prefixLift 8193093
  have htrace : WordTrace (prefixWord ++ tailWord_8193093) baseStart_8193093 baseEnd_8193093 := by
    simpa [prefixWord, tailWord_8193093, baseEnd_8193093] using wordTrace_append hprefix tailTrace_8193093
  have hstable : (prefixWord ++ tailWord_8193093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8193093).length < 2 ^ (prefixWord ++ tailWord_8193093).sum := by decide
  have hdescent : baseEnd_8193093 < baseStart_8193093 := by decide
  rcases family_descends (prefixWord ++ tailWord_8193093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8193146 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9]
def baseStart_8193146 : Nat := 118140960795 + 8193146 * 2 ^ 59
def prefixEnd_8193146 : Nat := 4983230072969 + 3 ^ 40 * 8193146 * 2
def baseEnd_8193146 : Nat := 4207021970462106512295413

theorem tailTrace_8193146 : CollatzResearch.WordTrace tailWord_8193146 prefixEnd_8193146 4207021970462106512295413 := by
  unfold tailWord_8193146
  simp only [CollatzResearch.WordTrace]
  refine ⟨74707146093909698694925823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199219056250425863186468861 74707146093909698694925823)
  ·
    refine ⟨112060719140864548042388735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74707146093909698694925823 112060719140864548042388735)
    ·
      refine ⟨168091078711296822063583103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112060719140864548042388735 168091078711296822063583103)
      ·
        refine ⟨252136618066945233095374655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168091078711296822063583103 252136618066945233095374655)
        ·
          refine ⟨378204927100417849643061983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252136618066945233095374655 378204927100417849643061983)
          ·
            refine ⟨567307390650626774464592975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378204927100417849643061983 567307390650626774464592975)
            ·
              refine ⟨850961085975940161696889463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 567307390650626774464592975 850961085975940161696889463)
              ·
                refine ⟨1276441628963910242545334195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 850961085975940161696889463 1276441628963910242545334195)
                ·
                  refine ⟨1914662443445865363818001293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1276441628963910242545334195 1914662443445865363818001293)
                  ·
                    refine ⟨717998416292199511431750485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1914662443445865363818001293 717998416292199511431750485)
                    ·
                      refine ⟨4207021970462106512295413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 717998416292199511431750485 4207021970462106512295413)
                      ·
                        rfl

theorem cell23_8193146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 3, 9].length) (baseStart_8193146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8193146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8193146 prefixEnd_8193146 := by exact prefixLift 8193146
  have htrace : WordTrace (prefixWord ++ tailWord_8193146) baseStart_8193146 baseEnd_8193146 := by
    simpa [prefixWord, tailWord_8193146, baseEnd_8193146] using wordTrace_append hprefix tailTrace_8193146
  have hstable : (prefixWord ++ tailWord_8193146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8193146).length < 2 ^ (prefixWord ++ tailWord_8193146).sum := by decide
  have hdescent : baseEnd_8193146 < baseStart_8193146 := by decide
  rcases family_descends (prefixWord ++ tailWord_8193146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8193153 : List Nat := [1, 2, 4, 2, 2, 1, 1, 2, 8]
def baseStart_8193153 : Nat := 118140960795 + 8193153 * 2 ^ 59
def prefixEnd_8193153 : Nat := 4983230072969 + 3 ^ 40 * 8193153 * 2
def baseEnd_8193153 : Nat := 467447284980743109434209

theorem tailTrace_8193153 : CollatzResearch.WordTrace tailWord_8193153 prefixEnd_8193153 467447284980743109434209 := by
  unfold tailWord_8193153
  simp only [CollatzResearch.WordTrace]
  refine ⟨298828839686613434975208113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199219226457742289983472075 298828839686613434975208113)
  ·
    refine ⟨224121629764960076231406085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298828839686613434975208113 224121629764960076231406085)
    ·
      refine ⟨42022805580930014293388641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224121629764960076231406085 42022805580930014293388641)
      ·
        refine ⟨31517104185697510720041481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42022805580930014293388641 31517104185697510720041481)
        ·
          refine ⟨23637828139273133040031111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31517104185697510720041481 23637828139273133040031111)
          ·
            refine ⟨35456742208909699560046667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23637828139273133040031111 35456742208909699560046667)
            ·
              refine ⟨53185113313364549340070001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35456742208909699560046667 53185113313364549340070001)
              ·
                refine ⟨39888834985023412005052501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53185113313364549340070001 39888834985023412005052501)
                ·
                  refine ⟨467447284980743109434209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39888834985023412005052501 467447284980743109434209)
                  ·
                    rfl

theorem cell23_8193153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 8].length) (baseStart_8193153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8193153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8193153 prefixEnd_8193153 := by exact prefixLift 8193153
  have htrace : WordTrace (prefixWord ++ tailWord_8193153) baseStart_8193153 baseEnd_8193153 := by
    simpa [prefixWord, tailWord_8193153, baseEnd_8193153] using wordTrace_append hprefix tailTrace_8193153
  have hstable : (prefixWord ++ tailWord_8193153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8193153).length < 2 ^ (prefixWord ++ tailWord_8193153).sum := by decide
  have hdescent : baseEnd_8193153 < baseStart_8193153 := by decide
  rcases family_descends (prefixWord ++ tailWord_8193153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8193207 : List Nat := [1, 1, 3, 1, 4, 1, 4, 1, 2, 3, 2]
def baseStart_8193207 : Nat := 118140960795 + 8193207 * 2 ^ 59
def prefixEnd_8193207 : Nat := 4983230072969 + 3 ^ 40 * 8193207 * 2
def baseEnd_8193207 : Nat := 4207053292782030773632633

theorem tailTrace_8193207 : CollatzResearch.WordTrace tailWord_8193207 prefixEnd_8193207 4207053292782030773632633 := by
  unfold tailWord_8193207
  simp only [CollatzResearch.WordTrace]
  refine ⟨298830809228417802197673875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199220539485611868131782583 298830809228417802197673875)
  ·
    refine ⟨448246213842626703296510813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298830809228417802197673875 448246213842626703296510813)
    ·
      refine ⟨168092330190985013736191555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 448246213842626703296510813 168092330190985013736191555)
      ·
        refine ⟨252138495286477520604287333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168092330190985013736191555 252138495286477520604287333)
        ·
          refine ⟨47275967866214535113303875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 252138495286477520604287333 47275967866214535113303875)
          ·
            refine ⟨70913951799321802669955813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47275967866214535113303875 70913951799321802669955813)
            ·
              refine ⟨13296365962372838000616715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70913951799321802669955813 13296365962372838000616715)
              ·
                refine ⟨19944548943559257000925073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13296365962372838000616715 19944548943559257000925073)
                ·
                  refine ⟨14958411707669442750693805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19944548943559257000925073 14958411707669442750693805)
                  ·
                    refine ⟨5609404390376041031510177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14958411707669442750693805 5609404390376041031510177)
                    ·
                      refine ⟨4207053292782030773632633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5609404390376041031510177 4207053292782030773632633)
                      ·
                        rfl

theorem cell23_8193207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 2, 3, 2].length) (baseStart_8193207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8193207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8193207 prefixEnd_8193207 := by exact prefixLift 8193207
  have htrace : WordTrace (prefixWord ++ tailWord_8193207) baseStart_8193207 baseEnd_8193207 := by
    simpa [prefixWord, tailWord_8193207, baseEnd_8193207] using wordTrace_append hprefix tailTrace_8193207
  have hstable : (prefixWord ++ tailWord_8193207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8193207).length < 2 ^ (prefixWord ++ tailWord_8193207).sum := by decide
  have hdescent : baseEnd_8193207 < baseStart_8193207 := by decide
  rcases family_descends (prefixWord ++ tailWord_8193207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8193213 : List Nat := [1, 4, 1, 2, 1, 1, 3, 1, 3, 6]
def baseStart_8193213 : Nat := 118140960795 + 8193213 * 2 ^ 59
def prefixEnd_8193213 : Nat := 4983230072969 + 3 ^ 40 * 8193213 * 2
def baseEnd_8193213 : Nat := 1402352124555319250052535

theorem tailTrace_8193213 : CollatzResearch.WordTrace tailWord_8193213 prefixEnd_8193213 1402352124555319250052535 := by
  unfold tailWord_8193213
  simp only [CollatzResearch.WordTrace]
  refine ⟨298831028066396065222392293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199220685377597376814928195 298831028066396065222392293)
  ·
    refine ⟨56030817762449262229198555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 298831028066396065222392293 56030817762449262229198555)
    ·
      refine ⟨84046226643673893343797833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56030817762449262229198555 84046226643673893343797833)
      ·
        refine ⟨63034669982755420007848375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84046226643673893343797833 63034669982755420007848375)
        ·
          refine ⟨94552004974133130011772563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63034669982755420007848375 94552004974133130011772563)
          ·
            refine ⟨141828007461199695017658845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94552004974133130011772563 141828007461199695017658845)
            ·
              refine ⟨53185502797949885631622067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141828007461199695017658845 53185502797949885631622067)
              ·
                refine ⟨79778254196924828447433101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53185502797949885631622067 79778254196924828447433101)
                ·
                  refine ⟨29916845323846810667787413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79778254196924828447433101 29916845323846810667787413)
                  ·
                    refine ⟨1402352124555319250052535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29916845323846810667787413 1402352124555319250052535)
                    ·
                      rfl

theorem cell23_8193213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 6].length) (baseStart_8193213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8193213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8193213 prefixEnd_8193213 := by exact prefixLift 8193213
  have htrace : WordTrace (prefixWord ++ tailWord_8193213) baseStart_8193213 baseEnd_8193213 := by
    simpa [prefixWord, tailWord_8193213, baseEnd_8193213] using wordTrace_append hprefix tailTrace_8193213
  have hstable : (prefixWord ++ tailWord_8193213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8193213).length < 2 ^ (prefixWord ++ tailWord_8193213).sum := by decide
  have hdescent : baseEnd_8193213 < baseStart_8193213 := by decide
  rcases family_descends (prefixWord ++ tailWord_8193213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8193233 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 5, 2, 4]
def baseStart_8193233 : Nat := 118140960795 + 8193233 * 2 ^ 59
def prefixEnd_8193233 : Nat := 4983230072969 + 3 ^ 40 * 8193233 * 2
def baseEnd_8193233 : Nat := 4207066643279047671907513

theorem tailTrace_8193233 : CollatzResearch.WordTrace tailWord_8193233 prefixEnd_8193233 4207066643279047671907513 := by
  unfold tailWord_8193233
  simp only [CollatzResearch.WordTrace]
  refine ⟨298831757526323608638120353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199221171684215739092080235 298831757526323608638120353)
  ·
    refine ⟨224123818144742706478590265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298831757526323608638120353 224123818144742706478590265)
    ·
      refine ⟨168092863608557029858942699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224123818144742706478590265 168092863608557029858942699)
      ·
        refine ⟨252139295412835544788414049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168092863608557029858942699 252139295412835544788414049)
        ·
          refine ⟨189104471559626658591310537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252139295412835544788414049 189104471559626658591310537)
          ·
            refine ⟨141828353669719993943482903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189104471559626658591310537 141828353669719993943482903)
            ·
              refine ⟨212742530504579990915224355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141828353669719993943482903 212742530504579990915224355)
              ·
                refine ⟨319113795756869986372836533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212742530504579990915224355 319113795756869986372836533)
                ·
                  refine ⟨29916918352206561222453425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 319113795756869986372836533 29916918352206561222453425)
                  ·
                    refine ⟨22437688764154920916840069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29916918352206561222453425 22437688764154920916840069)
                    ·
                      refine ⟨4207066643279047671907513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22437688764154920916840069 4207066643279047671907513)
                      ·
                        rfl

theorem cell23_8193233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 2, 4].length) (baseStart_8193233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8193233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8193233 prefixEnd_8193233 := by exact prefixLift 8193233
  have htrace : WordTrace (prefixWord ++ tailWord_8193233) baseStart_8193233 baseEnd_8193233 := by
    simpa [prefixWord, tailWord_8193233, baseEnd_8193233] using wordTrace_append hprefix tailTrace_8193233
  have hstable : (prefixWord ++ tailWord_8193233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8193233).length < 2 ^ (prefixWord ++ tailWord_8193233).sum := by decide
  have hdescent : baseEnd_8193233 < baseStart_8193233 := by decide
  rcases family_descends (prefixWord ++ tailWord_8193233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8193260 : List Nat := [2, 2, 1, 1, 2, 5, 3, 7]
def baseStart_8193260 : Nat := 118140960795 + 8193260 * 2 ^ 59
def prefixEnd_8193260 : Nat := 4983230072969 + 3 ^ 40 * 8193260 * 2
def baseEnd_8193260 : Nat := 155817796565063669121107

theorem tailTrace_8193260 : CollatzResearch.WordTrace tailWord_8193260 prefixEnd_8193260 155817796565063669121107 := by
  unfold tailWord_8193260
  simp only [CollatzResearch.WordTrace]
  refine ⟨149416371148612896124676617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199221828198150528166235489 149416371148612896124676617)
  ·
    refine ⟨112062278361459672093507463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149416371148612896124676617 112062278361459672093507463)
    ·
      refine ⟨168093417542189508140261195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112062278361459672093507463 168093417542189508140261195)
      ·
        refine ⟨252140126313284262210391793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168093417542189508140261195 252140126313284262210391793)
        ·
          refine ⟨189105094734963196657793845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252140126313284262210391793 189105094734963196657793845)
          ·
            refine ⟨17728602631402799686668173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 189105094734963196657793845 17728602631402799686668173)
            ·
              refine ⟨6648225986776049882500565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17728602631402799686668173 6648225986776049882500565)
              ·
                refine ⟨155817796565063669121107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6648225986776049882500565 155817796565063669121107)
                ·
                  rfl

theorem cell23_8193260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 7].length) (baseStart_8193260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8193260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8193260 prefixEnd_8193260 := by exact prefixLift 8193260
  have htrace : WordTrace (prefixWord ++ tailWord_8193260) baseStart_8193260 baseEnd_8193260 := by
    simpa [prefixWord, tailWord_8193260, baseEnd_8193260] using wordTrace_append hprefix tailTrace_8193260
  have hstable : (prefixWord ++ tailWord_8193260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8193260).length < 2 ^ (prefixWord ++ tailWord_8193260).sum := by decide
  have hdescent : baseEnd_8193260 < baseStart_8193260 := by decide
  rcases family_descends (prefixWord ++ tailWord_8193260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8193298 : List Nat := [3, 2, 4, 2, 1, 1, 3, 1, 2, 4]
def baseStart_8193298 : Nat := 118140960795 + 8193298 * 2 ^ 59
def prefixEnd_8193298 : Nat := 4983230072969 + 3 ^ 40 * 8193298 * 2
def baseEnd_8193298 : Nat := 1402366673173863305864905

theorem tailTrace_8193298 : CollatzResearch.WordTrace tailWord_8193298 prefixEnd_8193298 1402366673173863305864905 := by
  unfold tailWord_8193298
  simp only [CollatzResearch.WordTrace]
  refine ⟨74708532067772031184809137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199222752180725416492824365 74708532067772031184809137)
  ·
    refine ⟨56031399050829023388606853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74708532067772031184809137 56031399050829023388606853)
    ·
      refine ⟨10505887322030441885363785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56031399050829023388606853 10505887322030441885363785)
      ·
        refine ⟨7879415491522831414022839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10505887322030441885363785 7879415491522831414022839)
        ·
          refine ⟨11819123237284247121034259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7879415491522831414022839 11819123237284247121034259)
          ·
            refine ⟨17728684855926370681551389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11819123237284247121034259 17728684855926370681551389)
            ·
              refine ⟨6648256820972389005581771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17728684855926370681551389 6648256820972389005581771)
              ·
                refine ⟨9972385231458583508372657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6648256820972389005581771 9972385231458583508372657)
                ·
                  refine ⟨7479288923593937631279493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9972385231458583508372657 7479288923593937631279493)
                  ·
                    refine ⟨1402366673173863305864905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7479288923593937631279493 1402366673173863305864905)
                    ·
                      rfl

theorem cell23_8193298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_8193298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8193298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8193298 prefixEnd_8193298 := by exact prefixLift 8193298
  have htrace : WordTrace (prefixWord ++ tailWord_8193298) baseStart_8193298 baseEnd_8193298 := by
    simpa [prefixWord, tailWord_8193298, baseEnd_8193298] using wordTrace_append hprefix tailTrace_8193298
  have hstable : (prefixWord ++ tailWord_8193298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8193298).length < 2 ^ (prefixWord ++ tailWord_8193298).sum := by decide
  have hdescent : baseEnd_8193298 < baseStart_8193298 := by decide
  rcases family_descends (prefixWord ++ tailWord_8193298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8193330 : List Nat := [3, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5]
def baseStart_8193330 : Nat := 118140960795 + 8193330 * 2 ^ 59
def prefixEnd_8193330 : Nat := 4983230072969 + 3 ^ 40 * 8193330 * 2
def baseEnd_8193330 : Nat := 4207116450902533792394567

theorem tailTrace_8193330 : CollatzResearch.WordTrace tailWord_8193330 prefixEnd_8193330 4207116450902533792394567 := by
  unfold tailWord_8193330
  simp only [CollatzResearch.WordTrace]
  refine ⟨74708823851743048551100361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199223530271314796136267629 74708823851743048551100361)
  ·
    refine ⟨56031617888807286413325271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74708823851743048551100361 56031617888807286413325271)
    ·
      refine ⟨84047426833210929619987907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56031617888807286413325271 84047426833210929619987907)
      ·
        refine ⟨126071140249816394429981861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84047426833210929619987907 126071140249816394429981861)
        ·
          refine ⟨23638338796840573955621599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126071140249816394429981861 23638338796840573955621599)
          ·
            refine ⟨35457508195260860933432399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23638338796840573955621599 35457508195260860933432399)
            ·
              refine ⟨53186262292891291400148599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35457508195260860933432399 53186262292891291400148599)
              ·
                refine ⟨79779393439336937100222899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53186262292891291400148599 79779393439336937100222899)
                ·
                  refine ⟨119669090159005405650334349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79779393439336937100222899 119669090159005405650334349)
                  ·
                    refine ⟨44875908809627027118875381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 119669090159005405650334349 44875908809627027118875381)
                    ·
                      refine ⟨4207116450902533792394567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44875908809627027118875381 4207116450902533792394567)
                      ·
                        rfl

theorem cell23_8193330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_8193330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8193330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8193330 prefixEnd_8193330 := by exact prefixLift 8193330
  have htrace : WordTrace (prefixWord ++ tailWord_8193330) baseStart_8193330 baseEnd_8193330 := by
    simpa [prefixWord, tailWord_8193330, baseEnd_8193330] using wordTrace_append hprefix tailTrace_8193330
  have hstable : (prefixWord ++ tailWord_8193330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8193330).length < 2 ^ (prefixWord ++ tailWord_8193330).sum := by decide
  have hdescent : baseEnd_8193330 < baseStart_8193330 := by decide
  rcases family_descends (prefixWord ++ tailWord_8193330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8193344 : List Nat := [2, 1, 1, 2, 2, 1, 4, 4, 2, 2, 2]
def baseStart_8193344 : Nat := 118140960795 + 8193344 * 2 ^ 59
def prefixEnd_8193344 : Nat := 4983230072969 + 3 ^ 40 * 8193344 * 2
def baseEnd_8193344 : Nat := 4207123639631696737619503

theorem tailTrace_8193344 : CollatzResearch.WordTrace tailWord_8193344 prefixEnd_8193344 4207123639631696737619503 := by
  unfold tailWord_8193344
  simp only [CollatzResearch.WordTrace]
  refine ⟨149417903014460737297705543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199223870685947649730274057 149417903014460737297705543)
  ·
    refine ⟨224126854521691105946558315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149417903014460737297705543 224126854521691105946558315)
    ·
      refine ⟨336190281782536658919837473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224126854521691105946558315 336190281782536658919837473)
      ·
        refine ⟨252142711336902494189878105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336190281782536658919837473 252142711336902494189878105)
        ·
          refine ⟨189107033502676870642408579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252142711336902494189878105 189107033502676870642408579)
          ·
            refine ⟨283660550254015305963612869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189107033502676870642408579 283660550254015305963612869)
            ·
              refine ⟨53186353172627869868177413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 283660550254015305963612869 53186353172627869868177413)
              ·
                refine ⟨9972441219867725600283265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53186353172627869868177413 9972441219867725600283265)
                ·
                  refine ⟨7479330914900794200212449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9972441219867725600283265 7479330914900794200212449)
                  ·
                    refine ⟨5609498186175595650159337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7479330914900794200212449 5609498186175595650159337)
                    ·
                      refine ⟨4207123639631696737619503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5609498186175595650159337 4207123639631696737619503)
                      ·
                        rfl

theorem cell23_8193344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 4, 2, 2, 2].length) (baseStart_8193344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8193344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8193344 prefixEnd_8193344 := by exact prefixLift 8193344
  have htrace : WordTrace (prefixWord ++ tailWord_8193344) baseStart_8193344 baseEnd_8193344 := by
    simpa [prefixWord, tailWord_8193344, baseEnd_8193344] using wordTrace_append hprefix tailTrace_8193344
  have hstable : (prefixWord ++ tailWord_8193344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8193344).length < 2 ^ (prefixWord ++ tailWord_8193344).sum := by decide
  have hdescent : baseEnd_8193344 < baseStart_8193344 := by decide
  rcases family_descends (prefixWord ++ tailWord_8193344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8193360 : List Nat := [2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 3]
def baseStart_8193360 : Nat := 118140960795 + 8193360 * 2 ^ 59
def prefixEnd_8193360 : Nat := 4983230072969 + 3 ^ 40 * 8193360 * 2
def baseEnd_8193360 : Nat := 4207131855322168675019429

theorem tailTrace_8193360 : CollatzResearch.WordTrace tailWord_8193360 prefixEnd_8193360 4207131855322168675019429 := by
  unfold tailWord_8193360
  simp only [CollatzResearch.WordTrace]
  refine ⟨149418194798431754663996767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199224259731242339551995689 149418194798431754663996767)
  ·
    refine ⟨224127292197647631995995151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149418194798431754663996767 224127292197647631995995151)
    ·
      refine ⟨336190938296471447993992727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224127292197647631995995151 336190938296471447993992727)
      ·
        refine ⟨504286407444707171990989091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336190938296471447993992727 504286407444707171990989091)
        ·
          refine ⟨756429611167060757986483637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504286407444707171990989091 756429611167060757986483637)
          ·
            refine ⟨70915276046911946061232841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 756429611167060757986483637 70915276046911946061232841)
            ·
              refine ⟨53186457035183959545924631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70915276046911946061232841 53186457035183959545924631)
              ·
                refine ⟨79779685552775939318886947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53186457035183959545924631 79779685552775939318886947)
                ·
                  refine ⟨119669528329163908978330421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79779685552775939318886947 119669528329163908978330421)
                  ·
                    refine ⟨11219018280859116466718477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 119669528329163908978330421 11219018280859116466718477)
                    ·
                      refine ⟨4207131855322168675019429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11219018280859116466718477 4207131855322168675019429)
                      ·
                        rfl

theorem cell23_8193360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 3].length) (baseStart_8193360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8193360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8193360 prefixEnd_8193360 := by exact prefixLift 8193360
  have htrace : WordTrace (prefixWord ++ tailWord_8193360) baseStart_8193360 baseEnd_8193360 := by
    simpa [prefixWord, tailWord_8193360, baseEnd_8193360] using wordTrace_append hprefix tailTrace_8193360
  have hstable : (prefixWord ++ tailWord_8193360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8193360).length < 2 ^ (prefixWord ++ tailWord_8193360).sum := by decide
  have hdescent : baseEnd_8193360 < baseStart_8193360 := by decide
  rcases family_descends (prefixWord ++ tailWord_8193360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8193440 : List Nat := [2, 1, 1, 4, 1, 2, 2, 2, 8]
def baseStart_8193440 : Nat := 118140960795 + 8193440 * 2 ^ 59
def prefixEnd_8193440 : Nat := 4983230072969 + 3 ^ 40 * 8193440 * 2
def baseEnd_8193440 : Nat := 467463659308280929113229

theorem tailTrace_8193440 : CollatzResearch.WordTrace tailWord_8193440 prefixEnd_8193440 467463659308280929113229 := by
  unfold tailWord_8193440
  simp only [CollatzResearch.WordTrace]
  refine ⟨149419653718286841495452887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199226204957715788660603849 149419653718286841495452887)
  ·
    refine ⟨224129480577430262243179331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149419653718286841495452887 224129480577430262243179331)
    ·
      refine ⟨336194220866145393364768997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224129480577430262243179331 336194220866145393364768997)
      ·
        refine ⟨63036416412402261255894187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 336194220866145393364768997 63036416412402261255894187)
        ·
          refine ⟨94554624618603391883841281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63036416412402261255894187 94554624618603391883841281)
          ·
            refine ⟨70915968463952543912880961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94554624618603391883841281 70915968463952543912880961)
            ·
              refine ⟨53186976347964407934660721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70915968463952543912880961 53186976347964407934660721)
              ·
                refine ⟨39890232260973305950995541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53186976347964407934660721 39890232260973305950995541)
                ·
                  refine ⟨467463659308280929113229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39890232260973305950995541 467463659308280929113229)
                  ·
                    rfl

theorem cell23_8193440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 8].length) (baseStart_8193440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8193440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8193440 prefixEnd_8193440 := by exact prefixLift 8193440
  have htrace : WordTrace (prefixWord ++ tailWord_8193440) baseStart_8193440 baseEnd_8193440 := by
    simpa [prefixWord, tailWord_8193440, baseEnd_8193440] using wordTrace_append hprefix tailTrace_8193440
  have hstable : (prefixWord ++ tailWord_8193440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8193440).length < 2 ^ (prefixWord ++ tailWord_8193440).sum := by decide
  have hdescent : baseEnd_8193440 < baseStart_8193440 := by decide
  rcases family_descends (prefixWord ++ tailWord_8193440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8193461 : List Nat := [1, 3, 3, 2, 2, 1, 2, 4, 1, 4]
def baseStart_8193461 : Nat := 118140960795 + 8193461 * 2 ^ 59
def prefixEnd_8193461 : Nat := 4983230072969 + 3 ^ 40 * 8193461 * 2
def baseEnd_8193461 : Nat := 1402394572289424259952155

theorem tailTrace_8193461 : CollatzResearch.WordTrace tailWord_8193461 prefixEnd_8193461 1402394572289424259952155 := by
  unfold tailWord_8193461
  simp only [CollatzResearch.WordTrace]
  refine ⟨298840073369497603577420237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199226715579665069051613491 298840073369497603577420237)
  ·
    refine ⟨112065027513561601341532589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298840073369497603577420237 112065027513561601341532589)
    ·
      refine ⟨42024385317585600503074721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112065027513561601341532589 42024385317585600503074721)
      ·
        refine ⟨31518288988189200377306041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42024385317585600503074721 31518288988189200377306041)
        ·
          refine ⟨23638716741141900282979531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31518288988189200377306041 23638716741141900282979531)
          ·
            refine ⟨35458075111712850424469297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23638716741141900282979531 35458075111712850424469297)
            ·
              refine ⟨26593556333784637818351973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35458075111712850424469297 26593556333784637818351973)
              ·
                refine ⟨4986291812584619590940995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26593556333784637818351973 4986291812584619590940995)
                ·
                  refine ⟨7479437718876929386411493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4986291812584619590940995 7479437718876929386411493)
                  ·
                    refine ⟨1402394572289424259952155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7479437718876929386411493 1402394572289424259952155)
                    ·
                      rfl

theorem cell23_8193461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_8193461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8193461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8193461 prefixEnd_8193461 := by exact prefixLift 8193461
  have htrace : WordTrace (prefixWord ++ tailWord_8193461) baseStart_8193461 baseEnd_8193461 := by
    simpa [prefixWord, tailWord_8193461, baseEnd_8193461] using wordTrace_append hprefix tailTrace_8193461
  have hstable : (prefixWord ++ tailWord_8193461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8193461).length < 2 ^ (prefixWord ++ tailWord_8193461).sum := by decide
  have hdescent : baseEnd_8193461 < baseStart_8193461 := by decide
  rcases family_descends (prefixWord ++ tailWord_8193461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8193487 : List Nat := [1, 1, 2, 1, 1, 4, 3, 4, 1, 5]
def baseStart_8193487 : Nat := 118140960795 + 8193487 * 2 ^ 59
def prefixEnd_8193487 : Nat := 4983230072969 + 3 ^ 40 * 8193487 * 2
def baseEnd_8193487 : Nat := 1402399022455096559377115

theorem tailTrace_8193487 : CollatzResearch.WordTrace tailWord_8193487 prefixEnd_8193487 1402399022455096559377115 := by
  unfold tailWord_8193487
  simp only [CollatzResearch.WordTrace]
  refine ⟨298841021667403410017866715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199227347778268940011911143 298841021667403410017866715)
  ·
    refine ⟨448261532501105115026800073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298841021667403410017866715 448261532501105115026800073)
    ·
      refine ⟨336196149375828836270100055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 448261532501105115026800073 336196149375828836270100055)
      ·
        refine ⟨504294224063743254405150083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336196149375828836270100055 504294224063743254405150083)
        ·
          refine ⟨756441336095614881607725125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504294224063743254405150083 756441336095614881607725125)
          ·
            refine ⟨141832750517927790301448461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 756441336095614881607725125 141832750517927790301448461)
            ·
              refine ⟨53187281444222921363043173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141832750517927790301448461 53187281444222921363043173)
              ·
                refine ⟨9972615270791797755570595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53187281444222921363043173 9972615270791797755570595)
                ·
                  refine ⟨14958922906187696633355893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9972615270791797755570595 14958922906187696633355893)
                  ·
                    refine ⟨1402399022455096559377115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14958922906187696633355893 1402399022455096559377115)
                    ·
                      rfl

theorem cell23_8193487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 4, 1, 5].length) (baseStart_8193487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8193487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8193487 prefixEnd_8193487 := by exact prefixLift 8193487
  have htrace : WordTrace (prefixWord ++ tailWord_8193487) baseStart_8193487 baseEnd_8193487 := by
    simpa [prefixWord, tailWord_8193487, baseEnd_8193487] using wordTrace_append hprefix tailTrace_8193487
  have hstable : (prefixWord ++ tailWord_8193487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8193487).length < 2 ^ (prefixWord ++ tailWord_8193487).sum := by decide
  have hdescent : baseEnd_8193487 < baseStart_8193487 := by decide
  rcases family_descends (prefixWord ++ tailWord_8193487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8193511 : List Nat := [1, 1, 5, 2, 1, 3, 1, 2, 2, 3, 2]
def baseStart_8193511 : Nat := 118140960795 + 8193511 * 2 ^ 59
def prefixEnd_8193511 : Nat := 4983230072969 + 3 ^ 40 * 8193511 * 2
def baseEnd_8193511 : Nat := 4207209390900997584231235

theorem tailTrace_8193511 : CollatzResearch.WordTrace tailWord_8193511 prefixEnd_8193511 4207209390900997584231235 := by
  unfold tailWord_8193511
  simp only [CollatzResearch.WordTrace]
  refine ⟨298841897019316462116740387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199227931346210974744493591 298841897019316462116740387)
  ·
    refine ⟨448262845528974693175110581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298841897019316462116740387 448262845528974693175110581)
    ·
      refine ⟨42024641768341377485166617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 448262845528974693175110581 42024641768341377485166617)
      ·
        refine ⟨31518481326256033113874963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42024641768341377485166617 31518481326256033113874963)
        ·
          refine ⟨47277721989384049670812445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31518481326256033113874963 47277721989384049670812445)
          ·
            refine ⟨17729145746019018626554667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47277721989384049670812445 17729145746019018626554667)
            ·
              refine ⟨26593718619028527939832001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17729145746019018626554667 26593718619028527939832001)
              ·
                refine ⟨19945288964271395954874001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26593718619028527939832001 19945288964271395954874001)
                ·
                  refine ⟨14958966723203546966155501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19945288964271395954874001 14958966723203546966155501)
                  ·
                    refine ⟨5609612521201330112308313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14958966723203546966155501 5609612521201330112308313)
                    ·
                      refine ⟨4207209390900997584231235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5609612521201330112308313 4207209390900997584231235)
                      ·
                        rfl

theorem cell23_8193511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_8193511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8193511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8193511 prefixEnd_8193511 := by exact prefixLift 8193511
  have htrace : WordTrace (prefixWord ++ tailWord_8193511) baseStart_8193511 baseEnd_8193511 := by
    simpa [prefixWord, tailWord_8193511, baseEnd_8193511] using wordTrace_append hprefix tailTrace_8193511
  have hstable : (prefixWord ++ tailWord_8193511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8193511).length < 2 ^ (prefixWord ++ tailWord_8193511).sum := by decide
  have hdescent : baseEnd_8193511 < baseStart_8193511 := by decide
  rcases family_descends (prefixWord ++ tailWord_8193511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8193538 : List Nat := [3, 4, 1, 2, 1, 3, 1, 2, 1, 5]
def baseStart_8193538 : Nat := 118140960795 + 8193538 * 2 ^ 59
def prefixEnd_8193538 : Nat := 4983230072969 + 3 ^ 40 * 8193538 * 2
def baseEnd_8193538 : Nat := 1402407751626222992864537

theorem tailTrace_8193538 : CollatzResearch.WordTrace tailWord_8193538 prefixEnd_8193538 1402407751626222992864537 := by
  unfold tailWord_8193538
  simp only [CollatzResearch.WordTrace]
  refine ⟨74710720447554661431993317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199228587860145763818648845 74710720447554661431993317)
  ·
    refine ⟨14008260083916499018498747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74710720447554661431993317 14008260083916499018498747)
    ·
      refine ⟨21012390125874748527748121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14008260083916499018498747 21012390125874748527748121)
      ·
        refine ⟨15759292594406061395811091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21012390125874748527748121 15759292594406061395811091)
        ·
          refine ⟨23638938891609092093716637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15759292594406061395811091 23638938891609092093716637)
          ·
            refine ⟨8864602084353409535143739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23638938891609092093716637 8864602084353409535143739)
            ·
              refine ⟨13296903126530114302715609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8864602084353409535143739 13296903126530114302715609)
              ·
                refine ⟨9972677344897585727036707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13296903126530114302715609 9972677344897585727036707)
                ·
                  refine ⟨14959016017346378590555061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9972677344897585727036707 14959016017346378590555061)
                  ·
                    refine ⟨1402407751626222992864537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14959016017346378590555061 1402407751626222992864537)
                    ·
                      rfl

theorem cell23_8193538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_8193538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8193538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8193538 prefixEnd_8193538 := by exact prefixLift 8193538
  have htrace : WordTrace (prefixWord ++ tailWord_8193538) baseStart_8193538 baseEnd_8193538 := by
    simpa [prefixWord, tailWord_8193538, baseEnd_8193538] using wordTrace_append hprefix tailTrace_8193538
  have hstable : (prefixWord ++ tailWord_8193538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8193538).length < 2 ^ (prefixWord ++ tailWord_8193538).sum := by decide
  have hdescent : baseEnd_8193538 < baseStart_8193538 := by decide
  rcases family_descends (prefixWord ++ tailWord_8193538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8193591 : List Nat := [1, 1, 3, 1, 2, 4, 2, 3, 2, 1, 3]
def baseStart_8193591 : Nat := 118140960795 + 8193591 * 2 ^ 59
def prefixEnd_8193591 : Nat := 4983230072969 + 3 ^ 40 * 8193591 * 2
def baseEnd_8193591 : Nat := 4207250469353357271230867

theorem tailTrace_8193591 : CollatzResearch.WordTrace tailWord_8193591 prefixEnd_8193591 4207250469353357271230867 := by
  unfold tailWord_8193591
  simp only [CollatzResearch.WordTrace]
  refine ⟨298844814859026635779652627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199229876572684423853101751 298844814859026635779652627)
  ·
    refine ⟨448267222288539953669478941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298844814859026635779652627 448267222288539953669478941)
    ·
      refine ⟨168100208358202482626054603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 448267222288539953669478941 168100208358202482626054603)
      ·
        refine ⟨252150312537303723939081905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168100208358202482626054603 252150312537303723939081905)
        ·
          refine ⟨189112734402977792954311429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252150312537303723939081905 189112734402977792954311429)
          ·
            refine ⟨35458637700558336178933393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189112734402977792954311429 35458637700558336178933393)
            ·
              refine ⟨26593978275418752134200045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35458637700558336178933393 26593978275418752134200045)
              ·
                refine ⟨9972741853282032050325017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26593978275418752134200045 9972741853282032050325017)
                ·
                  refine ⟨7479556389961524037743763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9972741853282032050325017 7479556389961524037743763)
                  ·
                    refine ⟨11219334584942286056615645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7479556389961524037743763 11219334584942286056615645)
                    ·
                      refine ⟨4207250469353357271230867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11219334584942286056615645 4207250469353357271230867)
                      ·
                        rfl

theorem cell23_8193591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 3, 2, 1, 3].length) (baseStart_8193591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8193591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8193591 prefixEnd_8193591 := by exact prefixLift 8193591
  have htrace : WordTrace (prefixWord ++ tailWord_8193591) baseStart_8193591 baseEnd_8193591 := by
    simpa [prefixWord, tailWord_8193591, baseEnd_8193591] using wordTrace_append hprefix tailTrace_8193591
  have hstable : (prefixWord ++ tailWord_8193591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8193591).length < 2 ^ (prefixWord ++ tailWord_8193591).sum := by decide
  have hdescent : baseEnd_8193591 < baseStart_8193591 := by decide
  rcases family_descends (prefixWord ++ tailWord_8193591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8193601 : List Nat := [1, 2, 5, 1, 1, 1, 1, 3, 3, 3, 2]
def baseStart_8193601 : Nat := 118140960795 + 8193601 * 2 ^ 59
def prefixEnd_8193601 : Nat := 4983230072969 + 3 ^ 40 * 8193601 * 2
def baseEnd_8193601 : Nat := 4207255604159902232105821

theorem tailTrace_8193601 : CollatzResearch.WordTrace tailWord_8193601 prefixEnd_8193601 4207255604159902232105821 := by
  unfold tailWord_8193601
  simp only [CollatzResearch.WordTrace]
  refine ⟨298845179588990407487516657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199230119725993604991677771 298845179588990407487516657)
  ·
    refine ⟨224133884691742805615637493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298845179588990407487516657 224133884691742805615637493)
    ·
      refine ⟨21012551689850888026466015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 224133884691742805615637493 21012551689850888026466015)
      ·
        refine ⟨31518827534776332039699023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21012551689850888026466015 31518827534776332039699023)
        ·
          refine ⟨47278241302164498059548535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31518827534776332039699023 47278241302164498059548535)
          ·
            refine ⟨70917361953246747089322803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47278241302164498059548535 70917361953246747089322803)
            ·
              refine ⟨106376042929870120633984205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70917361953246747089322803 106376042929870120633984205)
              ·
                refine ⟨39891016098701295237744077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106376042929870120633984205 39891016098701295237744077)
                ·
                  refine ⟨14959131037012985714154029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39891016098701295237744077 14959131037012985714154029)
                  ·
                    refine ⟨5609674138879869642807761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14959131037012985714154029 5609674138879869642807761)
                    ·
                      refine ⟨4207255604159902232105821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5609674138879869642807761 4207255604159902232105821)
                      ·
                        rfl

theorem cell23_8193601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_8193601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8193601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8193601 prefixEnd_8193601 := by exact prefixLift 8193601
  have htrace : WordTrace (prefixWord ++ tailWord_8193601) baseStart_8193601 baseEnd_8193601 := by
    simpa [prefixWord, tailWord_8193601, baseEnd_8193601] using wordTrace_append hprefix tailTrace_8193601
  have hstable : (prefixWord ++ tailWord_8193601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8193601).length < 2 ^ (prefixWord ++ tailWord_8193601).sum := by decide
  have hdescent : baseEnd_8193601 < baseStart_8193601 := by decide
  rcases family_descends (prefixWord ++ tailWord_8193601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8193617 : List Nat := [1, 2, 2, 1, 3, 2, 2, 1, 1, 3, 5]
def baseStart_8193617 : Nat := 118140960795 + 8193617 * 2 ^ 59
def prefixEnd_8193617 : Nat := 4983230072969 + 3 ^ 40 * 8193617 * 2
def baseEnd_8193617 : Nat := 4207263819850374169505747

theorem tailTrace_8193617 : CollatzResearch.WordTrace tailWord_8193617 prefixEnd_8193617 4207263819850374169505747 := by
  unfold tailWord_8193617
  simp only [CollatzResearch.WordTrace]
  refine ⟨298845763156932442220099105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199230508771288294813399403 298845763156932442220099105)
  ·
    refine ⟨224134322367699331665074329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298845763156932442220099105 224134322367699331665074329)
    ·
      refine ⟨168100741775774498748805747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224134322367699331665074329 168100741775774498748805747)
      ·
        refine ⟨252151112663661748123208621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168100741775774498748805747 252151112663661748123208621)
        ·
          refine ⟨94556667248873155546203233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252151112663661748123208621 94556667248873155546203233)
          ·
            refine ⟨70917500436654866659652425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94556667248873155546203233 70917500436654866659652425)
            ·
              refine ⟨53188125327491149994739319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70917500436654866659652425 53188125327491149994739319)
              ·
                refine ⟨79782187991236724992108979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53188125327491149994739319 79782187991236724992108979)
                ·
                  refine ⟨119673281986855087488163469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79782187991236724992108979 119673281986855087488163469)
                  ·
                    refine ⟨44877480745070657808061301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 119673281986855087488163469 44877480745070657808061301)
                    ·
                      refine ⟨4207263819850374169505747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44877480745070657808061301 4207263819850374169505747)
                      ·
                        rfl

theorem cell23_8193617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 3, 5].length) (baseStart_8193617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8193617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8193617 prefixEnd_8193617 := by exact prefixLift 8193617
  have htrace : WordTrace (prefixWord ++ tailWord_8193617) baseStart_8193617 baseEnd_8193617 := by
    simpa [prefixWord, tailWord_8193617, baseEnd_8193617] using wordTrace_append hprefix tailTrace_8193617
  have hstable : (prefixWord ++ tailWord_8193617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8193617).length < 2 ^ (prefixWord ++ tailWord_8193617).sum := by decide
  have hdescent : baseEnd_8193617 < baseStart_8193617 := by decide
  rcases family_descends (prefixWord ++ tailWord_8193617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8193618 : List Nat := [3, 2, 2, 1, 2, 3, 1, 3, 1, 3, 2]
def baseStart_8193618 : Nat := 118140960795 + 8193618 * 2 ^ 59
def prefixEnd_8193618 : Nat := 4983230072969 + 3 ^ 40 * 8193618 * 2
def baseEnd_8193618 : Nat := 4207264333331028665593243

theorem tailTrace_8193618 : CollatzResearch.WordTrace tailWord_8193618 prefixEnd_8193618 4207264333331028665593243 := by
  unfold tailWord_8193618
  simp only [CollatzResearch.WordTrace]
  refine ⟨74711449907482204847721377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199230533086619212927257005 74711449907482204847721377)
  ·
    refine ⟨56033587430611653635791033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74711449907482204847721377 56033587430611653635791033)
    ·
      refine ⟨42025190572958740226843275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56033587430611653635791033 42025190572958740226843275)
      ·
        refine ⟨63037785859438110340264913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42025190572958740226843275 63037785859438110340264913)
        ·
          refine ⟨47278339394578582755198685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63037785859438110340264913 47278339394578582755198685)
          ·
            refine ⟨17729377272966968533199507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47278339394578582755198685 17729377272966968533199507)
            ·
              refine ⟨26594065909450452799799261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17729377272966968533199507 26594065909450452799799261)
              ·
                refine ⟨9972774716043919799924723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26594065909450452799799261 9972774716043919799924723)
                ·
                  refine ⟨14959162074065879699887085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9972774716043919799924723 14959162074065879699887085)
                  ·
                    refine ⟨5609685777774704887457657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14959162074065879699887085 5609685777774704887457657)
                    ·
                      refine ⟨4207264333331028665593243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5609685777774704887457657 4207264333331028665593243)
                      ·
                        rfl

theorem cell23_8193618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 3, 1, 3, 2].length) (baseStart_8193618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8193618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8193618 prefixEnd_8193618 := by exact prefixLift 8193618
  have htrace : WordTrace (prefixWord ++ tailWord_8193618) baseStart_8193618 baseEnd_8193618 := by
    simpa [prefixWord, tailWord_8193618, baseEnd_8193618] using wordTrace_append hprefix tailTrace_8193618
  have hstable : (prefixWord ++ tailWord_8193618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8193618).length < 2 ^ (prefixWord ++ tailWord_8193618).sum := by decide
  have hdescent : baseEnd_8193618 < baseStart_8193618 := by decide
  rcases family_descends (prefixWord ++ tailWord_8193618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8193648 : List Nat := [2, 1, 1, 1, 6, 3, 1, 1, 1, 4, 2]
def baseStart_8193648 : Nat := 118140960795 + 8193648 * 2 ^ 59
def prefixEnd_8193648 : Nat := 4983230072969 + 3 ^ 40 * 8193648 * 2
def baseEnd_8193648 : Nat := 4207279737750663548218105

theorem tailTrace_8193648 : CollatzResearch.WordTrace tailWord_8193648 prefixEnd_8193648 4207279737750663548218105 := by
  unfold tailWord_8193648
  simp only [CollatzResearch.WordTrace]
  refine ⟨149423446909910067257238799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199231262546546756342985065 149423446909910067257238799)
  ·
    refine ⟨224135170364865100885858199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149423446909910067257238799 224135170364865100885858199)
    ·
      refine ⟨336202755547297651328787299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224135170364865100885858199 336202755547297651328787299)
      ·
        refine ⟨504304133320946476993180949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336202755547297651328787299 504304133320946476993180949)
        ·
          refine ⟨23639256249419366109055357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 504304133320946476993180949 23639256249419366109055357)
          ·
            refine ⟨8864721093532262290895759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23639256249419366109055357 8864721093532262290895759)
            ·
              refine ⟨13297081640298393436343639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8864721093532262290895759 13297081640298393436343639)
              ·
                refine ⟨19945622460447590154515459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13297081640298393436343639 19945622460447590154515459)
                ·
                  refine ⟨29918433690671385231773189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19945622460447590154515459 29918433690671385231773189)
                  ·
                    refine ⟨5609706317000884730957473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29918433690671385231773189 5609706317000884730957473)
                    ·
                      refine ⟨4207279737750663548218105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5609706317000884730957473 4207279737750663548218105)
                      ·
                        rfl

theorem cell23_8193648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 1, 4, 2].length) (baseStart_8193648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8193648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8193648 prefixEnd_8193648 := by exact prefixLift 8193648
  have htrace : WordTrace (prefixWord ++ tailWord_8193648) baseStart_8193648 baseEnd_8193648 := by
    simpa [prefixWord, tailWord_8193648, baseEnd_8193648] using wordTrace_append hprefix tailTrace_8193648
  have hstable : (prefixWord ++ tailWord_8193648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8193648).length < 2 ^ (prefixWord ++ tailWord_8193648).sum := by decide
  have hdescent : baseEnd_8193648 < baseStart_8193648 := by decide
  rcases family_descends (prefixWord ++ tailWord_8193648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8193671 : List Nat := [1, 1, 4, 2, 1, 3, 3, 3, 5]
def baseStart_8193671 : Nat := 118140960795 + 8193671 * 2 ^ 59
def prefixEnd_8193671 : Nat := 4983230072969 + 3 ^ 40 * 8193671 * 2
def baseEnd_8193671 : Nat := 467476838645079662025611

theorem tailTrace_8193671 : CollatzResearch.WordTrace tailWord_8193671 prefixEnd_8193671 467476838645079662025611 := by
  unfold tailWord_8193671
  simp only [CollatzResearch.WordTrace]
  refine ⟨298847732698736809442564867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199231821799157872961709911 298847732698736809442564867)
  ·
    refine ⟨448271599048105214163847301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298847732698736809442564867 448271599048105214163847301)
    ·
      refine ⟨84050924821519727655721369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 448271599048105214163847301 84050924821519727655721369)
      ·
        refine ⟨63038193616139795741791027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84050924821519727655721369 63038193616139795741791027)
        ·
          refine ⟨94557290424209693612686541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63038193616139795741791027 94557290424209693612686541)
          ·
            refine ⟨35458983909078635104757453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94557290424209693612686541 35458983909078635104757453)
            ·
              refine ⟨13297118965904488164284045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35458983909078635104757453 13297118965904488164284045)
              ·
                refine ⟨4986419612214183061606517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13297118965904488164284045 4986419612214183061606517)
                ·
                  refine ⟨467476838645079662025611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4986419612214183061606517 467476838645079662025611)
                  ·
                    rfl

theorem cell23_8193671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 3, 5].length) (baseStart_8193671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8193671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8193671 prefixEnd_8193671 := by exact prefixLift 8193671
  have htrace : WordTrace (prefixWord ++ tailWord_8193671) baseStart_8193671 baseEnd_8193671 := by
    simpa [prefixWord, tailWord_8193671, baseEnd_8193671] using wordTrace_append hprefix tailTrace_8193671
  have hstable : (prefixWord ++ tailWord_8193671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8193671).length < 2 ^ (prefixWord ++ tailWord_8193671).sum := by decide
  have hdescent : baseEnd_8193671 < baseStart_8193671 := by decide
  rcases family_descends (prefixWord ++ tailWord_8193671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8193688 : List Nat := [2, 1, 2, 4, 1, 3, 3, 2, 5]
def baseStart_8193688 : Nat := 118140960795 + 8193688 * 2 ^ 59
def prefixEnd_8193688 : Nat := 4983230072969 + 3 ^ 40 * 8193688 * 2
def baseEnd_8193688 : Nat := 467477808552982599079769

theorem tailTrace_8193688 : CollatzResearch.WordTrace tailWord_8193688 prefixEnd_8193688 467477808552982599079769 := by
  unfold tailWord_8193688
  simp only [CollatzResearch.WordTrace]
  refine ⟨149424176369837610672966859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199232235159783480897289145 149424176369837610672966859)
  ·
    refine ⟨224136264554756416009450289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149424176369837610672966859 224136264554756416009450289)
    ·
      refine ⟨168102198416067312007087717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224136264554756416009450289 168102198416067312007087717)
      ·
        refine ⟨31519162203012621001328947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168102198416067312007087717 31519162203012621001328947)
        ·
          refine ⟨47278743304518931501993421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31519162203012621001328947 47278743304518931501993421)
          ·
            refine ⟨17729528739194599313247533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47278743304518931501993421 17729528739194599313247533)
            ·
              refine ⟨6648573277197974742467825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17729528739194599313247533 6648573277197974742467825)
              ·
                refine ⟨4986429957898481056850869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6648573277197974742467825 4986429957898481056850869)
                ·
                  refine ⟨467477808552982599079769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4986429957898481056850869 467477808552982599079769)
                  ·
                    rfl

theorem cell23_8193688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 2, 5].length) (baseStart_8193688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8193688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8193688 prefixEnd_8193688 := by exact prefixLift 8193688
  have htrace : WordTrace (prefixWord ++ tailWord_8193688) baseStart_8193688 baseEnd_8193688 := by
    simpa [prefixWord, tailWord_8193688, baseEnd_8193688] using wordTrace_append hprefix tailTrace_8193688
  have hstable : (prefixWord ++ tailWord_8193688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8193688).length < 2 ^ (prefixWord ++ tailWord_8193688).sum := by decide
  have hdescent : baseEnd_8193688 < baseStart_8193688 := by decide
  rcases family_descends (prefixWord ++ tailWord_8193688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8193718 : List Nat := [5, 1, 3, 1, 1, 1, 1, 3, 2, 5]
def baseStart_8193718 : Nat := 118140960795 + 8193718 * 2 ^ 59
def prefixEnd_8193718 : Nat := 4983230072969 + 3 ^ 40 * 8193718 * 2
def baseEnd_8193718 : Nat := 1402438560465492758114261

theorem tailTrace_8193718 : CollatzResearch.WordTrace tailWord_8193718 prefixEnd_8193718 1402438560465492758114261 := by
  unfold tailWord_8193718
  simp only [CollatzResearch.WordTrace]
  refine ⟨18678090433097908529345363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199232964619711024313017205 18678090433097908529345363)
  ·
    refine ⟨28017135649646862794018045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18678090433097908529345363 28017135649646862794018045)
    ·
      refine ⟨10506425868617573547756767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28017135649646862794018045 10506425868617573547756767)
      ·
        refine ⟨15759638802926360321635151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10506425868617573547756767 15759638802926360321635151)
        ·
          refine ⟨23639458204389540482452727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15759638802926360321635151 23639458204389540482452727)
          ·
            refine ⟨35459187306584310723679091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23639458204389540482452727 35459187306584310723679091)
            ·
              refine ⟨53188780959876466085518637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35459187306584310723679091 53188780959876466085518637)
              ·
                refine ⟨19945792859953674782069489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53188780959876466085518637 19945792859953674782069489)
                ·
                  refine ⟨14959344644965256086552117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19945792859953674782069489 14959344644965256086552117)
                  ·
                    refine ⟨1402438560465492758114261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14959344644965256086552117 1402438560465492758114261)
                    ·
                      rfl

theorem cell23_8193718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_8193718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8193718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8193718 prefixEnd_8193718 := by exact prefixLift 8193718
  have htrace : WordTrace (prefixWord ++ tailWord_8193718) baseStart_8193718 baseEnd_8193718 := by
    simpa [prefixWord, tailWord_8193718, baseEnd_8193718] using wordTrace_append hprefix tailTrace_8193718
  have hstable : (prefixWord ++ tailWord_8193718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8193718).length < 2 ^ (prefixWord ++ tailWord_8193718).sum := by decide
  have hdescent : baseEnd_8193718 < baseStart_8193718 := by decide
  rcases family_descends (prefixWord ++ tailWord_8193718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8193771 : List Nat := [1, 1, 1, 1, 2, 4, 3, 1, 5, 1, 3]
def baseStart_8193771 : Nat := 118140960795 + 8193771 * 2 ^ 59
def prefixEnd_8193771 : Nat := 4983230072969 + 3 ^ 40 * 8193771 * 2
def baseEnd_8193771 : Nat := 4207342895871166566980039

theorem tailTrace_8193771 : CollatzResearch.WordTrace tailWord_8193771 prefixEnd_8193771 4207342895871166566980039 := by
  unfold tailWord_8193771
  simp only [CollatzResearch.WordTrace]
  refine ⟨298851379998374526521205167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199234253332249684347470111 298851379998374526521205167)
  ·
    refine ⟨448277069997561789781807751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298851379998374526521205167 448277069997561789781807751)
    ·
      refine ⟨672415604996342684672711627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448277069997561789781807751 672415604996342684672711627)
      ·
        refine ⟨1008623407494514027009067441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 672415604996342684672711627 1008623407494514027009067441)
        ·
          refine ⟨756467555620885520256800581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1008623407494514027009067441 756467555620885520256800581)
          ·
            refine ⟨141837666678916035048150109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 756467555620885520256800581 141837666678916035048150109)
            ·
              refine ⟨53189125004593513143056291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141837666678916035048150109 53189125004593513143056291)
              ·
                refine ⟨79783687506890269714584437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53189125004593513143056291 79783687506890269714584437)
                ·
                  refine ⟨7479720703770962785742291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79783687506890269714584437 7479720703770962785742291)
                  ·
                    refine ⟨11219581055656444178613437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7479720703770962785742291 11219581055656444178613437)
                    ·
                      refine ⟨4207342895871166566980039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11219581055656444178613437 4207342895871166566980039)
                      ·
                        rfl

theorem cell23_8193771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 5, 1, 3].length) (baseStart_8193771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8193771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8193771 prefixEnd_8193771 := by exact prefixLift 8193771
  have htrace : WordTrace (prefixWord ++ tailWord_8193771) baseStart_8193771 baseEnd_8193771 := by
    simpa [prefixWord, tailWord_8193771, baseEnd_8193771] using wordTrace_append hprefix tailTrace_8193771
  have hstable : (prefixWord ++ tailWord_8193771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8193771).length < 2 ^ (prefixWord ++ tailWord_8193771).sum := by decide
  have hdescent : baseEnd_8193771 < baseStart_8193771 := by decide
  rcases family_descends (prefixWord ++ tailWord_8193771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8193804 : List Nat := [2, 2, 1, 2, 2, 1, 2, 2, 3, 6]
def baseStart_8193804 : Nat := 118140960795 + 8193804 * 2 ^ 59
def prefixEnd_8193804 : Nat := 4983230072969 + 3 ^ 40 * 8193804 * 2
def baseEnd_8193804 : Nat := 1402453280244254979289129

theorem tailTrace_8193804 : CollatzResearch.WordTrace tailWord_8193804 prefixEnd_8193804 1402453280244254979289129 := by
  unfold tailWord_8193804
  simp only [CollatzResearch.WordTrace]
  refine ⟨149426291803627486578578233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199235055738169982104770977 149426291803627486578578233)
  ·
    refine ⟨112069718852720614933933675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149426291803627486578578233 112069718852720614933933675)
    ·
      refine ⟨168104578279080922400900513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112069718852720614933933675 168104578279080922400900513)
      ·
        refine ⟨126078433709310691800675385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168104578279080922400900513 126078433709310691800675385)
        ·
          refine ⟨94558825281983018850506539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126078433709310691800675385 94558825281983018850506539)
          ·
            refine ⟨141838237922974528275759809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94558825281983018850506539 141838237922974528275759809)
            ·
              refine ⟨106378678442230896206819857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141838237922974528275759809 106378678442230896206819857)
              ·
                refine ⟨79784008831673172155114893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106378678442230896206819857 79784008831673172155114893)
                ·
                  refine ⟨29919003311877439558168085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79784008831673172155114893 29919003311877439558168085)
                  ·
                    refine ⟨1402453280244254979289129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29919003311877439558168085 1402453280244254979289129)
                    ·
                      rfl

theorem cell23_8193804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 3, 6].length) (baseStart_8193804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8193804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8193804 prefixEnd_8193804 := by exact prefixLift 8193804
  have htrace : WordTrace (prefixWord ++ tailWord_8193804) baseStart_8193804 baseEnd_8193804 := by
    simpa [prefixWord, tailWord_8193804, baseEnd_8193804] using wordTrace_append hprefix tailTrace_8193804
  have hstable : (prefixWord ++ tailWord_8193804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8193804).length < 2 ^ (prefixWord ++ tailWord_8193804).sum := by decide
  have hdescent : baseEnd_8193804 < baseStart_8193804 := by decide
  rcases family_descends (prefixWord ++ tailWord_8193804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8193828 : List Nat := [2, 3, 1, 3, 2, 1, 1, 4, 1, 1, 4]
def baseStart_8193828 : Nat := 118140960795 + 8193828 * 2 ^ 59
def prefixEnd_8193828 : Nat := 4983230072969 + 3 ^ 40 * 8193828 * 2
def baseEnd_8193828 : Nat := 4207372164268472843967277

theorem tailTrace_8193828 : CollatzResearch.WordTrace tailWord_8193828 prefixEnd_8193828 4207372164268472843967277 := by
  unfold tailWord_8193828
  simp only [CollatzResearch.WordTrace]
  refine ⟨149426729479584012628015069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199235639306112016837353425 149426729479584012628015069)
  ·
    refine ⟨56035023554844004735505651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149426729479584012628015069 56035023554844004735505651)
    ·
      refine ⟨84052535332266007103258477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56035023554844004735505651 84052535332266007103258477)
      ·
        refine ⟨31519700749599752663721929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84052535332266007103258477 31519700749599752663721929)
        ·
          refine ⟨23639775562199814497791447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31519700749599752663721929 23639775562199814497791447)
          ·
            refine ⟨35459663343299721746687171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23639775562199814497791447 35459663343299721746687171)
            ·
              refine ⟨53189495014949582620030757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35459663343299721746687171 53189495014949582620030757)
              ·
                refine ⟨9973030315303046741255767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53189495014949582620030757 9973030315303046741255767)
                ·
                  refine ⟨14959545472954570111883651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9973030315303046741255767 14959545472954570111883651)
                  ·
                    refine ⟨22439318209431855167825477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14959545472954570111883651 22439318209431855167825477)
                    ·
                      refine ⟨4207372164268472843967277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22439318209431855167825477 4207372164268472843967277)
                      ·
                        rfl

theorem cell23_8193828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_8193828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8193828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8193828 prefixEnd_8193828 := by exact prefixLift 8193828
  have htrace : WordTrace (prefixWord ++ tailWord_8193828) baseStart_8193828 baseEnd_8193828 := by
    simpa [prefixWord, tailWord_8193828, baseEnd_8193828] using wordTrace_append hprefix tailTrace_8193828
  have hstable : (prefixWord ++ tailWord_8193828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8193828).length < 2 ^ (prefixWord ++ tailWord_8193828).sum := by decide
  have hdescent : baseEnd_8193828 < baseStart_8193828 := by decide
  rcases family_descends (prefixWord ++ tailWord_8193828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8193848 : List Nat := [2, 1, 2, 1, 3, 3, 2, 3, 1, 2, 3]
def baseStart_8193848 : Nat := 118140960795 + 8193848 * 2 ^ 59
def prefixEnd_8193848 : Nat := 4983230072969 + 3 ^ 40 * 8193848 * 2
def baseEnd_8193848 : Nat := 4207382433881562765717185

theorem tailTrace_8193848 : CollatzResearch.WordTrace tailWord_8193848 prefixEnd_8193848 4207382433881562765717185 := by
  unfold tailWord_8193848
  simp only [CollatzResearch.WordTrace]
  refine ⟨149427094209547784335879099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199236125612730379114505465 149427094209547784335879099)
  ·
    refine ⟨224140641314321676503818649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149427094209547784335879099 224140641314321676503818649)
    ·
      refine ⟨168105480985741257377863987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224140641314321676503818649 168105480985741257377863987)
      ·
        refine ⟨252158221478611886066795981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168105480985741257377863987 252158221478611886066795981)
        ·
          refine ⟨94559333054479457275048493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252158221478611886066795981 94559333054479457275048493)
          ·
            refine ⟨35459749895429796478143185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94559333054479457275048493 35459749895429796478143185)
            ·
              refine ⟨26594812421572347358607389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35459749895429796478143185 26594812421572347358607389)
              ·
                refine ⟨9973054658089630259477771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26594812421572347358607389 9973054658089630259477771)
                ·
                  refine ⟨14959581987134445389216657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9973054658089630259477771 14959581987134445389216657)
                  ·
                    refine ⟨11219686490350834041912493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14959581987134445389216657 11219686490350834041912493)
                    ·
                      refine ⟨4207382433881562765717185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11219686490350834041912493 4207382433881562765717185)
                      ·
                        rfl

theorem cell23_8193848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 3, 1, 2, 3].length) (baseStart_8193848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8193848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8193848 prefixEnd_8193848 := by exact prefixLift 8193848
  have htrace : WordTrace (prefixWord ++ tailWord_8193848) baseStart_8193848 baseEnd_8193848 := by
    simpa [prefixWord, tailWord_8193848, baseEnd_8193848] using wordTrace_append hprefix tailTrace_8193848
  have hstable : (prefixWord ++ tailWord_8193848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8193848).length < 2 ^ (prefixWord ++ tailWord_8193848).sum := by decide
  have hdescent : baseEnd_8193848 < baseStart_8193848 := by decide
  rcases family_descends (prefixWord ++ tailWord_8193848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8193928 : List Nat := [2, 1, 3, 3, 3, 1, 1, 1, 2, 6]
def baseStart_8193928 : Nat := 118140960795 + 8193928 * 2 ^ 59
def prefixEnd_8193928 : Nat := 4983230072969 + 3 ^ 40 * 8193928 * 2
def baseEnd_8193928 : Nat := 1402474504111307484238939

theorem tailTrace_8193928 : CollatzResearch.WordTrace tailWord_8193928 prefixEnd_8193928 1402474504111307484238939 := by
  unfold tailWord_8193928
  simp only [CollatzResearch.WordTrace]
  refine ⟨149428553129402871167335219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199238070839203828223113625 149428553129402871167335219)
  ·
    refine ⟨224142829694104306751002829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149428553129402871167335219 224142829694104306751002829)
    ·
      refine ⟨84053561135289115031626061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224142829694104306751002829 84053561135289115031626061)
      ·
        refine ⟨31520085425733418136859773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84053561135289115031626061 31520085425733418136859773)
        ·
          refine ⟨11820032034650031801322415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31520085425733418136859773 11820032034650031801322415)
          ·
            refine ⟨17730048051975047701983623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11820032034650031801322415 17730048051975047701983623)
            ·
              refine ⟨26595072077962571552975435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17730048051975047701983623 26595072077962571552975435)
              ·
                refine ⟨39892608116943857329463153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26595072077962571552975435 39892608116943857329463153)
                ·
                  refine ⟨29919456087707892997097365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39892608116943857329463153 29919456087707892997097365)
                  ·
                    refine ⟨1402474504111307484238939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29919456087707892997097365 1402474504111307484238939)
                    ·
                      rfl

theorem cell23_8193928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 2, 6].length) (baseStart_8193928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8193928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8193928 prefixEnd_8193928 := by exact prefixLift 8193928
  have htrace : WordTrace (prefixWord ++ tailWord_8193928) baseStart_8193928 baseEnd_8193928 := by
    simpa [prefixWord, tailWord_8193928, baseEnd_8193928] using wordTrace_append hprefix tailTrace_8193928
  have hstable : (prefixWord ++ tailWord_8193928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8193928).length < 2 ^ (prefixWord ++ tailWord_8193928).sum := by decide
  have hdescent : baseEnd_8193928 < baseStart_8193928 := by decide
  rcases family_descends (prefixWord ++ tailWord_8193928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8193941 : List Nat := [1, 3, 2, 1, 1, 3, 3, 2, 7]
def baseStart_8193941 : Nat := 118140960795 + 8193941 * 2 ^ 59
def prefixEnd_8193941 : Nat := 4983230072969 + 3 ^ 40 * 8193941 * 2
def baseEnd_8193941 : Nat := 467492243064714544650473

theorem tailTrace_8193941 : CollatzResearch.WordTrace tailWord_8193941 prefixEnd_8193941 467492243064714544650473 := by
  unfold tailWord_8193941
  simp only [CollatzResearch.WordTrace]
  refine ⟨298857580407758645554893677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199238386938505763703262451 298857580407758645554893677)
  ·
    refine ⟨112071592652909492083085129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298857580407758645554893677 112071592652909492083085129)
    ·
      refine ⟨84053694489682119062313847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112071592652909492083085129 84053694489682119062313847)
      ·
        refine ⟨126080541734523178593470771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84053694489682119062313847 126080541734523178593470771)
        ·
          refine ⟨189120812601784767890206157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126080541734523178593470771 189120812601784767890206157)
          ·
            refine ⟨70920304725669287958827309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189120812601784767890206157 70920304725669287958827309)
            ·
              refine ⟨26595114272125982984560241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70920304725669287958827309 26595114272125982984560241)
              ·
                refine ⟨19946335704094487238420181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26595114272125982984560241 19946335704094487238420181)
                ·
                  refine ⟨467492243064714544650473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19946335704094487238420181 467492243064714544650473)
                  ·
                    rfl

theorem cell23_8193941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 7].length) (baseStart_8193941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8193941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8193941 prefixEnd_8193941 := by exact prefixLift 8193941
  have htrace : WordTrace (prefixWord ++ tailWord_8193941) baseStart_8193941 baseEnd_8193941 := by
    simpa [prefixWord, tailWord_8193941, baseEnd_8193941] using wordTrace_append hprefix tailTrace_8193941
  have hstable : (prefixWord ++ tailWord_8193941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8193941).length < 2 ^ (prefixWord ++ tailWord_8193941).sum := by decide
  have hdescent : baseEnd_8193941 < baseStart_8193941 := by decide
  rcases family_descends (prefixWord ++ tailWord_8193941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8193969 : List Nat := [1, 2, 2, 4, 2, 3, 1, 2, 2, 2, 2]
def baseStart_8193969 : Nat := 118140960795 + 8193969 * 2 ^ 59
def prefixEnd_8193969 : Nat := 4983230072969 + 3 ^ 40 * 8193969 * 2
def baseEnd_8193969 : Nat := 4207444565040756792304129

theorem tailTrace_8193969 : CollatzResearch.WordTrace tailWord_8193969 prefixEnd_8193969 4207444565040756792304129 := by
  unfold tailWord_8193969
  simp only [CollatzResearch.WordTrace]
  refine ⟨298858601651657206336912961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199239067767771470891275307 298858601651657206336912961)
  ·
    refine ⟨224143951238742904752684721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298858601651657206336912961 224143951238742904752684721)
    ·
      refine ⟨168107963429057178564513541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224143951238742904752684721 168107963429057178564513541)
      ·
        refine ⟨31520243142948220980846289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168107963429057178564513541 31520243142948220980846289)
        ·
          refine ⟨23640182357211165735634717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31520243142948220980846289 23640182357211165735634717)
          ·
            refine ⟨8865068383954187150863019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23640182357211165735634717 8865068383954187150863019)
            ·
              refine ⟨13297602575931280726294529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8865068383954187150863019 13297602575931280726294529)
              ·
                refine ⟨9973201931948460544720897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13297602575931280726294529 9973201931948460544720897)
                ·
                  refine ⟨7479901448961345408540673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9973201931948460544720897 7479901448961345408540673)
                  ·
                    refine ⟨5609926086721009056405505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7479901448961345408540673 5609926086721009056405505)
                    ·
                      refine ⟨4207444565040756792304129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5609926086721009056405505 4207444565040756792304129)
                      ·
                        rfl

theorem cell23_8193969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_8193969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8193969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8193969 prefixEnd_8193969 := by exact prefixLift 8193969
  have htrace : WordTrace (prefixWord ++ tailWord_8193969) baseStart_8193969 baseEnd_8193969 := by
    simpa [prefixWord, tailWord_8193969, baseEnd_8193969] using wordTrace_append hprefix tailTrace_8193969
  have hstable : (prefixWord ++ tailWord_8193969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8193969).length < 2 ^ (prefixWord ++ tailWord_8193969).sum := by decide
  have hdescent : baseEnd_8193969 < baseStart_8193969 := by decide
  rcases family_descends (prefixWord ++ tailWord_8193969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8193971 : List Nat := [1, 1, 1, 2, 3, 1, 4, 1, 4, 5]
def baseStart_8193971 : Nat := 118140960795 + 8193971 * 2 ^ 59
def prefixEnd_8193971 : Nat := 4983230072969 + 3 ^ 40 * 8193971 * 2
def baseEnd_8193971 : Nat := 1402481864000688594826373

theorem tailTrace_8193971 : CollatzResearch.WordTrace tailWord_8193971 prefixEnd_8193971 1402481864000688594826373 := by
  unfold tailWord_8193971
  simp only [CollatzResearch.WordTrace]
  refine ⟨298858674597649960678485767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199239116398433307118990511 298858674597649960678485767)
  ·
    refine ⟨448288011896474941017728651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298858674597649960678485767 448288011896474941017728651)
    ·
      refine ⟨672432017844712411526592977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448288011896474941017728651 672432017844712411526592977)
      ·
        refine ⟨504324013383534308644944733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 672432017844712411526592977 504324013383534308644944733)
        ·
          refine ⟨189121505018825365741854275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 504324013383534308644944733 189121505018825365741854275)
          ·
            refine ⟨283682257528238048612781413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189121505018825365741854275 283682257528238048612781413)
            ·
              refine ⟨53190423286544634114896515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 283682257528238048612781413 53190423286544634114896515)
              ·
                refine ⟨79785634929816951172344773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53190423286544634114896515 79785634929816951172344773)
                ·
                  refine ⟨14959806549340678344814645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79785634929816951172344773 14959806549340678344814645)
                  ·
                    refine ⟨1402481864000688594826373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14959806549340678344814645 1402481864000688594826373)
                    ·
                      rfl

theorem cell23_8193971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 4, 5].length) (baseStart_8193971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8193971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8193971 prefixEnd_8193971 := by exact prefixLift 8193971
  have htrace : WordTrace (prefixWord ++ tailWord_8193971) baseStart_8193971 baseEnd_8193971 := by
    simpa [prefixWord, tailWord_8193971, baseEnd_8193971] using wordTrace_append hprefix tailTrace_8193971
  have hstable : (prefixWord ++ tailWord_8193971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8193971).length < 2 ^ (prefixWord ++ tailWord_8193971).sum := by decide
  have hdescent : baseEnd_8193971 < baseStart_8193971 := by decide
  rcases family_descends (prefixWord ++ tailWord_8193971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8193978 : List Nat := [3, 1, 1, 1, 2, 1, 2, 3, 2, 5, 2]
def baseStart_8193978 : Nat := 118140960795 + 8193978 * 2 ^ 59
def prefixEnd_8193978 : Nat := 4983230072969 + 3 ^ 40 * 8193978 * 2
def baseEnd_8193978 : Nat := 4207449186366647257091587

theorem tailTrace_8193978 : CollatzResearch.WordTrace tailWord_8193978 prefixEnd_8193978 4207449186366647257091587 := by
  unfold tailWord_8193978
  simp only [CollatzResearch.WordTrace]
  refine ⟨74714732477156150218497647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199239286605749733915993725 74714732477156150218497647)
  ·
    refine ⟨112072098715734225327746471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74714732477156150218497647 112072098715734225327746471)
    ·
      refine ⟨168108148073601337991619707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112072098715734225327746471 168108148073601337991619707)
      ·
        refine ⟨252162222110402006987429561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168108148073601337991619707 252162222110402006987429561)
        ·
          refine ⟨189121666582801505240572171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252162222110402006987429561 189121666582801505240572171)
          ·
            refine ⟨283682499874202257860858257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189121666582801505240572171 283682499874202257860858257)
            ·
              refine ⟨212761874905651693395643693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283682499874202257860858257 212761874905651693395643693)
              ·
                refine ⟨79785703089619385023366385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 212761874905651693395643693 79785703089619385023366385)
                ·
                  refine ⟨59839277317214538767524789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79785703089619385023366385 59839277317214538767524789)
                  ·
                    refine ⟨5609932248488863009455449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59839277317214538767524789 5609932248488863009455449)
                    ·
                      refine ⟨4207449186366647257091587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5609932248488863009455449 4207449186366647257091587)
                      ·
                        rfl

theorem cell23_8193978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 2, 5, 2].length) (baseStart_8193978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8193978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8193978 prefixEnd_8193978 := by exact prefixLift 8193978
  have htrace : WordTrace (prefixWord ++ tailWord_8193978) baseStart_8193978 baseEnd_8193978 := by
    simpa [prefixWord, tailWord_8193978, baseEnd_8193978] using wordTrace_append hprefix tailTrace_8193978
  have hstable : (prefixWord ++ tailWord_8193978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8193978).length < 2 ^ (prefixWord ++ tailWord_8193978).sum := by decide
  have hdescent : baseEnd_8193978 < baseStart_8193978 := by decide
  rcases family_descends (prefixWord ++ tailWord_8193978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8194008 : List Nat := [2, 1, 2, 2, 2, 2, 2, 3, 2, 1, 4]
def baseStart_8194008 : Nat := 118140960795 + 8194008 * 2 ^ 59
def prefixEnd_8194008 : Nat := 4983230072969 + 3 ^ 40 * 8194008 * 2
def baseEnd_8194008 : Nat := 4207464590786282139716449

theorem tailTrace_8194008 : CollatzResearch.WordTrace tailWord_8194008 prefixEnd_8194008 4207464590786282139716449 := by
  unfold tailWord_8194008
  simp only [CollatzResearch.WordTrace]
  refine ⟨149430012049257957998791339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199240016065677277331721785 149430012049257957998791339)
  ·
    refine ⟨224145018073886936998187009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149430012049257957998791339 224145018073886936998187009)
    ·
      refine ⟨168108763555415202748640257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224145018073886936998187009 168108763555415202748640257)
      ·
        refine ⟨126081572666561402061480193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168108763555415202748640257 126081572666561402061480193)
        ·
          refine ⟨94561179499921051546110145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126081572666561402061480193 94561179499921051546110145)
          ·
            refine ⟨70920884624940788659582609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94561179499921051546110145 70920884624940788659582609)
            ·
              refine ⟨53190663468705591494686957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70920884624940788659582609 53190663468705591494686957)
              ·
                refine ⟨19946498800764596810507609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53190663468705591494686957 19946498800764596810507609)
                ·
                  refine ⟨14959874100573447607880707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19946498800764596810507609 14959874100573447607880707)
                  ·
                    refine ⟨22439811150860171411821061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14959874100573447607880707 22439811150860171411821061)
                    ·
                      refine ⟨4207464590786282139716449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22439811150860171411821061 4207464590786282139716449)
                      ·
                        rfl

theorem cell23_8194008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_8194008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8194008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8194008 prefixEnd_8194008 := by exact prefixLift 8194008
  have htrace : WordTrace (prefixWord ++ tailWord_8194008) baseStart_8194008 baseEnd_8194008 := by
    simpa [prefixWord, tailWord_8194008, baseEnd_8194008] using wordTrace_append hprefix tailTrace_8194008
  have hstable : (prefixWord ++ tailWord_8194008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8194008).length < 2 ^ (prefixWord ++ tailWord_8194008).sum := by decide
  have hdescent : baseEnd_8194008 < baseStart_8194008 := by decide
  rcases family_descends (prefixWord ++ tailWord_8194008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8194031 : List Nat := [1, 1, 2, 1, 4, 2, 1, 3, 8]
def baseStart_8194031 : Nat := 118140960795 + 8194031 * 2 ^ 59
def prefixEnd_8194031 : Nat := 4983230072969 + 3 ^ 40 * 8194031 * 2
def baseEnd_8194031 : Nat := 467497377871259505525427

theorem tailTrace_8194031 : CollatzResearch.WordTrace tailWord_8194031 prefixEnd_8194031 467497377871259505525427 := by
  unfold tailWord_8194031
  simp only [CollatzResearch.WordTrace]
  refine ⟨298860862977432590925669947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199240575318288393950446631 298860862977432590925669947)
  ·
    refine ⟨448291294466148886388504921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298860862977432590925669947 448291294466148886388504921)
    ·
      refine ⟨336218470849611664791378691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 448291294466148886388504921 336218470849611664791378691)
      ·
        refine ⟨504327706274417497187068037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336218470849611664791378691 504327706274417497187068037)
        ·
          refine ⟨94561444926453280722575257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 504327706274417497187068037 94561444926453280722575257)
          ·
            refine ⟨70921083694839960541931443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94561444926453280722575257 70921083694839960541931443)
            ·
              refine ⟨106381625542259940812897165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70921083694839960541931443 106381625542259940812897165)
              ·
                refine ⟨39893109578347477804836437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106381625542259940812897165 39893109578347477804836437)
                ·
                  refine ⟨467497377871259505525427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39893109578347477804836437 467497377871259505525427)
                  ·
                    rfl

theorem cell23_8194031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 8].length) (baseStart_8194031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8194031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8194031 prefixEnd_8194031 := by exact prefixLift 8194031
  have htrace : WordTrace (prefixWord ++ tailWord_8194031) baseStart_8194031 baseEnd_8194031 := by
    simpa [prefixWord, tailWord_8194031, baseEnd_8194031] using wordTrace_append hprefix tailTrace_8194031
  have hstable : (prefixWord ++ tailWord_8194031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8194031).length < 2 ^ (prefixWord ++ tailWord_8194031).sum := by decide
  have hdescent : baseEnd_8194031 < baseStart_8194031 := by decide
  rcases family_descends (prefixWord ++ tailWord_8194031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8194035 : List Nat := [1, 1, 1, 2, 2, 2, 1, 8, 1, 4]
def baseStart_8194035 : Nat := 118140960795 + 8194035 * 2 ^ 59
def prefixEnd_8194035 : Nat := 4983230072969 + 3 ^ 40 * 8194035 * 2
def baseEnd_8194035 : Nat := 1402492818254651178026275

theorem tailTrace_8194035 : CollatzResearch.WordTrace tailWord_8194035 prefixEnd_8194035 1402492818254651178026275 := by
  unfold tailWord_8194035
  simp only [CollatzResearch.WordTrace]
  refine ⟨298861008869418099608815559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199240672579612066405877039 298861008869418099608815559)
  ·
    refine ⟨448291513304127149413223339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298861008869418099608815559 448291513304127149413223339)
    ·
      refine ⟨672437269956190724119835009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448291513304127149413223339 672437269956190724119835009)
      ·
        refine ⟨504327952467143043089876257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 672437269956190724119835009 504327952467143043089876257)
        ·
          refine ⟨378245964350357282317407193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 504327952467143043089876257 378245964350357282317407193)
          ·
            refine ⟨283684473262767961738055395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 378245964350357282317407193 283684473262767961738055395)
            ·
              refine ⟨425526709894151942607083093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283684473262767961738055395 425526709894151942607083093)
              ·
                refine ⟨4986641131572093077426755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 425526709894151942607083093 4986641131572093077426755)
                ·
                  refine ⟨7479961697358139616140133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4986641131572093077426755 7479961697358139616140133)
                  ·
                    refine ⟨1402492818254651178026275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7479961697358139616140133 1402492818254651178026275)
                    ·
                      rfl

theorem cell23_8194035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 8, 1, 4].length) (baseStart_8194035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8194035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8194035 prefixEnd_8194035 := by exact prefixLift 8194035
  have htrace : WordTrace (prefixWord ++ tailWord_8194035) baseStart_8194035 baseEnd_8194035 := by
    simpa [prefixWord, tailWord_8194035, baseEnd_8194035] using wordTrace_append hprefix tailTrace_8194035
  have hstable : (prefixWord ++ tailWord_8194035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8194035).length < 2 ^ (prefixWord ++ tailWord_8194035).sum := by decide
  have hdescent : baseEnd_8194035 < baseStart_8194035 := by decide
  rcases family_descends (prefixWord ++ tailWord_8194035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8194051 : List Nat := [1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 6]
def baseStart_8194051 : Nat := 118140960795 + 8194051 * 2 ^ 59
def prefixEnd_8194051 : Nat := 4983230072969 + 3 ^ 40 * 8194051 * 2
def baseEnd_8194051 : Nat := 4207486670454425471478751

theorem tailTrace_8194051 : CollatzResearch.WordTrace tailWord_8194051 prefixEnd_8194051 4207486670454425471478751 := by
  unfold tailWord_8194051
  simp only [CollatzResearch.WordTrace]
  refine ⟨298861592437360134341398007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199241061624906756227598671 298861592437360134341398007)
  ·
    refine ⟨448292388656040201512097011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298861592437360134341398007 448292388656040201512097011)
    ·
      refine ⟨672438582984060302268145517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448292388656040201512097011 672438582984060302268145517)
      ·
        refine ⟨252164468619022613350554569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 672438582984060302268145517 252164468619022613350554569)
        ·
          refine ⟨189123351464266960012915927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252164468619022613350554569 189123351464266960012915927)
          ·
            refine ⟨283685027196400440019373891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189123351464266960012915927 283685027196400440019373891)
            ·
              refine ⟨425527540794600660029060837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283685027196400440019373891 425527540794600660029060837)
              ·
                refine ⟨79786413898987623755448907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 425527540794600660029060837 79786413898987623755448907)
                ·
                  refine ⟨119679620848481435633173361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79786413898987623755448907 119679620848481435633173361)
                  ·
                    refine ⟨89759715636361076724880021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 119679620848481435633173361 89759715636361076724880021)
                    ·
                      refine ⟨4207486670454425471478751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89759715636361076724880021 4207486670454425471478751)
                      ·
                        rfl

theorem cell23_8194051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 6].length) (baseStart_8194051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8194051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8194051 prefixEnd_8194051 := by exact prefixLift 8194051
  have htrace : WordTrace (prefixWord ++ tailWord_8194051) baseStart_8194051 baseEnd_8194051 := by
    simpa [prefixWord, tailWord_8194051, baseEnd_8194051] using wordTrace_append hprefix tailTrace_8194051
  have hstable : (prefixWord ++ tailWord_8194051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8194051).length < 2 ^ (prefixWord ++ tailWord_8194051).sum := by decide
  have hdescent : baseEnd_8194051 < baseStart_8194051 := by decide
  rcases family_descends (prefixWord ++ tailWord_8194051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8194102 : List Nat := [5, 1, 2, 1, 1, 1, 2, 2, 1, 5, 2]
def baseStart_8194102 : Nat := 118140960795 + 8194102 * 2 ^ 59
def prefixEnd_8194102 : Nat := 4983230072969 + 3 ^ 40 * 8194102 * 2
def baseEnd_8194102 : Nat := 4207512857967804771941017

theorem tailTrace_8194102 : CollatzResearch.WordTrace tailWord_8194102 prefixEnd_8194102 4207512857967804771941017 := by
  unfold tailWord_8194102
  simp only [CollatzResearch.WordTrace]
  refine ⟨18678965785010960628219035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199242301706783580034336373 18678965785010960628219035)
  ·
    refine ⟨28018448677516440942328553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18678965785010960628219035 28018448677516440942328553)
    ·
      refine ⟨21013836508137330706746415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28018448677516440942328553 21013836508137330706746415)
      ·
        refine ⟨31520754762205996060119623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21013836508137330706746415 31520754762205996060119623)
        ·
          refine ⟨47281132143308994090179435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31520754762205996060119623 47281132143308994090179435)
          ·
            refine ⟨70921698214963491135269153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47281132143308994090179435 70921698214963491135269153)
            ·
              refine ⟨53191273661222618351451865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70921698214963491135269153 53191273661222618351451865)
              ·
                refine ⟨39893455245916963763588899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53191273661222618351451865 39893455245916963763588899)
                ·
                  refine ⟨59840182868875445645383349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39893455245916963763588899 59840182868875445645383349)
                  ·
                    refine ⟨5610017143957073029254689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59840182868875445645383349 5610017143957073029254689)
                    ·
                      refine ⟨4207512857967804771941017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5610017143957073029254689 4207512857967804771941017)
                      ·
                        rfl

theorem cell23_8194102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_8194102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8194102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8194102 prefixEnd_8194102 := by exact prefixLift 8194102
  have htrace : WordTrace (prefixWord ++ tailWord_8194102) baseStart_8194102 baseEnd_8194102 := by
    simpa [prefixWord, tailWord_8194102, baseEnd_8194102] using wordTrace_append hprefix tailTrace_8194102
  have hstable : (prefixWord ++ tailWord_8194102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8194102).length < 2 ^ (prefixWord ++ tailWord_8194102).sum := by decide
  have hdescent : baseEnd_8194102 < baseStart_8194102 := by decide
  rcases family_descends (prefixWord ++ tailWord_8194102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8194125 : List Nat := [1, 6, 1, 1, 1, 1, 1, 4, 1, 6]
def baseStart_8194125 : Nat := 118140960795 + 8194125 * 2 ^ 59
def prefixEnd_8194125 : Nat := 4983230072969 + 3 ^ 40 * 8194125 * 2
def baseEnd_8194125 : Nat := 1402508222674286060651137

theorem tailTrace_8194125 : CollatzResearch.WordTrace tailWord_8194125 prefixEnd_8194125 1402508222674286060651137 := by
  unfold tailWord_8194125
  simp only [CollatzResearch.WordTrace]
  refine ⟨298864291439092044979591829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199242860959394696653061219 298864291439092044979591829)
  ·
    refine ⟨14009263661207439608418367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 298864291439092044979591829 14009263661207439608418367)
    ·
      refine ⟨21013895491811159412627551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14009263661207439608418367 21013895491811159412627551)
      ·
        refine ⟨31520843237716739118941327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21013895491811159412627551 31520843237716739118941327)
        ·
          refine ⟨47281264856575108678411991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31520843237716739118941327 47281264856575108678411991)
          ·
            refine ⟨70921897284862663017617987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47281264856575108678411991 70921897284862663017617987)
            ·
              refine ⟨106382845927293994526426981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70921897284862663017617987 106382845927293994526426981)
              ·
                refine ⟨19946783611367623973705059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106382845927293994526426981 19946783611367623973705059)
                ·
                  refine ⟨29920175417051435960557589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19946783611367623973705059 29920175417051435960557589)
                  ·
                    refine ⟨1402508222674286060651137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29920175417051435960557589 1402508222674286060651137)
                    ·
                      rfl

theorem cell23_8194125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_8194125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8194125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8194125 prefixEnd_8194125 := by exact prefixLift 8194125
  have htrace : WordTrace (prefixWord ++ tailWord_8194125) baseStart_8194125 baseEnd_8194125 := by
    simpa [prefixWord, tailWord_8194125, baseEnd_8194125] using wordTrace_append hprefix tailTrace_8194125
  have hstable : (prefixWord ++ tailWord_8194125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8194125).length < 2 ^ (prefixWord ++ tailWord_8194125).sum := by decide
  have hdescent : baseEnd_8194125 < baseStart_8194125 := by decide
  rcases family_descends (prefixWord ++ tailWord_8194125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8194132 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 7, 2, 2]
def baseStart_8194132 : Nat := 118140960795 + 8194132 * 2 ^ 59
def prefixEnd_8194132 : Nat := 4983230072969 + 3 ^ 40 * 8194132 * 2
def baseEnd_8194132 : Nat := 4207528262387439654565879

theorem tailTrace_8194132 : CollatzResearch.WordTrace tailWord_8194132 prefixEnd_8194132 4207528262387439654565879 := by
  unfold tailWord_8194132
  simp only [CollatzResearch.WordTrace]
  refine ⟨149432273375033342587548325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199243031166711123450064433 149432273375033342587548325)
  ·
    refine ⟨28018551257818751735165311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149432273375033342587548325 28018551257818751735165311)
    ·
      refine ⟨42027826886728127602747967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28018551257818751735165311 42027826886728127602747967)
      ·
        refine ⟨63041740330092191404121951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42027826886728127602747967 63041740330092191404121951)
        ·
          refine ⟨94562610495138287106182927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63041740330092191404121951 94562610495138287106182927)
          ·
            refine ⟨141843915742707430659274391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94562610495138287106182927 141843915742707430659274391)
            ·
              refine ⟨212765873614061145988911587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141843915742707430659274391 212765873614061145988911587)
              ·
                refine ⟨319148810421091718983367381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212765873614061145988911587 319148810421091718983367381)
                ·
                  refine ⟨7480050244244337163672673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 319148810421091718983367381 7480050244244337163672673)
                  ·
                    refine ⟨5610037683183252872754505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7480050244244337163672673 5610037683183252872754505)
                    ·
                      refine ⟨4207528262387439654565879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5610037683183252872754505 4207528262387439654565879)
                      ·
                        rfl

theorem cell23_8194132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 7, 2, 2].length) (baseStart_8194132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8194132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8194132 prefixEnd_8194132 := by exact prefixLift 8194132
  have htrace : WordTrace (prefixWord ++ tailWord_8194132) baseStart_8194132 baseEnd_8194132 := by
    simpa [prefixWord, tailWord_8194132, baseEnd_8194132] using wordTrace_append hprefix tailTrace_8194132
  have hstable : (prefixWord ++ tailWord_8194132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8194132).length < 2 ^ (prefixWord ++ tailWord_8194132).sum := by decide
  have hdescent : baseEnd_8194132 < baseStart_8194132 := by decide
  rcases family_descends (prefixWord ++ tailWord_8194132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8194149 : List Nat := [1, 3, 1, 3, 2, 3, 2, 1, 3, 2, 2]
def baseStart_8194149 : Nat := 118140960795 + 8194149 * 2 ^ 59
def prefixEnd_8194149 : Nat := 4983230072969 + 3 ^ 40 * 8194149 * 2
def baseEnd_8194149 : Nat := 4207536991558566088053301

theorem tailTrace_8194149 : CollatzResearch.WordTrace tailWord_8194149 prefixEnd_8194149 4207536991558566088053301 := by
  unfold tailWord_8194149
  simp only [CollatzResearch.WordTrace]
  refine ⟨298865166791005097078465501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199243444527336731385643667 298865166791005097078465501)
  ·
    refine ⟨112074437546626911404424563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298865166791005097078465501 112074437546626911404424563)
    ·
      refine ⟨168111656319940367106636845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112074437546626911404424563 168111656319940367106636845)
      ·
        refine ⟨63041871119977637664988817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168111656319940367106636845 63041871119977637664988817)
        ·
          refine ⟨47281403339983228248741613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63041871119977637664988817 47281403339983228248741613)
          ·
            refine ⟨17730526252493710593278105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47281403339983228248741613 17730526252493710593278105)
            ·
              refine ⟨13297894689370282944958579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17730526252493710593278105 13297894689370282944958579)
              ·
                refine ⟨19946842034055424417437869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13297894689370282944958579 19946842034055424417437869)
                ·
                  refine ⟨7480065762770784156539201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19946842034055424417437869 7480065762770784156539201)
                  ·
                    refine ⟨5610049322078088117404401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7480065762770784156539201 5610049322078088117404401)
                    ·
                      refine ⟨4207536991558566088053301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5610049322078088117404401 4207536991558566088053301)
                      ·
                        rfl

theorem cell23_8194149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 3, 2, 2].length) (baseStart_8194149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8194149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8194149 prefixEnd_8194149 := by exact prefixLift 8194149
  have htrace : WordTrace (prefixWord ++ tailWord_8194149) baseStart_8194149 baseEnd_8194149 := by
    simpa [prefixWord, tailWord_8194149, baseEnd_8194149] using wordTrace_append hprefix tailTrace_8194149
  have hstable : (prefixWord ++ tailWord_8194149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8194149).length < 2 ^ (prefixWord ++ tailWord_8194149).sum := by decide
  have hdescent : baseEnd_8194149 < baseStart_8194149 := by decide
  rcases family_descends (prefixWord ++ tailWord_8194149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8194162 : List Nat := [3, 2, 1, 2, 2, 4, 1, 1, 1, 2, 4]
def baseStart_8194162 : Nat := 118140960795 + 8194162 * 2 ^ 59
def prefixEnd_8194162 : Nat := 4983230072969 + 3 ^ 40 * 8194162 * 2
def baseEnd_8194162 : Nat := 4207543666807074537190741

theorem tailTrace_8194162 : CollatzResearch.WordTrace tailWord_8194162 prefixEnd_8194162 4207543666807074537190741 := by
  unfold tailWord_8194162
  simp only [CollatzResearch.WordTrace]
  refine ⟨74716410234989500074672185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199243760626638666865792493 74716410234989500074672185)
  ·
    refine ⟨56037307676242125056004139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74716410234989500074672185 56037307676242125056004139)
    ·
      refine ⟨84055961514363187584006209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56037307676242125056004139 84055961514363187584006209)
      ·
        refine ⟨63041971135772390688004657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84055961514363187584006209 63041971135772390688004657)
        ·
          refine ⟨47281478351829293016003493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63041971135772390688004657 47281478351829293016003493)
          ·
            refine ⟨8865277190967992440500655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47281478351829293016003493 8865277190967992440500655)
            ·
              refine ⟨13297915786451988660750983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8865277190967992440500655 13297915786451988660750983)
              ·
                refine ⟨19946873679677982991126475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13297915786451988660750983 19946873679677982991126475)
                ·
                  refine ⟨29920310519516974486689713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19946873679677982991126475 29920310519516974486689713)
                  ·
                    refine ⟨22440232889637730865017285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29920310519516974486689713 22440232889637730865017285)
                    ·
                      refine ⟨4207543666807074537190741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22440232889637730865017285 4207543666807074537190741)
                      ·
                        rfl

theorem cell23_8194162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_8194162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8194162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8194162 prefixEnd_8194162 := by exact prefixLift 8194162
  have htrace : WordTrace (prefixWord ++ tailWord_8194162) baseStart_8194162 baseEnd_8194162 := by
    simpa [prefixWord, tailWord_8194162, baseEnd_8194162] using wordTrace_append hprefix tailTrace_8194162
  have hstable : (prefixWord ++ tailWord_8194162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8194162).length < 2 ^ (prefixWord ++ tailWord_8194162).sum := by decide
  have hdescent : baseEnd_8194162 < baseStart_8194162 := by decide
  rcases family_descends (prefixWord ++ tailWord_8194162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8194188 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 3, 5, 4]
def baseStart_8194188 : Nat := 118140960795 + 8194188 * 2 ^ 59
def prefixEnd_8194188 : Nat := 4983230072969 + 3 ^ 40 * 8194188 * 2
def baseEnd_8194188 : Nat := 4207557017304091435465621

theorem tailTrace_8194188 : CollatzResearch.WordTrace tailWord_8194188 prefixEnd_8194188 4207557017304091435465621 := by
  unfold tailWord_8194188
  simp only [CollatzResearch.WordTrace]
  refine ⟨149433294618931903369567609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199244392825242537826090145 149433294618931903369567609)
  ·
    refine ⟨112074970964198927527175707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149433294618931903369567609 112074970964198927527175707)
    ·
      refine ⟨168112456446298391290763561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112074970964198927527175707 168112456446298391290763561)
      ·
        refine ⟨126084342334723793468072671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168112456446298391290763561 126084342334723793468072671)
        ·
          refine ⟨189126513502085690202109007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126084342334723793468072671 189126513502085690202109007)
          ·
            refine ⟨283689770253128535303163511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189126513502085690202109007 283689770253128535303163511)
            ·
              refine ⟨425534655379692802954745267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283689770253128535303163511 425534655379692802954745267)
              ·
                refine ⟨638301983069539204432117901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 425534655379692802954745267 638301983069539204432117901)
                ·
                  refine ⟨239363243651077201662044213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 638301983069539204432117901 239363243651077201662044213)
                  ·
                    refine ⟨22440304092288487655816645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 239363243651077201662044213 22440304092288487655816645)
                    ·
                      refine ⟨4207557017304091435465621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22440304092288487655816645 4207557017304091435465621)
                      ·
                        rfl

theorem cell23_8194188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_8194188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8194188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8194188 prefixEnd_8194188 := by exact prefixLift 8194188
  have htrace : WordTrace (prefixWord ++ tailWord_8194188) baseStart_8194188 baseEnd_8194188 := by
    simpa [prefixWord, tailWord_8194188, baseEnd_8194188] using wordTrace_append hprefix tailTrace_8194188
  have hstable : (prefixWord ++ tailWord_8194188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8194188).length < 2 ^ (prefixWord ++ tailWord_8194188).sum := by decide
  have hdescent : baseEnd_8194188 < baseStart_8194188 := by decide
  rcases family_descends (prefixWord ++ tailWord_8194188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8194192 : List Nat := [2, 1, 1, 1, 1, 1, 5, 5, 1, 3, 2]
def baseStart_8194192 : Nat := 118140960795 + 8194192 * 2 ^ 59
def prefixEnd_8194192 : Nat := 4983230072969 + 3 ^ 40 * 8194192 * 2
def baseEnd_8194192 : Nat := 4207559071226709419815603

theorem tailTrace_8194192 : CollatzResearch.WordTrace tailWord_8194192 prefixEnd_8194192 4207559071226709419815603 := by
  unfold tailWord_8194192
  simp only [CollatzResearch.WordTrace]
  refine ⟨149433367564924657711140415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199244490086566210281520553 149433367564924657711140415)
  ·
    refine ⟨224150051347386986566710623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149433367564924657711140415 224150051347386986566710623)
    ·
      refine ⟨336225077021080479850065935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224150051347386986566710623 336225077021080479850065935)
      ·
        refine ⟨504337615531620719775098903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336225077021080479850065935 504337615531620719775098903)
        ·
          refine ⟨756506423297431079662648355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504337615531620719775098903 756506423297431079662648355)
          ·
            refine ⟨1134759634946146619493972533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 756506423297431079662648355 1134759634946146619493972533)
            ·
              refine ⟨106383715776201245577559925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1134759634946146619493972533 106383715776201245577559925)
              ·
                refine ⟨9973473354018866772896243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106383715776201245577559925 9973473354018866772896243)
                ·
                  refine ⟨14960210031028300159344365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9973473354018866772896243 14960210031028300159344365)
                  ·
                    refine ⟨5610078761635612559754137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14960210031028300159344365 5610078761635612559754137)
                    ·
                      refine ⟨4207559071226709419815603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5610078761635612559754137 4207559071226709419815603)
                      ·
                        rfl

theorem cell23_8194192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 5, 1, 3, 2].length) (baseStart_8194192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8194192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8194192 prefixEnd_8194192 := by exact prefixLift 8194192
  have htrace : WordTrace (prefixWord ++ tailWord_8194192) baseStart_8194192 baseEnd_8194192 := by
    simpa [prefixWord, tailWord_8194192, baseEnd_8194192] using wordTrace_append hprefix tailTrace_8194192
  have hstable : (prefixWord ++ tailWord_8194192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8194192).length < 2 ^ (prefixWord ++ tailWord_8194192).sum := by decide
  have hdescent : baseEnd_8194192 < baseStart_8194192 := by decide
  rcases family_descends (prefixWord ++ tailWord_8194192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8194255 : List Nat := [1, 1, 2, 1, 1, 3, 4, 2, 2, 3, 3]
def baseStart_8194255 : Nat := 118140960795 + 8194255 * 2 ^ 59
def prefixEnd_8194255 : Nat := 4983230072969 + 3 ^ 40 * 8194255 * 2
def baseEnd_8194255 : Nat := 4207591420507942673327813

theorem tailTrace_8194255 : CollatzResearch.WordTrace tailWord_8194255 prefixEnd_8194255 4207591420507942673327813 := by
  unfold tailWord_8194255
  simp only [CollatzResearch.WordTrace]
  refine ⟨298869032928621077181824219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199246021952414051454549479 298869032928621077181824219)
  ·
    refine ⟨448303549392931615772736329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298869032928621077181824219 448303549392931615772736329)
    ·
      refine ⟨336227662044698711829552247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 448303549392931615772736329 336227662044698711829552247)
      ·
        refine ⟨504341493067048067744328371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336227662044698711829552247 504341493067048067744328371)
        ·
          refine ⟨756512239600572101616492557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504341493067048067744328371 756512239600572101616492557)
          ·
            refine ⟨283692089850214538106184709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 756512239600572101616492557 283692089850214538106184709)
            ·
              refine ⟨53192266846915225894909633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 283692089850214538106184709 53192266846915225894909633)
              ·
                refine ⟨39894200135186419421182225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53192266846915225894909633 39894200135186419421182225)
                ·
                  refine ⟨29920650101389814565886669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39894200135186419421182225 29920650101389814565886669)
                  ·
                    refine ⟨11220243788021180462207501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29920650101389814565886669 11220243788021180462207501)
                    ·
                      refine ⟨4207591420507942673327813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11220243788021180462207501 4207591420507942673327813)
                      ·
                        rfl

theorem cell23_8194255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 3, 3].length) (baseStart_8194255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8194255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8194255 prefixEnd_8194255 := by exact prefixLift 8194255
  have htrace : WordTrace (prefixWord ++ tailWord_8194255) baseStart_8194255 baseEnd_8194255 := by
    simpa [prefixWord, tailWord_8194255, baseEnd_8194255] using wordTrace_append hprefix tailTrace_8194255
  have hstable : (prefixWord ++ tailWord_8194255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8194255).length < 2 ^ (prefixWord ++ tailWord_8194255).sum := by decide
  have hdescent : baseEnd_8194255 < baseStart_8194255 := by decide
  rcases family_descends (prefixWord ++ tailWord_8194255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8194282 : List Nat := [3, 1, 3, 1, 1, 2, 1, 2, 2, 5, 2]
def baseStart_8194282 : Nat := 118140960795 + 8194282 * 2 ^ 59
def prefixEnd_8194282 : Nat := 4983230072969 + 3 ^ 40 * 8194282 * 2
def baseEnd_8194282 : Nat := 4207605284485614067690189

theorem tailTrace_8194282 : CollatzResearch.WordTrace tailWord_8194282 prefixEnd_8194282 4207605284485614067690189 := by
  unfold tailWord_8194282
  simp only [CollatzResearch.WordTrace]
  refine ⟨74717504424880815198264275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199246678466348840528704733 74717504424880815198264275)
  ·
    refine ⟨112076256637321222797396413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74717504424880815198264275 112076256637321222797396413)
    ·
      refine ⟨42028596238995458549023655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112076256637321222797396413 42028596238995458549023655)
      ·
        refine ⟨63042894358493187823535483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42028596238995458549023655 63042894358493187823535483)
        ·
          refine ⟨94564341537739781735303225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63042894358493187823535483 94564341537739781735303225)
          ·
            refine ⟨70923256153304836301477419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94564341537739781735303225 70923256153304836301477419)
            ·
              refine ⟨106384884229957254452216129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70923256153304836301477419 106384884229957254452216129)
              ·
                refine ⟨79788663172467940839162097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106384884229957254452216129 79788663172467940839162097)
                ·
                  refine ⟨59841497379350955629371573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79788663172467940839162097 59841497379350955629371573)
                  ·
                    refine ⟨5610140379314152090253585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59841497379350955629371573 5610140379314152090253585)
                    ·
                      refine ⟨4207605284485614067690189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5610140379314152090253585 4207605284485614067690189)
                      ·
                        rfl

theorem cell23_8194282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 2, 5, 2].length) (baseStart_8194282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8194282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8194282 prefixEnd_8194282 := by exact prefixLift 8194282
  have htrace : WordTrace (prefixWord ++ tailWord_8194282) baseStart_8194282 baseEnd_8194282 := by
    simpa [prefixWord, tailWord_8194282, baseEnd_8194282] using wordTrace_append hprefix tailTrace_8194282
  have hstable : (prefixWord ++ tailWord_8194282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8194282).length < 2 ^ (prefixWord ++ tailWord_8194282).sum := by decide
  have hdescent : baseEnd_8194282 < baseStart_8194282 := by decide
  rcases family_descends (prefixWord ++ tailWord_8194282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8194415 : List Nat := [1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 6]
def baseStart_8194415 : Nat := 118140960795 + 8194415 * 2 ^ 59
def prefixEnd_8194415 : Nat := 4983230072969 + 3 ^ 40 * 8194415 * 2
def baseEnd_8194415 : Nat := 4207673577412662047327077

theorem tailTrace_8194415 : CollatzResearch.WordTrace tailWord_8194415 prefixEnd_8194415 4207673577412662047327077 := by
  unfold tailWord_8194415
  simp only [CollatzResearch.WordTrace]
  refine ⟨298874868608041424507648699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199249912405360949671765799 298874868608041424507648699)
  ·
    refine ⟨448312302912062136761473049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298874868608041424507648699 448312302912062136761473049)
    ·
      refine ⟨336234227184046602571104787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 448312302912062136761473049 336234227184046602571104787)
      ·
        refine ⟨504351340776069903856657181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336234227184046602571104787 504351340776069903856657181)
        ·
          refine ⟨189131752791026213946246443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 504351340776069903856657181 189131752791026213946246443)
          ·
            refine ⟨283697629186539320919369665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189131752791026213946246443 283697629186539320919369665)
            ·
              refine ⟨212773221889904490689527249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283697629186539320919369665 212773221889904490689527249)
              ·
                refine ⟨159579916417428368017145437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212773221889904490689527249 159579916417428368017145437)
                ·
                  refine ⟨59842468656535638006429539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159579916417428368017145437 59842468656535638006429539)
                  ·
                    refine ⟨89763702984803457009644309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59842468656535638006429539 89763702984803457009644309)
                    ·
                      refine ⟨4207673577412662047327077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89763702984803457009644309 4207673577412662047327077)
                      ·
                        rfl

theorem cell23_8194415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 6].length) (baseStart_8194415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8194415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8194415 prefixEnd_8194415 := by exact prefixLift 8194415
  have htrace : WordTrace (prefixWord ++ tailWord_8194415) baseStart_8194415 baseEnd_8194415 := by
    simpa [prefixWord, tailWord_8194415, baseEnd_8194415] using wordTrace_append hprefix tailTrace_8194415
  have hstable : (prefixWord ++ tailWord_8194415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8194415).length < 2 ^ (prefixWord ++ tailWord_8194415).sum := by decide
  have hdescent : baseEnd_8194415 < baseStart_8194415 := by decide
  rcases family_descends (prefixWord ++ tailWord_8194415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8194419 : List Nat := [1, 1, 1, 2, 2, 1, 2, 4, 5, 2, 2]
def baseStart_8194419 : Nat := 118140960795 + 8194419 * 2 ^ 59
def prefixEnd_8194419 : Nat := 4983230072969 + 3 ^ 40 * 8194419 * 2
def baseEnd_8194419 : Nat := 4207675631335280031677059

theorem tailTrace_8194419 : CollatzResearch.WordTrace tailWord_8194419 prefixEnd_8194419 4207675631335280031677059 := by
  unfold tailWord_8194419
  simp only [CollatzResearch.WordTrace]
  refine ⟨298875014500026933190794311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199250009666684622127196207 298875014500026933190794311)
  ·
    refine ⟨448312521750040399786191467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298875014500026933190794311 448312521750040399786191467)
    ·
      refine ⟨672468782625060599679287201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448312521750040399786191467 672468782625060599679287201)
      ·
        refine ⟨504351586968795449759465401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 672468782625060599679287201 504351586968795449759465401)
        ·
          refine ⟨378263690226596587319599051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 504351586968795449759465401 378263690226596587319599051)
          ·
            refine ⟨567395535339894880979398577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378263690226596587319599051 567395535339894880979398577)
            ·
              refine ⟨425546651504921160734548933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 567395535339894880979398577 425546651504921160734548933)
              ·
                refine ⟨79789997157172717637727925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 425546651504921160734548933 79789997157172717637727925)
                ·
                  refine ⟨7480312233484942278536993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79789997157172717637727925 7480312233484942278536993)
                  ·
                    refine ⟨5610234175113706708902745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7480312233484942278536993 5610234175113706708902745)
                    ·
                      refine ⟨4207675631335280031677059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5610234175113706708902745 4207675631335280031677059)
                      ·
                        rfl

theorem cell23_8194419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 5, 2, 2].length) (baseStart_8194419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8194419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8194419 prefixEnd_8194419 := by exact prefixLift 8194419
  have htrace : WordTrace (prefixWord ++ tailWord_8194419) baseStart_8194419 baseEnd_8194419 := by
    simpa [prefixWord, tailWord_8194419, baseEnd_8194419] using wordTrace_append hprefix tailTrace_8194419
  have hstable : (prefixWord ++ tailWord_8194419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8194419).length < 2 ^ (prefixWord ++ tailWord_8194419).sum := by decide
  have hdescent : baseEnd_8194419 < baseStart_8194419 := by decide
  rcases family_descends (prefixWord ++ tailWord_8194419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8194429 : List Nat := [1, 4, 1, 1, 2, 3, 1, 4, 2, 4]
def baseStart_8194429 : Nat := 118140960795 + 8194429 * 2 ^ 59
def prefixEnd_8194429 : Nat := 4983230072969 + 3 ^ 40 * 8194429 * 2
def baseEnd_8194429 : Nat := 1402560255380608330850671

theorem tailTrace_8194429 : CollatzResearch.WordTrace tailWord_8194429 prefixEnd_8194429 1402560255380608330850671 := by
  unfold tailWord_8194429
  simp only [CollatzResearch.WordTrace]
  refine ⟨298875379229990704898658341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199250252819993803265772227 298875379229990704898658341)
  ·
    refine ⟨56039133605623257168498439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 298875379229990704898658341 56039133605623257168498439)
    ·
      refine ⟨84058700408434885752747659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56039133605623257168498439 84058700408434885752747659)
      ·
        refine ⟨126088050612652328629121489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84058700408434885752747659 126088050612652328629121489)
        ·
          refine ⟨94566037959489246471841117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126088050612652328629121489 94566037959489246471841117)
          ·
            refine ⟨35462264234808467426940419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94566037959489246471841117 35462264234808467426940419)
            ·
              refine ⟨53193396352212701140410629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35462264234808467426940419 53193396352212701140410629)
              ·
                refine ⟨9973761816039881463826993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53193396352212701140410629 9973761816039881463826993)
                ·
                  refine ⟨7480321362029911097870245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9973761816039881463826993 7480321362029911097870245)
                  ·
                    refine ⟨1402560255380608330850671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7480321362029911097870245 1402560255380608330850671)
                    ·
                      rfl

theorem cell23_8194429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 4, 2, 4].length) (baseStart_8194429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8194429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8194429 prefixEnd_8194429 := by exact prefixLift 8194429
  have htrace : WordTrace (prefixWord ++ tailWord_8194429) baseStart_8194429 baseEnd_8194429 := by
    simpa [prefixWord, tailWord_8194429, baseEnd_8194429] using wordTrace_append hprefix tailTrace_8194429
  have hstable : (prefixWord ++ tailWord_8194429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8194429).length < 2 ^ (prefixWord ++ tailWord_8194429).sum := by decide
  have hdescent : baseEnd_8194429 < baseStart_8194429 := by decide
  rcases family_descends (prefixWord ++ tailWord_8194429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8194436 : List Nat := [2, 3, 2, 1, 1, 2, 2, 3, 3, 2, 2]
def baseStart_8194436 : Nat := 118140960795 + 8194436 * 2 ^ 59
def prefixEnd_8194436 : Nat := 4983230072969 + 3 ^ 40 * 8194436 * 2
def baseEnd_8194436 : Nat := 4207684360506406465164481

theorem tailTrace_8194436 : CollatzResearch.WordTrace tailWord_8194436 prefixEnd_8194436 4207684360506406465164481 := by
  unfold tailWord_8194436
  simp only [CollatzResearch.WordTrace]
  refine ⟨149437817270482672547081581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199250423027310230062775441 149437817270482672547081581)
  ·
    refine ⟨56039181476431002205155593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149437817270482672547081581 56039181476431002205155593)
    ·
      refine ⟨42029386107323251653866695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56039181476431002205155593 42029386107323251653866695)
      ·
        refine ⟨63044079160984877480800043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42029386107323251653866695 63044079160984877480800043)
        ·
          refine ⟨94566118741477316221200065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63044079160984877480800043 94566118741477316221200065)
          ·
            refine ⟨70924589056107987165900049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94566118741477316221200065 70924589056107987165900049)
            ·
              refine ⟨53193441792080990374425037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70924589056107987165900049 53193441792080990374425037)
              ·
                refine ⟨19947540672030371390409389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53193441792080990374425037 19947540672030371390409389)
                ·
                  refine ⟨7480327752011389271403521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19947540672030371390409389 7480327752011389271403521)
                  ·
                    refine ⟨5610245814008541953552641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7480327752011389271403521 5610245814008541953552641)
                    ·
                      refine ⟨4207684360506406465164481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5610245814008541953552641 4207684360506406465164481)
                      ·
                        rfl

theorem cell23_8194436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 3, 2, 2].length) (baseStart_8194436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8194436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8194436 prefixEnd_8194436 := by exact prefixLift 8194436
  have htrace : WordTrace (prefixWord ++ tailWord_8194436) baseStart_8194436 baseEnd_8194436 := by
    simpa [prefixWord, tailWord_8194436, baseEnd_8194436] using wordTrace_append hprefix tailTrace_8194436
  have hstable : (prefixWord ++ tailWord_8194436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8194436).length < 2 ^ (prefixWord ++ tailWord_8194436).sum := by decide
  have hdescent : baseEnd_8194436 < baseStart_8194436 := by decide
  rcases family_descends (prefixWord ++ tailWord_8194436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8194446 : List Nat := [4, 1, 1, 4, 1, 1, 2, 3, 2, 4]
def baseStart_8194446 : Nat := 118140960795 + 8194446 * 2 ^ 59
def prefixEnd_8194446 : Nat := 4983230072969 + 3 ^ 40 * 8194446 * 2
def baseEnd_8194446 : Nat := 1402563165104317142013145

theorem tailTrace_8194446 : CollatzResearch.WordTrace tailWord_8194446 prefixEnd_8194446 1402563165104317142013145 := by
  unfold tailWord_8194446
  simp only [CollatzResearch.WordTrace]
  refine ⟨37359499908866139600253399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199250666180619411201351461 37359499908866139600253399)
  ·
    refine ⟨56039249863299209400380099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37359499908866139600253399 56039249863299209400380099)
    ·
      refine ⟨84058874794948814100570149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56039249863299209400380099 84058874794948814100570149)
      ·
        refine ⟨15761039024052902643856903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84058874794948814100570149 15761039024052902643856903)
        ·
          refine ⟨23641558536079353965785355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15761039024052902643856903 23641558536079353965785355)
          ·
            refine ⟨35462337804119030948678033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23641558536079353965785355 35462337804119030948678033)
            ·
              refine ⟨26596753353089273211508525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35462337804119030948678033 26596753353089273211508525)
              ·
                refine ⟨9973782507408477454315697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26596753353089273211508525 9973782507408477454315697)
                ·
                  refine ⟨7480336880556358090736773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9973782507408477454315697 7480336880556358090736773)
                  ·
                    refine ⟨1402563165104317142013145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7480336880556358090736773 1402563165104317142013145)
                    ·
                      rfl

theorem cell23_8194446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 3, 2, 4].length) (baseStart_8194446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8194446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8194446 prefixEnd_8194446 := by exact prefixLift 8194446
  have htrace : WordTrace (prefixWord ++ tailWord_8194446) baseStart_8194446 baseEnd_8194446 := by
    simpa [prefixWord, tailWord_8194446, baseEnd_8194446] using wordTrace_append hprefix tailTrace_8194446
  have hstable : (prefixWord ++ tailWord_8194446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8194446).length < 2 ^ (prefixWord ++ tailWord_8194446).sum := by decide
  have hdescent : baseEnd_8194446 < baseStart_8194446 := by decide
  rcases family_descends (prefixWord ++ tailWord_8194446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8194469 : List Nat := [1, 3, 1, 2, 1, 1, 4, 2, 4, 1, 3]
def baseStart_8194469 : Nat := 118140960795 + 8194469 * 2 ^ 59
def prefixEnd_8194469 : Nat := 4983230072969 + 3 ^ 40 * 8194469 * 2
def baseEnd_8194469 : Nat := 4207701305368004836051829

theorem tailTrace_8194469 : CollatzResearch.WordTrace tailWord_8194469 prefixEnd_8194469 4207701305368004836051829 := by
  unfold tailWord_8194469
  simp only [CollatzResearch.WordTrace]
  refine ⟨298876838149845791730114461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199251225433230527820076307 298876838149845791730114461)
  ·
    refine ⟨112078814306192171898792923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298876838149845791730114461 112078814306192171898792923)
    ·
      refine ⟨168118221459288257848189385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112078814306192171898792923 168118221459288257848189385)
      ·
        refine ⟨126088666094466193386142039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168118221459288257848189385 126088666094466193386142039)
        ·
          refine ⟨189132999141699290079213059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126088666094466193386142039 189132999141699290079213059)
          ·
            refine ⟨283699498712548935118819589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189132999141699290079213059 283699498712548935118819589)
            ·
              refine ⟨53193656008602925334778673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 283699498712548935118819589 53193656008602925334778673)
              ·
                refine ⟨39895242006452194001084005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53193656008602925334778673 39895242006452194001084005)
                ·
                  refine ⟨7480357876209786375203251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39895242006452194001084005 7480357876209786375203251)
                  ·
                    refine ⟨11220536814314679562804877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7480357876209786375203251 11220536814314679562804877)
                    ·
                      refine ⟨4207701305368004836051829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11220536814314679562804877 4207701305368004836051829)
                      ·
                        rfl

theorem cell23_8194469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 4, 1, 3].length) (baseStart_8194469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8194469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8194469 prefixEnd_8194469 := by exact prefixLift 8194469
  have htrace : WordTrace (prefixWord ++ tailWord_8194469) baseStart_8194469 baseEnd_8194469 := by
    simpa [prefixWord, tailWord_8194469, baseEnd_8194469] using wordTrace_append hprefix tailTrace_8194469
  have hstable : (prefixWord ++ tailWord_8194469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8194469).length < 2 ^ (prefixWord ++ tailWord_8194469).sum := by decide
  have hdescent : baseEnd_8194469 < baseStart_8194469 := by decide
  rcases family_descends (prefixWord ++ tailWord_8194469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8194497 : List Nat := [1, 2, 7, 1, 1, 1, 3, 1, 2, 4]
def baseStart_8194497 : Nat := 118140960795 + 8194497 * 2 ^ 59
def prefixEnd_8194497 : Nat := 4983230072969 + 3 ^ 40 * 8194497 * 2
def baseEnd_8194497 : Nat := 1402571894275443575500567

theorem tailTrace_8194497 : CollatzResearch.WordTrace tailWord_8194497 prefixEnd_8194497 1402571894275443575500567 := by
  unfold tailWord_8194497
  simp only [CollatzResearch.WordTrace]
  refine ⟨298877859393744352512133745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199251906262496235008089163 298877859393744352512133745)
  ·
    refine ⟨224158394545308264384100309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298877859393744352512133745 224158394545308264384100309)
    ·
      refine ⟨5253712372155662446502351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 224158394545308264384100309 5253712372155662446502351)
      ·
        refine ⟨7880568558233493669753527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5253712372155662446502351 7880568558233493669753527)
        ·
          refine ⟨11820852837350240504630291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7880568558233493669753527 11820852837350240504630291)
          ·
            refine ⟨17731279256025360756945437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11820852837350240504630291 17731279256025360756945437)
            ·
              refine ⟨6649229721009510283854539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17731279256025360756945437 6649229721009510283854539)
              ·
                refine ⟨9973844581514265425781809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6649229721009510283854539 9973844581514265425781809)
                ·
                  refine ⟨7480383436135699069336357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9973844581514265425781809 7480383436135699069336357)
                  ·
                    refine ⟨1402571894275443575500567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7480383436135699069336357 1402571894275443575500567)
                    ·
                      rfl

theorem cell23_8194497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_8194497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8194497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8194497 prefixEnd_8194497 := by exact prefixLift 8194497
  have htrace : WordTrace (prefixWord ++ tailWord_8194497) baseStart_8194497 baseEnd_8194497 := by
    simpa [prefixWord, tailWord_8194497, baseEnd_8194497] using wordTrace_append hprefix tailTrace_8194497
  have hstable : (prefixWord ++ tailWord_8194497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8194497).length < 2 ^ (prefixWord ++ tailWord_8194497).sum := by decide
  have hdescent : baseEnd_8194497 < baseStart_8194497 := by decide
  rcases family_descends (prefixWord ++ tailWord_8194497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8194503 : List Nat := [1, 1, 4, 1, 1, 5, 3, 1, 2, 1, 3]
def baseStart_8194503 : Nat := 118140960795 + 8194503 * 2 ^ 59
def prefixEnd_8194503 : Nat := 4983230072969 + 3 ^ 40 * 8194503 * 2
def baseEnd_8194503 : Nat := 4207718763710257703026673

theorem tailTrace_8194503 : CollatzResearch.WordTrace tailWord_8194503 prefixEnd_8194503 4207718763710257703026673 := by
  unfold tailWord_8194503
  simp only [CollatzResearch.WordTrace]
  refine ⟨298878078231722615536852163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199252052154481743691234775 298878078231722615536852163)
  ·
    refine ⟨448317117347583923305278245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298878078231722615536852163 448317117347583923305278245)
    ·
      refine ⟨84059459502671985619739671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 448317117347583923305278245 84059459502671985619739671)
      ·
        refine ⟨126089189254007978429609507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84059459502671985619739671 126089189254007978429609507)
        ·
          refine ⟨189133783881011967644414261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126089189254007978429609507 189133783881011967644414261)
          ·
            refine ⟨17731292238844871966663837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 189133783881011967644414261 17731292238844871966663837)
            ·
              refine ⟨6649234589566826987498939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17731292238844871966663837 6649234589566826987498939)
              ·
                refine ⟨9973851884350240481248409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6649234589566826987498939 9973851884350240481248409)
                ·
                  refine ⟨7480388913262680360936307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9973851884350240481248409 7480388913262680360936307)
                  ·
                    refine ⟨11220583369894020541404461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7480388913262680360936307 11220583369894020541404461)
                    ·
                      refine ⟨4207718763710257703026673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11220583369894020541404461 4207718763710257703026673)
                      ·
                        rfl

theorem cell23_8194503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 1, 2, 1, 3].length) (baseStart_8194503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8194503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8194503 prefixEnd_8194503 := by exact prefixLift 8194503
  have htrace : WordTrace (prefixWord ++ tailWord_8194503) baseStart_8194503 baseEnd_8194503 := by
    simpa [prefixWord, tailWord_8194503, baseEnd_8194503] using wordTrace_append hprefix tailTrace_8194503
  have hstable : (prefixWord ++ tailWord_8194503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8194503).length < 2 ^ (prefixWord ++ tailWord_8194503).sum := by decide
  have hdescent : baseEnd_8194503 < baseStart_8194503 := by decide
  rcases family_descends (prefixWord ++ tailWord_8194503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8194569 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 4, 5, 2]
def baseStart_8194569 : Nat := 118140960795 + 8194569 * 2 ^ 59
def prefixEnd_8194569 : Nat := 4983230072969 + 3 ^ 40 * 8194569 * 2
def baseEnd_8194569 : Nat := 4207752653433454444801369

theorem tailTrace_8194569 : CollatzResearch.WordTrace tailWord_8194569 prefixEnd_8194569 4207752653433454444801369 := by
  unfold tailWord_8194569
  simp only [CollatzResearch.WordTrace]
  refine ⟨298880485449483508808754761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199253656966322339205836507 298880485449483508808754761)
  ·
    refine ⟨224160364087112631606566071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298880485449483508808754761 224160364087112631606566071)
    ·
      refine ⟨336240546130668947409849107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224160364087112631606566071 336240546130668947409849107)
      ·
        refine ⟨504360819196003421114773661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336240546130668947409849107 504360819196003421114773661)
        ·
          refine ⟨189135307198501282918040123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 504360819196003421114773661 189135307198501282918040123)
          ·
            refine ⟨283702960797751924377060185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189135307198501282918040123 283702960797751924377060185)
            ·
              refine ⟨212777220598313943282795139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283702960797751924377060185 212777220598313943282795139)
              ·
                refine ⟨319165830897470914924192709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212777220598313943282795139 319165830897470914924192709)
                ·
                  refine ⟨59843593293275796548286133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 319165830897470914924192709 59843593293275796548286133)
                  ·
                    refine ⟨5610336871244605926401825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59843593293275796548286133 5610336871244605926401825)
                    ·
                      refine ⟨4207752653433454444801369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5610336871244605926401825 4207752653433454444801369)
                      ·
                        rfl

theorem cell23_8194569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 5, 2].length) (baseStart_8194569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8194569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8194569 prefixEnd_8194569 := by exact prefixLift 8194569
  have htrace : WordTrace (prefixWord ++ tailWord_8194569) baseStart_8194569 baseEnd_8194569 := by
    simpa [prefixWord, tailWord_8194569, baseEnd_8194569] using wordTrace_append hprefix tailTrace_8194569
  have hstable : (prefixWord ++ tailWord_8194569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8194569).length < 2 ^ (prefixWord ++ tailWord_8194569).sum := by decide
  have hdescent : baseEnd_8194569 < baseStart_8194569 := by decide
  rcases family_descends (prefixWord ++ tailWord_8194569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8194579 : List Nat := [1, 1, 1, 2, 1, 5, 4, 1, 2, 5]
def baseStart_8194579 : Nat := 118140960795 + 8194579 * 2 ^ 59
def prefixEnd_8194579 : Nat := 4983230072969 + 3 ^ 40 * 8194579 * 2
def baseEnd_8194579 : Nat := 1402585929413333135225441

theorem tailTrace_8194579 : CollatzResearch.WordTrace tailWord_8194579 prefixEnd_8194579 1402585929413333135225441 := by
  unfold tailWord_8194579
  simp only [CollatzResearch.WordTrace]
  refine ⟨298880850179447280516618791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199253900119631520344412527 298880850179447280516618791)
  ·
    refine ⟨448321275269170920774928187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298880850179447280516618791 448321275269170920774928187)
    ·
      refine ⟨672481912903756381162392281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448321275269170920774928187 672481912903756381162392281)
      ·
        refine ⟨504361434677817285871794211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 672481912903756381162392281 504361434677817285871794211)
        ·
          refine ⟨756542152016725928807691317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504361434677817285871794211 756542152016725928807691317)
          ·
            refine ⟨70925826751568055825721061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 756542152016725928807691317 70925826751568055825721061)
            ·
              refine ⟨13298592515919010467322699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70925826751568055825721061 13298592515919010467322699)
              ·
                refine ⟨19947888773878515700984049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13298592515919010467322699 19947888773878515700984049)
                ·
                  refine ⟨14960916580408886775738037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19947888773878515700984049 14960916580408886775738037)
                  ·
                    refine ⟨1402585929413333135225441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14960916580408886775738037 1402585929413333135225441)
                    ·
                      rfl

theorem cell23_8194579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 2, 5].length) (baseStart_8194579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8194579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8194579 prefixEnd_8194579 := by exact prefixLift 8194579
  have htrace : WordTrace (prefixWord ++ tailWord_8194579) baseStart_8194579 baseEnd_8194579 := by
    simpa [prefixWord, tailWord_8194579, baseEnd_8194579] using wordTrace_append hprefix tailTrace_8194579
  have hstable : (prefixWord ++ tailWord_8194579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8194579).length < 2 ^ (prefixWord ++ tailWord_8194579).sum := by decide
  have hdescent : baseEnd_8194579 < baseStart_8194579 := by decide
  rcases family_descends (prefixWord ++ tailWord_8194579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8194589 : List Nat := [1, 4, 2, 2, 1, 2, 1, 2, 1, 2, 5]
def baseStart_8194589 : Nat := 118140960795 + 8194589 * 2 ^ 59
def prefixEnd_8194589 : Nat := 4983230072969 + 3 ^ 40 * 8194589 * 2
def baseEnd_8194589 : Nat := 4207762923046544366551277

theorem tailTrace_8194589 : CollatzResearch.WordTrace tailWord_8194589 prefixEnd_8194589 4207762923046544366551277 := by
  unfold tailWord_8194589
  simp only [CollatzResearch.WordTrace]
  refine ⟨298881214909411052224482821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199254143272940701482988547 298881214909411052224482821)
  ·
    refine ⟨56040227795514572292090529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 298881214909411052224482821 56040227795514572292090529)
    ·
      refine ⟨42030170846635929219067897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56040227795514572292090529 42030170846635929219067897)
      ·
        refine ⟨31522628134976946914300923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42030170846635929219067897 31522628134976946914300923)
        ·
          refine ⟨47283942202465420371451385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31522628134976946914300923 47283942202465420371451385)
          ·
            refine ⟨35462956651849065278588539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47283942202465420371451385 35462956651849065278588539)
            ·
              refine ⟨53194434977773597917882809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35462956651849065278588539 53194434977773597917882809)
              ·
                refine ⟨39895826233330198438412107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53194434977773597917882809 39895826233330198438412107)
                ·
                  refine ⟨59843739349995297657618161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39895826233330198438412107 59843739349995297657618161)
                  ·
                    refine ⟨44882804512496473243213621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59843739349995297657618161 44882804512496473243213621)
                    ·
                      refine ⟨4207762923046544366551277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44882804512496473243213621 4207762923046544366551277)
                      ·
                        rfl

theorem cell23_8194589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_8194589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8194589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8194589 prefixEnd_8194589 := by exact prefixLift 8194589
  have htrace : WordTrace (prefixWord ++ tailWord_8194589) baseStart_8194589 baseEnd_8194589 := by
    simpa [prefixWord, tailWord_8194589, baseEnd_8194589] using wordTrace_append hprefix tailTrace_8194589
  have hstable : (prefixWord ++ tailWord_8194589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8194589).length < 2 ^ (prefixWord ++ tailWord_8194589).sum := by decide
  have hdescent : baseEnd_8194589 < baseStart_8194589 := by decide
  rcases family_descends (prefixWord ++ tailWord_8194589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8194600 : List Nat := [2, 1, 5, 2, 1, 3, 2, 2, 5]
def baseStart_8194600 : Nat := 118140960795 + 8194600 * 2 ^ 59
def prefixEnd_8194600 : Nat := 4983230072969 + 3 ^ 40 * 8194600 * 2
def baseEnd_8194600 : Nat := 467529841259304869279303

theorem tailTrace_8194600 : CollatzResearch.WordTrace tailWord_8194600 prefixEnd_8194600 467529841259304869279303 := by
  unfold tailWord_8194600
  simp only [CollatzResearch.WordTrace]
  refine ⟨149440808056185600551566627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199254410741580800735422169 149440808056185600551566627)
  ·
    refine ⟨224161212084278400827349941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149440808056185600551566627 224161212084278400827349941)
    ·
      refine ⟨21015113632901100077564057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 224161212084278400827349941 21015113632901100077564057)
      ·
        refine ⟨15761335224675825058173043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21015113632901100077564057 15761335224675825058173043)
        ·
          refine ⟨23642002837013737587259565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15761335224675825058173043 23642002837013737587259565)
          ·
            refine ⟨8865751063880151595222337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23642002837013737587259565 8865751063880151595222337)
            ·
              refine ⟨6649313297910113696416753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8865751063880151595222337 6649313297910113696416753)
              ·
                refine ⟨4986984973432585272312565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6649313297910113696416753 4986984973432585272312565)
                ·
                  refine ⟨467529841259304869279303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4986984973432585272312565 467529841259304869279303)
                  ·
                    rfl

theorem cell23_8194600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 2, 5].length) (baseStart_8194600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8194600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8194600 prefixEnd_8194600 := by exact prefixLift 8194600
  have htrace : WordTrace (prefixWord ++ tailWord_8194600) baseStart_8194600 baseEnd_8194600 := by
    simpa [prefixWord, tailWord_8194600, baseEnd_8194600] using wordTrace_append hprefix tailTrace_8194600
  have hstable : (prefixWord ++ tailWord_8194600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8194600).length < 2 ^ (prefixWord ++ tailWord_8194600).sum := by decide
  have hdescent : baseEnd_8194600 < baseStart_8194600 := by decide
  rcases family_descends (prefixWord ++ tailWord_8194600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8194616 : List Nat := [2, 1, 2, 1, 4, 1, 3, 1, 2, 4, 2]
def baseStart_8194616 : Nat := 118140960795 + 8194616 * 2 ^ 59
def prefixEnd_8194616 : Nat := 4983230072969 + 3 ^ 40 * 8194616 * 2
def baseEnd_8194616 : Nat := 4207776787024215760913653

theorem tailTrace_8194616 : CollatzResearch.WordTrace tailWord_8194616 prefixEnd_8194616 4207776787024215760913653 := by
  unfold tailWord_8194616
  simp only [CollatzResearch.WordTrace]
  refine ⟨149441099840156617917857851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199254799786875490557143801 149441099840156617917857851)
  ·
    refine ⟨224161649760234926876786777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149441099840156617917857851 224161649760234926876786777)
    ·
      refine ⟨168121237320176195157590083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224161649760234926876786777 168121237320176195157590083)
      ·
        refine ⟨252181855980264292736385125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168121237320176195157590083 252181855980264292736385125)
        ·
          refine ⟨47284097996299554888072211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 252181855980264292736385125 47284097996299554888072211)
          ·
            refine ⟨70926146994449332332108317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47284097996299554888072211 70926146994449332332108317)
            ·
              refine ⟨26597305122918499624540619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70926146994449332332108317 26597305122918499624540619)
              ·
                refine ⟨39895957684377749436810929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26597305122918499624540619 39895957684377749436810929)
                ·
                  refine ⟨29921968263283312077608197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39895957684377749436810929 29921968263283312077608197)
                  ·
                    refine ⟨5610369049365621014551537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29921968263283312077608197 5610369049365621014551537)
                    ·
                      refine ⟨4207776787024215760913653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5610369049365621014551537 4207776787024215760913653)
                      ·
                        rfl

theorem cell23_8194616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 2, 4, 2].length) (baseStart_8194616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8194616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8194616 prefixEnd_8194616 := by exact prefixLift 8194616
  have htrace : WordTrace (prefixWord ++ tailWord_8194616) baseStart_8194616 baseEnd_8194616 := by
    simpa [prefixWord, tailWord_8194616, baseEnd_8194616] using wordTrace_append hprefix tailTrace_8194616
  have hstable : (prefixWord ++ tailWord_8194616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8194616).length < 2 ^ (prefixWord ++ tailWord_8194616).sum := by decide
  have hdescent : baseEnd_8194616 < baseStart_8194616 := by decide
  rcases family_descends (prefixWord ++ tailWord_8194616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8194630 : List Nat := [6, 1, 1, 1, 2, 3, 1, 1, 2, 5]
def baseStart_8194630 : Nat := 118140960795 + 8194630 * 2 ^ 59
def prefixEnd_8194630 : Nat := 4983230072969 + 3 ^ 40 * 8194630 * 2
def baseEnd_8194630 : Nat := 1402594658584459568712863

theorem tailTrace_8194630 : CollatzResearch.WordTrace tailWord_8194630 prefixEnd_8194630 1402594658584459568712863 := by
  unfold tailWord_8194630
  simp only [CollatzResearch.WordTrace]
  refine ⟨9340084696945703632085167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 199255140201508344151150229 9340084696945703632085167)
  ·
    refine ⟨14010127045418555448127751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9340084696945703632085167 14010127045418555448127751)
    ·
      refine ⟨21015190568127833172191627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14010127045418555448127751 21015190568127833172191627)
      ·
        refine ⟨31522785852191749758287441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21015190568127833172191627 31522785852191749758287441)
        ·
          refine ⟨23642089389143812318715581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31522785852191749758287441 23642089389143812318715581)
          ·
            refine ⟨8865783520928929619518343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23642089389143812318715581 8865783520928929619518343)
            ·
              refine ⟨13298675281393394429277515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8865783520928929619518343 13298675281393394429277515)
              ·
                refine ⟨19948012922090091643916273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13298675281393394429277515 19948012922090091643916273)
                ·
                  refine ⟨14961009691567568732937205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19948012922090091643916273 14961009691567568732937205)
                  ·
                    refine ⟨1402594658584459568712863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14961009691567568732937205 1402594658584459568712863)
                    ·
                      rfl

theorem cell23_8194630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_8194630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8194630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8194630 prefixEnd_8194630 := by exact prefixLift 8194630
  have htrace : WordTrace (prefixWord ++ tailWord_8194630) baseStart_8194630 baseEnd_8194630 := by
    simpa [prefixWord, tailWord_8194630, baseEnd_8194630] using wordTrace_append hprefix tailTrace_8194630
  have hstable : (prefixWord ++ tailWord_8194630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8194630).length < 2 ^ (prefixWord ++ tailWord_8194630).sum := by decide
  have hdescent : baseEnd_8194630 < baseStart_8194630 := by decide
  rcases family_descends (prefixWord ++ tailWord_8194630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8194723 : List Nat := [1, 1, 1, 4, 1, 1, 2, 5, 3, 2, 2]
def baseStart_8194723 : Nat := 118140960795 + 8194723 * 2 ^ 59
def prefixEnd_8194723 : Nat := 4983230072969 + 3 ^ 40 * 8194723 * 2
def baseEnd_8194723 : Nat := 4207831729454246842275661

theorem tailTrace_8194723 : CollatzResearch.WordTrace tailWord_8194723 prefixEnd_8194723 4207831729454246842275661 := by
  unfold tailWord_8194723
  simp only [CollatzResearch.WordTrace]
  refine ⟨298886102290925593109860823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199257401527283728739907215 298886102290925593109860823)
  ·
    refine ⟨448329153436388389664791235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298886102290925593109860823 448329153436388389664791235)
    ·
      refine ⟨672493730154582584497186853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448329153436388389664791235 672493730154582584497186853)
      ·
        refine ⟨126092574403984234593222535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 672493730154582584497186853 126092574403984234593222535)
        ·
          refine ⟨189138861605976351889833803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126092574403984234593222535 189138861605976351889833803)
          ·
            refine ⟨283708292408964527834750705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189138861605976351889833803 283708292408964527834750705)
            ·
              refine ⟨212781219306723395876063029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283708292408964527834750705 212781219306723395876063029)
              ·
                refine ⟨19948239310005318363380909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 212781219306723395876063029 19948239310005318363380909)
                ·
                  refine ⟨7480589741251994386267841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19948239310005318363380909 7480589741251994386267841)
                  ·
                    refine ⟨5610442305938995789700881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7480589741251994386267841 5610442305938995789700881)
                    ·
                      refine ⟨4207831729454246842275661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5610442305938995789700881 4207831729454246842275661)
                      ·
                        rfl

theorem cell23_8194723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 3, 2, 2].length) (baseStart_8194723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8194723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8194723 prefixEnd_8194723 := by exact prefixLift 8194723
  have htrace : WordTrace (prefixWord ++ tailWord_8194723) baseStart_8194723 baseEnd_8194723 := by
    simpa [prefixWord, tailWord_8194723, baseEnd_8194723] using wordTrace_append hprefix tailTrace_8194723
  have hstable : (prefixWord ++ tailWord_8194723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8194723).length < 2 ^ (prefixWord ++ tailWord_8194723).sum := by decide
  have hdescent : baseEnd_8194723 < baseStart_8194723 := by decide
  rcases family_descends (prefixWord ++ tailWord_8194723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8194737 : List Nat := [1, 2, 2, 6, 2, 1, 1, 2, 1, 5]
def baseStart_8194737 : Nat := 118140960795 + 8194737 * 2 ^ 59
def prefixEnd_8194737 : Nat := 4983230072969 + 3 ^ 40 * 8194737 * 2
def baseEnd_8194737 : Nat := 1402612972727803262500199

theorem tailTrace_8194737 : CollatzResearch.WordTrace tailWord_8194737 prefixEnd_8194737 1402612972727803262500199 := by
  unfold tailWord_8194737
  simp only [CollatzResearch.WordTrace]
  refine ⟨298886612912874873500870465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199257741941916582333913643 298886612912874873500870465)
  ·
    refine ⟨224164959684656155125652849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298886612912874873500870465 224164959684656155125652849)
    ·
      refine ⟨168123719763492116344239637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224164959684656155125652849 168123719763492116344239637)
      ·
        refine ⟨7880799363913692953636233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 168123719763492116344239637 7880799363913692953636233)
        ·
          refine ⟨5910599522935269715227175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7880799363913692953636233 5910599522935269715227175)
          ·
            refine ⟨8865899284402904572840763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5910599522935269715227175 8865899284402904572840763)
            ·
              refine ⟨13298848926604356859261145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8865899284402904572840763 13298848926604356859261145)
              ·
                refine ⟨9974136694953267644445859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13298848926604356859261145 9974136694953267644445859)
                ·
                  refine ⟨14961205042429901466668789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9974136694953267644445859 14961205042429901466668789)
                  ·
                    refine ⟨1402612972727803262500199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14961205042429901466668789 1402612972727803262500199)
                    ·
                      rfl

theorem cell23_8194737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 2, 1, 5].length) (baseStart_8194737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8194737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8194737 prefixEnd_8194737 := by exact prefixLift 8194737
  have htrace : WordTrace (prefixWord ++ tailWord_8194737) baseStart_8194737 baseEnd_8194737 := by
    simpa [prefixWord, tailWord_8194737, baseEnd_8194737] using wordTrace_append hprefix tailTrace_8194737
  have hstable : (prefixWord ++ tailWord_8194737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8194737).length < 2 ^ (prefixWord ++ tailWord_8194737).sum := by decide
  have hdescent : baseEnd_8194737 < baseStart_8194737 := by decide
  rcases family_descends (prefixWord ++ tailWord_8194737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8194743 : List Nat := [1, 1, 3, 1, 6, 1, 1, 1, 3, 2, 3]
def baseStart_8194743 : Nat := 118140960795 + 8194743 * 2 ^ 59
def prefixEnd_8194743 : Nat := 4983230072969 + 3 ^ 40 * 8194743 * 2
def baseEnd_8194743 : Nat := 4207841999067336764025569

theorem tailTrace_8194743 : CollatzResearch.WordTrace tailWord_8194743 prefixEnd_8194743 4207841999067336764025569 := by
  unfold tailWord_8194743
  simp only [CollatzResearch.WordTrace]
  refine ⟨298886831750853136525588883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199257887833902091017059255 298886831750853136525588883)
  ·
    refine ⟨448330247626279704788383325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298886831750853136525588883 448330247626279704788383325)
    ·
      refine ⟨168123842859854889295643747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 448330247626279704788383325 168123842859854889295643747)
      ·
        refine ⟨252185764289782333943465621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168123842859854889295643747 252185764289782333943465621)
        ·
          refine ⟨11821207701083546903599951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 252185764289782333943465621 11821207701083546903599951)
          ·
            refine ⟨17731811551625320355399927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11821207701083546903599951 17731811551625320355399927)
            ·
              refine ⟨26597717327437980533099891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17731811551625320355399927 26597717327437980533099891)
              ·
                refine ⟨39896575991156970799649837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26597717327437980533099891 39896575991156970799649837)
                ·
                  refine ⟨14961215996683864049868689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39896575991156970799649837 14961215996683864049868689)
                  ·
                    refine ⟨11220911997512898037401517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14961215996683864049868689 11220911997512898037401517)
                    ·
                      refine ⟨4207841999067336764025569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11220911997512898037401517 4207841999067336764025569)
                      ·
                        rfl

theorem cell23_8194743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 3, 2, 3].length) (baseStart_8194743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8194743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8194743 prefixEnd_8194743 := by exact prefixLift 8194743
  have htrace : WordTrace (prefixWord ++ tailWord_8194743) baseStart_8194743 baseEnd_8194743 := by
    simpa [prefixWord, tailWord_8194743, baseEnd_8194743] using wordTrace_append hprefix tailTrace_8194743
  have hstable : (prefixWord ++ tailWord_8194743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8194743).length < 2 ^ (prefixWord ++ tailWord_8194743).sum := by decide
  have hdescent : baseEnd_8194743 < baseStart_8194743 := by decide
  rcases family_descends (prefixWord ++ tailWord_8194743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8194760 : List Nat := [2, 1, 3, 1, 2, 4, 3, 1, 1, 2, 3]
def baseStart_8194760 : Nat := 118140960795 + 8194760 * 2 ^ 59
def prefixEnd_8194760 : Nat := 4983230072969 + 3 ^ 40 * 8194760 * 2
def baseEnd_8194760 : Nat := 4207850728238463197512991

theorem tailTrace_8194760 : CollatzResearch.WordTrace tailWord_8194760 prefixEnd_8194760 4207850728238463197512991 := by
  unfold tailWord_8194760
  simp only [CollatzResearch.WordTrace]
  refine ⟨149443725895895774214478867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199258301194527698952638489 149443725895895774214478867)
  ·
    refine ⟨224165588843843661321718301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149443725895895774214478867 224165588843843661321718301)
    ·
      refine ⟨84062095816441372995644363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224165588843843661321718301 84062095816441372995644363)
      ·
        refine ⟨126093143724662059493466545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84062095816441372995644363 126093143724662059493466545)
        ·
          refine ⟨94569857793496544620099909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126093143724662059493466545 94569857793496544620099909)
          ·
            refine ⟨17731848336280602116268733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94569857793496544620099909 17731848336280602116268733)
            ·
              refine ⟨6649443126105225793600775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17731848336280602116268733 6649443126105225793600775)
              ·
                refine ⟨9974164689157838690401163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6649443126105225793600775 9974164689157838690401163)
                ·
                  refine ⟨14961247033736758035601745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9974164689157838690401163 14961247033736758035601745)
                  ·
                    refine ⟨11220935275302568526701309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14961247033736758035601745 11220935275302568526701309)
                    ·
                      refine ⟨4207850728238463197512991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11220935275302568526701309 4207850728238463197512991)
                      ·
                        rfl

theorem cell23_8194760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 1, 1, 2, 3].length) (baseStart_8194760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8194760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8194760 prefixEnd_8194760 := by exact prefixLift 8194760
  have htrace : WordTrace (prefixWord ++ tailWord_8194760) baseStart_8194760 baseEnd_8194760 := by
    simpa [prefixWord, tailWord_8194760, baseEnd_8194760] using wordTrace_append hprefix tailTrace_8194760
  have hstable : (prefixWord ++ tailWord_8194760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8194760).length < 2 ^ (prefixWord ++ tailWord_8194760).sum := by decide
  have hdescent : baseEnd_8194760 < baseStart_8194760 := by decide
  rcases family_descends (prefixWord ++ tailWord_8194760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8194783 : List Nat := [1, 1, 2, 3, 2, 3, 1, 2, 3, 3, 2]
def baseStart_8194783 : Nat := 118140960795 + 8194783 * 2 ^ 59
def prefixEnd_8194783 : Nat := 4983230072969 + 3 ^ 40 * 8194783 * 2
def baseEnd_8194783 : Nat := 4207862538293516607525385

theorem tailTrace_8194783 : CollatzResearch.WordTrace tailWord_8194783 prefixEnd_8194783 4207862538293516607525385 := by
  unfold tailWord_8194783
  simp only [CollatzResearch.WordTrace]
  refine ⟨298888290670708223357045003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199258860447138815571363335 298888290670708223357045003)
  ·
    refine ⟨448332436006062335035567505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298888290670708223357045003 448332436006062335035567505)
    ·
      refine ⟨336249327004546751276675629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 448332436006062335035567505 336249327004546751276675629)
      ·
        refine ⟨126093497626705031728753361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 336249327004546751276675629 126093497626705031728753361)
        ·
          refine ⟨94570123220028773796565021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126093497626705031728753361 94570123220028773796565021)
          ·
            refine ⟨35463796207510790173711883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94570123220028773796565021 35463796207510790173711883)
            ·
              refine ⟨53195694311266185260567825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35463796207510790173711883 53195694311266185260567825)
              ·
                refine ⟨39896770733449638945425869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53195694311266185260567825 39896770733449638945425869)
                ·
                  refine ⟨14961289025043614604534701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39896770733449638945425869 14961289025043614604534701)
                  ·
                    refine ⟨5610483384391355476700513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14961289025043614604534701 5610483384391355476700513)
                    ·
                      refine ⟨4207862538293516607525385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5610483384391355476700513 4207862538293516607525385)
                      ·
                        rfl

theorem cell23_8194783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 3, 3, 2].length) (baseStart_8194783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8194783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8194783 prefixEnd_8194783 := by exact prefixLift 8194783
  have htrace : WordTrace (prefixWord ++ tailWord_8194783) baseStart_8194783 baseEnd_8194783 := by
    simpa [prefixWord, tailWord_8194783, baseEnd_8194783] using wordTrace_append hprefix tailTrace_8194783
  have hstable : (prefixWord ++ tailWord_8194783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8194783).length < 2 ^ (prefixWord ++ tailWord_8194783).sum := by decide
  have hdescent : baseEnd_8194783 < baseStart_8194783 := by decide
  rcases family_descends (prefixWord ++ tailWord_8194783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8194806 : List Nat := [5, 1, 1, 1, 1, 2, 1, 2, 1, 8]
def baseStart_8194806 : Nat := 118140960795 + 8194806 * 2 ^ 59
def prefixEnd_8194806 : Nat := 4983230072969 + 3 ^ 40 * 8194806 * 2
def baseEnd_8194806 : Nat := 1402624782782856672512593

theorem tailTrace_8194806 : CollatzResearch.WordTrace tailWord_8194806 prefixEnd_8194806 1402624782782856672512593 := by
  unfold tailWord_8194806
  simp only [CollatzResearch.WordTrace]
  refine ⟨18680570596851556142820767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199259419699749932190088181 18680570596851556142820767)
  ·
    refine ⟨28020855895277334214231151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18680570596851556142820767 28020855895277334214231151)
    ·
      refine ⟨42031283842916001321346727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28020855895277334214231151 42031283842916001321346727)
      ·
        refine ⟨63046925764374001982020091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42031283842916001321346727 63046925764374001982020091)
        ·
          refine ⟨94570388646561002973030137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63046925764374001982020091 94570388646561002973030137)
          ·
            refine ⟨70927791484920752229772603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94570388646561002973030137 70927791484920752229772603)
            ·
              refine ⟨106391687227381128344658905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70927791484920752229772603 106391687227381128344658905)
              ·
                refine ⟨79793765420535846258494179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106391687227381128344658905 79793765420535846258494179)
                ·
                  refine ⟨119690648130803769387741269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79793765420535846258494179 119690648130803769387741269)
                  ·
                    refine ⟨1402624782782856672512593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 119690648130803769387741269 1402624782782856672512593)
                    ·
                      rfl

theorem cell23_8194806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_8194806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8194806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8194806 prefixEnd_8194806 := by exact prefixLift 8194806
  have htrace : WordTrace (prefixWord ++ tailWord_8194806) baseStart_8194806 baseEnd_8194806 := by
    simpa [prefixWord, tailWord_8194806, baseEnd_8194806] using wordTrace_append hprefix tailTrace_8194806
  have hstable : (prefixWord ++ tailWord_8194806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8194806).length < 2 ^ (prefixWord ++ tailWord_8194806).sum := by decide
  have hdescent : baseEnd_8194806 < baseStart_8194806 := by decide
  rcases family_descends (prefixWord ++ tailWord_8194806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8194813 : List Nat := [1, 4, 1, 1, 1, 1, 3, 4, 1, 4, 2]
def baseStart_8194813 : Nat := 118140960795 + 8194813 * 2 ^ 59
def prefixEnd_8194813 : Nat := 4983230072969 + 3 ^ 40 * 8194813 * 2
def baseEnd_8194813 : Nat := 4207877942713151490150247

theorem tailTrace_8194813 : CollatzResearch.WordTrace tailWord_8194813 prefixEnd_8194813 4207877942713151490150247 := by
  unfold tailWord_8194813
  simp only [CollatzResearch.WordTrace]
  refine ⟨298889384860599538480637093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199259589907066358987091395 298889384860599538480637093)
  ·
    refine ⟨56041759661362413465119455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 298889384860599538480637093 56041759661362413465119455)
    ·
      refine ⟨84062639492043620197679183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56041759661362413465119455 84062639492043620197679183)
      ·
        refine ⟨126093959238065430296518775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84062639492043620197679183 126093959238065430296518775)
        ·
          refine ⟨189140938857098145444778163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126093959238065430296518775 189140938857098145444778163)
          ·
            refine ⟨283711408285647218167167245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189140938857098145444778163 283711408285647218167167245)
            ·
              refine ⟨106391778107117706812687717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 283711408285647218167167245 106391778107117706812687717)
              ·
                refine ⟨19948458395084570027378947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106391778107117706812687717 19948458395084570027378947)
                ·
                  refine ⟨29922687592626855041068421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19948458395084570027378947 29922687592626855041068421)
                  ·
                    refine ⟨5610503923617535320200329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29922687592626855041068421 5610503923617535320200329)
                    ·
                      refine ⟨4207877942713151490150247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5610503923617535320200329 4207877942713151490150247)
                      ·
                        rfl

theorem cell23_8194813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 4, 2].length) (baseStart_8194813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8194813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8194813 prefixEnd_8194813 := by exact prefixLift 8194813
  have htrace : WordTrace (prefixWord ++ tailWord_8194813) baseStart_8194813 baseEnd_8194813 := by
    simpa [prefixWord, tailWord_8194813, baseEnd_8194813] using wordTrace_append hprefix tailTrace_8194813
  have hstable : (prefixWord ++ tailWord_8194813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8194813).length < 2 ^ (prefixWord ++ tailWord_8194813).sum := by decide
  have hdescent : baseEnd_8194813 < baseStart_8194813 := by decide
  rcases family_descends (prefixWord ++ tailWord_8194813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8194819 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 11]
def baseStart_8194819 : Nat := 118140960795 + 8194819 * 2 ^ 59
def prefixEnd_8194819 : Nat := 4983230072969 + 3 ^ 40 * 8194819 * 2
def baseEnd_8194819 : Nat := 467542335955230940741691

theorem tailTrace_8194819 : CollatzResearch.WordTrace tailWord_8194819 prefixEnd_8194819 467542335955230940741691 := by
  unfold tailWord_8194819
  simp only [CollatzResearch.WordTrace]
  refine ⟨298889603698577801505355511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199259735799051867670237007 298889603698577801505355511)
  ·
    refine ⟨448334405547866702258033267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298889603698577801505355511 448334405547866702258033267)
    ·
      refine ⟨672501608321800053387049901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448334405547866702258033267 672501608321800053387049901)
      ·
        refine ⟨252188103120675020020143713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 672501608321800053387049901 252188103120675020020143713)
        ·
          refine ⟨189141077340506265015107785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252188103120675020020143713 189141077340506265015107785)
          ·
            refine ⟨141855808005379698761330839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189141077340506265015107785 141855808005379698761330839)
            ·
              refine ⟨212783712008069548141996259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141855808005379698761330839 212783712008069548141996259)
              ·
                refine ⟨319175568012104322212994389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212783712008069548141996259 319175568012104322212994389)
                ·
                  refine ⟨467542335955230940741691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 319175568012104322212994389 467542335955230940741691)
                  ·
                    rfl

theorem cell23_8194819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 11].length) (baseStart_8194819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8194819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8194819 prefixEnd_8194819 := by exact prefixLift 8194819
  have htrace : WordTrace (prefixWord ++ tailWord_8194819) baseStart_8194819 baseEnd_8194819 := by
    simpa [prefixWord, tailWord_8194819, baseEnd_8194819] using wordTrace_append hprefix tailTrace_8194819
  have hstable : (prefixWord ++ tailWord_8194819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8194819).length < 2 ^ (prefixWord ++ tailWord_8194819).sum := by decide
  have hdescent : baseEnd_8194819 < baseStart_8194819 := by decide
  rcases family_descends (prefixWord ++ tailWord_8194819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8194826 : List Nat := [3, 1, 2, 2, 1, 2, 1, 1, 4, 2, 4]
def baseStart_8194826 : Nat := 118140960795 + 8194826 * 2 ^ 59
def prefixEnd_8194826 : Nat := 4983230072969 + 3 ^ 40 * 8194826 * 2
def baseEnd_8194826 : Nat := 4207884617961659939287687

theorem tailTrace_8194826 : CollatzResearch.WordTrace tailWord_8194826 prefixEnd_8194826 4207884617961659939287687 := by
  unfold tailWord_8194826
  simp only [CollatzResearch.WordTrace]
  refine ⟨74722464752388110425215083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199259906006368294467240221 74722464752388110425215083)
  ·
    refine ⟨112083697128582165637822625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74722464752388110425215083 112083697128582165637822625)
    ·
      refine ⟨84062772846436624228366969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112083697128582165637822625 84062772846436624228366969)
      ·
        refine ⟨63047079634827468171275227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84062772846436624228366969 63047079634827468171275227)
        ·
          refine ⟨94570619452241202256912841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63047079634827468171275227 94570619452241202256912841)
          ·
            refine ⟨70927964589180901692684631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94570619452241202256912841 70927964589180901692684631)
            ·
              refine ⟨106391946883771352539026947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70927964589180901692684631 106391946883771352539026947)
              ·
                refine ⟨159587920325657028808540421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106391946883771352539026947 159587920325657028808540421)
                ·
                  refine ⟨29922735061060692901601329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 159587920325657028808540421 29922735061060692901601329)
                  ·
                    refine ⟨22442051295795519676200997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29922735061060692901601329 22442051295795519676200997)
                    ·
                      refine ⟨4207884617961659939287687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22442051295795519676200997 4207884617961659939287687)
                      ·
                        rfl

theorem cell23_8194826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_8194826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8194826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8194826 prefixEnd_8194826 := by exact prefixLift 8194826
  have htrace : WordTrace (prefixWord ++ tailWord_8194826) baseStart_8194826 baseEnd_8194826 := by
    simpa [prefixWord, tailWord_8194826, baseEnd_8194826] using wordTrace_append hprefix tailTrace_8194826
  have hstable : (prefixWord ++ tailWord_8194826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8194826).length < 2 ^ (prefixWord ++ tailWord_8194826).sum := by decide
  have hdescent : baseEnd_8194826 < baseStart_8194826 := by decide
  rcases family_descends (prefixWord ++ tailWord_8194826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8194866 : List Nat := [3, 2, 1, 1, 3, 1, 1, 3, 1, 7]
def baseStart_8194866 : Nat := 118140960795 + 8194866 * 2 ^ 59
def prefixEnd_8194866 : Nat := 4983230072969 + 3 ^ 40 * 8194866 * 2
def baseEnd_8194866 : Nat := 1402635052395946594262501

theorem tailTrace_8194866 : CollatzResearch.WordTrace tailWord_8194866 prefixEnd_8194866 1402635052395946594262501 := by
  unfold tailWord_8194866
  simp only [CollatzResearch.WordTrace]
  refine ⟨74722829482351882133079113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199260878619605019021544301 74722829482351882133079113)
  ·
    refine ⟨56042122111763911599809335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74722829482351882133079113 56042122111763911599809335)
    ·
      refine ⟨84063183167645867399714003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56042122111763911599809335 84063183167645867399714003)
      ·
        refine ⟨126094774751468801099571005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84063183167645867399714003 126094774751468801099571005)
        ·
          refine ⟨47285540531800800412339127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126094774751468801099571005 47285540531800800412339127)
          ·
            refine ⟨70928310797701200618508691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47285540531800800412339127 70928310797701200618508691)
            ·
              refine ⟨106392466196551800927763037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70928310797701200618508691 106392466196551800927763037)
              ·
                refine ⟨39897174823706925347911139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106392466196551800927763037 39897174823706925347911139)
                ·
                  refine ⟨59845762235560388021866709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39897174823706925347911139 59845762235560388021866709)
                  ·
                    refine ⟨1402635052395946594262501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59845762235560388021866709 1402635052395946594262501)
                    ·
                      rfl

theorem cell23_8194866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 1, 7].length) (baseStart_8194866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8194866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8194866 prefixEnd_8194866 := by exact prefixLift 8194866
  have htrace : WordTrace (prefixWord ++ tailWord_8194866) baseStart_8194866 baseEnd_8194866 := by
    simpa [prefixWord, tailWord_8194866, baseEnd_8194866] using wordTrace_append hprefix tailTrace_8194866
  have hstable : (prefixWord ++ tailWord_8194866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8194866).length < 2 ^ (prefixWord ++ tailWord_8194866).sum := by decide
  have hdescent : baseEnd_8194866 < baseStart_8194866 := by decide
  rcases family_descends (prefixWord ++ tailWord_8194866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8194876 : List Nat := [2, 2, 2, 2, 1, 1, 1, 4, 1, 2, 5]
def baseStart_8194876 : Nat := 118140960795 + 8194876 * 2 ^ 59
def prefixEnd_8194876 : Nat := 4983230072969 + 3 ^ 40 * 8194876 * 2
def baseEnd_8194876 : Nat := 4207910291994384743662457

theorem tailTrace_8194876 : CollatzResearch.WordTrace tailWord_8194876 prefixEnd_8194876 4207910291994384743662457 := by
  unfold tailWord_8194876
  simp only [CollatzResearch.WordTrace]
  refine ⟨149445841329685650120090241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199261121772914200160120321 149445841329685650120090241)
  ·
    refine ⟨112084380997264237590067681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149445841329685650120090241 112084380997264237590067681)
    ·
      refine ⟨84063285747948178192550761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112084380997264237590067681 84063285747948178192550761)
      ·
        refine ⟨63047464310961133644413071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84063285747948178192550761 63047464310961133644413071)
        ·
          refine ⟨94571196466441700466619607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63047464310961133644413071 94571196466441700466619607)
          ·
            refine ⟨141856794699662550699929411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94571196466441700466619607 141856794699662550699929411)
            ·
              refine ⟨212785192049493826049894117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141856794699662550699929411 212785192049493826049894117)
              ·
                refine ⟨39897223509280092384355147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 212785192049493826049894117 39897223509280092384355147)
                ·
                  refine ⟨59845835263920138576532721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39897223509280092384355147 59845835263920138576532721)
                  ·
                    refine ⟨44884376447940103932399541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59845835263920138576532721 44884376447940103932399541)
                    ·
                      refine ⟨4207910291994384743662457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44884376447940103932399541 4207910291994384743662457)
                      ·
                        rfl

theorem cell23_8194876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_8194876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8194876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8194876 prefixEnd_8194876 := by exact prefixLift 8194876
  have htrace : WordTrace (prefixWord ++ tailWord_8194876) baseStart_8194876 baseEnd_8194876 := by
    simpa [prefixWord, tailWord_8194876, baseEnd_8194876] using wordTrace_append hprefix tailTrace_8194876
  have hstable : (prefixWord ++ tailWord_8194876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8194876).length < 2 ^ (prefixWord ++ tailWord_8194876).sum := by decide
  have hdescent : baseEnd_8194876 < baseStart_8194876 := by decide
  rcases family_descends (prefixWord ++ tailWord_8194876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8194920 : List Nat := [2, 1, 4, 2, 1, 3, 2, 1, 2, 1, 4]
def baseStart_8194920 : Nat := 118140960795 + 8194920 * 2 ^ 59
def prefixEnd_8194920 : Nat := 4983230072969 + 3 ^ 40 * 8194920 * 2
def baseEnd_8194920 : Nat := 4207932885143182571512255

theorem tailTrace_8194920 : CollatzResearch.WordTrace tailWord_8194920 prefixEnd_8194920 4207932885143182571512255 := by
  unfold tailWord_8194920
  simp only [CollatzResearch.WordTrace]
  refine ⟨149446643735605947877391107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199262191647474597169854809 149446643735605947877391107)
  ·
    refine ⟨224169965603408921816086661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149446643735605947877391107 224169965603408921816086661)
    ·
      refine ⟨42031868550639172840516249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224169965603408921816086661 42031868550639172840516249)
      ·
        refine ⟨31523901412979379630387187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42031868550639172840516249 31523901412979379630387187)
        ·
          refine ⟨47285852119469069445580781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31523901412979379630387187 47285852119469069445580781)
          ·
            refine ⟨17732194544800901042092793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47285852119469069445580781 17732194544800901042092793)
            ·
              refine ⟨13299145908600675781569595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17732194544800901042092793 13299145908600675781569595)
              ·
                refine ⟨19948718862901013672354393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13299145908600675781569595 19948718862901013672354393)
                ·
                  refine ⟨14961539147175760254265795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19948718862901013672354393 14961539147175760254265795)
                  ·
                    refine ⟨22442308720763640381398693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14961539147175760254265795 22442308720763640381398693)
                    ·
                      refine ⟨4207932885143182571512255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22442308720763640381398693 4207932885143182571512255)
                      ·
                        rfl

theorem cell23_8194920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_8194920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8194920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8194920 prefixEnd_8194920 := by exact prefixLift 8194920
  have htrace : WordTrace (prefixWord ++ tailWord_8194920) baseStart_8194920 baseEnd_8194920 := by
    simpa [prefixWord, tailWord_8194920, baseEnd_8194920] using wordTrace_append hprefix tailTrace_8194920
  have hstable : (prefixWord ++ tailWord_8194920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8194920).length < 2 ^ (prefixWord ++ tailWord_8194920).sum := by decide
  have hdescent : baseEnd_8194920 < baseStart_8194920 := by decide
  rcases family_descends (prefixWord ++ tailWord_8194920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8194923 : List Nat := [1, 1, 1, 1, 2, 2, 5, 3, 2, 2, 3]
def baseStart_8194923 : Nat := 118140960795 + 8194923 * 2 ^ 59
def prefixEnd_8194923 : Nat := 4983230072969 + 3 ^ 40 * 8194923 * 2
def baseEnd_8194923 : Nat := 4207934425585146059774741

theorem tailTrace_8194923 : CollatzResearch.WordTrace tailWord_8194923 prefixEnd_8194923 4207934425585146059774741 := by
  unfold tailWord_8194923
  simp only [CollatzResearch.WordTrace]
  refine ⟨298893396890201027267141423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199262264593467351511427615 298893396890201027267141423)
  ·
    refine ⟨448340095335301540900712135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298893396890201027267141423 448340095335301540900712135)
    ·
      refine ⟨672510143002952311351068203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448340095335301540900712135 672510143002952311351068203)
      ·
        refine ⟨1008765214504428467026602305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 672510143002952311351068203 1008765214504428467026602305)
        ·
          refine ⟨756573910878321350269951729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1008765214504428467026602305 756573910878321350269951729)
          ·
            refine ⟨567430433158741012702463797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 756573910878321350269951729 567430433158741012702463797)
            ·
              refine ⟨53196603108631969940855981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 567430433158741012702463797 53196603108631969940855981)
              ·
                refine ⟨19948726165736988727820993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53196603108631969940855981 19948726165736988727820993)
                ·
                  refine ⟨14961544624302741545865745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19948726165736988727820993 14961544624302741545865745)
                  ·
                    refine ⟨11221158468227056159399309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14961544624302741545865745 11221158468227056159399309)
                    ·
                      refine ⟨4207934425585146059774741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11221158468227056159399309 4207934425585146059774741)
                      ·
                        rfl

theorem cell23_8194923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 2, 2, 3].length) (baseStart_8194923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8194923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8194923 prefixEnd_8194923 := by exact prefixLift 8194923
  have htrace : WordTrace (prefixWord ++ tailWord_8194923) baseStart_8194923 baseEnd_8194923 := by
    simpa [prefixWord, tailWord_8194923, baseEnd_8194923] using wordTrace_append hprefix tailTrace_8194923
  have hstable : (prefixWord ++ tailWord_8194923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8194923).length < 2 ^ (prefixWord ++ tailWord_8194923).sum := by decide
  have hdescent : baseEnd_8194923 < baseStart_8194923 := by decide
  rcases family_descends (prefixWord ++ tailWord_8194923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8194973 : List Nat := [1, 4, 2, 1, 2, 1, 1, 3, 3, 5]
def baseStart_8194973 : Nat := 118140960795 + 8194973 * 2 ^ 59
def prefixEnd_8194973 : Nat := 4983230072969 + 3 ^ 40 * 8194973 * 2
def baseEnd_8194973 : Nat := 1402653366539290288049837

theorem tailTrace_8194973 : CollatzResearch.WordTrace tailWord_8194973 prefixEnd_8194973 1402653366539290288049837 := by
  unfold tailWord_8194973
  simp only [CollatzResearch.WordTrace]
  refine ⟨298895220540019885806461573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199263480360013257204307715 298895220540019885806461573)
  ·
    refine ⟨56042853851253728588711545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 298895220540019885806461573 56042853851253728588711545)
    ·
      refine ⟨42032140388440296441533659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56042853851253728588711545 42032140388440296441533659)
      ·
        refine ⟨63048210582660444662300489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42032140388440296441533659 63048210582660444662300489)
        ·
          refine ⟨47286157936995333496725367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63048210582660444662300489 47286157936995333496725367)
          ·
            refine ⟨70929236905493000245088051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47286157936995333496725367 70929236905493000245088051)
            ·
              refine ⟨106393855358239500367632077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70929236905493000245088051 106393855358239500367632077)
              ·
                refine ⟨39897695759339812637862029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106393855358239500367632077 39897695759339812637862029)
                ·
                  refine ⟨14961635909752429739198261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39897695759339812637862029 14961635909752429739198261)
                  ·
                    refine ⟨1402653366539290288049837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14961635909752429739198261 1402653366539290288049837)
                    ·
                      rfl

theorem cell23_8194973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_8194973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8194973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8194973 prefixEnd_8194973 := by exact prefixLift 8194973
  have htrace : WordTrace (prefixWord ++ tailWord_8194973) baseStart_8194973 baseEnd_8194973 := by
    simpa [prefixWord, tailWord_8194973, baseEnd_8194973] using wordTrace_append hprefix tailTrace_8194973
  have hstable : (prefixWord ++ tailWord_8194973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8194973).length < 2 ^ (prefixWord ++ tailWord_8194973).sum := by decide
  have hdescent : baseEnd_8194973 < baseStart_8194973 := by decide
  rcases family_descends (prefixWord ++ tailWord_8194973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8194980 : List Nat := [2, 3, 1, 2, 1, 2, 3, 1, 1, 5, 2]
def baseStart_8194980 : Nat := 118140960795 + 8194980 * 2 ^ 59
def prefixEnd_8194980 : Nat := 4983230072969 + 3 ^ 40 * 8194980 * 2
def baseEnd_8194980 : Nat := 4207963693982452336761979

theorem tailTrace_8194980 : CollatzResearch.WordTrace tailWord_8194980 prefixEnd_8194980 4207963693982452336761979 := by
  unfold tailWord_8194980
  simp only [CollatzResearch.WordTrace]
  refine ⟨149447737925497263000983197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199263650567329684001310929 149447737925497263000983197)
  ·
    refine ⟨56042901722061473625368699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149447737925497263000983197 56042901722061473625368699)
    ·
      refine ⟨84064352583092210438053049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56042901722061473625368699 84064352583092210438053049)
      ·
        refine ⟨63048264437319157828539787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84064352583092210438053049 63048264437319157828539787)
        ·
          refine ⟨94572396655978736742809681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63048264437319157828539787 94572396655978736742809681)
          ·
            refine ⟨70929297491984052557107261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94572396655978736742809681 70929297491984052557107261)
            ·
              refine ⟨26598486559494019708915223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70929297491984052557107261 26598486559494019708915223)
              ·
                refine ⟨39897729839241029563372835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26598486559494019708915223 39897729839241029563372835)
                ·
                  refine ⟨59846594758861544345059253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39897729839241029563372835 59846594758861544345059253)
                  ·
                    refine ⟨5610618258643269782349305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59846594758861544345059253 5610618258643269782349305)
                    ·
                      refine ⟨4207963693982452336761979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5610618258643269782349305 4207963693982452336761979)
                      ·
                        rfl

theorem cell23_8194980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 1, 5, 2].length) (baseStart_8194980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8194980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8194980 prefixEnd_8194980 := by exact prefixLift 8194980
  have htrace : WordTrace (prefixWord ++ tailWord_8194980) baseStart_8194980 baseEnd_8194980 := by
    simpa [prefixWord, tailWord_8194980, baseEnd_8194980] using wordTrace_append hprefix tailTrace_8194980
  have hstable : (prefixWord ++ tailWord_8194980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8194980).length < 2 ^ (prefixWord ++ tailWord_8194980).sum := by decide
  have hdescent : baseEnd_8194980 < baseStart_8194980 := by decide
  rcases family_descends (prefixWord ++ tailWord_8194980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8195023 : List Nat := [1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 6]
def baseStart_8195023 : Nat := 118140960795 + 8195023 * 2 ^ 59
def prefixEnd_8195023 : Nat := 4983230072969 + 3 ^ 40 * 8195023 * 2
def baseEnd_8195023 : Nat := 4207985773650595668524281

theorem tailTrace_8195023 : CollatzResearch.WordTrace tailWord_8195023 prefixEnd_8195023 4207985773650595668524281 := by
  unfold tailWord_8195023
  simp only [CollatzResearch.WordTrace]
  refine ⟨298897044189838744345781723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199264696126559162897187815 298897044189838744345781723)
  ·
    refine ⟨448345566284758116518672585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298897044189838744345781723 448345566284758116518672585)
    ·
      refine ⟨336259174713568587389004439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 448345566284758116518672585 336259174713568587389004439)
      ·
        refine ⟨504388762070352881083506659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336259174713568587389004439 504388762070352881083506659)
        ·
          refine ⟨756583143105529321625259989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504388762070352881083506659 756583143105529321625259989)
          ·
            refine ⟨17732417416535843475592031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 756583143105529321625259989 17732417416535843475592031)
            ·
              refine ⟨26598626124803765213388047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17732417416535843475592031 26598626124803765213388047)
              ·
                refine ⟨39897939187205647820082071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26598626124803765213388047 39897939187205647820082071)
                ·
                  refine ⟨59846908780808471730123107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39897939187205647820082071 59846908780808471730123107)
                  ·
                    refine ⟨89770363171212707595184661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59846908780808471730123107 89770363171212707595184661)
                    ·
                      refine ⟨4207985773650595668524281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89770363171212707595184661 4207985773650595668524281)
                      ·
                        rfl

theorem cell23_8195023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 6].length) (baseStart_8195023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8195023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8195023 prefixEnd_8195023 := by exact prefixLift 8195023
  have htrace : WordTrace (prefixWord ++ tailWord_8195023) baseStart_8195023 baseEnd_8195023 := by
    simpa [prefixWord, tailWord_8195023, baseEnd_8195023] using wordTrace_append hprefix tailTrace_8195023
  have hstable : (prefixWord ++ tailWord_8195023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8195023).length < 2 ^ (prefixWord ++ tailWord_8195023).sum := by decide
  have hdescent : baseEnd_8195023 < baseStart_8195023 := by decide
  rcases family_descends (prefixWord ++ tailWord_8195023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8195033 : List Nat := [1, 2, 1, 2, 5, 2, 1, 9]
def baseStart_8195033 : Nat := 118140960795 + 8195033 * 2 ^ 59
def prefixEnd_8195033 : Nat := 4983230072969 + 3 ^ 40 * 8195033 * 2
def baseEnd_8195033 : Nat := 155851515128042245533305

theorem tailTrace_8195033 : CollatzResearch.WordTrace tailWord_8195033 prefixEnd_8195033 155851515128042245533305 := by
  unfold tailWord_8195033
  simp only [CollatzResearch.WordTrace]
  refine ⟨298897408919802516053645753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199264939279868344035763835 298897408919802516053645753)
  ·
    refine ⟨224173056689851887040234315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298897408919802516053645753 224173056689851887040234315)
    ·
      refine ⟨336259585034777830560351473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224173056689851887040234315 336259585034777830560351473)
      ·
        refine ⟨252194688776083372920263605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336259585034777830560351473 252194688776083372920263605)
        ·
          refine ⟨23643252072757816211274713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 252194688776083372920263605 23643252072757816211274713)
          ·
            refine ⟨17732439054568362158456035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23643252072757816211274713 17732439054568362158456035)
            ·
              refine ⟨26598658581852543237684053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17732439054568362158456035 26598658581852543237684053)
              ·
                refine ⟨155851515128042245533305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26598658581852543237684053 155851515128042245533305)
                ·
                  rfl

theorem cell23_8195033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 9].length) (baseStart_8195033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8195033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8195033 prefixEnd_8195033 := by exact prefixLift 8195033
  have htrace : WordTrace (prefixWord ++ tailWord_8195033) baseStart_8195033 baseEnd_8195033 := by
    simpa [prefixWord, tailWord_8195033, baseEnd_8195033] using wordTrace_append hprefix tailTrace_8195033
  have hstable : (prefixWord ++ tailWord_8195033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8195033).length < 2 ^ (prefixWord ++ tailWord_8195033).sum := by decide
  have hdescent : baseEnd_8195033 < baseStart_8195033 := by decide
  rcases family_descends (prefixWord ++ tailWord_8195033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8195044 : List Nat := [2, 3, 1, 1, 1, 1, 2, 7, 1, 2, 2]
def baseStart_8195044 : Nat := 118140960795 + 8195044 * 2 ^ 59
def prefixEnd_8195044 : Nat := 4983230072969 + 3 ^ 40 * 8195044 * 2
def baseEnd_8195044 : Nat := 4207996556744340086361685

theorem tailTrace_8195044 : CollatzResearch.WordTrace tailWord_8195044 prefixEnd_8195044 4207996556744340086361685 := by
  unfold tailWord_8195044
  simp only [CollatzResearch.WordTrace]
  refine ⟨149448905061381332466148093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199265206748508443288197457 149448905061381332466148093)
  ·
    refine ⟨56043339398017999674805535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149448905061381332466148093 56043339398017999674805535)
    ·
      refine ⟨84065009097026999512208303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56043339398017999674805535 84065009097026999512208303)
      ·
        refine ⟨126097513645540499268312455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84065009097026999512208303 126097513645540499268312455)
        ·
          refine ⟨189146270468310748902468683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126097513645540499268312455 189146270468310748902468683)
          ·
            refine ⟨283719405702466123353703025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189146270468310748902468683 283719405702466123353703025)
            ·
              refine ⟨212789554276849592515277269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283719405702466123353703025 212789554276849592515277269)
              ·
                refine ⟨4987255178363662324576811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 212789554276849592515277269 4987255178363662324576811)
                ·
                  refine ⟨7480882767545493486865217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4987255178363662324576811 7480882767545493486865217)
                  ·
                    refine ⟨5610662075659120115148913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7480882767545493486865217 5610662075659120115148913)
                    ·
                      refine ⟨4207996556744340086361685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5610662075659120115148913 4207996556744340086361685)
                      ·
                        rfl

theorem cell23_8195044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 7, 1, 2, 2].length) (baseStart_8195044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8195044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8195044 prefixEnd_8195044 := by exact prefixLift 8195044
  have htrace : WordTrace (prefixWord ++ tailWord_8195044) baseStart_8195044 baseEnd_8195044 := by
    simpa [prefixWord, tailWord_8195044, baseEnd_8195044] using wordTrace_append hprefix tailTrace_8195044
  have hstable : (prefixWord ++ tailWord_8195044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8195044).length < 2 ^ (prefixWord ++ tailWord_8195044).sum := by decide
  have hdescent : baseEnd_8195044 < baseStart_8195044 := by decide
  rcases family_descends (prefixWord ++ tailWord_8195044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8195047 : List Nat := [1, 1, 5, 2, 2, 1, 2, 3, 1, 2, 3]
def baseStart_8195047 : Nat := 118140960795 + 8195047 * 2 ^ 59
def prefixEnd_8195047 : Nat := 4983230072969 + 3 ^ 40 * 8195047 * 2
def baseEnd_8195047 : Nat := 4207998097186303574624171

theorem tailTrace_8195047 : CollatzResearch.WordTrace tailWord_8195047 prefixEnd_8195047 4207998097186303574624171 := by
  unfold tailWord_8195047
  simp only [CollatzResearch.WordTrace]
  refine ⟨298897919541751796444655395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199265279694501197629770263 298897919541751796444655395)
  ·
    refine ⟨448346879312627694666983093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298897919541751796444655395 448346879312627694666983093)
    ·
      refine ⟨42032519935558846375029665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 448346879312627694666983093 42032519935558846375029665)
      ·
        refine ⟨31524389951669134781272249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42032519935558846375029665 31524389951669134781272249)
        ·
          refine ⟨23643292463751851085954187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31524389951669134781272249 23643292463751851085954187)
          ·
            refine ⟨35464938695627776628931281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23643292463751851085954187 35464938695627776628931281)
            ·
              refine ⟨26598704021720832471698461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35464938695627776628931281 26598704021720832471698461)
              ·
                refine ⟨9974514008145312176886923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26598704021720832471698461 9974514008145312176886923)
                ·
                  refine ⟨14961771012217968265330385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9974514008145312176886923 14961771012217968265330385)
                  ·
                    refine ⟨11221328259163476198997789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14961771012217968265330385 11221328259163476198997789)
                    ·
                      refine ⟨4207998097186303574624171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11221328259163476198997789 4207998097186303574624171)
                      ·
                        rfl

theorem cell23_8195047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_8195047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8195047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8195047 prefixEnd_8195047 := by exact prefixLift 8195047
  have htrace : WordTrace (prefixWord ++ tailWord_8195047) baseStart_8195047 baseEnd_8195047 := by
    simpa [prefixWord, tailWord_8195047, baseEnd_8195047] using wordTrace_append hprefix tailTrace_8195047
  have hstable : (prefixWord ++ tailWord_8195047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8195047).length < 2 ^ (prefixWord ++ tailWord_8195047).sum := by decide
  have hdescent : baseEnd_8195047 < baseStart_8195047 := by decide
  rcases family_descends (prefixWord ++ tailWord_8195047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8195077 : List Nat := [1, 3, 1, 1, 2, 3, 3, 3, 2, 1, 3]
def baseStart_8195077 : Nat := 118140960795 + 8195077 * 2 ^ 59
def prefixEnd_8195077 : Nat := 4983230072969 + 3 ^ 40 * 8195077 * 2
def baseEnd_8195077 : Nat := 4208013501605938457249033

theorem tailTrace_8195077 : CollatzResearch.WordTrace tailWord_8195077 prefixEnd_8195077 4208013501605938457249033 := by
  unfold tailWord_8195077
  simp only [CollatzResearch.WordTrace]
  refine ⟨298899013731643111568247485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199266009154428741045498323 298899013731643111568247485)
  ·
    refine ⟨112087130149366166838092807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298899013731643111568247485 112087130149366166838092807)
    ·
      refine ⟨168130695224049250257139211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112087130149366166838092807 168130695224049250257139211)
      ·
        refine ⟨252196042836073875385708817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168130695224049250257139211 252196042836073875385708817)
        ·
          refine ⟨189147032127055406539281613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252196042836073875385708817 189147032127055406539281613)
          ·
            refine ⟨70930137047645777452230605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189147032127055406539281613 70930137047645777452230605)
            ·
              refine ⟨26598801392867166544586477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70930137047645777452230605 26598801392867166544586477)
              ·
                refine ⟨9974550522325187454219929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26598801392867166544586477 9974550522325187454219929)
                ·
                  refine ⟨7480912891743890590664947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9974550522325187454219929 7480912891743890590664947)
                  ·
                    refine ⟨11221369337615835885997421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7480912891743890590664947 11221369337615835885997421)
                    ·
                      refine ⟨4208013501605938457249033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11221369337615835885997421 4208013501605938457249033)
                      ·
                        rfl

theorem cell23_8195077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 3, 2, 1, 3].length) (baseStart_8195077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8195077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8195077 prefixEnd_8195077 := by exact prefixLift 8195077
  have htrace : WordTrace (prefixWord ++ tailWord_8195077) baseStart_8195077 baseEnd_8195077 := by
    simpa [prefixWord, tailWord_8195077, baseEnd_8195077] using wordTrace_append hprefix tailTrace_8195077
  have hstable : (prefixWord ++ tailWord_8195077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8195077).length < 2 ^ (prefixWord ++ tailWord_8195077).sum := by decide
  have hdescent : baseEnd_8195077 < baseStart_8195077 := by decide
  rcases family_descends (prefixWord ++ tailWord_8195077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8195111 : List Nat := [1, 1, 7, 1, 1, 2, 2, 2, 2, 1, 3]
def baseStart_8195111 : Nat := 118140960795 + 8195111 * 2 ^ 59
def prefixEnd_8195111 : Nat := 4983230072969 + 3 ^ 40 * 8195111 * 2
def baseEnd_8195111 : Nat := 4208030959948191324223877

theorem tailTrace_8195111 : CollatzResearch.WordTrace tailWord_8195111 prefixEnd_8195111 4208030959948191324223877 := by
  unfold tailWord_8195111
  simp only [CollatzResearch.WordTrace]
  refine ⟨298900253813519935374985187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199266835875679956916656791 298900253813519935374985187)
  ·
    refine ⟨448350380720279903062477781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298900253813519935374985187 448350380720279903062477781)
    ·
      refine ⟨10508212048131560228026823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 448350380720279903062477781 10508212048131560228026823)
      ·
        refine ⟨15762318072197340342040235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10508212048131560228026823 15762318072197340342040235)
        ·
          refine ⟨23643477108296010513060353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15762318072197340342040235 23643477108296010513060353)
          ·
            refine ⟨17732607831222007884795265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23643477108296010513060353 17732607831222007884795265)
            ·
              refine ⟨13299455873416505913596449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17732607831222007884795265 13299455873416505913596449)
              ·
                refine ⟨9974591905062379435197337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13299455873416505913596449 9974591905062379435197337)
                ·
                  refine ⟨7480943928796784576398003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9974591905062379435197337 7480943928796784576398003)
                  ·
                    refine ⟨11221415893195176864597005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7480943928796784576398003 11221415893195176864597005)
                    ·
                      refine ⟨4208030959948191324223877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11221415893195176864597005 4208030959948191324223877)
                      ·
                        rfl

theorem cell23_8195111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_8195111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8195111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8195111 prefixEnd_8195111 := by exact prefixLift 8195111
  have htrace : WordTrace (prefixWord ++ tailWord_8195111) baseStart_8195111 baseEnd_8195111 := by
    simpa [prefixWord, tailWord_8195111, baseEnd_8195111] using wordTrace_append hprefix tailTrace_8195111
  have hstable : (prefixWord ++ tailWord_8195111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8195111).length < 2 ^ (prefixWord ++ tailWord_8195111).sum := by decide
  have hdescent : baseEnd_8195111 < baseStart_8195111 := by decide
  rcases family_descends (prefixWord ++ tailWord_8195111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8195123 : List Nat := [1, 1, 1, 2, 4, 1, 1, 5, 7]
def baseStart_8195123 : Nat := 118140960795 + 8195123 * 2 ^ 59
def prefixEnd_8195123 : Nat := 4983230072969 + 3 ^ 40 * 8195123 * 2
def baseEnd_8195123 : Nat := 467559680190671697474869

theorem tailTrace_8195123 : CollatzResearch.WordTrace tailWord_8195123 prefixEnd_8195123 467559680190671697474869 := by
  unfold tailWord_8195123
  simp only [CollatzResearch.WordTrace]
  refine ⟨298900691489476461424422023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199267127659650974282948015 298900691489476461424422023)
  ·
    refine ⟨448351037234214692136633035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298900691489476461424422023 448351037234214692136633035)
    ·
      refine ⟨672526555851322038204949553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448351037234214692136633035 672526555851322038204949553)
      ·
        refine ⟨504394916888491528653712165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 672526555851322038204949553 504394916888491528653712165)
        ·
          refine ⟨94574046916592161622571031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 504394916888491528653712165 94574046916592161622571031)
          ·
            refine ⟨141861070374888242433856547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94574046916592161622571031 141861070374888242433856547)
            ·
              refine ⟨212791605562332363650784821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141861070374888242433856547 212791605562332363650784821)
              ·
                refine ⟨19949213021468659092261077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 212791605562332363650784821 19949213021468659092261077)
                ·
                  refine ⟨467559680190671697474869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19949213021468659092261077 467559680190671697474869)
                  ·
                    rfl

theorem cell23_8195123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 7].length) (baseStart_8195123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8195123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8195123 prefixEnd_8195123 := by exact prefixLift 8195123
  have htrace : WordTrace (prefixWord ++ tailWord_8195123) baseStart_8195123 baseEnd_8195123 := by
    simpa [prefixWord, tailWord_8195123, baseEnd_8195123] using wordTrace_append hprefix tailTrace_8195123
  have hstable : (prefixWord ++ tailWord_8195123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8195123).length < 2 ^ (prefixWord ++ tailWord_8195123).sum := by decide
  have hdescent : baseEnd_8195123 < baseStart_8195123 := by decide
  rcases family_descends (prefixWord ++ tailWord_8195123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8195134 : List Nat := [4, 2, 1, 3, 1, 1, 1, 3, 1, 4, 2]
def baseStart_8195134 : Nat := 118140960795 + 8195134 * 2 ^ 59
def prefixEnd_8195134 : Nat := 4983230072969 + 3 ^ 40 * 8195134 * 2
def baseEnd_8195134 : Nat := 4208042770003244734236271

theorem tailTrace_8195134 : CollatzResearch.WordTrace tailWord_8195134 prefixEnd_8195134 4208042770003244734236271 := by
  unfold tailWord_8195134
  simp only [CollatzResearch.WordTrace]
  refine ⟨37362636586554576287884057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199267395128291073535381637 37362636586554576287884057)
  ·
    refine ⟨28021977439915932215913043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37362636586554576287884057 28021977439915932215913043)
    ·
      refine ⟨42032966159873898323869565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28021977439915932215913043 42032966159873898323869565)
      ·
        refine ⟨15762362309952711871451087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42032966159873898323869565 15762362309952711871451087)
        ·
          refine ⟨23643543464929067807176631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15762362309952711871451087 23643543464929067807176631)
          ·
            refine ⟨35465315197393601710764947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23643543464929067807176631 35465315197393601710764947)
            ·
              refine ⟨53197972796090402566147421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35465315197393601710764947 53197972796090402566147421)
              ·
                refine ⟨19949239798533900962305283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53197972796090402566147421 19949239798533900962305283)
                ·
                  refine ⟨29923859697800851443457925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19949239798533900962305283 29923859697800851443457925)
                  ·
                    refine ⟨5610723693337659645648361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29923859697800851443457925 5610723693337659645648361)
                    ·
                      refine ⟨4208042770003244734236271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5610723693337659645648361 4208042770003244734236271)
                      ·
                        rfl

theorem cell23_8195134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_8195134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8195134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8195134 prefixEnd_8195134 := by exact prefixLift 8195134
  have htrace : WordTrace (prefixWord ++ tailWord_8195134) baseStart_8195134 baseEnd_8195134 := by
    simpa [prefixWord, tailWord_8195134, baseEnd_8195134] using wordTrace_append hprefix tailTrace_8195134
  have hstable : (prefixWord ++ tailWord_8195134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8195134).length < 2 ^ (prefixWord ++ tailWord_8195134).sum := by decide
  have hdescent : baseEnd_8195134 < baseStart_8195134 := by decide
  rcases family_descends (prefixWord ++ tailWord_8195134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8195150 : List Nat := [4, 1, 1, 1, 1, 3, 1, 2, 1, 5, 3]
def baseStart_8195150 : Nat := 118140960795 + 8195150 * 2 ^ 59
def prefixEnd_8195150 : Nat := 4983230072969 + 3 ^ 40 * 8195150 * 2
def baseEnd_8195150 : Nat := 4208050985693716671636197

theorem tailTrace_8195150 : CollatzResearch.WordTrace tailWord_8195150 prefixEnd_8195150 4208050985693716671636197 := by
  unfold tailWord_8195150
  simp only [CollatzResearch.WordTrace]
  refine ⟨37362709532547330629456863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199267784173585763357103269 37362709532547330629456863)
  ·
    refine ⟨56044064298820995944185295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37362709532547330629456863 56044064298820995944185295)
    ·
      refine ⟨84066096448231493916277943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56044064298820995944185295 84066096448231493916277943)
      ·
        refine ⟨126099144672347240874416915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84066096448231493916277943 126099144672347240874416915)
        ·
          refine ⟨189148717008520861311625373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126099144672347240874416915 189148717008520861311625373)
          ·
            refine ⟨70930768878195322991859515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189148717008520861311625373 70930768878195322991859515)
            ·
              refine ⟨106396153317292984487789273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70930768878195322991859515 106396153317292984487789273)
              ·
                refine ⟨79797114987969738365841955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106396153317292984487789273 79797114987969738365841955)
                ·
                  refine ⟨119695672481954607548762933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79797114987969738365841955 119695672481954607548762933)
                  ·
                    refine ⟨11221469295183244457696525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 119695672481954607548762933 11221469295183244457696525)
                    ·
                      refine ⟨4208050985693716671636197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11221469295183244457696525 4208050985693716671636197)
                      ·
                        rfl

theorem cell23_8195150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 1, 5, 3].length) (baseStart_8195150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8195150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8195150 prefixEnd_8195150 := by exact prefixLift 8195150
  have htrace : WordTrace (prefixWord ++ tailWord_8195150) baseStart_8195150 baseEnd_8195150 := by
    simpa [prefixWord, tailWord_8195150, baseEnd_8195150] using wordTrace_append hprefix tailTrace_8195150
  have hstable : (prefixWord ++ tailWord_8195150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8195150).length < 2 ^ (prefixWord ++ tailWord_8195150).sum := by decide
  have hdescent : baseEnd_8195150 < baseStart_8195150 := by decide
  rcases family_descends (prefixWord ++ tailWord_8195150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8195157 : List Nat := [1, 3, 2, 2, 1, 2, 4, 3, 5]
def baseStart_8195157 : Nat := 118140960795 + 8195157 * 2 ^ 59
def prefixEnd_8195157 : Nat := 4983230072969 + 3 ^ 40 * 8195157 * 2
def baseEnd_8195157 : Nat := 467561620006477571583185

theorem tailTrace_8195157 : CollatzResearch.WordTrace tailWord_8195157 prefixEnd_8195157 467561620006477571583185 := by
  unfold tailWord_8195157
  simp only [CollatzResearch.WordTrace]
  refine ⟨298901931571353285231159725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199267954380902190154106483 298901931571353285231159725)
  ·
    refine ⟨112088224339257481961684897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298901931571353285231159725 112088224339257481961684897)
    ·
      refine ⟨84066168254443111471263673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112088224339257481961684897 84066168254443111471263673)
      ·
        refine ⟨63049626190832333603447755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84066168254443111471263673 63049626190832333603447755)
        ·
          refine ⟨94574439286248500405171633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63049626190832333603447755 94574439286248500405171633)
          ·
            refine ⟨70930829464686375303878725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94574439286248500405171633 70930829464686375303878725)
            ·
              refine ⟨13299530524628695369477261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70930829464686375303878725 13299530524628695369477261)
              ·
                refine ⟨4987323946735760763553973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13299530524628695369477261 4987323946735760763553973)
                ·
                  refine ⟨467561620006477571583185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4987323946735760763553973 467561620006477571583185)
                  ·
                    rfl

theorem cell23_8195157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 3, 5].length) (baseStart_8195157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8195157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8195157 prefixEnd_8195157 := by exact prefixLift 8195157
  have htrace : WordTrace (prefixWord ++ tailWord_8195157) baseStart_8195157 baseEnd_8195157 := by
    simpa [prefixWord, tailWord_8195157, baseEnd_8195157] using wordTrace_append hprefix tailTrace_8195157
  have hstable : (prefixWord ++ tailWord_8195157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8195157).length < 2 ^ (prefixWord ++ tailWord_8195157).sum := by decide
  have hdescent : baseEnd_8195157 < baseStart_8195157 := by decide
  rcases family_descends (prefixWord ++ tailWord_8195157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8195247 : List Nat := [1, 1, 2, 1, 2, 3, 6, 1, 6]
def baseStart_8195247 : Nat := 118140960795 + 8195247 * 2 ^ 59
def prefixEnd_8195247 : Nat := 4983230072969 + 3 ^ 40 * 8195247 * 2
def baseEnd_8195247 : Nat := 467566754813022532458139

theorem tailTrace_8195247 : CollatzResearch.WordTrace tailWord_8195247 prefixEnd_8195247 467566754813022532458139 := by
  unfold tailWord_8195247
  simp only [CollatzResearch.WordTrace]
  refine ⟨298905214141027230601935995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199270142760684820401290663 298905214141027230601935995)
  ·
    refine ⟨448357821211540845902903993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298905214141027230601935995 448357821211540845902903993)
    ·
      refine ⟨336268365908655634427177995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 448357821211540845902903993 336268365908655634427177995)
      ·
        refine ⟨504402548862983451640766993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336268365908655634427177995 504402548862983451640766993)
        ·
          refine ⟨378301911647237588730575245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 504402548862983451640766993 378301911647237588730575245)
          ·
            refine ⟨141863216867714095773965717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 378301911647237588730575245 141863216867714095773965717)
            ·
              refine ⟨6649838290674098239404643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 141863216867714095773965717 6649838290674098239404643)
              ·
                refine ⟨9974757436011147359106965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6649838290674098239404643 9974757436011147359106965)
                ·
                  refine ⟨467566754813022532458139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9974757436011147359106965 467566754813022532458139)
                  ·
                    rfl

theorem cell23_8195247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 1, 6].length) (baseStart_8195247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8195247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8195247 prefixEnd_8195247 := by exact prefixLift 8195247
  have htrace : WordTrace (prefixWord ++ tailWord_8195247) baseStart_8195247 baseEnd_8195247 := by
    simpa [prefixWord, tailWord_8195247, baseEnd_8195247] using wordTrace_append hprefix tailTrace_8195247
  have hstable : (prefixWord ++ tailWord_8195247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8195247).length < 2 ^ (prefixWord ++ tailWord_8195247).sum := by decide
  have hdescent : baseEnd_8195247 < baseStart_8195247 := by decide
  rcases family_descends (prefixWord ++ tailWord_8195247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8195290 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 5, 6]
def baseStart_8195290 : Nat := 118140960795 + 8195290 * 2 ^ 59
def prefixEnd_8195290 : Nat := 4983230072969 + 3 ^ 40 * 8195290 * 2
def baseEnd_8195290 : Nat := 1402707624328448707961851

theorem tailTrace_8195290 : CollatzResearch.WordTrace tailWord_8195290 prefixEnd_8195290 1402707624328448707961851 := by
  unfold tailWord_8195290
  simp only [CollatzResearch.WordTrace]
  refine ⟨74726695619967862236437831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199271188319914299297167549 74726695619967862236437831)
  ·
    refine ⟨112090043429951793354656747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74726695619967862236437831 112090043429951793354656747)
    ·
      refine ⟨168135065144927690031985121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112090043429951793354656747 168135065144927690031985121)
      ·
        refine ⟨126101298858695767523988841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168135065144927690031985121 126101298858695767523988841)
        ·
          refine ⟨94575974144021825642991631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126101298858695767523988841 94575974144021825642991631)
          ·
            refine ⟨141863961216032738464487447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94575974144021825642991631 141863961216032738464487447)
            ·
              refine ⟨212795941824049107696731171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141863961216032738464487447 212795941824049107696731171)
              ·
                refine ⟨319193912736073661545096757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212795941824049107696731171 319193912736073661545096757)
                ·
                  refine ⟨29924429319006905769852821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 319193912736073661545096757 29924429319006905769852821)
                  ·
                    refine ⟨1402707624328448707961851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29924429319006905769852821 1402707624328448707961851)
                    ·
                      rfl

theorem cell23_8195290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 5, 6].length) (baseStart_8195290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8195290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8195290 prefixEnd_8195290 := by exact prefixLift 8195290
  have htrace : WordTrace (prefixWord ++ tailWord_8195290) baseStart_8195290 baseEnd_8195290 := by
    simpa [prefixWord, tailWord_8195290, baseEnd_8195290] using wordTrace_append hprefix tailTrace_8195290
  have hstable : (prefixWord ++ tailWord_8195290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8195290).length < 2 ^ (prefixWord ++ tailWord_8195290).sum := by decide
  have hdescent : baseEnd_8195290 < baseStart_8195290 := by decide
  rcases family_descends (prefixWord ++ tailWord_8195290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8195297 : List Nat := [1, 2, 3, 1, 3, 2, 1, 2, 3, 1, 4]
def baseStart_8195297 : Nat := 118140960795 + 8195297 * 2 ^ 59
def prefixEnd_8195297 : Nat := 4983230072969 + 3 ^ 40 * 8195297 * 2
def baseEnd_8195297 : Nat := 4208126467349927596498021

theorem tailTrace_8195297 : CollatzResearch.WordTrace tailWord_8195297 prefixEnd_8195297 4208126467349927596498021 := by
  unfold tailWord_8195297
  simp only [CollatzResearch.WordTrace]
  refine ⟨298907037790846089141256145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199271358527230726094170763 298907037790846089141256145)
  ·
    refine ⟨224180278343134566855942109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298907037790846089141256145 224180278343134566855942109)
    ·
      refine ⟨84067604378675462570978291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224180278343134566855942109 84067604378675462570978291)
      ·
        refine ⟨126101406568013193856467437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84067604378675462570978291 126101406568013193856467437)
        ·
          refine ⟨47288027463004947696175289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126101406568013193856467437 47288027463004947696175289)
          ·
            refine ⟨35466020597253710772131467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47288027463004947696175289 35466020597253710772131467)
            ·
              refine ⟨53199030895880566158197201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35466020597253710772131467 53199030895880566158197201)
              ·
                refine ⟨39899273171910424618647901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53199030895880566158197201 39899273171910424618647901)
                ·
                  refine ⟨14962227439466409231992963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39899273171910424618647901 14962227439466409231992963)
                  ·
                    refine ⟨22443341159199613847989445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14962227439466409231992963 22443341159199613847989445)
                    ·
                      refine ⟨4208126467349927596498021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22443341159199613847989445 4208126467349927596498021)
                      ·
                        rfl

theorem cell23_8195297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_8195297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8195297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8195297 prefixEnd_8195297 := by exact prefixLift 8195297
  have htrace : WordTrace (prefixWord ++ tailWord_8195297) baseStart_8195297 baseEnd_8195297 := by
    simpa [prefixWord, tailWord_8195297, baseEnd_8195297] using wordTrace_append hprefix tailTrace_8195297
  have hstable : (prefixWord ++ tailWord_8195297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8195297).length < 2 ^ (prefixWord ++ tailWord_8195297).sum := by decide
  have hdescent : baseEnd_8195297 < baseStart_8195297 := by decide
  rcases family_descends (prefixWord ++ tailWord_8195297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8195307 : List Nat := [1, 1, 1, 1, 2, 7, 2, 1, 1, 6]
def baseStart_8195307 : Nat := 118140960795 + 8195307 * 2 ^ 59
def prefixEnd_8195307 : Nat := 4983230072969 + 3 ^ 40 * 8195307 * 2
def baseEnd_8195307 : Nat := 1402710534052157519124325

theorem tailTrace_8195307 : CollatzResearch.WordTrace tailWord_8195307 prefixEnd_8195307 1402710534052157519124325 := by
  unfold tailWord_8195307
  simp only [CollatzResearch.WordTrace]
  refine ⟨298907402520809860849120175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199271601680539907232746783 298907402520809860849120175)
  ·
    refine ⟨448361103781214791273680263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298907402520809860849120175 448361103781214791273680263)
    ·
      refine ⟨672541655671822186910520395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448361103781214791273680263 672541655671822186910520395)
      ·
        refine ⟨1008812483507733280365780593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 672541655671822186910520395 1008812483507733280365780593)
        ·
          refine ⟨756609362630799960274335445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1008812483507733280365780593 756609362630799960274335445)
          ·
            refine ⟨17733031936659374068929737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 756609362630799960274335445 17733031936659374068929737)
            ·
              refine ⟨13299773952494530551697303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17733031936659374068929737 13299773952494530551697303)
              ·
                refine ⟨19949660928741795827545955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13299773952494530551697303 19949660928741795827545955)
                ·
                  refine ⟨29924491393112693741318933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19949660928741795827545955 29924491393112693741318933)
                  ·
                    refine ⟨1402710534052157519124325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29924491393112693741318933 1402710534052157519124325)
                    ·
                      rfl

theorem cell23_8195307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 6].length) (baseStart_8195307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8195307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8195307 prefixEnd_8195307 := by exact prefixLift 8195307
  have htrace : WordTrace (prefixWord ++ tailWord_8195307) baseStart_8195307 baseEnd_8195307 := by
    simpa [prefixWord, tailWord_8195307, baseEnd_8195307] using wordTrace_append hprefix tailTrace_8195307
  have hstable : (prefixWord ++ tailWord_8195307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8195307).length < 2 ^ (prefixWord ++ tailWord_8195307).sum := by decide
  have hdescent : baseEnd_8195307 < baseStart_8195307 := by decide
  rcases family_descends (prefixWord ++ tailWord_8195307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8195327 : List Nat := [1, 1, 2, 2, 1, 5, 2, 2, 1, 2, 4]
def baseStart_8195327 : Nat := 118140960795 + 8195327 * 2 ^ 59
def prefixEnd_8195327 : Nat := 4983230072969 + 3 ^ 40 * 8195327 * 2
def baseEnd_8195327 : Nat := 4208141871769562479122883

theorem tailTrace_8195327 : CollatzResearch.WordTrace tailWord_8195327 prefixEnd_8195327 4208141871769562479122883 := by
  unfold tailWord_8195327
  simp only [CollatzResearch.WordTrace]
  refine ⟨298908131980737404264848235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199272087987158269509898823 298908131980737404264848235)
  ·
    refine ⟨448362197971106106397272353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298908131980737404264848235 448362197971106106397272353)
    ·
      refine ⟨336271648478329579797954265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 448362197971106106397272353 336271648478329579797954265)
      ·
        refine ⟨252203736358747184848465699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336271648478329579797954265 252203736358747184848465699)
        ·
          refine ⟨378305604538120777272698549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252203736358747184848465699 378305604538120777272698549)
          ·
            refine ⟨35466150425448822869315489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 378305604538120777272698549 35466150425448822869315489)
            ·
              refine ⟨26599612819086617151986617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35466150425448822869315489 26599612819086617151986617)
              ·
                refine ⟨19949709614314962863989963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26599612819086617151986617 19949709614314962863989963)
                ·
                  refine ⟨29924564421472444295984945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19949709614314962863989963 29924564421472444295984945)
                  ·
                    refine ⟨22443423316104333221988709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29924564421472444295984945 22443423316104333221988709)
                    ·
                      refine ⟨4208141871769562479122883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22443423316104333221988709 4208141871769562479122883)
                      ·
                        rfl

theorem cell23_8195327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 2, 4].length) (baseStart_8195327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8195327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8195327 prefixEnd_8195327 := by exact prefixLift 8195327
  have htrace : WordTrace (prefixWord ++ tailWord_8195327) baseStart_8195327 baseEnd_8195327 := by
    simpa [prefixWord, tailWord_8195327, baseEnd_8195327] using wordTrace_append hprefix tailTrace_8195327
  have hstable : (prefixWord ++ tailWord_8195327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8195327).length < 2 ^ (prefixWord ++ tailWord_8195327).sum := by decide
  have hdescent : baseEnd_8195327 < baseStart_8195327 := by decide
  rcases family_descends (prefixWord ++ tailWord_8195327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8195331 : List Nat := [1, 1, 1, 3, 2, 6, 2, 1, 1, 1, 4]
def baseStart_8195331 : Nat := 118140960795 + 8195331 * 2 ^ 59
def prefixEnd_8195331 : Nat := 4983230072969 + 3 ^ 40 * 8195331 * 2
def baseEnd_8195331 : Nat := 4208143925692180463472865

theorem tailTrace_8195331 : CollatzResearch.WordTrace tailWord_8195331 prefixEnd_8195331 4208143925692180463472865 := by
  unfold tailWord_8195331
  simp only [CollatzResearch.WordTrace]
  refine ⟨298908277872722912947993847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199272185248481941965329231 298908277872722912947993847)
  ·
    refine ⟨448362416809084369421990771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298908277872722912947993847 448362416809084369421990771)
    ·
      refine ⟨672543625213626554132986157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448362416809084369421990771 672543625213626554132986157)
      ·
        refine ⟨252203859455109957799869809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 672543625213626554132986157 252203859455109957799869809)
        ·
          refine ⟨189152894591332468349902357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252203859455109957799869809 189152894591332468349902357)
          ·
            refine ⟨8866541933968709453901673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 189152894591332468349902357 8866541933968709453901673)
            ·
              refine ⟨6649906450476532090426255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8866541933968709453901673 6649906450476532090426255)
              ·
                refine ⟨9974859675714798135639383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6649906450476532090426255 9974859675714798135639383)
                ·
                  refine ⟨14962289513572197203459075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9974859675714798135639383 14962289513572197203459075)
                  ·
                    refine ⟨22443434270358295805188613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14962289513572197203459075 22443434270358295805188613)
                    ·
                      refine ⟨4208143925692180463472865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22443434270358295805188613 4208143925692180463472865)
                      ·
                        rfl

theorem cell23_8195331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 2, 1, 1, 1, 4].length) (baseStart_8195331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8195331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8195331 prefixEnd_8195331 := by exact prefixLift 8195331
  have htrace : WordTrace (prefixWord ++ tailWord_8195331) baseStart_8195331 baseEnd_8195331 := by
    simpa [prefixWord, tailWord_8195331, baseEnd_8195331] using wordTrace_append hprefix tailTrace_8195331
  have hstable : (prefixWord ++ tailWord_8195331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8195331).length < 2 ^ (prefixWord ++ tailWord_8195331).sum := by decide
  have hdescent : baseEnd_8195331 < baseStart_8195331 := by decide
  rcases family_descends (prefixWord ++ tailWord_8195331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8195358 : List Nat := [4, 3, 2, 1, 2, 2, 1, 1, 1, 6]
def baseStart_8195358 : Nat := 118140960795 + 8195358 * 2 ^ 59
def prefixEnd_8195358 : Nat := 4983230072969 + 3 ^ 40 * 8195358 * 2
def baseEnd_8195358 : Nat := 1402719263223283952611747

theorem tailTrace_8195358 : CollatzResearch.WordTrace tailWord_8195358 prefixEnd_8195358 1402719263223283952611747 := by
  unfold tailWord_8195358
  simp only [CollatzResearch.WordTrace]
  refine ⟨37363657830453137069903341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199272841762416731039484485 37363657830453137069903341)
  ·
    refine ⟨14011371686419926401213753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37363657830453137069903341 14011371686419926401213753)
    ·
      refine ⟨10508528764814944800910315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14011371686419926401213753 10508528764814944800910315)
      ·
        refine ⟨15762793147222417201365473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10508528764814944800910315 15762793147222417201365473)
        ·
          refine ⟨11822094860416812901024105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15762793147222417201365473 11822094860416812901024105)
          ·
            refine ⟨8866571145312609675768079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11822094860416812901024105 8866571145312609675768079)
            ·
              refine ⟨13299856717968914513652119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8866571145312609675768079 13299856717968914513652119)
              ·
                refine ⟨19949785076953371770478179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13299856717968914513652119 19949785076953371770478179)
                ·
                  refine ⟨29924677615430057655717269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19949785076953371770478179 29924677615430057655717269)
                  ·
                    refine ⟨1402719263223283952611747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29924677615430057655717269 1402719263223283952611747)
                    ·
                      rfl

theorem cell23_8195358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_8195358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8195358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8195358 prefixEnd_8195358 := by exact prefixLift 8195358
  have htrace : WordTrace (prefixWord ++ tailWord_8195358) baseStart_8195358 baseEnd_8195358 := by
    simpa [prefixWord, tailWord_8195358, baseEnd_8195358] using wordTrace_append hprefix tailTrace_8195358
  have hstable : (prefixWord ++ tailWord_8195358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8195358).length < 2 ^ (prefixWord ++ tailWord_8195358).sum := by decide
  have hdescent : baseEnd_8195358 < baseStart_8195358 := by decide
  rcases family_descends (prefixWord ++ tailWord_8195358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8195377 : List Nat := [1, 2, 2, 3, 3, 1, 1, 1, 2, 2, 5]
def baseStart_8195377 : Nat := 118140960795 + 8195377 * 2 ^ 59
def prefixEnd_8195377 : Nat := 4983230072969 + 3 ^ 40 * 8195377 * 2
def baseEnd_8195377 : Nat := 4208167545802287283497653

theorem tailTrace_8195377 : CollatzResearch.WordTrace tailWord_8195377 prefixEnd_8195377 4208167545802287283497653 := by
  unfold tailWord_8195377
  simp only [CollatzResearch.WordTrace]
  refine ⟨298909955630556262804168385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199273303753704175202778923 298909955630556262804168385)
  ·
    refine ⟨224182466722917197103126289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298909955630556262804168385 224182466722917197103126289)
    ·
      refine ⟨168136850042187897827344717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224182466722917197103126289 168136850042187897827344717)
      ·
        refine ⟨63051318765820461685254269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168136850042187897827344717 63051318765820461685254269)
        ·
          refine ⟨23644244537182673131970351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63051318765820461685254269 23644244537182673131970351)
          ·
            refine ⟨35466366805774009697955527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23644244537182673131970351 35466366805774009697955527)
            ·
              refine ⟨53199550208661014546933291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35466366805774009697955527 53199550208661014546933291)
              ·
                refine ⟨79799325312991521820399937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53199550208661014546933291 79799325312991521820399937)
                ·
                  refine ⟨59849493984743641365299953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79799325312991521820399937 59849493984743641365299953)
                  ·
                    refine ⟨44887120488557731023974965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59849493984743641365299953 44887120488557731023974965)
                    ·
                      refine ⟨4208167545802287283497653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44887120488557731023974965 4208167545802287283497653)
                      ·
                        rfl

theorem cell23_8195377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_8195377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8195377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8195377 prefixEnd_8195377 := by exact prefixLift 8195377
  have htrace : WordTrace (prefixWord ++ tailWord_8195377) baseStart_8195377 baseEnd_8195377 := by
    simpa [prefixWord, tailWord_8195377, baseEnd_8195377] using wordTrace_append hprefix tailTrace_8195377
  have hstable : (prefixWord ++ tailWord_8195377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8195377).length < 2 ^ (prefixWord ++ tailWord_8195377).sum := by decide
  have hdescent : baseEnd_8195377 < baseStart_8195377 := by decide
  rcases family_descends (prefixWord ++ tailWord_8195377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8195391 : List Nat := [1, 1, 2, 2, 4, 2, 2, 3, 1, 3, 2]
def baseStart_8195391 : Nat := 118140960795 + 8195391 * 2 ^ 59
def prefixEnd_8195391 : Nat := 4983230072969 + 3 ^ 40 * 8195391 * 2
def baseEnd_8195391 : Nat := 4208174734531450228722589

theorem tailTrace_8195391 : CollatzResearch.WordTrace tailWord_8195391 prefixEnd_8195391 4208174734531450228722589 := by
  unfold tailWord_8195391
  simp only [CollatzResearch.WordTrace]
  refine ⟨298910466252505543195178027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199273644168337028796785351 298910466252505543195178027)
  ·
    refine ⟨448365699378758314792767041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298910466252505543195178027 448365699378758314792767041)
    ·
      refine ⟨336274274534068736094575281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 448365699378758314792767041 336274274534068736094575281)
      ·
        refine ⟨252205705900551552070931461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336274274534068736094575281 252205705900551552070931461)
        ·
          refine ⟨47288569856353416013299649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 252205705900551552070931461 47288569856353416013299649)
          ·
            refine ⟨35466427392265062009974737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47288569856353416013299649 35466427392265062009974737)
            ·
              refine ⟨26599820544198796507481053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35466427392265062009974737 26599820544198796507481053)
              ·
                refine ⟨9974932704074548690305395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26599820544198796507481053 9974932704074548690305395)
                ·
                  refine ⟨14962399056111823035458093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9974932704074548690305395 14962399056111823035458093)
                  ·
                    refine ⟨5610899646041933638296785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14962399056111823035458093 5610899646041933638296785)
                    ·
                      refine ⟨4208174734531450228722589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5610899646041933638296785 4208174734531450228722589)
                      ·
                        rfl

theorem cell23_8195391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 3, 1, 3, 2].length) (baseStart_8195391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8195391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8195391 prefixEnd_8195391 := by exact prefixLift 8195391
  have htrace : WordTrace (prefixWord ++ tailWord_8195391) baseStart_8195391 baseEnd_8195391 := by
    simpa [prefixWord, tailWord_8195391, baseEnd_8195391] using wordTrace_append hprefix tailTrace_8195391
  have hstable : (prefixWord ++ tailWord_8195391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8195391).length < 2 ^ (prefixWord ++ tailWord_8195391).sum := by decide
  have hdescent : baseEnd_8195391 < baseStart_8195391 := by decide
  rcases family_descends (prefixWord ++ tailWord_8195391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8195417 : List Nat := [1, 2, 1, 2, 2, 2, 2, 3, 2, 2, 4]
def baseStart_8195417 : Nat := 118140960795 + 8195417 * 2 ^ 59
def prefixEnd_8195417 : Nat := 4983230072969 + 3 ^ 40 * 8195417 * 2
def baseEnd_8195417 : Nat := 4208188085028467126997469

theorem tailTrace_8195417 : CollatzResearch.WordTrace tailWord_8195417 prefixEnd_8195417 4208188085028467126997469 := by
  unfold tailWord_8195417
  simp only [CollatzResearch.WordTrace]
  refine ⟨298911414550411349635624505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199274276366940899757083003 298911414550411349635624505)
  ·
    refine ⟨224183560912808512226718379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298911414550411349635624505 224183560912808512226718379)
    ·
      refine ⟨336275341369212768340077569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224183560912808512226718379 336275341369212768340077569)
      ·
        refine ⟨252206506026909576255058177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336275341369212768340077569 252206506026909576255058177)
        ·
          refine ⟨189154879520182182191293633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252206506026909576255058177 189154879520182182191293633)
          ·
            refine ⟨141866159640136636643470225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189154879520182182191293633 141866159640136636643470225)
            ·
              refine ⟨106399619730102477482602669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141866159640136636643470225 106399619730102477482602669)
              ·
                refine ⟨39899857398788429055976001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106399619730102477482602669 39899857398788429055976001)
                ·
                  refine ⟨29924893049091321791982001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39899857398788429055976001 29924893049091321791982001)
                  ·
                    refine ⟨22443669786818491343986501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29924893049091321791982001 22443669786818491343986501)
                    ·
                      refine ⟨4208188085028467126997469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22443669786818491343986501 4208188085028467126997469)
                      ·
                        rfl

theorem cell23_8195417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 2, 4].length) (baseStart_8195417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8195417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8195417 prefixEnd_8195417 := by exact prefixLift 8195417
  have htrace : WordTrace (prefixWord ++ tailWord_8195417) baseStart_8195417 baseEnd_8195417 := by
    simpa [prefixWord, tailWord_8195417, baseEnd_8195417] using wordTrace_append hprefix tailTrace_8195417
  have hstable : (prefixWord ++ tailWord_8195417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8195417).length < 2 ^ (prefixWord ++ tailWord_8195417).sum := by decide
  have hdescent : baseEnd_8195417 < baseStart_8195417 := by decide
  rcases family_descends (prefixWord ++ tailWord_8195417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8195461 : List Nat := [1, 3, 1, 1, 3, 1, 6, 2, 5]
def baseStart_8195461 : Nat := 118140960795 + 8195461 * 2 ^ 59
def prefixEnd_8195461 : Nat := 4983230072969 + 3 ^ 40 * 8195461 * 2
def baseEnd_8195461 : Nat := 467578964241918328316363

theorem tailTrace_8195461 : CollatzResearch.WordTrace tailWord_8195461 prefixEnd_8195461 467578964241918328316363 := by
  unfold tailWord_8195461
  simp only [CollatzResearch.WordTrace]
  refine ⟨298913019362251945150226237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199275346241501296766817491 298913019362251945150226237)
  ·
    refine ⟨112092382260844479431334839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298913019362251945150226237 112092382260844479431334839)
    ·
      refine ⟨168138573391266719147002259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112092382260844479431334839 168138573391266719147002259)
      ·
        refine ⟨252207860086900078720503389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168138573391266719147002259 252207860086900078720503389)
        ·
          refine ⟨94577947532587529520188771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252207860086900078720503389 94577947532587529520188771)
          ·
            refine ⟨141866921298881294280283157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94577947532587529520188771 141866921298881294280283157)
            ·
              refine ⟨6650011935885060669388273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 141866921298881294280283157 6650011935885060669388273)
              ·
                refine ⟨4987508951913795502041205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6650011935885060669388273 4987508951913795502041205)
                ·
                  refine ⟨467578964241918328316363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4987508951913795502041205 467578964241918328316363)
                  ·
                    rfl

theorem cell23_8195461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 2, 5].length) (baseStart_8195461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8195461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8195461 prefixEnd_8195461 := by exact prefixLift 8195461
  have htrace : WordTrace (prefixWord ++ tailWord_8195461) baseStart_8195461 baseEnd_8195461 := by
    simpa [prefixWord, tailWord_8195461, baseEnd_8195461] using wordTrace_append hprefix tailTrace_8195461
  have hstable : (prefixWord ++ tailWord_8195461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8195461).length < 2 ^ (prefixWord ++ tailWord_8195461).sum := by decide
  have hdescent : baseEnd_8195461 < baseStart_8195461 := by decide
  rcases family_descends (prefixWord ++ tailWord_8195461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8195467 : List Nat := [1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 5]
def baseStart_8195467 : Nat := 118140960795 + 8195467 * 2 ^ 59
def prefixEnd_8195467 : Nat := 4983230072969 + 3 ^ 40 * 8195467 * 2
def baseEnd_8195467 : Nat := 4208213759061191931372239

theorem tailTrace_8195467 : CollatzResearch.WordTrace tailWord_8195467 prefixEnd_8195467 4208213759061191931372239 := by
  unfold tailWord_8195467
  simp only [CollatzResearch.WordTrace]
  refine ⟨298913238200230208174944655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199275492133486805449963103 298913238200230208174944655)
  ·
    refine ⟨448369857300345312262416983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298913238200230208174944655 448369857300345312262416983)
    ·
      refine ⟨672554785950517968393625475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448369857300345312262416983 672554785950517968393625475)
      ·
        refine ⟨1008832178925776952590438213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 672554785950517968393625475 1008832178925776952590438213)
        ·
          refine ⟨189156033548583178610707165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1008832178925776952590438213 189156033548583178610707165)
          ·
            refine ⟨70933512580718691979015187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189156033548583178610707165 70933512580718691979015187)
            ·
              refine ⟨106400268871078037968522781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70933512580718691979015187 106400268871078037968522781)
              ·
                refine ⟨39900100826654264238196043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106400268871078037968522781 39900100826654264238196043)
                ·
                  refine ⟨59850151239981396357294065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39900100826654264238196043 59850151239981396357294065)
                  ·
                    refine ⟨44887613429986047267970549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59850151239981396357294065 44887613429986047267970549)
                    ·
                      refine ⟨4208213759061191931372239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44887613429986047267970549 4208213759061191931372239)
                      ·
                        rfl

theorem cell23_8195467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 5].length) (baseStart_8195467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8195467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8195467 prefixEnd_8195467 := by exact prefixLift 8195467
  have htrace : WordTrace (prefixWord ++ tailWord_8195467) baseStart_8195467 baseEnd_8195467 := by
    simpa [prefixWord, tailWord_8195467, baseEnd_8195467] using wordTrace_append hprefix tailTrace_8195467
  have hstable : (prefixWord ++ tailWord_8195467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8195467).length < 2 ^ (prefixWord ++ tailWord_8195467).sum := by decide
  have hdescent : baseEnd_8195467 < baseStart_8195467 := by decide
  rcases family_descends (prefixWord ++ tailWord_8195467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8195507 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 1, 6, 4]
def baseStart_8195507 : Nat := 118140960795 + 8195507 * 2 ^ 59
def prefixEnd_8195507 : Nat := 4983230072969 + 3 ^ 40 * 8195507 * 2
def baseEnd_8195507 : Nat := 4208234298287371774872055

theorem tailTrace_8195507 : CollatzResearch.WordTrace tailWord_8195507 prefixEnd_8195507 4208234298287371774872055 := by
  unfold tailWord_8195507
  simp only [CollatzResearch.WordTrace]
  refine ⟨298914697120085295006400775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199276464746723530004267183 298914697120085295006400775)
  ·
    refine ⟨448372045680127942509601163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298914697120085295006400775 448372045680127942509601163)
    ·
      refine ⟨672558068520191913764401745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448372045680127942509601163 672558068520191913764401745)
      ·
        refine ⟨504418551390143935323301309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 672558068520191913764401745 504418551390143935323301309)
        ·
          refine ⟨189156956771303975746237991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 504418551390143935323301309 189156956771303975746237991)
          ·
            refine ⟨283735435156955963619356987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189156956771303975746237991 283735435156955963619356987)
            ·
              refine ⟨425603152735433945429035481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283735435156955963619356987 425603152735433945429035481)
              ·
                refine ⟨319202364551575459071776611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 425603152735433945429035481 319202364551575459071776611)
                ·
                  refine ⟨478803546827363188607664917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 319202364551575459071776611 478803546827363188607664917)
                  ·
                    refine ⟨22443916257532649465984293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 478803546827363188607664917 22443916257532649465984293)
                    ·
                      refine ⟨4208234298287371774872055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22443916257532649465984293 4208234298287371774872055)
                      ·
                        rfl

theorem cell23_8195507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 6, 4].length) (baseStart_8195507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8195507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8195507 prefixEnd_8195507 := by exact prefixLift 8195507
  have htrace : WordTrace (prefixWord ++ tailWord_8195507) baseStart_8195507 baseEnd_8195507 := by
    simpa [prefixWord, tailWord_8195507, baseEnd_8195507] using wordTrace_append hprefix tailTrace_8195507
  have hstable : (prefixWord ++ tailWord_8195507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8195507).length < 2 ^ (prefixWord ++ tailWord_8195507).sum := by decide
  have hdescent : baseEnd_8195507 < baseStart_8195507 := by decide
  rcases family_descends (prefixWord ++ tailWord_8195507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8195534 : List Nat := [4, 1, 1, 1, 2, 1, 2, 5, 6]
def baseStart_8195534 : Nat := 118140960795 + 8195534 * 2 ^ 59
def prefixEnd_8195534 : Nat := 4983230072969 + 3 ^ 40 * 8195534 * 2
def baseEnd_8195534 : Nat := 467583129140560352137159

theorem tailTrace_8195534 : CollatzResearch.WordTrace tailWord_8195534 prefixEnd_8195534 467583129140560352137159 := by
  unfold tailWord_8195534
  simp only [CollatzResearch.WordTrace]
  refine ⟨37364460236373434827204207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199277121260658319078422437 37364460236373434827204207)
  ·
    refine ⟨56046690354560152240806311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37364460236373434827204207 56046690354560152240806311)
    ·
      refine ⟨84070035531840228361209467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56046690354560152240806311 84070035531840228361209467)
      ·
        refine ⟨126105053297760342541814201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84070035531840228361209467 126105053297760342541814201)
        ·
          refine ⟨94578789973320256906360651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126105053297760342541814201 94578789973320256906360651)
          ·
            refine ⟨141868184959980385359540977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94578789973320256906360651 141868184959980385359540977)
            ·
              refine ⟨106401138719985289019655733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141868184959980385359540977 106401138719985289019655733)
              ·
                refine ⟨9975106754998620845592725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106401138719985289019655733 9975106754998620845592725)
                ·
                  refine ⟨467583129140560352137159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9975106754998620845592725 467583129140560352137159)
                  ·
                    rfl

theorem cell23_8195534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 5, 6].length) (baseStart_8195534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8195534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8195534 prefixEnd_8195534 := by exact prefixLift 8195534
  have htrace : WordTrace (prefixWord ++ tailWord_8195534) baseStart_8195534 baseEnd_8195534 := by
    simpa [prefixWord, tailWord_8195534, baseEnd_8195534] using wordTrace_append hprefix tailTrace_8195534
  have hstable : (prefixWord ++ tailWord_8195534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8195534).length < 2 ^ (prefixWord ++ tailWord_8195534).sum := by decide
  have hdescent : baseEnd_8195534 < baseStart_8195534 := by decide
  rcases family_descends (prefixWord ++ tailWord_8195534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8195555 : List Nat := [1, 1, 1, 6, 2, 3, 1, 3, 1, 4]
def baseStart_8195555 : Nat := 118140960795 + 8195555 * 2 ^ 59
def prefixEnd_8195555 : Nat := 4983230072969 + 3 ^ 40 * 8195555 * 2
def baseEnd_8195555 : Nat := 1402752981786262529023945

theorem tailTrace_8195555 : CollatzResearch.WordTrace tailWord_8195555 prefixEnd_8195555 1402752981786262529023945 := by
  unfold tailWord_8195555
  simp only [CollatzResearch.WordTrace]
  refine ⟨298916447823911399204148119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199277631882607599469432079 298916447823911399204148119)
  ·
    refine ⟨448374671735867098806222179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298916447823911399204148119 448374671735867098806222179)
    ·
      refine ⟨672562007603800648209333269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448374671735867098806222179 672562007603800648209333269)
      ·
        refine ⟨31526344106428155384812497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 672562007603800648209333269 31526344106428155384812497)
        ·
          refine ⟨23644758079821116538609373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31526344106428155384812497 23644758079821116538609373)
          ·
            refine ⟨8866784279932918701978515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23644758079821116538609373 8866784279932918701978515)
            ·
              refine ⟨13300176419899378052967773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8866784279932918701978515 13300176419899378052967773)
              ·
                refine ⟨4987566157462266769862915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13300176419899378052967773 4987566157462266769862915)
                ·
                  refine ⟨7481349236193400154794373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4987566157462266769862915 7481349236193400154794373)
                  ·
                    refine ⟨1402752981786262529023945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7481349236193400154794373 1402752981786262529023945)
                    ·
                      rfl

theorem cell23_8195555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 3, 1, 4].length) (baseStart_8195555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8195555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8195555 prefixEnd_8195555 := by exact prefixLift 8195555
  have htrace : WordTrace (prefixWord ++ tailWord_8195555) baseStart_8195555 baseEnd_8195555 := by
    simpa [prefixWord, tailWord_8195555, baseEnd_8195555] using wordTrace_append hprefix tailTrace_8195555
  have hstable : (prefixWord ++ tailWord_8195555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8195555).length < 2 ^ (prefixWord ++ tailWord_8195555).sum := by decide
  have hdescent : baseEnd_8195555 < baseStart_8195555 := by decide
  rcases family_descends (prefixWord ++ tailWord_8195555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8195585 : List Nat := [1, 2, 4, 1, 5, 1, 2, 1, 6]
def baseStart_8195585 : Nat := 118140960795 + 8195585 * 2 ^ 59
def prefixEnd_8195585 : Nat := 4983230072969 + 3 ^ 40 * 8195585 * 2
def baseEnd_8195585 : Nat := 467586038864269163299633

theorem tailTrace_8195585 : CollatzResearch.WordTrace tailWord_8195585 prefixEnd_8195585 467586038864269163299633 := by
  unfold tailWord_8195585
  simp only [CollatzResearch.WordTrace]
  refine ⟨298917542013802714327740209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199278361342535142885160139 298917542013802714327740209)
  ·
    refine ⟨224188156510352035745805157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298917542013802714327740209 224188156510352035745805157)
    ·
      refine ⟨42035279345691006702338467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224188156510352035745805157 42035279345691006702338467)
      ·
        refine ⟨63052919018536510053507701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42035279345691006702338467 63052919018536510053507701)
        ·
          refine ⟨5911211157987797817516347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63052919018536510053507701 5911211157987797817516347)
          ·
            refine ⟨8866816736981696726274521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5911211157987797817516347 8866816736981696726274521)
            ·
              refine ⟨6650112552736272544705891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8866816736981696726274521 6650112552736272544705891)
              ·
                refine ⟨9975168829104408817058837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6650112552736272544705891 9975168829104408817058837)
                ·
                  refine ⟨467586038864269163299633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9975168829104408817058837 467586038864269163299633)
                  ·
                    rfl

theorem cell23_8195585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 1, 6].length) (baseStart_8195585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8195585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8195585 prefixEnd_8195585 := by exact prefixLift 8195585
  have htrace : WordTrace (prefixWord ++ tailWord_8195585) baseStart_8195585 baseEnd_8195585 := by
    simpa [prefixWord, tailWord_8195585, baseEnd_8195585] using wordTrace_append hprefix tailTrace_8195585
  have hstable : (prefixWord ++ tailWord_8195585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8195585).length < 2 ^ (prefixWord ++ tailWord_8195585).sum := by decide
  have hdescent : baseEnd_8195585 < baseStart_8195585 := by decide
  rcases family_descends (prefixWord ++ tailWord_8195585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8195624 : List Nat := [2, 1, 5, 2, 13]
def baseStart_8195624 : Nat := 118140960795 + 8195624 * 2 ^ 59
def prefixEnd_8195624 : Nat := 4983230072969 + 3 ^ 40 * 8195624 * 2
def baseEnd_8195624 : Nat := 5772694616630929790273

theorem tailTrace_8195624 : CollatzResearch.WordTrace tailWord_8195624 prefixEnd_8195624 5772694616630929790273 := by
  unfold tailWord_8195624
  simp only [CollatzResearch.WordTrace]
  refine ⟨149459482230330711994204963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199279309640440949325606617 149459482230330711994204963)
  ·
    refine ⟨224189223345496067991307445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149459482230330711994204963 224189223345496067991307445)
    ·
      refine ⟨21017739688640256374185073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 224189223345496067991307445 21017739688640256374185073)
      ·
        refine ⟨15763304766480192280638805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21017739688640256374185073 15763304766480192280638805)
        ·
          refine ⟨5772694616630929790273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 15763304766480192280638805 5772694616630929790273)
          ·
            rfl

theorem cell23_8195624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 13].length) (baseStart_8195624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8195624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8195624 prefixEnd_8195624 := by exact prefixLift 8195624
  have htrace : WordTrace (prefixWord ++ tailWord_8195624) baseStart_8195624 baseEnd_8195624 := by
    simpa [prefixWord, tailWord_8195624, baseEnd_8195624] using wordTrace_append hprefix tailTrace_8195624
  have hstable : (prefixWord ++ tailWord_8195624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8195624).length < 2 ^ (prefixWord ++ tailWord_8195624).sum := by decide
  have hdescent : baseEnd_8195624 < baseStart_8195624 := by decide
  rcases family_descends (prefixWord ++ tailWord_8195624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8195641 : List Nat := [1, 2, 1, 5, 1, 4, 1, 8]
def baseStart_8195641 : Nat := 118140960795 + 8195641 * 2 ^ 59
def prefixEnd_8195641 : Nat := 4983230072969 + 3 ^ 40 * 8195641 * 2
def baseEnd_8195641 : Nat := 155863077951669416688757

theorem tailTrace_8195641 : CollatzResearch.WordTrace tailWord_8195641 prefixEnd_8195641 155863077951669416688757 := by
  unfold tailWord_8195641
  simp only [CollatzResearch.WordTrace]
  refine ⟨298919584501599835891778777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199279723001066557261185851 298919584501599835891778777)
  ·
    refine ⟨224189688376199876918834083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298919584501599835891778777 224189688376199876918834083)
    ·
      refine ⟨336284532564299815378251125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224189688376199876918834083 336284532564299815378251125)
      ·
        refine ⟨31526674927903107691711043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 336284532564299815378251125 31526674927903107691711043)
        ·
          refine ⟨47290012391854661537566565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31526674927903107691711043 47290012391854661537566565)
          ·
            refine ⟨8866877323472749038293731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47290012391854661537566565 8866877323472749038293731)
            ·
              refine ⟨13300315985209123557440597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8866877323472749038293731 13300315985209123557440597)
              ·
                refine ⟨155863077951669416688757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13300315985209123557440597 155863077951669416688757)
                ·
                  rfl

theorem cell23_8195641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 8].length) (baseStart_8195641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8195641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8195641 prefixEnd_8195641 := by exact prefixLift 8195641
  have htrace : WordTrace (prefixWord ++ tailWord_8195641) baseStart_8195641 baseEnd_8195641 := by
    simpa [prefixWord, tailWord_8195641, baseEnd_8195641] using wordTrace_append hprefix tailTrace_8195641
  have hstable : (prefixWord ++ tailWord_8195641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8195641).length < 2 ^ (prefixWord ++ tailWord_8195641).sum := by decide
  have hdescent : baseEnd_8195641 < baseStart_8195641 := by decide
  rcases family_descends (prefixWord ++ tailWord_8195641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8195651 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 8, 1, 3]
def baseStart_8195651 : Nat := 118140960795 + 8195651 * 2 ^ 59
def prefixEnd_8195651 : Nat := 4983230072969 + 3 ^ 40 * 8195651 * 2
def baseEnd_8195651 : Nat := 4208308239501619211471393

theorem tailTrace_8195651 : CollatzResearch.WordTrace tailWord_8195651 prefixEnd_8195651 4208308239501619211471393 := by
  unfold tailWord_8195651
  simp only [CollatzResearch.WordTrace]
  refine ⟨298919949231563607599642807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199279966154375738399761871 298919949231563607599642807)
  ·
    refine ⟨448379923847345411399464211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298919949231563607599642807 448379923847345411399464211)
    ·
      refine ⟨672569885771018117099196317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448379923847345411399464211 672569885771018117099196317)
      ·
        refine ⟨252213707164131793912198619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 672569885771018117099196317 252213707164131793912198619)
        ·
          refine ⟨378320560746197690868297929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252213707164131793912198619 378320560746197690868297929)
          ·
            refine ⟨283740420559648268151223447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 378320560746197690868297929 283740420559648268151223447)
            ·
              refine ⟨425610630839472402226835171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283740420559648268151223447 425610630839472402226835171)
              ·
                refine ⟨638415946259208603340252757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 425610630839472402226835171 638415946259208603340252757)
                ·
                  refine ⟨7481436870225100820393587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 638415946259208603340252757 7481436870225100820393587)
                  ·
                    refine ⟨11222155305337651230590381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7481436870225100820393587 11222155305337651230590381)
                    ·
                      refine ⟨4208308239501619211471393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11222155305337651230590381 4208308239501619211471393)
                      ·
                        rfl

theorem cell23_8195651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 8, 1, 3].length) (baseStart_8195651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8195651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8195651 prefixEnd_8195651 := by exact prefixLift 8195651
  have htrace : WordTrace (prefixWord ++ tailWord_8195651) baseStart_8195651 baseEnd_8195651 := by
    simpa [prefixWord, tailWord_8195651, baseEnd_8195651] using wordTrace_append hprefix tailTrace_8195651
  have hstable : (prefixWord ++ tailWord_8195651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8195651).length < 2 ^ (prefixWord ++ tailWord_8195651).sum := by decide
  have hdescent : baseEnd_8195651 < baseStart_8195651 := by decide
  rcases family_descends (prefixWord ++ tailWord_8195651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8195664 : List Nat := [2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 5]
def baseStart_8195664 : Nat := 118140960795 + 8195664 * 2 ^ 59
def prefixEnd_8195664 : Nat := 4983230072969 + 3 ^ 40 * 8195664 * 2
def baseEnd_8195664 : Nat := 4208314914750127660608833

theorem tailTrace_8195664 : CollatzResearch.WordTrace tailWord_8195664 prefixEnd_8195664 4208314914750127660608833 := by
  unfold tailWord_8195664
  simp only [CollatzResearch.WordTrace]
  refine ⟨149460211690258255409933023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199280282253677673879910697 149460211690258255409933023)
  ·
    refine ⟨224190317535387383114899535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149460211690258255409933023 224190317535387383114899535)
    ·
      refine ⟨336285476303081074672349303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224190317535387383114899535 336285476303081074672349303)
      ·
        refine ⟨504428214454621612008523955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336285476303081074672349303 504428214454621612008523955)
        ·
          refine ⟨756642321681932418012785933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504428214454621612008523955 756642321681932418012785933)
          ·
            refine ⟨283740870630724656754794725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 756642321681932418012785933 283740870630724656754794725)
            ·
              refine ⟨53201413243260873141524011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 283740870630724656754794725 53201413243260873141524011)
              ·
                refine ⟨79802119864891309712286017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53201413243260873141524011 79802119864891309712286017)
                ·
                  refine ⟨59851589898668482284214513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79802119864891309712286017 59851589898668482284214513)
                  ·
                    refine ⟨44888692424001361713160885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59851589898668482284214513 44888692424001361713160885)
                    ·
                      refine ⟨4208314914750127660608833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44888692424001361713160885 4208314914750127660608833)
                      ·
                        rfl

theorem cell23_8195664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 5].length) (baseStart_8195664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8195664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8195664 prefixEnd_8195664 := by exact prefixLift 8195664
  have htrace : WordTrace (prefixWord ++ tailWord_8195664) baseStart_8195664 baseEnd_8195664 := by
    simpa [prefixWord, tailWord_8195664, baseEnd_8195664] using wordTrace_append hprefix tailTrace_8195664
  have hstable : (prefixWord ++ tailWord_8195664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8195664).length < 2 ^ (prefixWord ++ tailWord_8195664).sum := by decide
  have hdescent : baseEnd_8195664 < baseStart_8195664 := by decide
  rcases family_descends (prefixWord ++ tailWord_8195664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8195668 : List Nat := [2, 4, 1, 1, 1, 2, 2, 2, 4, 1, 3]
def baseStart_8195668 : Nat := 118140960795 + 8195668 * 2 ^ 59
def prefixEnd_8195668 : Nat := 4983230072969 + 3 ^ 40 * 8195668 * 2
def baseEnd_8195668 : Nat := 4208316968672745644958815

theorem tailTrace_8195668 : CollatzResearch.WordTrace tailWord_8195668 prefixEnd_8195668 4208316968672745644958815 := by
  unfold tailWord_8195668
  simp only [CollatzResearch.WordTrace]
  refine ⟨149460284636251009751505829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199280379515001346335341105 149460284636251009751505829)
  ·
    refine ⟨28023803369297064328407343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149460284636251009751505829 28023803369297064328407343)
    ·
      refine ⟨42035705053945596492611015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28023803369297064328407343 42035705053945596492611015)
      ·
        refine ⟨63053557580918394738916523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42035705053945596492611015 63053557580918394738916523)
        ·
          refine ⟨94580336371377592108374785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63053557580918394738916523 94580336371377592108374785)
          ·
            refine ⟨70935252278533194081281089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94580336371377592108374785 70935252278533194081281089)
            ·
              refine ⟨53201439208899895560960817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70935252278533194081281089 53201439208899895560960817)
              ·
                refine ⟨39901079406674921670720613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53201439208899895560960817 39901079406674921670720613)
                ·
                  refine ⟨7481452388751547813260115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39901079406674921670720613 7481452388751547813260115)
                  ·
                    refine ⟨11222178583127321719890173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7481452388751547813260115 11222178583127321719890173)
                    ·
                      refine ⟨4208316968672745644958815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11222178583127321719890173 4208316968672745644958815)
                      ·
                        rfl

theorem cell23_8195668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_8195668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8195668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8195668 prefixEnd_8195668 := by exact prefixLift 8195668
  have htrace : WordTrace (prefixWord ++ tailWord_8195668) baseStart_8195668 baseEnd_8195668 := by
    simpa [prefixWord, tailWord_8195668, baseEnd_8195668] using wordTrace_append hprefix tailTrace_8195668
  have hstable : (prefixWord ++ tailWord_8195668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8195668).length < 2 ^ (prefixWord ++ tailWord_8195668).sum := by decide
  have hdescent : baseEnd_8195668 < baseStart_8195668 := by decide
  rcases family_descends (prefixWord ++ tailWord_8195668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8195685 : List Nat := [1, 3, 1, 3, 3, 1, 3, 2, 2, 1, 3]
def baseStart_8195685 : Nat := 118140960795 + 8195685 * 2 ^ 59
def prefixEnd_8195685 : Nat := 4983230072969 + 3 ^ 40 * 8195685 * 2
def baseEnd_8195685 : Nat := 4208325697843872078446237

theorem tailTrace_8195685 : CollatzResearch.WordTrace tailWord_8195685 prefixEnd_8195685 4208325697843872078446237 := by
  unfold tailWord_8195685
  simp only [CollatzResearch.WordTrace]
  refine ⟨298921189313440431406380509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199280792875626954270920339 298921189313440431406380509)
  ·
    refine ⟨112095445992540161777392691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298921189313440431406380509 112095445992540161777392691)
    ·
      refine ⟨168143168988810242666089037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112095445992540161777392691 168143168988810242666089037)
      ·
        refine ⟨63053688370803840999783389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168143168988810242666089037 63053688370803840999783389)
        ·
          refine ⟨23645133139051440374918771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63053688370803840999783389 23645133139051440374918771)
          ·
            refine ⟨35467699708577160562378157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23645133139051440374918771 35467699708577160562378157)
            ·
              refine ⟨13300387390716435210891809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35467699708577160562378157 13300387390716435210891809)
              ·
                refine ⟨9975290543037326408168857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13300387390716435210891809 9975290543037326408168857)
                ·
                  refine ⟨7481467907277994806126643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9975290543037326408168857 7481467907277994806126643)
                  ·
                    refine ⟨11222201860916992209189965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7481467907277994806126643 11222201860916992209189965)
                    ·
                      refine ⟨4208325697843872078446237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11222201860916992209189965 4208325697843872078446237)
                      ·
                        rfl

theorem cell23_8195685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_8195685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8195685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8195685 prefixEnd_8195685 := by exact prefixLift 8195685
  have htrace : WordTrace (prefixWord ++ tailWord_8195685) baseStart_8195685 baseEnd_8195685 := by
    simpa [prefixWord, tailWord_8195685, baseEnd_8195685] using wordTrace_append hprefix tailTrace_8195685
  have hstable : (prefixWord ++ tailWord_8195685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8195685).length < 2 ^ (prefixWord ++ tailWord_8195685).sum := by decide
  have hdescent : baseEnd_8195685 < baseStart_8195685 := by decide
  rcases family_descends (prefixWord ++ tailWord_8195685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8195742 : List Nat := [4, 3, 1, 1, 1, 2, 2, 1, 4, 2, 2]
def baseStart_8195742 : Nat := 118140960795 + 8195742 * 2 ^ 59
def prefixEnd_8195742 : Nat := 4983230072969 + 3 ^ 40 * 8195742 * 2
def baseEnd_8195742 : Nat := 4208354966241178355433475

theorem tailTrace_8195742 : CollatzResearch.WordTrace tailWord_8195742 prefixEnd_8195742 4208354966241178355433475 := by
  unfold tailWord_8195742
  simp only [CollatzResearch.WordTrace]
  refine ⟨37365408534279241267650685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199282178849489286760803653 37365408534279241267650685)
  ·
    refine ⟨14012028200354715475369007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37365408534279241267650685 14012028200354715475369007)
    ·
      refine ⟨21018042300532073213053511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14012028200354715475369007 21018042300532073213053511)
      ·
        refine ⟨31527063450798109819580267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21018042300532073213053511 31527063450798109819580267)
        ·
          refine ⟨47290595176197164729370401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31527063450798109819580267 47290595176197164729370401)
          ·
            refine ⟨35467946382147873547027801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47290595176197164729370401 35467946382147873547027801)
            ·
              refine ⟨26600959786610905160270851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35467946382147873547027801 26600959786610905160270851)
              ·
                refine ⟨39901439679916357740406277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26600959786610905160270851 39901439679916357740406277)
                ·
                  refine ⟨7481519939984317076326177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39901439679916357740406277 7481519939984317076326177)
                  ·
                    refine ⟨5611139954988237807244633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7481519939984317076326177 5611139954988237807244633)
                    ·
                      refine ⟨4208354966241178355433475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5611139954988237807244633 4208354966241178355433475)
                      ·
                        rfl

theorem cell23_8195742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_8195742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8195742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8195742 prefixEnd_8195742 := by exact prefixLift 8195742
  have htrace : WordTrace (prefixWord ++ tailWord_8195742) baseStart_8195742 baseEnd_8195742 := by
    simpa [prefixWord, tailWord_8195742, baseEnd_8195742] using wordTrace_append hprefix tailTrace_8195742
  have hstable : (prefixWord ++ tailWord_8195742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8195742).length < 2 ^ (prefixWord ++ tailWord_8195742).sum := by decide
  have hdescent : baseEnd_8195742 < baseStart_8195742 := by decide
  rcases family_descends (prefixWord ++ tailWord_8195742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8195748 : List Nat := [2, 3, 1, 2, 2, 4, 1, 1, 7]
def baseStart_8195748 : Nat := 118140960795 + 8195748 * 2 ^ 59
def prefixEnd_8195748 : Nat := 4983230072969 + 3 ^ 40 * 8195748 * 2
def baseEnd_8195748 : Nat := 467595338569456147995383

theorem tailTrace_8195748 : CollatzResearch.WordTrace tailWord_8195748 prefixEnd_8195748 467595338569456147995383 := by
  unfold tailWord_8195748
  simp only [CollatzResearch.WordTrace]
  refine ⟨149461743556106096582961949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199282324741474795443949265 149461743556106096582961949)
  ·
    refine ⟨56048153833539786218610731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149461743556106096582961949 56048153833539786218610731)
    ·
      refine ⟨84072230750309679327916097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56048153833539786218610731 84072230750309679327916097)
      ·
        refine ⟨63054173062732259495937073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84072230750309679327916097 63054173062732259495937073)
        ·
          refine ⟨47290629797049194621952805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63054173062732259495937073 47290629797049194621952805)
          ·
            refine ⟨8866993086946723991616151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47290629797049194621952805 8866993086946723991616151)
            ·
              refine ⟨13300489630420085987424227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8866993086946723991616151 13300489630420085987424227)
              ·
                refine ⟨19950734445630128981136341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13300489630420085987424227 19950734445630128981136341)
                ·
                  refine ⟨467595338569456147995383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19950734445630128981136341 467595338569456147995383)
                  ·
                    rfl

theorem cell23_8195748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 7].length) (baseStart_8195748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8195748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8195748 prefixEnd_8195748 := by exact prefixLift 8195748
  have htrace : WordTrace (prefixWord ++ tailWord_8195748) baseStart_8195748 baseEnd_8195748 := by
    simpa [prefixWord, tailWord_8195748, baseEnd_8195748] using wordTrace_append hprefix tailTrace_8195748
  have hstable : (prefixWord ++ tailWord_8195748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8195748).length < 2 ^ (prefixWord ++ tailWord_8195748).sum := by decide
  have hdescent : baseEnd_8195748 < baseStart_8195748 := by decide
  rcases family_descends (prefixWord ++ tailWord_8195748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8195781 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 6, 1, 4]
def baseStart_8195781 : Nat := 118140960795 + 8195781 * 2 ^ 59
def prefixEnd_8195781 : Nat := 4983230072969 + 3 ^ 40 * 8195781 * 2
def baseEnd_8195781 : Nat := 4208374991986703702845795

theorem tailTrace_8195781 : CollatzResearch.WordTrace tailWord_8195781 prefixEnd_8195781 4208374991986703702845795 := by
  unfold tailWord_8195781
  simp only [CollatzResearch.WordTrace]
  refine ⟨298924690721092639801875197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199283127147395093201250131 298924690721092639801875197)
  ·
    refine ⟨112096759020409739925703199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298924690721092639801875197 112096759020409739925703199)
    ·
      refine ⟨168145138530614609888554799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112096759020409739925703199 168145138530614609888554799)
      ·
        refine ⟨252217707795921914832832199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168145138530614609888554799 252217707795921914832832199)
        ·
          refine ⟨378326561693882872249248299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252217707795921914832832199 378326561693882872249248299)
          ·
            refine ⟨567489842540824308373872449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378326561693882872249248299 567489842540824308373872449)
            ·
              refine ⟨425617381905618231280404337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 567489842540824308373872449 425617381905618231280404337)
              ·
                refine ⟨319213036429213673460303253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 425617381905618231280404337 319213036429213673460303253)
                ·
                  refine ⟨14963111082619390943451715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 319213036429213673460303253 14963111082619390943451715)
                  ·
                    refine ⟨22444666623929086415177573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14963111082619390943451715 22444666623929086415177573)
                    ·
                      refine ⟨4208374991986703702845795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22444666623929086415177573 4208374991986703702845795)
                      ·
                        rfl

theorem cell23_8195781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 6, 1, 4].length) (baseStart_8195781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8195781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8195781 prefixEnd_8195781 := by exact prefixLift 8195781
  have htrace : WordTrace (prefixWord ++ tailWord_8195781) baseStart_8195781 baseEnd_8195781 := by
    simpa [prefixWord, tailWord_8195781, baseEnd_8195781] using wordTrace_append hprefix tailTrace_8195781
  have hstable : (prefixWord ++ tailWord_8195781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8195781).length < 2 ^ (prefixWord ++ tailWord_8195781).sum := by decide
  have hdescent : baseEnd_8195781 < baseStart_8195781 := by decide
  rcases family_descends (prefixWord ++ tailWord_8195781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8195818 : List Nat := [3, 1, 3, 1, 1, 1, 2, 2, 4, 2, 3]
def baseStart_8195818 : Nat := 118140960795 + 8195818 * 2 ^ 59
def prefixEnd_8195818 : Nat := 4983230072969 + 3 ^ 40 * 8195818 * 2
def baseEnd_8195818 : Nat := 4208393990770920058083125

theorem tailTrace_8195818 : CollatzResearch.WordTrace tailWord_8195818 prefixEnd_8195818 4208393990770920058083125 := by
  unfold tailWord_8195818
  simp only [CollatzResearch.WordTrace]
  refine ⟨74731510055489648780243027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199284026814639063413981405 74731510055489648780243027)
  ·
    refine ⟨112097265083234473170364541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74731510055489648780243027 112097265083234473170364541)
    ·
      refine ⟨42036474406212927438886703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112097265083234473170364541 42036474406212927438886703)
      ·
        refine ⟨63054711609319391158330055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42036474406212927438886703 63054711609319391158330055)
        ·
          refine ⟨94582067413979086737495083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63054711609319391158330055 94582067413979086737495083)
          ·
            refine ⟨141873101120968630106242625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94582067413979086737495083 141873101120968630106242625)
            ·
              refine ⟨106404825840726472579681969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141873101120968630106242625 106404825840726472579681969)
              ·
                refine ⟨79803619380544854434761477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106404825840726472579681969 79803619380544854434761477)
                ·
                  refine ⟨14963178633852160206517777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79803619380544854434761477 14963178633852160206517777)
                  ·
                    refine ⟨11222383975389120154888333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14963178633852160206517777 11222383975389120154888333)
                    ·
                      refine ⟨4208393990770920058083125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11222383975389120154888333 4208393990770920058083125)
                      ·
                        rfl

theorem cell23_8195818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_8195818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8195818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8195818 prefixEnd_8195818 := by exact prefixLift 8195818
  have htrace : WordTrace (prefixWord ++ tailWord_8195818) baseStart_8195818 baseEnd_8195818 := by
    simpa [prefixWord, tailWord_8195818, baseEnd_8195818] using wordTrace_append hprefix tailTrace_8195818
  have hstable : (prefixWord ++ tailWord_8195818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8195818).length < 2 ^ (prefixWord ++ tailWord_8195818).sum := by decide
  have hdescent : baseEnd_8195818 < baseStart_8195818 := by decide
  rcases family_descends (prefixWord ++ tailWord_8195818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8195892 : List Nat := [2, 5, 1, 1, 2, 1, 2, 1, 1, 5, 2]
def baseStart_8195892 : Nat := 118140960795 + 8195892 * 2 ^ 59
def prefixEnd_8195892 : Nat := 4983230072969 + 3 ^ 40 * 8195892 * 2
def baseEnd_8195892 : Nat := 4208431988339352768557785

theorem tailTrace_8195892 : CollatzResearch.WordTrace tailWord_8195892 prefixEnd_8195892 4208431988339352768557785 := by
  unfold tailWord_8195892
  simp only [CollatzResearch.WordTrace]
  refine ⟨149464369611845252879582965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199285826149127003839443953 149464369611845252879582965)
  ·
    refine ⟨14012284651110492457460903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149464369611845252879582965 14012284651110492457460903)
    ·
      refine ⟨21018426976665738686191355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14012284651110492457460903 21018426976665738686191355)
      ·
        refine ⟨31527640464998608029287033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21018426976665738686191355 31527640464998608029287033)
        ·
          refine ⟨23645730348748956021965275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31527640464998608029287033 23645730348748956021965275)
          ·
            refine ⟨35468595523123434032947913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23645730348748956021965275 35468595523123434032947913)
            ·
              refine ⟨26601446642342575524710935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35468595523123434032947913 26601446642342575524710935)
              ·
                refine ⟨39902169963513863287066403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26601446642342575524710935 39902169963513863287066403)
                ·
                  refine ⟨59853254945270794930599605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39902169963513863287066403 59853254945270794930599605)
                  ·
                    refine ⟨5611242651119137024743713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59853254945270794930599605 5611242651119137024743713)
                    ·
                      refine ⟨4208431988339352768557785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5611242651119137024743713 4208431988339352768557785)
                      ·
                        rfl

theorem cell23_8195892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_8195892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8195892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8195892 prefixEnd_8195892 := by exact prefixLift 8195892
  have htrace : WordTrace (prefixWord ++ tailWord_8195892) baseStart_8195892 baseEnd_8195892 := by
    simpa [prefixWord, tailWord_8195892, baseEnd_8195892] using wordTrace_append hprefix tailTrace_8195892
  have hstable : (prefixWord ++ tailWord_8195892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8195892).length < 2 ^ (prefixWord ++ tailWord_8195892).sum := by decide
  have hdescent : baseEnd_8195892 < baseStart_8195892 := by decide
  rcases family_descends (prefixWord ++ tailWord_8195892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8195911 : List Nat := [1, 1, 4, 1, 2, 1, 13]
def baseStart_8195911 : Nat := 118140960795 + 8195911 * 2 ^ 59
def prefixEnd_8195911 : Nat := 4983230072969 + 3 ^ 40 * 8195911 * 2
def baseEnd_8195911 : Nat := 51956070919404792521237

theorem tailTrace_8195911 : CollatzResearch.WordTrace tailWord_8195911 prefixEnd_8195911 51956070919404792521237 := by
  unfold tailWord_8195911
  simp only [CollatzResearch.WordTrace]
  refine ⟨298929432210621672004107587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199286288140414448002738391 298929432210621672004107587)
  ·
    refine ⟨448394148315932508006161381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298929432210621672004107587 448394148315932508006161381)
    ·
      refine ⟨84073902809237345251155259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 448394148315932508006161381 84073902809237345251155259)
      ·
        refine ⟨126110854213856017876732889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84073902809237345251155259 126110854213856017876732889)
        ·
          refine ⟨94583140660392013407549667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126110854213856017876732889 94583140660392013407549667)
          ·
            refine ⟨141874710990588020111324501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94583140660392013407549667 141874710990588020111324501)
            ·
              refine ⟨51956070919404792521237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 141874710990588020111324501 51956070919404792521237)
              ·
                rfl

theorem cell23_8195911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 13].length) (baseStart_8195911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8195911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8195911 prefixEnd_8195911 := by exact prefixLift 8195911
  have htrace : WordTrace (prefixWord ++ tailWord_8195911) baseStart_8195911 baseEnd_8195911 := by
    simpa [prefixWord, tailWord_8195911, baseEnd_8195911] using wordTrace_append hprefix tailTrace_8195911
  have hstable : (prefixWord ++ tailWord_8195911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8195911).length < 2 ^ (prefixWord ++ tailWord_8195911).sum := by decide
  have hdescent : baseEnd_8195911 < baseStart_8195911 := by decide
  rcases family_descends (prefixWord ++ tailWord_8195911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8195916 : List Nat := [2, 2, 1, 3, 4, 1, 3, 2, 1, 1, 3]
def baseStart_8195916 : Nat := 118140960795 + 8195916 * 2 ^ 59
def prefixEnd_8195916 : Nat := 4983230072969 + 3 ^ 40 * 8195916 * 2
def baseEnd_8195916 : Nat := 4208444311875060674657675

theorem tailTrace_8195916 : CollatzResearch.WordTrace tailWord_8195916 prefixEnd_8195916 4208444311875060674657675 := by
  unfold tailWord_8195916
  simp only [CollatzResearch.WordTrace]
  refine ⟨149464807287801778929019801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199286409717069038572026401 149464807287801778929019801)
  ·
    refine ⟨112098605465851334196764851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149464807287801778929019801 112098605465851334196764851)
    ·
      refine ⟨168147908198777001295147277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112098605465851334196764851 168147908198777001295147277)
      ·
        refine ⟨63055465574541375485680229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168147908198777001295147277 63055465574541375485680229)
        ·
          refine ⟨11822899795226507903565043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63055465574541375485680229 11822899795226507903565043)
          ·
            refine ⟨17734349692839761855347565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11822899795226507903565043 17734349692839761855347565)
            ·
              refine ⟨6650381134814910695755337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17734349692839761855347565 6650381134814910695755337)
              ·
                refine ⟨4987785851111183021816503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6650381134814910695755337 4987785851111183021816503)
                ·
                  refine ⟨7481678776666774532724755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4987785851111183021816503 7481678776666774532724755)
                  ·
                    refine ⟨11222518165000161799087133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7481678776666774532724755 11222518165000161799087133)
                    ·
                      refine ⟨4208444311875060674657675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11222518165000161799087133 4208444311875060674657675)
                      ·
                        rfl

theorem cell23_8195916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 2, 1, 1, 3].length) (baseStart_8195916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8195916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8195916 prefixEnd_8195916 := by exact prefixLift 8195916
  have htrace : WordTrace (prefixWord ++ tailWord_8195916) baseStart_8195916 baseEnd_8195916 := by
    simpa [prefixWord, tailWord_8195916, baseEnd_8195916] using wordTrace_append hprefix tailTrace_8195916
  have hstable : (prefixWord ++ tailWord_8195916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8195916).length < 2 ^ (prefixWord ++ tailWord_8195916).sum := by decide
  have hdescent : baseEnd_8195916 < baseStart_8195916 := by decide
  rcases family_descends (prefixWord ++ tailWord_8195916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8195939 : List Nat := [1, 1, 1, 5, 5, 1, 1, 2, 1, 1, 4]
def baseStart_8195939 : Nat := 118140960795 + 8195939 * 2 ^ 59
def prefixEnd_8195939 : Nat := 4983230072969 + 3 ^ 40 * 8195939 * 2
def baseEnd_8195939 : Nat := 4208456121930114084670069

theorem tailTrace_8195939 : CollatzResearch.WordTrace tailWord_8195939 prefixEnd_8195939 4208456121930114084670069 := by
  unfold tailWord_8195939
  simp only [CollatzResearch.WordTrace]
  refine ⟨298930453454520232786126871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199286968969680155190751247 298930453454520232786126871)
  ·
    refine ⟨448395680181780349179190307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298930453454520232786126871 448395680181780349179190307)
    ·
      refine ⟨672593520272670523768785461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448395680181780349179190307 672593520272670523768785461)
      ·
        refine ⟨63055642525562861603323637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 672593520272670523768785461 63055642525562861603323637)
        ·
          refine ⟨5911466486771518275311591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63055642525562861603323637 5911466486771518275311591)
          ·
            refine ⟨8867199730157277412967387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5911466486771518275311591 8867199730157277412967387)
            ·
              refine ⟨13300799595235916119451081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8867199730157277412967387 13300799595235916119451081)
              ·
                refine ⟨9975599696426937089588311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13300799595235916119451081 9975599696426937089588311)
                ·
                  refine ⟨14963399544640405634382467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9975599696426937089588311 14963399544640405634382467)
                  ·
                    refine ⟨22445099316960608451573701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14963399544640405634382467 22445099316960608451573701)
                    ·
                      refine ⟨4208456121930114084670069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22445099316960608451573701 4208456121930114084670069)
                      ·
                        rfl

theorem cell23_8195939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 2, 1, 1, 4].length) (baseStart_8195939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8195939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8195939 prefixEnd_8195939 := by exact prefixLift 8195939
  have htrace : WordTrace (prefixWord ++ tailWord_8195939) baseStart_8195939 baseEnd_8195939 := by
    simpa [prefixWord, tailWord_8195939, baseEnd_8195939] using wordTrace_append hprefix tailTrace_8195939
  have hstable : (prefixWord ++ tailWord_8195939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8195939).length < 2 ^ (prefixWord ++ tailWord_8195939).sum := by decide
  have hdescent : baseEnd_8195939 < baseStart_8195939 := by decide
  rcases family_descends (prefixWord ++ tailWord_8195939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8195972 : List Nat := [2, 3, 2, 1, 1, 1, 3, 4, 2, 1, 3]
def baseStart_8195972 : Nat := 118140960795 + 8195972 * 2 ^ 59
def prefixEnd_8195972 : Nat := 4983230072969 + 3 ^ 40 * 8195972 * 2
def baseEnd_8195972 : Nat := 4208473066791712455557417

theorem tailTrace_8195972 : CollatzResearch.WordTrace tailWord_8195972 prefixEnd_8195972 4208473066791712455557417 := by
  unfold tailWord_8195972
  simp only [CollatzResearch.WordTrace]
  refine ⟨149465828531700339711039085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199287771375600452948052113 149465828531700339711039085)
  ·
    refine ⟨56049685699387627391639657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149465828531700339711039085 56049685699387627391639657)
    ·
      refine ⟨42037264274540720543729743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56049685699387627391639657 42037264274540720543729743)
      ·
        refine ⟨63055896411811080815594615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42037264274540720543729743 63055896411811080815594615)
        ·
          refine ⟨94583844617716621223391923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63055896411811080815594615 94583844617716621223391923)
          ·
            refine ⟨141875766926574931835087885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94583844617716621223391923 141875766926574931835087885)
            ·
              refine ⟨53203412597465599438157957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141875766926574931835087885 53203412597465599438157957)
              ·
                refine ⟨9975639862024799894654617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53203412597465599438157957 9975639862024799894654617)
                ·
                  refine ⟨7481729896518599920990963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9975639862024799894654617 7481729896518599920990963)
                  ·
                    refine ⟨11222594844777899881486445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7481729896518599920990963 11222594844777899881486445)
                    ·
                      refine ⟨4208473066791712455557417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11222594844777899881486445 4208473066791712455557417)
                      ·
                        rfl

theorem cell23_8195972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_8195972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8195972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8195972 prefixEnd_8195972 := by exact prefixLift 8195972
  have htrace : WordTrace (prefixWord ++ tailWord_8195972) baseStart_8195972 baseEnd_8195972 := by
    simpa [prefixWord, tailWord_8195972, baseEnd_8195972] using wordTrace_append hprefix tailTrace_8195972
  have hstable : (prefixWord ++ tailWord_8195972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8195972).length < 2 ^ (prefixWord ++ tailWord_8195972).sum := by decide
  have hdescent : baseEnd_8195972 < baseStart_8195972 := by decide
  rcases family_descends (prefixWord ++ tailWord_8195972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8196029 : List Nat := [1, 4, 1, 2, 3, 2, 1, 1, 4, 2, 2]
def baseStart_8196029 : Nat := 118140960795 + 8196029 * 2 ^ 59
def prefixEnd_8196029 : Nat := 4983230072969 + 3 ^ 40 * 8196029 * 2
def baseEnd_8196029 : Nat := 4208502335189018732544655

theorem tailTrace_8196029 : CollatzResearch.WordTrace tailWord_8196029 prefixEnd_8196029 4208502335189018732544655 := by
  unfold tailWord_8196029
  simp only [CollatzResearch.WordTrace]
  refine ⟨298933736024194178156903141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199289157349462785437935427 298933736024194178156903141)
  ·
    refine ⟨56050075504536408404419339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 298933736024194178156903141 56050075504536408404419339)
    ·
      refine ⟨84075113256804612606629009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56050075504536408404419339 84075113256804612606629009)
      ·
        refine ⟨63056334942603459454971757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84075113256804612606629009 63056334942603459454971757)
        ·
          refine ⟨23646125603476297295614409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63056334942603459454971757 23646125603476297295614409)
          ·
            refine ⟨17734594202607222971710807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23646125603476297295614409 17734594202607222971710807)
            ·
              refine ⟨26601891303910834457566211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17734594202607222971710807 26601891303910834457566211)
              ·
                refine ⟨39902836955866251686349317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26601891303910834457566211 39902836955866251686349317)
                ·
                  refine ⟨7481781929224922191190497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39902836955866251686349317 7481781929224922191190497)
                  ·
                    refine ⟨5611336446918691643392873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7481781929224922191190497 5611336446918691643392873)
                    ·
                      refine ⟨4208502335189018732544655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5611336446918691643392873 4208502335189018732544655)
                      ·
                        rfl

theorem cell23_8196029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 4, 2, 2].length) (baseStart_8196029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8196029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8196029 prefixEnd_8196029 := by exact prefixLift 8196029
  have htrace : WordTrace (prefixWord ++ tailWord_8196029) baseStart_8196029 baseEnd_8196029 := by
    simpa [prefixWord, tailWord_8196029, baseEnd_8196029] using wordTrace_append hprefix tailTrace_8196029
  have hstable : (prefixWord ++ tailWord_8196029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8196029).length < 2 ^ (prefixWord ++ tailWord_8196029).sum := by decide
  have hdescent : baseEnd_8196029 < baseStart_8196029 := by decide
  rcases family_descends (prefixWord ++ tailWord_8196029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8196046 : List Nat := [4, 1, 1, 1, 2, 2, 5, 1, 2, 2, 2]
def baseStart_8196046 : Nat := 118140960795 + 8196046 * 2 ^ 59
def prefixEnd_8196046 : Nat := 4983230072969 + 3 ^ 40 * 8196046 * 2
def baseEnd_8196046 : Nat := 4208511064360145166032077

theorem tailTrace_8196046 : CollatzResearch.WordTrace tailWord_8196046 prefixEnd_8196046 4208511064360145166032077 := by
  unfold tailWord_8196046
  simp only [CollatzResearch.WordTrace]
  refine ⟨37366794508141573757533999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199289570710088393373514661 37366794508141573757533999)
  ·
    refine ⟨56050191762212360636300999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37366794508141573757533999 56050191762212360636300999)
    ·
      refine ⟨84075287643318540954451499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56050191762212360636300999 84075287643318540954451499)
      ·
        refine ⟨126112931464977811431677249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84075287643318540954451499 126112931464977811431677249)
        ·
          refine ⟨94584698598733358573757937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126112931464977811431677249 94584698598733358573757937)
          ·
            refine ⟨70938523949050018930318453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94584698598733358573757937 70938523949050018930318453)
            ·
              refine ⟨6650486620223439274717355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70938523949050018930318453 6650486620223439274717355)
              ·
                refine ⟨9975729930335158912076033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6650486620223439274717355 9975729930335158912076033)
                ·
                  refine ⟨7481797447751369184057025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9975729930335158912076033 7481797447751369184057025)
                  ·
                    refine ⟨5611348085813526888042769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7481797447751369184057025 5611348085813526888042769)
                    ·
                      refine ⟨4208511064360145166032077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5611348085813526888042769 4208511064360145166032077)
                      ·
                        rfl

theorem cell23_8196046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 1, 2, 2, 2].length) (baseStart_8196046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8196046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8196046 prefixEnd_8196046 := by exact prefixLift 8196046
  have htrace : WordTrace (prefixWord ++ tailWord_8196046) baseStart_8196046 baseEnd_8196046 := by
    simpa [prefixWord, tailWord_8196046, baseEnd_8196046] using wordTrace_append hprefix tailTrace_8196046
  have hstable : (prefixWord ++ tailWord_8196046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8196046).length < 2 ^ (prefixWord ++ tailWord_8196046).sum := by decide
  have hdescent : baseEnd_8196046 < baseStart_8196046 := by decide
  rcases family_descends (prefixWord ++ tailWord_8196046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8196048 : List Nat := [2, 1, 1, 1, 1, 2, 5, 2, 1, 7]
def baseStart_8196048 : Nat := 118140960795 + 8196048 * 2 ^ 59
def prefixEnd_8196048 : Nat := 4983230072969 + 3 ^ 40 * 8196048 * 2
def baseEnd_8196048 : Nat := 1402837363773818052735689

theorem tailTrace_8196048 : CollatzResearch.WordTrace tailWord_8196048 prefixEnd_8196048 1402837363773818052735689 := by
  unfold tailWord_8196048
  simp only [CollatzResearch.WordTrace]
  refine ⟨149467214505562672200922399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199289619340750229601229865 149467214505562672200922399)
  ·
    refine ⟨224200821758344008301383599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149467214505562672200922399 224200821758344008301383599)
    ·
      refine ⟨336301232637516012452075399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224200821758344008301383599 336301232637516012452075399)
      ·
        refine ⟨504451848956274018678113099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336301232637516012452075399 504451848956274018678113099)
        ·
          refine ⟨756677773434411028017169649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504451848956274018678113099 756677773434411028017169649)
          ·
            refine ⟨567508330075808271012877237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 756677773434411028017169649 567508330075808271012877237)
            ·
              refine ⟨53203905944607025407457241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 567508330075808271012877237 53203905944607025407457241)
              ·
                refine ⟨39902929458455269055592931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53203905944607025407457241 39902929458455269055592931)
                ·
                  refine ⟨59854394187682903583389397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39902929458455269055592931 59854394187682903583389397)
                  ·
                    refine ⟨1402837363773818052735689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59854394187682903583389397 1402837363773818052735689)
                    ·
                      rfl

theorem cell23_8196048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 1, 7].length) (baseStart_8196048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8196048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8196048 prefixEnd_8196048 := by exact prefixLift 8196048
  have htrace : WordTrace (prefixWord ++ tailWord_8196048) baseStart_8196048 baseEnd_8196048 := by
    simpa [prefixWord, tailWord_8196048, baseEnd_8196048] using wordTrace_append hprefix tailTrace_8196048
  have hstable : (prefixWord ++ tailWord_8196048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8196048).length < 2 ^ (prefixWord ++ tailWord_8196048).sum := by decide
  have hdescent : baseEnd_8196048 < baseStart_8196048 := by decide
  rcases family_descends (prefixWord ++ tailWord_8196048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8196086 : List Nat := [5, 1, 1, 1, 4, 1, 3, 2, 5]
def baseStart_8196086 : Nat := 118140960795 + 8196086 * 2 ^ 59
def prefixEnd_8196086 : Nat := 4983230072969 + 3 ^ 40 * 8196086 * 2
def baseEnd_8196086 : Nat := 467614622620702778836877

theorem tailTrace_8196086 : CollatzResearch.WordTrace tailWord_8196086 prefixEnd_8196086 467614622620702778836877 := by
  unfold tailWord_8196086
  simp only [CollatzResearch.WordTrace]
  refine ⟨18683488436561729805733007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199290543323325117927818741 18683488436561729805733007)
  ·
    refine ⟨28025232654842594708599511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18683488436561729805733007 28025232654842594708599511)
    ·
      refine ⟨42037848982263892062899267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28025232654842594708599511 42037848982263892062899267)
      ·
        refine ⟨63056773473395838094348901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42037848982263892062899267 63056773473395838094348901)
        ·
          refine ⟨11823145026261719642690419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63056773473395838094348901 11823145026261719642690419)
          ·
            refine ⟨17734717539392579464035629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11823145026261719642690419 17734717539392579464035629)
            ·
              refine ⟨6650519077272217299013361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17734717539392579464035629 6650519077272217299013361)
              ·
                refine ⟨4987889307954162974260021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6650519077272217299013361 4987889307954162974260021)
                ·
                  refine ⟨467614622620702778836877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4987889307954162974260021 467614622620702778836877)
                  ·
                    rfl

theorem cell23_8196086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 2, 5].length) (baseStart_8196086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8196086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8196086 prefixEnd_8196086 := by exact prefixLift 8196086
  have htrace : WordTrace (prefixWord ++ tailWord_8196086) baseStart_8196086 baseEnd_8196086 := by
    simpa [prefixWord, tailWord_8196086, baseEnd_8196086] using wordTrace_append hprefix tailTrace_8196086
  have hstable : (prefixWord ++ tailWord_8196086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8196086).length < 2 ^ (prefixWord ++ tailWord_8196086).sum := by decide
  have hdescent : baseEnd_8196086 < baseStart_8196086 := by decide
  rcases family_descends (prefixWord ++ tailWord_8196086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8196116 : List Nat := [2, 4, 3, 2, 1, 1, 2, 1, 2, 5]
def baseStart_8196116 : Nat := 118140960795 + 8196116 * 2 ^ 59
def prefixEnd_8196116 : Nat := 4983230072969 + 3 ^ 40 * 8196116 * 2
def baseEnd_8196116 : Nat := 1402849002668653297385585

theorem tailTrace_8196116 : CollatzResearch.WordTrace tailWord_8196116 prefixEnd_8196116 1402849002668653297385585 := by
  unfold tailWord_8196116
  simp only [CollatzResearch.WordTrace]
  refine ⟨149468454587439496007660101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199291272783252661343546801 149468454587439496007660101)
  ·
    refine ⟨28025335235144905501436269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149468454587439496007660101 28025335235144905501436269)
    ·
      refine ⟨10509500713179339563038601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28025335235144905501436269 10509500713179339563038601)
      ·
        refine ⟨7882125534884504672278951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10509500713179339563038601 7882125534884504672278951)
        ·
          refine ⟨11823188302326757008418427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7882125534884504672278951 11823188302326757008418427)
          ·
            refine ⟨17734782453490135512627641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11823188302326757008418427 17734782453490135512627641)
            ·
              refine ⟨13301086840117601634470731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17734782453490135512627641 13301086840117601634470731)
              ·
                refine ⟨19951630260176402451706097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13301086840117601634470731 19951630260176402451706097)
                ·
                  refine ⟨14963722695132301838779573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19951630260176402451706097 14963722695132301838779573)
                  ·
                    refine ⟨1402849002668653297385585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14963722695132301838779573 1402849002668653297385585)
                    ·
                      rfl

theorem cell23_8196116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_8196116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8196116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8196116 prefixEnd_8196116 := by exact prefixLift 8196116
  have htrace : WordTrace (prefixWord ++ tailWord_8196116) baseStart_8196116 baseEnd_8196116 := by
    simpa [prefixWord, tailWord_8196116, baseEnd_8196116] using wordTrace_append hprefix tailTrace_8196116
  have hstable : (prefixWord ++ tailWord_8196116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8196116).length < 2 ^ (prefixWord ++ tailWord_8196116).sum := by decide
  have hdescent : baseEnd_8196116 < baseStart_8196116 := by decide
  rcases family_descends (prefixWord ++ tailWord_8196116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8196119 : List Nat := [1, 1, 3, 5, 2, 1, 2, 1, 2, 1, 4]
def baseStart_8196119 : Nat := 118140960795 + 8196119 * 2 ^ 59
def prefixEnd_8196119 : Nat := 4983230072969 + 3 ^ 40 * 8196119 * 2
def baseEnd_8196119 : Nat := 4208548548447923380419241

theorem tailTrace_8196119 : CollatzResearch.WordTrace tailWord_8196119 prefixEnd_8196119 4208548548447923380419241 := by
  unfold tailWord_8196119
  simp only [CollatzResearch.WordTrace]
  refine ⟨298937018593868123527679411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199291345729245415685119607 298937018593868123527679411)
  ·
    refine ⟨448405527890802185291519117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298937018593868123527679411 448405527890802185291519117)
    ·
      refine ⟨168152072959050819484319669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 448405527890802185291519117 168152072959050819484319669)
      ·
        refine ⟨15764256839911014326654969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 168152072959050819484319669 15764256839911014326654969)
        ·
          refine ⟨11823192629933260744991227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15764256839911014326654969 11823192629933260744991227)
          ·
            refine ⟨17734788944899891117486841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11823192629933260744991227 17734788944899891117486841)
            ·
              refine ⟨13301091708674918338115131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17734788944899891117486841 13301091708674918338115131)
              ·
                refine ⟨19951637563012377507172697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13301091708674918338115131 19951637563012377507172697)
                ·
                  refine ⟨14963728172259283130379523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19951637563012377507172697 14963728172259283130379523)
                  ·
                    refine ⟨22445592258388924695569285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14963728172259283130379523 22445592258388924695569285)
                    ·
                      refine ⟨4208548548447923380419241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22445592258388924695569285 4208548548447923380419241)
                      ·
                        rfl

theorem cell23_8196119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_8196119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8196119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8196119 prefixEnd_8196119 := by exact prefixLift 8196119
  have htrace : WordTrace (prefixWord ++ tailWord_8196119) baseStart_8196119 baseEnd_8196119 := by
    simpa [prefixWord, tailWord_8196119, baseEnd_8196119] using wordTrace_append hprefix tailTrace_8196119
  have hstable : (prefixWord ++ tailWord_8196119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8196119).length < 2 ^ (prefixWord ++ tailWord_8196119).sum := by decide
  have hdescent : baseEnd_8196119 < baseStart_8196119 := by decide
  rcases family_descends (prefixWord ++ tailWord_8196119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8196122 : List Nat := [3, 1, 1, 3, 1, 3, 1, 3, 2, 2, 3]
def baseStart_8196122 : Nat := 118140960795 + 8196122 * 2 ^ 59
def prefixEnd_8196122 : Nat := 4983230072969 + 3 ^ 40 * 8196122 * 2
def baseEnd_8196122 : Nat := 4208550088889886868681727

theorem tailTrace_8196122 : CollatzResearch.WordTrace tailWord_8196122 prefixEnd_8196122 4208550088889886868681727 := by
  unfold tailWord_8196122
  simp only [CollatzResearch.WordTrace]
  refine ⟨74734282003214313760009655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199291418675238170026692413 74734282003214313760009655)
  ·
    refine ⟨112101423004821470640014483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74734282003214313760009655 112101423004821470640014483)
    ·
      refine ⟨168152134507232205960021725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112101423004821470640014483 168152134507232205960021725)
      ·
        refine ⟨63057050440212077235008147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168152134507232205960021725 63057050440212077235008147)
        ·
          refine ⟨94585575660318115852512221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63057050440212077235008147 94585575660318115852512221)
          ·
            refine ⟨35469590872619293444692083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94585575660318115852512221 35469590872619293444692083)
            ·
              refine ⟨53204386308928940167038125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35469590872619293444692083 53204386308928940167038125)
              ·
                refine ⟨19951644865848352562639297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53204386308928940167038125 19951644865848352562639297)
                ·
                  refine ⟨14963733649386264421979473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19951644865848352562639297 14963733649386264421979473)
                  ·
                    refine ⟨11222800237039698316484605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14963733649386264421979473 11222800237039698316484605)
                    ·
                      refine ⟨4208550088889886868681727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11222800237039698316484605 4208550088889886868681727)
                      ·
                        rfl

theorem cell23_8196122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_8196122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8196122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8196122 prefixEnd_8196122 := by exact prefixLift 8196122
  have htrace : WordTrace (prefixWord ++ tailWord_8196122) baseStart_8196122 baseEnd_8196122 := by
    simpa [prefixWord, tailWord_8196122, baseEnd_8196122] using wordTrace_append hprefix tailTrace_8196122
  have hstable : (prefixWord ++ tailWord_8196122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8196122).length < 2 ^ (prefixWord ++ tailWord_8196122).sum := by decide
  have hdescent : baseEnd_8196122 < baseStart_8196122 := by decide
  rcases family_descends (prefixWord ++ tailWord_8196122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8196142 : List Nat := [4, 1, 3, 1, 1, 2, 1, 4, 6]
def baseStart_8196142 : Nat := 118140960795 + 8196142 * 2 ^ 59
def prefixEnd_8196142 : Nat := 4983230072969 + 3 ^ 40 * 8196142 * 2
def baseEnd_8196142 : Nat := 467617817611441865603515

theorem tailTrace_8196142 : CollatzResearch.WordTrace tailWord_8196142 prefixEnd_8196142 467617817611441865603515 := by
  unfold tailWord_8196142
  simp only [CollatzResearch.WordTrace]
  refine ⟨37367232184098099806970835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199291904981856532303844453 37367232184098099806970835)
  ·
    refine ⟨56050848276147149710456253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37367232184098099806970835 56050848276147149710456253)
    ·
      refine ⟨21019068103555181141421095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56050848276147149710456253 21019068103555181141421095)
      ·
        refine ⟨31528602155332771712131643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21019068103555181141421095 31528602155332771712131643)
        ·
          refine ⟨47292903232999157568197465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31528602155332771712131643 47292903232999157568197465)
          ·
            refine ⟨35469677424749368176148099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47292903232999157568197465 35469677424749368176148099)
            ·
              refine ⟨53204516137124052264222149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35469677424749368176148099 53204516137124052264222149)
              ·
                refine ⟨9975846775710759799541653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53204516137124052264222149 9975846775710759799541653)
                ·
                  refine ⟨467617817611441865603515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9975846775710759799541653 467617817611441865603515)
                  ·
                    rfl

theorem cell23_8196142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 4, 6].length) (baseStart_8196142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8196142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8196142 prefixEnd_8196142 := by exact prefixLift 8196142
  have htrace : WordTrace (prefixWord ++ tailWord_8196142) baseStart_8196142 baseEnd_8196142 := by
    simpa [prefixWord, tailWord_8196142, baseEnd_8196142] using wordTrace_append hprefix tailTrace_8196142
  have hstable : (prefixWord ++ tailWord_8196142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8196142).length < 2 ^ (prefixWord ++ tailWord_8196142).sum := by decide
  have hdescent : baseEnd_8196142 < baseStart_8196142 := by decide
  rcases family_descends (prefixWord ++ tailWord_8196142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8196146 : List Nat := [3, 2, 1, 1, 2, 3, 4, 2, 1, 4]
def baseStart_8196146 : Nat := 118140960795 + 8196146 * 2 ^ 59
def prefixEnd_8196146 : Nat := 4983230072969 + 3 ^ 40 * 8196146 * 2
def baseEnd_8196146 : Nat := 1402854137475198258260539

theorem tailTrace_8196146 : CollatzResearch.WordTrace tailWord_8196146 prefixEnd_8196146 1402854137475198258260539 := by
  unfold tailWord_8196146
  simp only [CollatzResearch.WordTrace]
  refine ⟨74734500841192576784728073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199292002243180204759274861 74734500841192576784728073)
  ·
    refine ⟨56050875630894432588546055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74734500841192576784728073 56050875630894432588546055)
    ·
      refine ⟨84076313446341648882819083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56050875630894432588546055 84076313446341648882819083)
      ·
        refine ⟨126114470169512473324228625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84076313446341648882819083 126114470169512473324228625)
        ·
          refine ⟨94585852627134354993171469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126114470169512473324228625 94585852627134354993171469)
          ·
            refine ⟨35469694735175383122439301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94585852627134354993171469 35469694735175383122439301)
            ·
              refine ⟨6650567762845384335457369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35469694735175383122439301 6650567762845384335457369)
              ·
                refine ⟨4987925822134038251593027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6650567762845384335457369 4987925822134038251593027)
                ·
                  refine ⟨7481888733201057377389541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4987925822134038251593027 7481888733201057377389541)
                  ·
                    refine ⟨1402854137475198258260539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7481888733201057377389541 1402854137475198258260539)
                    ·
                      rfl

theorem cell23_8196146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 2, 1, 4].length) (baseStart_8196146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8196146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8196146 prefixEnd_8196146 := by exact prefixLift 8196146
  have htrace : WordTrace (prefixWord ++ tailWord_8196146) baseStart_8196146 baseEnd_8196146 := by
    simpa [prefixWord, tailWord_8196146, baseEnd_8196146] using wordTrace_append hprefix tailTrace_8196146
  have hstable : (prefixWord ++ tailWord_8196146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8196146).length < 2 ^ (prefixWord ++ tailWord_8196146).sum := by decide
  have hdescent : baseEnd_8196146 < baseStart_8196146 := by decide
  rcases family_descends (prefixWord ++ tailWord_8196146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8196185 : List Nat := [1, 2, 1, 2, 2, 1, 3, 4, 1, 6]
def baseStart_8196185 : Nat := 118140960795 + 8196185 * 2 ^ 59
def prefixEnd_8196185 : Nat := 4983230072969 + 3 ^ 40 * 8196185 * 2
def baseEnd_8196185 : Nat := 1402860812723706707397979

theorem tailTrace_8196185 : CollatzResearch.WordTrace tailWord_8196185 prefixEnd_8196185 1402860812723706707397979 := by
  unfold tailWord_8196185
  simp only [CollatzResearch.WordTrace]
  refine ⟨298939425811629016799582009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199292950541086011199721339 298939425811629016799582009)
  ·
    refine ⟨224204569358721762599686507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298939425811629016799582009 224204569358721762599686507)
    ·
      refine ⟨336306854038082643899529761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224204569358721762599686507 336306854038082643899529761)
      ·
        refine ⟨252230140528561982924647321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336306854038082643899529761 252230140528561982924647321)
        ·
          refine ⟨189172605396421487193485491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252230140528561982924647321 189172605396421487193485491)
          ·
            refine ⟨283758908094632230790228237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189172605396421487193485491 283758908094632230790228237)
            ·
              refine ⟨106409590535487086546335589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 283758908094632230790228237 106409590535487086546335589)
              ·
                refine ⟨19951798225403828727437923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106409590535487086546335589 19951798225403828727437923)
                ·
                  refine ⟨29927697338105743091156885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19951798225403828727437923 29927697338105743091156885)
                  ·
                    refine ⟨1402860812723706707397979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29927697338105743091156885 1402860812723706707397979)
                    ·
                      rfl

theorem cell23_8196185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 6].length) (baseStart_8196185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8196185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8196185 prefixEnd_8196185 := by exact prefixLift 8196185
  have htrace : WordTrace (prefixWord ++ tailWord_8196185) baseStart_8196185 baseEnd_8196185 := by
    simpa [prefixWord, tailWord_8196185, baseEnd_8196185] using wordTrace_append hprefix tailTrace_8196185
  have hstable : (prefixWord ++ tailWord_8196185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8196185).length < 2 ^ (prefixWord ++ tailWord_8196185).sum := by decide
  have hdescent : baseEnd_8196185 < baseStart_8196185 := by decide
  rcases family_descends (prefixWord ++ tailWord_8196185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8196186 : List Nat := [3, 1, 1, 2, 1, 1, 6, 3, 1, 1, 3]
def baseStart_8196186 : Nat := 118140960795 + 8196186 * 2 ^ 59
def prefixEnd_8196186 : Nat := 4983230072969 + 3 ^ 40 * 8196186 * 2
def baseEnd_8196186 : Nat := 4208582951651774618281433

theorem tailTrace_8196186 : CollatzResearch.WordTrace tailWord_8196186 prefixEnd_8196186 4208582951651774618281433 := by
  unfold tailWord_8196186
  simp only [CollatzResearch.WordTrace]
  refine ⟨74734865571156348492592103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199292974856416929313578941 74734865571156348492592103)
  ·
    refine ⟨112102298356734522738888155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74734865571156348492592103 112102298356734522738888155)
    ·
      refine ⟨168153447535101784108332233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112102298356734522738888155 168153447535101784108332233)
      ·
        refine ⟨126115085651326338081249175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168153447535101784108332233 126115085651326338081249175)
        ·
          refine ⟨189172628476989507121873763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126115085651326338081249175 189172628476989507121873763)
          ·
            refine ⟨283758942715484260682810645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189172628476989507121873763 283758942715484260682810645)
            ·
              refine ⟨13301200439788324719506749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 283758942715484260682810645 13301200439788324719506749)
              ·
                refine ⟨4987950164920621769815031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13301200439788324719506749 4987950164920621769815031)
                ·
                  refine ⟨7481925247380932654722547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4987950164920621769815031 7481925247380932654722547)
                  ·
                    refine ⟨11222887871071398982083821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7481925247380932654722547 11222887871071398982083821)
                    ·
                      refine ⟨4208582951651774618281433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11222887871071398982083821 4208582951651774618281433)
                      ·
                        rfl

theorem cell23_8196186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 3, 1, 1, 3].length) (baseStart_8196186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8196186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8196186 prefixEnd_8196186 := by exact prefixLift 8196186
  have htrace : WordTrace (prefixWord ++ tailWord_8196186) baseStart_8196186 baseEnd_8196186 := by
    simpa [prefixWord, tailWord_8196186, baseEnd_8196186] using wordTrace_append hprefix tailTrace_8196186
  have hstable : (prefixWord ++ tailWord_8196186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8196186).length < 2 ^ (prefixWord ++ tailWord_8196186).sum := by decide
  have hdescent : baseEnd_8196186 < baseStart_8196186 := by decide
  rcases family_descends (prefixWord ++ tailWord_8196186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8196229 : List Nat := [1, 3, 1, 1, 5, 1, 1, 4, 1, 2, 3]
def baseStart_8196229 : Nat := 118140960795 + 8196229 * 2 ^ 59
def prefixEnd_8196229 : Nat := 4983230072969 + 3 ^ 40 * 8196229 * 2
def baseEnd_8196229 : Nat := 4208605031319917950043735

theorem tailTrace_8196229 : CollatzResearch.WordTrace tailWord_8196229 prefixEnd_8196229 4208605031319917950043735 := by
  unfold tailWord_8196229
  simp only [CollatzResearch.WordTrace]
  refine ⟨298941030623469612314183741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199294020415646408209455827 298941030623469612314183741)
  ·
    refine ⟨112102886483801104617818903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298941030623469612314183741 112102886483801104617818903)
    ·
      refine ⟨168154329725701656926728355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112102886483801104617818903 168154329725701656926728355)
      ·
        refine ⟨252231494588552485390092533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168154329725701656926728355 252231494588552485390092533)
        ·
          refine ⟨23646702617676795505321175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 252231494588552485390092533 23646702617676795505321175)
          ·
            refine ⟨35470053926515193257981763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23646702617676795505321175 35470053926515193257981763)
            ·
              refine ⟨53205080889772789886972645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35470053926515193257981763 53205080889772789886972645)
              ·
                refine ⟨9975952666832398103807371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53205080889772789886972645 9975952666832398103807371)
                ·
                  refine ⟨14963929000248597155711057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9975952666832398103807371 14963929000248597155711057)
                  ·
                    refine ⟨11222946750186447866783293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14963929000248597155711057 11222946750186447866783293)
                    ·
                      refine ⟨4208605031319917950043735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11222946750186447866783293 4208605031319917950043735)
                      ·
                        rfl

theorem cell23_8196229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 4, 1, 2, 3].length) (baseStart_8196229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8196229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8196229 prefixEnd_8196229 := by exact prefixLift 8196229
  have htrace : WordTrace (prefixWord ++ tailWord_8196229) baseStart_8196229 baseEnd_8196229 := by
    simpa [prefixWord, tailWord_8196229, baseEnd_8196229] using wordTrace_append hprefix tailTrace_8196229
  have hstable : (prefixWord ++ tailWord_8196229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8196229).length < 2 ^ (prefixWord ++ tailWord_8196229).sum := by decide
  have hdescent : baseEnd_8196229 < baseStart_8196229 := by decide
  rcases family_descends (prefixWord ++ tailWord_8196229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8196232 : List Nat := [2, 1, 3, 4, 1, 2, 1, 9]
def baseStart_8196232 : Nat := 118140960795 + 8196232 * 2 ^ 59
def prefixEnd_8196232 : Nat := 4983230072969 + 3 ^ 40 * 8196232 * 2
def baseEnd_8196232 : Nat := 155874317472662275492823

theorem tailTrace_8196232 : CollatzResearch.WordTrace tailWord_8196232 prefixEnd_8196232 155874317472662275492823 := by
  unfold tailWord_8196232
  simp only [CollatzResearch.WordTrace]
  refine ⟨149470570021229371913271475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199294093361639162551028633 149470570021229371913271475)
  ·
    refine ⟨224205855031844057869907213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149470570021229371913271475 224205855031844057869907213)
    ·
      refine ⟨84077195636941521701215205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224205855031844057869907213 84077195636941521701215205)
      ·
        refine ⟨15764474181926535318977851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84077195636941521701215205 15764474181926535318977851)
        ·
          refine ⟨23646711272889802978466777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15764474181926535318977851 23646711272889802978466777)
          ·
            refine ⟨17735033454667352233850083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23646711272889802978466777 17735033454667352233850083)
            ·
              refine ⟨26602550182001028350775125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17735033454667352233850083 26602550182001028350775125)
              ·
                refine ⟨155874317472662275492823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26602550182001028350775125 155874317472662275492823)
                ·
                  rfl

theorem cell23_8196232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 9].length) (baseStart_8196232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8196232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8196232 prefixEnd_8196232 := by exact prefixLift 8196232
  have htrace : WordTrace (prefixWord ++ tailWord_8196232) baseStart_8196232 baseEnd_8196232 := by
    simpa [prefixWord, tailWord_8196232, baseEnd_8196232] using wordTrace_append hprefix tailTrace_8196232
  have hstable : (prefixWord ++ tailWord_8196232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8196232).length < 2 ^ (prefixWord ++ tailWord_8196232).sum := by decide
  have hdescent : baseEnd_8196232 < baseStart_8196232 := by decide
  rcases family_descends (prefixWord ++ tailWord_8196232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8196260 : List Nat := [2, 3, 1, 2, 5, 1, 1, 1, 3, 2, 2]
def baseStart_8196260 : Nat := 118140960795 + 8196260 * 2 ^ 59
def prefixEnd_8196260 : Nat := 4983230072969 + 3 ^ 40 * 8196260 * 2
def baseEnd_8196260 : Nat := 4208620949220207328756093

theorem tailTrace_8196260 : CollatzResearch.WordTrace tailWord_8196260 prefixEnd_8196260 4208620949220207328756093 := by
  unfold tailWord_8196260
  simp only [CollatzResearch.WordTrace]
  refine ⟨149471080643178652304281117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199294774190904869739041489 149471080643178652304281117)
  ·
    refine ⟨56051655241191994614105419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149471080643178652304281117 56051655241191994614105419)
    ·
      refine ⟨84077482861787991921158129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56051655241191994614105419 84077482861787991921158129)
      ·
        refine ⟨63058112146340993940868597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84077482861787991921158129 63058112146340993940868597)
        ·
          refine ⟨5911698013719468181956431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63058112146340993940868597 5911698013719468181956431)
          ·
            refine ⟨8867547020579202272934647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5911698013719468181956431 8867547020579202272934647)
            ·
              refine ⟨13301320530868803409401971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8867547020579202272934647 13301320530868803409401971)
              ·
                refine ⟨19951980796303205114102957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13301320530868803409401971 19951980796303205114102957)
                ·
                  refine ⟨7481992798613701917788609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19951980796303205114102957 7481992798613701917788609)
                  ·
                    refine ⟨5611494598960276438341457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7481992798613701917788609 5611494598960276438341457)
                    ·
                      refine ⟨4208620949220207328756093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5611494598960276438341457 4208620949220207328756093)
                      ·
                        rfl

theorem cell23_8196260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 3, 2, 2].length) (baseStart_8196260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8196260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8196260 prefixEnd_8196260 := by exact prefixLift 8196260
  have htrace : WordTrace (prefixWord ++ tailWord_8196260) baseStart_8196260 baseEnd_8196260 := by
    simpa [prefixWord, tailWord_8196260, baseEnd_8196260] using wordTrace_append hprefix tailTrace_8196260
  have hstable : (prefixWord ++ tailWord_8196260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8196260).length < 2 ^ (prefixWord ++ tailWord_8196260).sum := by decide
  have hdescent : baseEnd_8196260 < baseStart_8196260 := by decide
  rcases family_descends (prefixWord ++ tailWord_8196260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8196275 : List Nat := [1, 1, 1, 2, 3, 2, 1, 3, 1, 8]
def baseStart_8196275 : Nat := 118140960795 + 8196275 * 2 ^ 59
def prefixEnd_8196275 : Nat := 4983230072969 + 3 ^ 40 * 8196275 * 2
def baseEnd_8196275 : Nat := 1402876217143341590022841

theorem tailTrace_8196275 : CollatzResearch.WordTrace tailWord_8196275 prefixEnd_8196275 1402876217143341590022841 := by
  unfold tailWord_8196275
  simp only [CollatzResearch.WordTrace]
  refine ⟨298942708381302962170358279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199295138920868641446905519 298942708381302962170358279)
  ·
    refine ⟨448414062571954443255537419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298942708381302962170358279 448414062571954443255537419)
    ·
      refine ⟨672621093857931664883306129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448414062571954443255537419 672621093857931664883306129)
      ·
        refine ⟨504465820393448748662479597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 672621093857931664883306129 504465820393448748662479597)
        ·
          refine ⟨189174682647543280748429849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 504465820393448748662479597 189174682647543280748429849)
          ·
            refine ⟨141881011985657460561322387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189174682647543280748429849 141881011985657460561322387)
            ·
              refine ⟨212821517978486190841983581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141881011985657460561322387 212821517978486190841983581)
              ·
                refine ⟨79808069241932321565743843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 212821517978486190841983581 79808069241932321565743843)
                ·
                  refine ⟨119712103862898482348615765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79808069241932321565743843 119712103862898482348615765)
                  ·
                    refine ⟨1402876217143341590022841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 119712103862898482348615765 1402876217143341590022841)
                    ·
                      rfl

theorem cell23_8196275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 8].length) (baseStart_8196275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8196275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8196275 prefixEnd_8196275 := by exact prefixLift 8196275
  have htrace : WordTrace (prefixWord ++ tailWord_8196275) baseStart_8196275 baseEnd_8196275 := by
    simpa [prefixWord, tailWord_8196275, baseEnd_8196275] using wordTrace_append hprefix tailTrace_8196275
  have hstable : (prefixWord ++ tailWord_8196275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8196275).length < 2 ^ (prefixWord ++ tailWord_8196275).sum := by decide
  have hdescent : baseEnd_8196275 < baseStart_8196275 := by decide
  rcases family_descends (prefixWord ++ tailWord_8196275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8196299 : List Nat := [1, 1, 1, 1, 3, 2, 5, 2, 1, 4, 2]
def baseStart_8196299 : Nat := 118140960795 + 8196299 * 2 ^ 59
def prefixEnd_8196299 : Nat := 4983230072969 + 3 ^ 40 * 8196299 * 2
def baseEnd_8196299 : Nat := 4208640974965732676168413

theorem tailTrace_8196299 : CollatzResearch.WordTrace tailWord_8196299 prefixEnd_8196299 4208640974965732676168413 := by
  unfold tailWord_8196299
  simp only [CollatzResearch.WordTrace]
  refine ⟨298943583733216014269231951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199295722488810676179487967 298943583733216014269231951)
  ·
    refine ⟨448415375599824021403847927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298943583733216014269231951 448415375599824021403847927)
    ·
      refine ⟨672623063399736032105771891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448415375599824021403847927 672623063399736032105771891)
      ·
        refine ⟨1008934595099604048158657837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 672623063399736032105771891 1008934595099604048158657837)
        ·
          refine ⟨378350473162351518059496689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1008934595099604048158657837 378350473162351518059496689)
          ·
            refine ⟨283762854871763638544622517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 378350473162351518059496689 283762854871763638544622517)
            ·
              refine ⟨26602767644227841113558361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 283762854871763638544622517 26602767644227841113558361)
              ·
                refine ⟨19952075733170880835168771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26602767644227841113558361 19952075733170880835168771)
                ·
                  refine ⟨29928113599756321252753157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19952075733170880835168771 29928113599756321252753157)
                  ·
                    refine ⟨5611521299954310234891217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29928113599756321252753157 5611521299954310234891217)
                    ·
                      refine ⟨4208640974965732676168413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5611521299954310234891217 4208640974965732676168413)
                      ·
                        rfl

theorem cell23_8196299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 4, 2].length) (baseStart_8196299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8196299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8196299 prefixEnd_8196299 := by exact prefixLift 8196299
  have htrace : WordTrace (prefixWord ++ tailWord_8196299) baseStart_8196299 baseEnd_8196299 := by
    simpa [prefixWord, tailWord_8196299, baseEnd_8196299] using wordTrace_append hprefix tailTrace_8196299
  have hstable : (prefixWord ++ tailWord_8196299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8196299).length < 2 ^ (prefixWord ++ tailWord_8196299).sum := by decide
  have hdescent : baseEnd_8196299 < baseStart_8196299 := by decide
  rcases family_descends (prefixWord ++ tailWord_8196299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8196310 : List Nat := [5, 2, 1, 2, 1, 2, 2, 2, 2, 1, 3]
def baseStart_8196310 : Nat := 118140960795 + 8196310 * 2 ^ 59
def prefixEnd_8196310 : Nat := 4983230072969 + 3 ^ 40 * 8196310 * 2
def baseEnd_8196310 : Nat := 4208646623252932133130863

theorem tailTrace_8196310 : CollatzResearch.WordTrace tailWord_8196310 prefixEnd_8196310 4208646623252932133130863 := by
  unfold tailWord_8196310
  simp only [CollatzResearch.WordTrace]
  refine ⟨18683999058511010196742649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199295989957450775431921589 18683999058511010196742649)
  ·
    refine ⟨14012999293883257647556987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18683999058511010196742649 14012999293883257647556987)
    ·
      refine ⟨21019498940824886471335481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14012999293883257647556987 21019498940824886471335481)
      ·
        refine ⟨15764624205618664853501611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21019498940824886471335481 15764624205618664853501611)
        ·
          refine ⟨23646936308427997280252417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15764624205618664853501611 23646936308427997280252417)
          ·
            refine ⟨17735202231320997960189313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23646936308427997280252417 17735202231320997960189313)
            ·
              refine ⟨13301401673490748470141985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17735202231320997960189313 13301401673490748470141985)
              ·
                refine ⟨9976051255118061352606489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13301401673490748470141985 9976051255118061352606489)
                ·
                  refine ⟨7482038441338546014454867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9976051255118061352606489 7482038441338546014454867)
                  ·
                    refine ⟨11223057662007819021682301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7482038441338546014454867 11223057662007819021682301)
                    ·
                      refine ⟨4208646623252932133130863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11223057662007819021682301 4208646623252932133130863)
                      ·
                        rfl

theorem cell23_8196310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_8196310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8196310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8196310 prefixEnd_8196310 := by exact prefixLift 8196310
  have htrace : WordTrace (prefixWord ++ tailWord_8196310) baseStart_8196310 baseEnd_8196310 := by
    simpa [prefixWord, tailWord_8196310, baseEnd_8196310] using wordTrace_append hprefix tailTrace_8196310
  have hstable : (prefixWord ++ tailWord_8196310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8196310).length < 2 ^ (prefixWord ++ tailWord_8196310).sum := by decide
  have hdescent : baseEnd_8196310 < baseStart_8196310 := by decide
  rcases family_descends (prefixWord ++ tailWord_8196310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8196315 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 9]
def baseStart_8196315 : Nat := 118140960795 + 8196315 * 2 ^ 59
def prefixEnd_8196315 : Nat := 4983230072969 + 3 ^ 40 * 8196315 * 2
def baseEnd_8196315 : Nat := 4208649190656204613568339

theorem tailTrace_8196315 : CollatzResearch.WordTrace tailWord_8196315 prefixEnd_8196315 4208649190656204613568339 := by
  unfold tailWord_8196315
  simp only [CollatzResearch.WordTrace]
  refine ⟨298944167301158049001814399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199296111534105366001209599 298944167301158049001814399)
  ·
    refine ⟨448416250951737073502721599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298944167301158049001814399 448416250951737073502721599)
    ·
      refine ⟨672624376427605610254082399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448416250951737073502721599 672624376427605610254082399)
      ·
        refine ⟨1008936564641408415381123599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 672624376427605610254082399 1008936564641408415381123599)
        ·
          refine ⟨1513404846962112623071685399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1008936564641408415381123599 1513404846962112623071685399)
          ·
            refine ⟨2270107270443168934607528099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1513404846962112623071685399 2270107270443168934607528099)
            ·
              refine ⟨3405160905664753401911292149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2270107270443168934607528099 3405160905664753401911292149)
              ·
                refine ⟨319233834906070631429183639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3405160905664753401911292149 319233834906070631429183639)
                ·
                  refine ⟨478850752359105947143775459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 319233834906070631429183639 478850752359105947143775459)
                  ·
                    refine ⟨718276128538658920715663189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 478850752359105947143775459 718276128538658920715663189)
                    ·
                      refine ⟨4208649190656204613568339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 718276128538658920715663189 4208649190656204613568339)
                      ·
                        rfl

theorem cell23_8196315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 9].length) (baseStart_8196315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8196315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8196315 prefixEnd_8196315 := by exact prefixLift 8196315
  have htrace : WordTrace (prefixWord ++ tailWord_8196315) baseStart_8196315 baseEnd_8196315 := by
    simpa [prefixWord, tailWord_8196315, baseEnd_8196315] using wordTrace_append hprefix tailTrace_8196315
  have hstable : (prefixWord ++ tailWord_8196315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8196315).length < 2 ^ (prefixWord ++ tailWord_8196315).sum := by decide
  have hdescent : baseEnd_8196315 < baseStart_8196315 := by decide
  rcases family_descends (prefixWord ++ tailWord_8196315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8196333 : List Nat := [1, 5, 1, 2, 3, 1, 2, 1, 1, 4, 2]
def baseStart_8196333 : Nat := 118140960795 + 8196333 * 2 ^ 59
def prefixEnd_8196333 : Nat := 4983230072969 + 3 ^ 40 * 8196333 * 2
def baseEnd_8196333 : Nat := 4208658433307985543143257

theorem tailTrace_8196333 : CollatzResearch.WordTrace tailWord_8196333 prefixEnd_8196333 4208658433307985543143257 := by
  unfold tailWord_8196333
  simp only [CollatzResearch.WordTrace]
  refine ⟨298944823815092838075969653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199296549210061892050646435 298944823815092838075969653)
  ·
    refine ⟨28026077232664953569622155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 298944823815092838075969653 28026077232664953569622155)
    ·
      refine ⟨42039115848997430354433233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28026077232664953569622155 42039115848997430354433233)
      ·
        refine ⟨31529336886748072765824925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42039115848997430354433233 31529336886748072765824925)
        ·
          refine ⟨11823501332530527287184347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31529336886748072765824925 11823501332530527287184347)
          ·
            refine ⟨17735251998795790930776521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11823501332530527287184347 17735251998795790930776521)
            ·
              refine ⟨13301438999096843198082391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17735251998795790930776521 13301438999096843198082391)
              ·
                refine ⟨19952158498645264797123587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13301438999096843198082391 19952158498645264797123587)
                ·
                  refine ⟨29928237747967897195685381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19952158498645264797123587 29928237747967897195685381)
                  ·
                    refine ⟨5611544577743980724191009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29928237747967897195685381 5611544577743980724191009)
                    ·
                      refine ⟨4208658433307985543143257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5611544577743980724191009 4208658433307985543143257)
                      ·
                        rfl

theorem cell23_8196333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_8196333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8196333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8196333 prefixEnd_8196333 := by exact prefixLift 8196333
  have htrace : WordTrace (prefixWord ++ tailWord_8196333) baseStart_8196333 baseEnd_8196333 := by
    simpa [prefixWord, tailWord_8196333, baseEnd_8196333] using wordTrace_append hprefix tailTrace_8196333
  have hstable : (prefixWord ++ tailWord_8196333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8196333).length < 2 ^ (prefixWord ++ tailWord_8196333).sum := by decide
  have hdescent : baseEnd_8196333 < baseStart_8196333 := by decide
  rcases family_descends (prefixWord ++ tailWord_8196333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8196362 : List Nat := [3, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5]
def baseStart_8196362 : Nat := 118140960795 + 8196362 * 2 ^ 59
def prefixEnd_8196362 : Nat := 4983230072969 + 3 ^ 40 * 8196362 * 2
def baseEnd_8196362 : Nat := 4208673324246965929680623

theorem tailTrace_8196362 : CollatzResearch.WordTrace tailWord_8196362 prefixEnd_8196362 4208673324246965929680623 := by
  unfold tailWord_8196362
  simp only [CollatzResearch.WordTrace]
  refine ⟨74736470382996944007193835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199297254354658517352516893 74736470382996944007193835)
  ·
    refine ⟨112104705574495416010790753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74736470382996944007193835 112104705574495416010790753)
    ·
      refine ⟨84078529180871562008093065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112104705574495416010790753 84078529180871562008093065)
      ·
        refine ⟨63058896885653671506069799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84078529180871562008093065 63058896885653671506069799)
        ·
          refine ⟨94588345328480507259104699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63058896885653671506069799 94588345328480507259104699)
          ·
            refine ⟨141882517992720760888657049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94588345328480507259104699 141882517992720760888657049)
            ·
              refine ⟨106411888494540570666492787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141882517992720760888657049 106411888494540570666492787)
              ·
                refine ⟨159617832741810855999739181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106411888494540570666492787 159617832741810855999739181)
                ·
                  refine ⟨59856687278179070999902193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159617832741810855999739181 59856687278179070999902193)
                  ·
                    refine ⟨44892515458634303249926645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59856687278179070999902193 44892515458634303249926645)
                    ·
                      refine ⟨4208673324246965929680623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44892515458634303249926645 4208673324246965929680623)
                      ·
                        rfl

theorem cell23_8196362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_8196362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8196362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8196362 prefixEnd_8196362 := by exact prefixLift 8196362
  have htrace : WordTrace (prefixWord ++ tailWord_8196362) baseStart_8196362 baseEnd_8196362 := by
    simpa [prefixWord, tailWord_8196362, baseEnd_8196362] using wordTrace_append hprefix tailTrace_8196362
  have hstable : (prefixWord ++ tailWord_8196362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8196362).length < 2 ^ (prefixWord ++ tailWord_8196362).sum := by decide
  have hdescent : baseEnd_8196362 < baseStart_8196362 := by decide
  rcases family_descends (prefixWord ++ tailWord_8196362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8196399 : List Nat := [1, 1, 2, 1, 2, 1, 6, 2, 3, 4]
def baseStart_8196399 : Nat := 118140960795 + 8196399 * 2 ^ 59
def prefixEnd_8196399 : Nat := 4983230072969 + 3 ^ 40 * 8196399 * 2
def baseEnd_8196399 : Nat := 1402897441010394094972651

theorem tailTrace_8196399 : CollatzResearch.WordTrace tailWord_8196399 prefixEnd_8196399 1402897441010394094972651 := by
  unfold tailWord_8196399
  simp only [CollatzResearch.WordTrace]
  refine ⟨298947231032853731347872251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199298154021902487565248167 298947231032853731347872251)
  ·
    refine ⟨448420846549280597021808377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298947231032853731347872251 448420846549280597021808377)
    ·
      refine ⟨336315634911960447766356283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 448420846549280597021808377 336315634911960447766356283)
      ·
        refine ⟨504473452367940671649534425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336315634911960447766356283 504473452367940671649534425)
        ·
          refine ⟨378355089275955503737150819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 504473452367940671649534425 378355089275955503737150819)
          ·
            refine ⟨567532633913933255605726229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378355089275955503737150819 567532633913933255605726229)
            ·
              refine ⟨26603092214715621356518417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 567532633913933255605726229 26603092214715621356518417)
              ·
                refine ⟨19952319161036716017388813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26603092214715621356518417 19952319161036716017388813)
                ·
                  refine ⟨7482119685388768506520805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19952319161036716017388813 7482119685388768506520805)
                  ·
                    refine ⟨1402897441010394094972651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7482119685388768506520805 1402897441010394094972651)
                    ·
                      rfl

theorem cell23_8196399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 3, 4].length) (baseStart_8196399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8196399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8196399 prefixEnd_8196399 := by exact prefixLift 8196399
  have htrace : WordTrace (prefixWord ++ tailWord_8196399) baseStart_8196399 baseEnd_8196399 := by
    simpa [prefixWord, tailWord_8196399, baseEnd_8196399] using wordTrace_append hprefix tailTrace_8196399
  have hstable : (prefixWord ++ tailWord_8196399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8196399).length < 2 ^ (prefixWord ++ tailWord_8196399).sum := by decide
  have hdescent : baseEnd_8196399 < baseStart_8196399 := by decide
  rcases family_descends (prefixWord ++ tailWord_8196399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8196412 : List Nat := [2, 2, 2, 2, 1, 2, 1, 1, 10]
def baseStart_8196412 : Nat := 118140960795 + 8196412 * 2 ^ 59
def prefixEnd_8196412 : Nat := 4983230072969 + 3 ^ 40 * 8196412 * 2
def baseEnd_8196412 : Nat := 467633222031076748228377

theorem tailTrace_8196412 : CollatzResearch.WordTrace tailWord_8196412 prefixEnd_8196412 467633222031076748228377 := by
  unfold tailWord_8196412
  simp only [CollatzResearch.WordTrace]
  refine ⟨149473852590903317284047745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199298470121204423045396993 149473852590903317284047745)
  ·
    refine ⟨112105389443177487963035809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149473852590903317284047745 112105389443177487963035809)
    ·
      refine ⟨84079042082383115972276857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112105389443177487963035809 84079042082383115972276857)
      ·
        refine ⟨63059281561787336979207643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84079042082383115972276857 63059281561787336979207643)
        ·
          refine ⟨94588922342681005468811465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63059281561787336979207643 94588922342681005468811465)
          ·
            refine ⟨70941691757010754101608599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94588922342681005468811465 70941691757010754101608599)
            ·
              refine ⟨106412537635516131152412899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70941691757010754101608599 106412537635516131152412899)
              ·
                refine ⟨159618806453274196728619349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106412537635516131152412899 159618806453274196728619349)
                ·
                  refine ⟨467633222031076748228377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 159618806453274196728619349 467633222031076748228377)
                  ·
                    rfl

theorem cell23_8196412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 10].length) (baseStart_8196412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8196412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8196412 prefixEnd_8196412 := by exact prefixLift 8196412
  have htrace : WordTrace (prefixWord ++ tailWord_8196412) baseStart_8196412 baseEnd_8196412 := by
    simpa [prefixWord, tailWord_8196412, baseEnd_8196412] using wordTrace_append hprefix tailTrace_8196412
  have hstable : (prefixWord ++ tailWord_8196412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8196412).length < 2 ^ (prefixWord ++ tailWord_8196412).sum := by decide
  have hdescent : baseEnd_8196412 < baseStart_8196412 := by decide
  rcases family_descends (prefixWord ++ tailWord_8196412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8196416 : List Nat := [2, 1, 1, 2, 2, 1, 2, 7, 1, 4]
def baseStart_8196416 : Nat := 118140960795 + 8196416 * 2 ^ 59
def prefixEnd_8196416 : Nat := 4983230072969 + 3 ^ 40 * 8196416 * 2
def baseEnd_8196416 : Nat := 1402900350734102906135125

theorem tailTrace_8196416 : CollatzResearch.WordTrace tailWord_8196416 prefixEnd_8196416 1402900350734102906135125 := by
  unfold tailWord_8196416
  simp only [CollatzResearch.WordTrace]
  refine ⟨149473925536896071625620551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199298567382528095500827401 149473925536896071625620551)
  ·
    refine ⟨224210888305344107438430827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149473925536896071625620551 224210888305344107438430827)
    ·
      refine ⟨336316332458016161157646241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224210888305344107438430827 336316332458016161157646241)
      ·
        refine ⟨252237249343512120868234681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336316332458016161157646241 252237249343512120868234681)
        ·
          refine ⟨189177937007634090651176011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252237249343512120868234681 189177937007634090651176011)
          ·
            refine ⟨283766905511451135976764017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189177937007634090651176011 283766905511451135976764017)
            ·
              refine ⟨212825179133588351982573013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283766905511451135976764017 212825179133588351982573013)
              ·
                refine ⟨4988090135943476999591555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 212825179133588351982573013 4988090135943476999591555)
                ·
                  refine ⟨7482135203915215499387333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4988090135943476999591555 7482135203915215499387333)
                  ·
                    refine ⟨1402900350734102906135125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7482135203915215499387333 1402900350734102906135125)
                    ·
                      rfl

theorem cell23_8196416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 7, 1, 4].length) (baseStart_8196416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8196416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8196416 prefixEnd_8196416 := by exact prefixLift 8196416
  have htrace : WordTrace (prefixWord ++ tailWord_8196416) baseStart_8196416 baseEnd_8196416 := by
    simpa [prefixWord, tailWord_8196416, baseEnd_8196416] using wordTrace_append hprefix tailTrace_8196416
  have hstable : (prefixWord ++ tailWord_8196416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8196416).length < 2 ^ (prefixWord ++ tailWord_8196416).sum := by decide
  have hdescent : baseEnd_8196416 < baseStart_8196416 := by decide
  rcases family_descends (prefixWord ++ tailWord_8196416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8196442 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 2, 9]
def baseStart_8196442 : Nat := 118140960795 + 8196442 * 2 ^ 59
def prefixEnd_8196442 : Nat := 4983230072969 + 3 ^ 40 * 8196442 * 2
def baseEnd_8196442 : Nat := 1402904800899775205560085

theorem tailTrace_8196442 : CollatzResearch.WordTrace tailWord_8196442 prefixEnd_8196442 1402904800899775205560085 := by
  unfold tailWord_8196442
  simp only [CollatzResearch.WordTrace]
  refine ⟨74737199842924487422921895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199299199581131966461125053 74737199842924487422921895)
  ·
    refine ⟨112105799764386731134382843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74737199842924487422921895 112105799764386731134382843)
    ·
      refine ⟨168158699646580096701574265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112105799764386731134382843 168158699646580096701574265)
      ·
        refine ⟨126119024734935072526180699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168158699646580096701574265 126119024734935072526180699)
        ·
          refine ⟨189178537102402608789271049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126119024734935072526180699 189178537102402608789271049)
          ·
            refine ⟨141883902826801956591953287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189178537102402608789271049 141883902826801956591953287)
            ·
              refine ⟨212825854240202934887929931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141883902826801956591953287 212825854240202934887929931)
              ·
                refine ⟨319238781360304402331894897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212825854240202934887929931 319238781360304402331894897)
                ·
                  refine ⟨239429086020228301748921173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 319238781360304402331894897 239429086020228301748921173)
                  ·
                    refine ⟨1402904800899775205560085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 239429086020228301748921173 1402904800899775205560085)
                    ·
                      rfl

theorem cell23_8196442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 2, 9].length) (baseStart_8196442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8196442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8196442 prefixEnd_8196442 := by exact prefixLift 8196442
  have htrace : WordTrace (prefixWord ++ tailWord_8196442) baseStart_8196442 baseEnd_8196442 := by
    simpa [prefixWord, tailWord_8196442, baseEnd_8196442] using wordTrace_append hprefix tailTrace_8196442
  have hstable : (prefixWord ++ tailWord_8196442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8196442).length < 2 ^ (prefixWord ++ tailWord_8196442).sum := by decide
  have hdescent : baseEnd_8196442 < baseStart_8196442 := by decide
  rcases family_descends (prefixWord ++ tailWord_8196442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8196473 : List Nat := [1, 2, 1, 3, 2, 1, 1, 7, 1, 1, 3]
def baseStart_8196473 : Nat := 118140960795 + 8196473 * 2 ^ 59
def prefixEnd_8196473 : Nat := 4983230072969 + 3 ^ 40 * 8196473 * 2
def baseEnd_8196473 : Nat := 4208730320599614995392613

theorem tailTrace_8196473 : CollatzResearch.WordTrace tailWord_8196473 prefixEnd_8196473 4208730320599614995392613 := by
  unfold tailWord_8196473
  simp only [CollatzResearch.WordTrace]
  refine ⟨298949930034585641986066073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199299953356390427990710715 298949930034585641986066073)
  ·
    refine ⟨224212447525939231489549555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298949930034585641986066073 224212447525939231489549555)
    ·
      refine ⟨336318671288908847234324333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224212447525939231489549555 336318671288908847234324333)
      ·
        refine ⟨126119501733340817712871625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 336318671288908847234324333 126119501733340817712871625)
        ·
          refine ⟨94589626300005613284653719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126119501733340817712871625 94589626300005613284653719)
          ·
            refine ⟨141884439450008419926980579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94589626300005613284653719 141884439450008419926980579)
            ·
              refine ⟨212826659175012629890470869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141884439450008419926980579 212826659175012629890470869)
              ·
                refine ⟨4988124824414358513057911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 212826659175012629890470869 4988124824414358513057911)
                ·
                  refine ⟨7482187236621537769586867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4988124824414358513057911 7482187236621537769586867)
                  ·
                    refine ⟨11223280854932306654380301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7482187236621537769586867 11223280854932306654380301)
                    ·
                      refine ⟨4208730320599614995392613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11223280854932306654380301 4208730320599614995392613)
                      ·
                        rfl

theorem cell23_8196473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 7, 1, 1, 3].length) (baseStart_8196473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8196473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8196473 prefixEnd_8196473 := by exact prefixLift 8196473
  have htrace : WordTrace (prefixWord ++ tailWord_8196473) baseStart_8196473 baseEnd_8196473 := by
    simpa [prefixWord, tailWord_8196473, baseEnd_8196473] using wordTrace_append hprefix tailTrace_8196473
  have hstable : (prefixWord ++ tailWord_8196473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8196473).length < 2 ^ (prefixWord ++ tailWord_8196473).sum := by decide
  have hdescent : baseEnd_8196473 < baseStart_8196473 := by decide
  rcases family_descends (prefixWord ++ tailWord_8196473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8196506 : List Nat := [3, 1, 1, 4, 1, 3, 2, 1, 1, 6]
def baseStart_8196506 : Nat := 118140960795 + 8196506 * 2 ^ 59
def prefixEnd_8196506 : Nat := 4983230072969 + 3 ^ 40 * 8196506 * 2
def baseEnd_8196506 : Nat := 1402915755153737788759987

theorem tailTrace_8196506 : CollatzResearch.WordTrace tailWord_8196506 prefixEnd_8196506 1402915755153737788759987 := by
  unfold tailWord_8196506
  simp only [CollatzResearch.WordTrace]
  refine ⟨74737783410866522155504343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199300755762310725748011581 74737783410866522155504343)
  ·
    refine ⟨112106675116299783233256515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74737783410866522155504343 112106675116299783233256515)
    ·
      refine ⟨168160012674449674849884773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112106675116299783233256515 168160012674449674849884773)
      ·
        refine ⟨31530002376459314034353395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168160012674449674849884773 31530002376459314034353395)
        ·
          refine ⟨47295003564688971051530093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31530002376459314034353395 47295003564688971051530093)
          ·
            refine ⟨17735626336758364144323785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47295003564688971051530093 17735626336758364144323785)
            ·
              refine ⟨13301719752568773108242839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17735626336758364144323785 13301719752568773108242839)
              ·
                refine ⟨19952579628853159662364259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13301719752568773108242839 19952579628853159662364259)
                ·
                  refine ⟨29928869443279739493546389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19952579628853159662364259 29928869443279739493546389)
                  ·
                    refine ⟨1402915755153737788759987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29928869443279739493546389 1402915755153737788759987)
                    ·
                      rfl

theorem cell23_8196506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 1, 6].length) (baseStart_8196506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8196506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8196506 prefixEnd_8196506 := by exact prefixLift 8196506
  have htrace : WordTrace (prefixWord ++ tailWord_8196506) baseStart_8196506 baseEnd_8196506 := by
    simpa [prefixWord, tailWord_8196506, baseEnd_8196506] using wordTrace_append hprefix tailTrace_8196506
  have hstable : (prefixWord ++ tailWord_8196506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8196506).length < 2 ^ (prefixWord ++ tailWord_8196506).sum := by decide
  have hdescent : baseEnd_8196506 < baseStart_8196506 := by decide
  rcases family_descends (prefixWord ++ tailWord_8196506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8196516 : List Nat := [2, 3, 1, 2, 1, 1, 4, 1, 3, 2, 3]
def baseStart_8196516 : Nat := 118140960795 + 8196516 * 2 ^ 59
def prefixEnd_8196516 : Nat := 4983230072969 + 3 ^ 40 * 8196516 * 2
def baseEnd_8196516 : Nat := 4208752400267758327154915

theorem tailTrace_8196516 : CollatzResearch.WordTrace tailWord_8196516 prefixEnd_8196516 4208752400267758327154915 := by
  unfold tailWord_8196516
  simp only [CollatzResearch.WordTrace]
  refine ⟨149475749186714930164940701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199300998915619906886587601 149475749186714930164940701)
  ·
    refine ⟨56053405945018098811852763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149475749186714930164940701 56053405945018098811852763)
    ·
      refine ⟨84080108917527148217779145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56053405945018098811852763 84080108917527148217779145)
      ·
        refine ⟨63060081688145361163334359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84080108917527148217779145 63060081688145361163334359)
        ·
          refine ⟨94590122532218041745001539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63060081688145361163334359 94590122532218041745001539)
          ·
            refine ⟨141885183798327062617502309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94590122532218041745001539 141885183798327062617502309)
            ·
              refine ⟨26603471962186324240781683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141885183798327062617502309 26603471962186324240781683)
              ·
                refine ⟨39905207943279486361172525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26603471962186324240781683 39905207943279486361172525)
                ·
                  refine ⟨14964452978729807385439697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39905207943279486361172525 14964452978729807385439697)
                  ·
                    refine ⟨11223339734047355539079773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14964452978729807385439697 11223339734047355539079773)
                    ·
                      refine ⟨4208752400267758327154915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11223339734047355539079773 4208752400267758327154915)
                      ·
                        rfl

theorem cell23_8196516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_8196516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8196516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8196516 prefixEnd_8196516 := by exact prefixLift 8196516
  have htrace : WordTrace (prefixWord ++ tailWord_8196516) baseStart_8196516 baseEnd_8196516 := by
    simpa [prefixWord, tailWord_8196516, baseEnd_8196516] using wordTrace_append hprefix tailTrace_8196516
  have hstable : (prefixWord ++ tailWord_8196516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8196516).length < 2 ^ (prefixWord ++ tailWord_8196516).sum := by decide
  have hdescent : baseEnd_8196516 < baseStart_8196516 := by decide
  rcases family_descends (prefixWord ++ tailWord_8196516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8196540 : List Nat := [2, 2, 2, 4, 1, 3, 1, 2, 2, 4]
def baseStart_8196540 : Nat := 118140960795 + 8196540 * 2 ^ 59
def prefixEnd_8196540 : Nat := 4983230072969 + 3 ^ 40 * 8196540 * 2
def baseEnd_8196540 : Nat := 1402921574601155411084935

theorem tailTrace_8196540 : CollatzResearch.WordTrace tailWord_8196540 prefixEnd_8196540 1402921574601155411084935 := by
  unfold tailWord_8196540
  simp only [CollatzResearch.WordTrace]
  refine ⟨149476186862671456214377537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199301582483561941619170049 149476186862671456214377537)
  ·
    refine ⟨112107140147003592160783153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149476186862671456214377537 112107140147003592160783153)
    ·
      refine ⟨84080355110252694120587365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112107140147003592160783153 84080355110252694120587365)
      ·
        refine ⟨15765066583172380147610131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84080355110252694120587365 15765066583172380147610131)
        ·
          refine ⟨23647599874758570221415197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15765066583172380147610131 23647599874758570221415197)
          ·
            refine ⟨8867849953034463833030699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23647599874758570221415197 8867849953034463833030699)
            ·
              refine ⟨13301774929551695749546049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8867849953034463833030699 13301774929551695749546049)
              ·
                refine ⟨9976331197163771812159537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13301774929551695749546049 9976331197163771812159537)
                ·
                  refine ⟨7482248397872828859119653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9976331197163771812159537 7482248397872828859119653)
                  ·
                    refine ⟨1402921574601155411084935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7482248397872828859119653 1402921574601155411084935)
                    ·
                      rfl

theorem cell23_8196540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 2, 2, 4].length) (baseStart_8196540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8196540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8196540 prefixEnd_8196540 := by exact prefixLift 8196540
  have htrace : WordTrace (prefixWord ++ tailWord_8196540) baseStart_8196540 baseEnd_8196540 := by
    simpa [prefixWord, tailWord_8196540, baseEnd_8196540] using wordTrace_append hprefix tailTrace_8196540
  have hstable : (prefixWord ++ tailWord_8196540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8196540).length < 2 ^ (prefixWord ++ tailWord_8196540).sum := by decide
  have hdescent : baseEnd_8196540 < baseStart_8196540 := by decide
  rcases family_descends (prefixWord ++ tailWord_8196540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8196581 : List Nat := [1, 3, 1, 5, 3, 1, 1, 3, 1, 2, 2]
def baseStart_8196581 : Nat := 118140960795 + 8196581 * 2 ^ 59
def prefixEnd_8196581 : Nat := 4983230072969 + 3 ^ 40 * 8196581 * 2
def baseEnd_8196581 : Nat := 4208785776510300572842117

theorem tailTrace_8196581 : CollatzResearch.WordTrace tailWord_8196581 prefixEnd_8196581 4208785776510300572842117 := by
  unfold tailWord_8196581
  simp only [CollatzResearch.WordTrace]
  refine ⟨298953869118194376430997597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199302579412129584287331731 298953869118194376430997597)
  ·
    refine ⟨112107700919322891161624099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298953869118194376430997597 112107700919322891161624099)
    ·
      refine ⟨168161551378984336742436149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112107700919322891161624099 168161551378984336742436149)
      ·
        refine ⟨15765145441779781569603389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 168161551378984336742436149 15765145441779781569603389)
        ·
          refine ⟨5911929540667418088601271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15765145441779781569603389 5911929540667418088601271)
          ·
            refine ⟨8867894311001127132901907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5911929540667418088601271 8867894311001127132901907)
            ·
              refine ⟨13301841466501690699352861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8867894311001127132901907 13301841466501690699352861)
              ·
                refine ⟨4988190549938134012257323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13301841466501690699352861 4988190549938134012257323)
                ·
                  refine ⟨7482285824907201018385985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4988190549938134012257323 7482285824907201018385985)
                  ·
                    refine ⟨5611714368680400763789489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7482285824907201018385985 5611714368680400763789489)
                    ·
                      refine ⟨4208785776510300572842117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5611714368680400763789489 4208785776510300572842117)
                      ·
                        rfl

theorem cell23_8196581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_8196581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8196581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8196581 prefixEnd_8196581 := by exact prefixLift 8196581
  have htrace : WordTrace (prefixWord ++ tailWord_8196581) baseStart_8196581 baseEnd_8196581 := by
    simpa [prefixWord, tailWord_8196581, baseEnd_8196581] using wordTrace_append hprefix tailTrace_8196581
  have hstable : (prefixWord ++ tailWord_8196581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8196581).length < 2 ^ (prefixWord ++ tailWord_8196581).sum := by decide
  have hdescent : baseEnd_8196581 < baseStart_8196581 := by decide
  rcases family_descends (prefixWord ++ tailWord_8196581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8196590 : List Nat := [4, 1, 2, 1, 2, 2, 2, 3, 1, 3, 2]
def baseStart_8196590 : Nat := 118140960795 + 8196590 * 2 ^ 59
def prefixEnd_8196590 : Nat := 4983230072969 + 3 ^ 40 * 8196590 * 2
def baseEnd_8196590 : Nat := 4208790397836191037629575

theorem tailTrace_8196590 : CollatzResearch.WordTrace tailWord_8196590 prefixEnd_8196590 4208790397836191037629575 := by
  unfold tailWord_8196590
  simp only [CollatzResearch.WordTrace]
  refine ⟨37369274671895221371009403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199302798250107847312050149 37369274671895221371009403)
  ·
    refine ⟨56053912007842832056514105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37369274671895221371009403 56053912007842832056514105)
    ·
      refine ⟨42040434005882124042385579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56053912007842832056514105 42040434005882124042385579)
      ·
        refine ⟨63060651008823186063578369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42040434005882124042385579 63060651008823186063578369)
        ·
          refine ⟨47295488256617389547683777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63060651008823186063578369 47295488256617389547683777)
          ·
            refine ⟨35471616192463042160762833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47295488256617389547683777 35471616192463042160762833)
            ·
              refine ⟨26603712144347281620572125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35471616192463042160762833 26603712144347281620572125)
              ·
                refine ⟨9976392054130230607714547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26603712144347281620572125 9976392054130230607714547)
                ·
                  refine ⟨14964588081195345911571821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9976392054130230607714547 14964588081195345911571821)
                  ·
                    refine ⟨5611720530448254716839433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14964588081195345911571821 5611720530448254716839433)
                    ·
                      refine ⟨4208790397836191037629575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5611720530448254716839433 4208790397836191037629575)
                      ·
                        rfl

theorem cell23_8196590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 3, 1, 3, 2].length) (baseStart_8196590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8196590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8196590 prefixEnd_8196590 := by exact prefixLift 8196590
  have htrace : WordTrace (prefixWord ++ tailWord_8196590) baseStart_8196590 baseEnd_8196590 := by
    simpa [prefixWord, tailWord_8196590, baseEnd_8196590] using wordTrace_append hprefix tailTrace_8196590
  have hstable : (prefixWord ++ tailWord_8196590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8196590).length < 2 ^ (prefixWord ++ tailWord_8196590).sum := by decide
  have hdescent : baseEnd_8196590 < baseStart_8196590 := by decide
  rcases family_descends (prefixWord ++ tailWord_8196590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8196654 : List Nat := [4, 1, 3, 1, 3, 1, 2, 2, 2, 2, 2]
def baseStart_8196654 : Nat := 118140960795 + 8196654 * 2 ^ 59
def prefixEnd_8196654 : Nat := 4983230072969 + 3 ^ 40 * 8196654 * 2
def baseEnd_8196654 : Nat := 4208823260598078787229281

theorem tailTrace_8196654 : CollatzResearch.WordTrace tailWord_8196654 prefixEnd_8196654 4208823260598078787229281 := by
  unfold tailWord_8196654
  simp only [CollatzResearch.WordTrace]
  refine ⟨37369566455866238737300627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199304354431286606598936677 37369566455866238737300627)
  ·
    refine ⟨56054349683799358105950941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37369566455866238737300627 56054349683799358105950941)
    ·
      refine ⟨21020381131424759289731603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56054349683799358105950941 21020381131424759289731603)
      ·
        refine ⟨31530571697137138934597405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21020381131424759289731603 31530571697137138934597405)
        ·
          refine ⟨11823964386426427100474027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31530571697137138934597405 11823964386426427100474027)
          ·
            refine ⟨17735946579639640650711041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11823964386426427100474027 17735946579639640650711041)
            ·
              refine ⟨13301959934729730488033281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17735946579639640650711041 13301959934729730488033281)
              ·
                refine ⟨9976469951047297866024961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13301959934729730488033281 9976469951047297866024961)
                ·
                  refine ⟨7482352463285473399518721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9976469951047297866024961 7482352463285473399518721)
                  ·
                    refine ⟨5611764347464105049639041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7482352463285473399518721 5611764347464105049639041)
                    ·
                      refine ⟨4208823260598078787229281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5611764347464105049639041 4208823260598078787229281)
                      ·
                        rfl

theorem cell23_8196654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_8196654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8196654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8196654 prefixEnd_8196654 := by exact prefixLift 8196654
  have htrace : WordTrace (prefixWord ++ tailWord_8196654) baseStart_8196654 baseEnd_8196654 := by
    simpa [prefixWord, tailWord_8196654, baseEnd_8196654] using wordTrace_append hprefix tailTrace_8196654
  have hstable : (prefixWord ++ tailWord_8196654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8196654).length < 2 ^ (prefixWord ++ tailWord_8196654).sum := by decide
  have hdescent : baseEnd_8196654 < baseStart_8196654 := by decide
  rcases family_descends (prefixWord ++ tailWord_8196654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8196656 : List Nat := [2, 1, 1, 1, 2, 3, 4, 2, 2, 5]
def baseStart_8196656 : Nat := 118140960795 + 8196656 * 2 ^ 59
def prefixEnd_8196656 : Nat := 4983230072969 + 3 ^ 40 * 8196656 * 2
def baseEnd_8196656 : Nat := 1402941429186462593134757

theorem tailTrace_8196656 : CollatzResearch.WordTrace tailWord_8196656 prefixEnd_8196656 1402941429186462593134757 := by
  unfold tailWord_8196656
  simp only [CollatzResearch.WordTrace]
  refine ⟨149478302296461332119988911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199304403061948442826651881 149478302296461332119988911)
  ·
    refine ⟨224217453444691998179983367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149478302296461332119988911 224217453444691998179983367)
    ·
      refine ⟨336326180167037997269975051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224217453444691998179983367 336326180167037997269975051)
      ·
        refine ⟨504489270250556995904962577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336326180167037997269975051 504489270250556995904962577)
        ·
          refine ⟨378366952687917746928721933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 504489270250556995904962577 378366952687917746928721933)
          ·
            refine ⟨141887607257969155098270725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 378366952687917746928721933 141887607257969155098270725)
            ·
              refine ⟨26603926360869216580925761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141887607257969155098270725 26603926360869216580925761)
              ·
                refine ⟨19952944770651912435694321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26603926360869216580925761 19952944770651912435694321)
                ·
                  refine ⟨14964708577988934326770741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19952944770651912435694321 14964708577988934326770741)
                  ·
                    refine ⟨1402941429186462593134757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14964708577988934326770741 1402941429186462593134757)
                    ·
                      rfl

theorem cell23_8196656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 2, 5].length) (baseStart_8196656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8196656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8196656 prefixEnd_8196656 := by exact prefixLift 8196656
  have htrace : WordTrace (prefixWord ++ tailWord_8196656) baseStart_8196656 baseEnd_8196656 := by
    simpa [prefixWord, tailWord_8196656, baseEnd_8196656] using wordTrace_append hprefix tailTrace_8196656
  have hstable : (prefixWord ++ tailWord_8196656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8196656).length < 2 ^ (prefixWord ++ tailWord_8196656).sum := by decide
  have hdescent : baseEnd_8196656 < baseStart_8196656 := by decide
  rcases family_descends (prefixWord ++ tailWord_8196656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8196666 : List Nat := [3, 1, 1, 1, 3, 3, 2, 1, 1, 2, 5]
def baseStart_8196666 : Nat := 118140960795 + 8196666 * 2 ^ 59
def prefixEnd_8196666 : Nat := 4983230072969 + 3 ^ 40 * 8196666 * 2
def baseEnd_8196666 : Nat := 4208829422365932740279225

theorem tailTrace_8196666 : CollatzResearch.WordTrace tailWord_8196666 prefixEnd_8196666 4208829422365932740279225 := by
  unfold tailWord_8196666
  simp only [CollatzResearch.WordTrace]
  refine ⟨74739242330721608986960463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199304646215257623965227901 74739242330721608986960463)
  ·
    refine ⟨112108863496082413480440695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74739242330721608986960463 112108863496082413480440695)
    ·
      refine ⟨168163295244123620220661043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112108863496082413480440695 168163295244123620220661043)
      ·
        refine ⟨252244942866185430330991565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168163295244123620220661043 252244942866185430330991565)
        ·
          refine ⟨94591853574819536374121837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252244942866185430330991565 94591853574819536374121837)
          ·
            refine ⟨35471945090557326140295689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94591853574819536374121837 35471945090557326140295689)
            ·
              refine ⟨26603958817917994605221767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35471945090557326140295689 26603958817917994605221767)
              ·
                refine ⟨39905938226876991907832651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26603958817917994605221767 39905938226876991907832651)
                ·
                  refine ⟨59858907340315487861748977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39905938226876991907832651 59858907340315487861748977)
                  ·
                    refine ⟨44894180505236615896311733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59858907340315487861748977 44894180505236615896311733)
                    ·
                      refine ⟨4208829422365932740279225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44894180505236615896311733 4208829422365932740279225)
                      ·
                        rfl

theorem cell23_8196666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 1, 2, 5].length) (baseStart_8196666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8196666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8196666 prefixEnd_8196666 := by exact prefixLift 8196666
  have htrace : WordTrace (prefixWord ++ tailWord_8196666) baseStart_8196666 baseEnd_8196666 := by
    simpa [prefixWord, tailWord_8196666, baseEnd_8196666] using wordTrace_append hprefix tailTrace_8196666
  have hstable : (prefixWord ++ tailWord_8196666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8196666).length < 2 ^ (prefixWord ++ tailWord_8196666).sum := by decide
  have hdescent : baseEnd_8196666 < baseStart_8196666 := by decide
  rcases family_descends (prefixWord ++ tailWord_8196666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8196693 : List Nat := [1, 3, 2, 2, 1, 1, 5, 1, 2, 1, 4]
def baseStart_8196693 : Nat := 118140960795 + 8196693 * 2 ^ 59
def prefixEnd_8196693 : Nat := 4983230072969 + 3 ^ 40 * 8196693 * 2
def baseEnd_8196693 : Nat := 4208843286343604134641601

theorem tailTrace_8196693 : CollatzResearch.WordTrace tailWord_8196693 prefixEnd_8196693 4208843286343604134641601 := by
  unfold tailWord_8196693
  simp only [CollatzResearch.WordTrace]
  refine ⟨298957954093788619559074733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199305302729192413039383155 298957954093788619559074733)
  ·
    refine ⟨112109232785170732334653025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298957954093788619559074733 112109232785170732334653025)
    ·
      refine ⟨84081924588878049250989769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112109232785170732334653025 84081924588878049250989769)
      ·
        refine ⟨63061443441658536938242327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84081924588878049250989769 63061443441658536938242327)
        ·
          refine ⟨94592165162487805407363491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63061443441658536938242327 94592165162487805407363491)
          ·
            refine ⟨141888247743731708111045237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94592165162487805407363491 141888247743731708111045237)
            ·
              refine ⟨13302023225974847635410491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 141888247743731708111045237 13302023225974847635410491)
              ·
                refine ⟨19953034838962271453115737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13302023225974847635410491 19953034838962271453115737)
                ·
                  refine ⟨14964776129221703589836803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19953034838962271453115737 14964776129221703589836803)
                  ·
                    refine ⟨22447164193832555384755205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14964776129221703589836803 22447164193832555384755205)
                    ·
                      refine ⟨4208843286343604134641601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22447164193832555384755205 4208843286343604134641601)
                      ·
                        rfl

theorem cell23_8196693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_8196693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8196693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8196693 prefixEnd_8196693 := by exact prefixLift 8196693
  have htrace : WordTrace (prefixWord ++ tailWord_8196693) baseStart_8196693 baseEnd_8196693 := by
    simpa [prefixWord, tailWord_8196693, baseEnd_8196693] using wordTrace_append hprefix tailTrace_8196693
  have hstable : (prefixWord ++ tailWord_8196693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8196693).length < 2 ^ (prefixWord ++ tailWord_8196693).sum := by decide
  have hdescent : baseEnd_8196693 < baseStart_8196693 := by decide
  rcases family_descends (prefixWord ++ tailWord_8196693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8196720 : List Nat := [2, 1, 1, 1, 7, 1, 2, 1, 3, 4]
def baseStart_8196720 : Nat := 118140960795 + 8196720 * 2 ^ 59
def prefixEnd_8196720 : Nat := 4983230072969 + 3 ^ 40 * 8196720 * 2
def baseEnd_8196720 : Nat := 1402952383440425176334659

theorem tailTrace_8196720 : CollatzResearch.WordTrace tailWord_8196720 prefixEnd_8196720 1402952383440425176334659 := by
  unfold tailWord_8196720
  simp only [CollatzResearch.WordTrace]
  refine ⟨149479469432345401585153807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199305959243127202113538409 149479469432345401585153807)
  ·
    refine ⟨224219204148518102377730711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149479469432345401585153807 224219204148518102377730711)
    ·
      refine ⟨336328806222777153566596067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224219204148518102377730711 336328806222777153566596067)
      ·
        refine ⟨504493209334165730349894101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336328806222777153566596067 504493209334165730349894101)
        ·
          refine ⟨11824059593769509305075643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 504493209334165730349894101 11824059593769509305075643)
          ·
            refine ⟨17736089390654263957613465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11824059593769509305075643 17736089390654263957613465)
            ·
              refine ⟨13302067042990697968210099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17736089390654263957613465 13302067042990697968210099)
              ·
                refine ⟨19953100564486046952315149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13302067042990697968210099 19953100564486046952315149)
                ·
                  refine ⟨7482412711682267607118181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19953100564486046952315149 7482412711682267607118181)
                  ·
                    refine ⟨1402952383440425176334659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7482412711682267607118181 1402952383440425176334659)
                    ·
                      rfl

theorem cell23_8196720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 3, 4].length) (baseStart_8196720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8196720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8196720 prefixEnd_8196720 := by exact prefixLift 8196720
  have htrace : WordTrace (prefixWord ++ tailWord_8196720) baseStart_8196720 baseEnd_8196720 := by
    simpa [prefixWord, tailWord_8196720, baseEnd_8196720] using wordTrace_append hprefix tailTrace_8196720
  have hstable : (prefixWord ++ tailWord_8196720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8196720).length < 2 ^ (prefixWord ++ tailWord_8196720).sum := by decide
  have hdescent : baseEnd_8196720 < baseStart_8196720 := by decide
  rcases family_descends (prefixWord ++ tailWord_8196720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8196754 : List Nat := [3, 2, 3, 1, 2, 3, 1, 3, 1, 4]
def baseStart_8196754 : Nat := 118140960795 + 8196754 * 2 ^ 59
def prefixEnd_8196754 : Nat := 4983230072969 + 3 ^ 40 * 8196754 * 2
def baseEnd_8196754 : Nat := 1402958202887842798659607

theorem tailTrace_8196754 : CollatzResearch.WordTrace tailWord_8196754 prefixEnd_8196754 1402958202887842798659607 := by
  unfold tailWord_8196754
  simp only [CollatzResearch.WordTrace]
  refine ⟨74740044736641906744261329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199306785964378417984696877 74740044736641906744261329)
  ·
    refine ⟨56055033552481430058195997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74740044736641906744261329 56055033552481430058195997)
    ·
      refine ⟨21020637582180536271823499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56055033552481430058195997 21020637582180536271823499)
      ·
        refine ⟨31530956373270804407735249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21020637582180536271823499 31530956373270804407735249)
        ·
          refine ⟨23648217279953103305801437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31530956373270804407735249 23648217279953103305801437)
          ·
            refine ⟨8868081479982413739675539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23648217279953103305801437 8868081479982413739675539)
            ·
              refine ⟨13302122219973620609513309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8868081479982413739675539 13302122219973620609513309)
              ·
                refine ⟨4988295832490107728567491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13302122219973620609513309 4988295832490107728567491)
                ·
                  refine ⟨7482443748735161592851237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4988295832490107728567491 7482443748735161592851237)
                  ·
                    refine ⟨1402958202887842798659607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7482443748735161592851237 1402958202887842798659607)
                    ·
                      rfl

theorem cell23_8196754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_8196754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8196754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8196754 prefixEnd_8196754 := by exact prefixLift 8196754
  have htrace : WordTrace (prefixWord ++ tailWord_8196754) baseStart_8196754 baseEnd_8196754 := by
    simpa [prefixWord, tailWord_8196754, baseEnd_8196754] using wordTrace_append hprefix tailTrace_8196754
  have hstable : (prefixWord ++ tailWord_8196754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8196754).length < 2 ^ (prefixWord ++ tailWord_8196754).sum := by decide
  have hdescent : baseEnd_8196754 < baseStart_8196754 := by decide
  rcases family_descends (prefixWord ++ tailWord_8196754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8196800 : List Nat := [2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 4]
def baseStart_8196800 : Nat := 118140960795 + 8196800 * 2 ^ 59
def prefixEnd_8196800 : Nat := 4983230072969 + 3 ^ 40 * 8196800 * 2
def baseEnd_8196800 : Nat := 4208898228773635216003609

theorem tailTrace_8196800 : CollatzResearch.WordTrace tailWord_8196800 prefixEnd_8196800 4208898228773635216003609 := by
  unfold tailWord_8196800
  simp only [CollatzResearch.WordTrace]
  refine ⟨149480928352200488416609927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199307904469600651222146569 149480928352200488416609927)
  ·
    refine ⟨224221392528300732624914891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149480928352200488416609927 224221392528300732624914891)
    ·
      refine ⟨336332088792451098937372337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224221392528300732624914891 336332088792451098937372337)
      ·
        refine ⟨252249066594338324203029253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336332088792451098937372337 252249066594338324203029253)
        ·
          refine ⟨47296699986438435788067985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 252249066594338324203029253 47296699986438435788067985)
          ·
            refine ⟨35472524989828826841050989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47296699986438435788067985 35472524989828826841050989)
            ·
              refine ⟨13302196871185810065394121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35472524989828826841050989 13302196871185810065394121)
              ·
                refine ⟨9976647653389357549045591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13302196871185810065394121 9976647653389357549045591)
                ·
                  refine ⟨14964971480084036323568387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9976647653389357549045591 14964971480084036323568387)
                  ·
                    refine ⟨22447457220126054485352581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14964971480084036323568387 22447457220126054485352581)
                    ·
                      refine ⟨4208898228773635216003609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22447457220126054485352581 4208898228773635216003609)
                      ·
                        rfl

theorem cell23_8196800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 4].length) (baseStart_8196800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8196800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8196800 prefixEnd_8196800 := by exact prefixLift 8196800
  have htrace : WordTrace (prefixWord ++ tailWord_8196800) baseStart_8196800 baseEnd_8196800 := by
    simpa [prefixWord, tailWord_8196800, baseEnd_8196800] using wordTrace_append hprefix tailTrace_8196800
  have hstable : (prefixWord ++ tailWord_8196800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8196800).length < 2 ^ (prefixWord ++ tailWord_8196800).sum := by decide
  have hdescent : baseEnd_8196800 < baseStart_8196800 := by decide
  rcases family_descends (prefixWord ++ tailWord_8196800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8196828 : List Nat := [2, 2, 5, 1, 1, 3, 2, 2, 1, 1, 3]
def baseStart_8196828 : Nat := 118140960795 + 8196828 * 2 ^ 59
def prefixEnd_8196828 : Nat := 4983230072969 + 3 ^ 40 * 8196828 * 2
def baseEnd_8196828 : Nat := 4208912606231961106453481

theorem tailTrace_8196828 : CollatzResearch.WordTrace tailWord_8196828 prefixEnd_8196828 4208912606231961106453481 := by
  unfold tailWord_8196828
  simp only [CollatzResearch.WordTrace]
  refine ⟨149481438974149768807619569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199308585298866358410159425 149481438974149768807619569)
  ·
    refine ⟨112111079230612326605714677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149481438974149768807619569 112111079230612326605714677)
    ·
      refine ⟨10510413677869905619285751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 112111079230612326605714677 10510413677869905619285751)
      ·
        refine ⟨15765620516804858428928627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10510413677869905619285751 15765620516804858428928627)
        ·
          refine ⟨23648430775207287643392941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15765620516804858428928627 23648430775207287643392941)
          ·
            refine ⟨8868161540702732866272353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23648430775207287643392941 8868161540702732866272353)
            ·
              refine ⟨6651121155527049649704265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8868161540702732866272353 6651121155527049649704265)
              ·
                refine ⟨4988340866645287237278199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6651121155527049649704265 4988340866645287237278199)
                ·
                  refine ⟨7482511299967930855917299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4988340866645287237278199 7482511299967930855917299)
                  ·
                    refine ⟨11223766949951896283875949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7482511299967930855917299 11223766949951896283875949)
                    ·
                      refine ⟨4208912606231961106453481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11223766949951896283875949 4208912606231961106453481)
                      ·
                        rfl

theorem cell23_8196828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_8196828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8196828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8196828 prefixEnd_8196828 := by exact prefixLift 8196828
  have htrace : WordTrace (prefixWord ++ tailWord_8196828) baseStart_8196828 baseEnd_8196828 := by
    simpa [prefixWord, tailWord_8196828, baseEnd_8196828] using wordTrace_append hprefix tailTrace_8196828
  have hstable : (prefixWord ++ tailWord_8196828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8196828).length < 2 ^ (prefixWord ++ tailWord_8196828).sum := by decide
  have hdescent : baseEnd_8196828 < baseStart_8196828 := by decide
  rcases family_descends (prefixWord ++ tailWord_8196828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8196840 : List Nat := [2, 1, 4, 1, 4, 2, 1, 8]
def baseStart_8196840 : Nat := 118140960795 + 8196840 * 2 ^ 59
def prefixEnd_8196840 : Nat := 4983230072969 + 3 ^ 40 * 8196840 * 2
def baseEnd_8196840 : Nat := 155885880296289446648275

theorem tailTrace_8196840 : CollatzResearch.WordTrace tailWord_8196840 prefixEnd_8196840 155885880296289446648275 := by
  unfold tailWord_8196840
  simp only [CollatzResearch.WordTrace]
  refine ⟨149481657812128031832337987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199308877082837375776450649 149481657812128031832337987)
  ·
    refine ⟨224222486718192047748506981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149481657812128031832337987 224222486718192047748506981)
    ·
      refine ⟨42041716259661008952845059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224222486718192047748506981 42041716259661008952845059)
      ·
        refine ⟨63062574389491513429267589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42041716259661008952845059 63062574389491513429267589)
        ·
          refine ⟨11824232698029658767987673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63062574389491513429267589 11824232698029658767987673)
          ·
            refine ⟨8868174523522244075990755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11824232698029658767987673 8868174523522244075990755)
            ·
              refine ⟨13302261785283366113986133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8868174523522244075990755 13302261785283366113986133)
              ·
                refine ⟨155885880296289446648275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13302261785283366113986133 155885880296289446648275)
                ·
                  rfl

theorem cell23_8196840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 8].length) (baseStart_8196840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8196840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8196840 prefixEnd_8196840 := by exact prefixLift 8196840
  have htrace : WordTrace (prefixWord ++ tailWord_8196840) baseStart_8196840 baseEnd_8196840 := by
    simpa [prefixWord, tailWord_8196840, baseEnd_8196840] using wordTrace_append hprefix tailTrace_8196840
  have hstable : (prefixWord ++ tailWord_8196840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8196840).length < 2 ^ (prefixWord ++ tailWord_8196840).sum := by decide
  have hdescent : baseEnd_8196840 < baseStart_8196840 := by decide
  rcases family_descends (prefixWord ++ tailWord_8196840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8196850 : List Nat := [3, 2, 1, 3, 1, 2, 1, 3, 1, 3, 3]
def baseStart_8196850 : Nat := 118140960795 + 8196850 * 2 ^ 59
def prefixEnd_8196850 : Nat := 4983230072969 + 3 ^ 40 * 8196850 * 2
def baseEnd_8196850 : Nat := 4208923902806360020378379

theorem tailTrace_8196850 : CollatzResearch.WordTrace tailWord_8196850 prefixEnd_8196850 4208923902806360020378379 := by
  unfold tailWord_8196850
  simp only [CollatzResearch.WordTrace]
  refine ⟨74740920088554958843135001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199309120236146556915026669 74740920088554958843135001)
  ·
    refine ⟨56055690066416219132351251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74740920088554958843135001 56055690066416219132351251)
    ·
      refine ⟨84083535099624328698526877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56055690066416219132351251 84083535099624328698526877)
      ·
        refine ⟨31531325662359123261947579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84083535099624328698526877 31531325662359123261947579)
        ·
          refine ⟨47296988493538684892921369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31531325662359123261947579 47296988493538684892921369)
          ·
            refine ⟨35472741370154013669691027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47296988493538684892921369 35472741370154013669691027)
            ·
              refine ⟨53209112055231020504536541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35472741370154013669691027 53209112055231020504536541)
              ·
                refine ⟨19953417020711632689201203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53209112055231020504536541 19953417020711632689201203)
                ·
                  refine ⟨29930125531067449033801805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19953417020711632689201203 29930125531067449033801805)
                  ·
                    refine ⟨11223797074150293387675677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29930125531067449033801805 11223797074150293387675677)
                    ·
                      refine ⟨4208923902806360020378379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11223797074150293387675677 4208923902806360020378379)
                      ·
                        rfl

theorem cell23_8196850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_8196850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8196850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8196850 prefixEnd_8196850 := by exact prefixLift 8196850
  have htrace : WordTrace (prefixWord ++ tailWord_8196850) baseStart_8196850 baseEnd_8196850 := by
    simpa [prefixWord, tailWord_8196850, baseEnd_8196850] using wordTrace_append hprefix tailTrace_8196850
  have hstable : (prefixWord ++ tailWord_8196850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8196850).length < 2 ^ (prefixWord ++ tailWord_8196850).sum := by decide
  have hdescent : baseEnd_8196850 < baseStart_8196850 := by decide
  rcases family_descends (prefixWord ++ tailWord_8196850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8196913 : List Nat := [1, 2, 2, 3, 2, 1, 1, 4, 7]
def baseStart_8196913 : Nat := 118140960795 + 8196913 * 2 ^ 59
def prefixEnd_8196913 : Nat := 4983230072969 + 3 ^ 40 * 8196913 * 2
def baseEnd_8196913 : Nat := 467661805787510363765621

theorem tailTrace_8196913 : CollatzResearch.WordTrace tailWord_8196913 prefixEnd_8196913 467661805787510363765621 := by
  unfold tailWord_8196913
  simp only [CollatzResearch.WordTrace]
  refine ⟨298965978152991597132083393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199310652101994398088055595 298965978152991597132083393)
  ·
    refine ⟨224224483614743697849062545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298965978152991597132083393 224224483614743697849062545)
    ·
      refine ⟨168168362711057773386796909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224224483614743697849062545 168168362711057773386796909)
      ·
        refine ⟨63063136016646665020048841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168168362711057773386796909 63063136016646665020048841)
        ·
          refine ⟨47297352012484998765036631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63063136016646665020048841 47297352012484998765036631)
          ·
            refine ⟨70946028018727498147554947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47297352012484998765036631 70946028018727498147554947)
            ·
              refine ⟨106419042028091247221332421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70946028018727498147554947 106419042028091247221332421)
              ·
                refine ⟨19953570380267108853999829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106419042028091247221332421 19953570380267108853999829)
                ·
                  refine ⟨467661805787510363765621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19953570380267108853999829 467661805787510363765621)
                  ·
                    rfl

theorem cell23_8196913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 7].length) (baseStart_8196913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8196913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8196913 prefixEnd_8196913 := by exact prefixLift 8196913
  have htrace : WordTrace (prefixWord ++ tailWord_8196913) baseStart_8196913 baseEnd_8196913 := by
    simpa [prefixWord, tailWord_8196913, baseEnd_8196913] using wordTrace_append hprefix tailTrace_8196913
  have hstable : (prefixWord ++ tailWord_8196913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8196913).length < 2 ^ (prefixWord ++ tailWord_8196913).sum := by decide
  have hdescent : baseEnd_8196913 < baseStart_8196913 := by decide
  rcases family_descends (prefixWord ++ tailWord_8196913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8196953 : List Nat := [1, 2, 1, 2, 2, 4, 1, 1, 1, 1, 7]
def baseStart_8196953 : Nat := 118140960795 + 8196953 * 2 ^ 59
def prefixEnd_8196953 : Nat := 4983230072969 + 3 ^ 40 * 8196953 * 2
def baseEnd_8196953 : Nat := 4208976791313773117390405

theorem tailTrace_8196953 : CollatzResearch.WordTrace tailWord_8196953 prefixEnd_8196953 4208976791313773117390405 := by
  unfold tailWord_8196953
  simp only [CollatzResearch.WordTrace]
  refine ⟨298967437072846683963539513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199311624715231122642359675 298967437072846683963539513)
  ·
    refine ⟨224225577804635012972654635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298967437072846683963539513 224225577804635012972654635)
    ·
      refine ⟨336338366706952519458981953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224225577804635012972654635 336338366706952519458981953)
      ·
        refine ⟨252253775030214389594236465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336338366706952519458981953 252253775030214389594236465)
        ·
          refine ⟨189190331272660792195677349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252253775030214389594236465 189190331272660792195677349)
          ·
            refine ⟨35473187113623898536689503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189190331272660792195677349 35473187113623898536689503)
            ·
              refine ⟨53209780670435847805034255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35473187113623898536689503 53209780670435847805034255)
              ·
                refine ⟨79814671005653771707551383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53209780670435847805034255 79814671005653771707551383)
                ·
                  refine ⟨119722006508480657561327075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79814671005653771707551383 119722006508480657561327075)
                  ·
                    refine ⟨179583009762720986341990613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 119722006508480657561327075 179583009762720986341990613)
                    ·
                      refine ⟨4208976791313773117390405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 179583009762720986341990613 4208976791313773117390405)
                      ·
                        rfl

theorem cell23_8196953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 1, 7].length) (baseStart_8196953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8196953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8196953 prefixEnd_8196953 := by exact prefixLift 8196953
  have htrace : WordTrace (prefixWord ++ tailWord_8196953) baseStart_8196953 baseEnd_8196953 := by
    simpa [prefixWord, tailWord_8196953, baseEnd_8196953] using wordTrace_append hprefix tailTrace_8196953
  have hstable : (prefixWord ++ tailWord_8196953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8196953).length < 2 ^ (prefixWord ++ tailWord_8196953).sum := by decide
  have hdescent : baseEnd_8196953 < baseStart_8196953 := by decide
  rcases family_descends (prefixWord ++ tailWord_8196953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197003 : List Nat := [1, 1, 1, 1, 4, 2, 2, 3, 8]
def baseStart_8197003 : Nat := 118140960795 + 8197003 * 2 ^ 59
def prefixEnd_8197003 : Nat := 4983230072969 + 3 ^ 40 * 8197003 * 2
def baseEnd_8197003 : Nat := 467666940594055324640575

theorem tailTrace_8197003 : CollatzResearch.WordTrace tailWord_8197003 prefixEnd_8197003 467666940594055324640575 := by
  unfold tailWord_8197003
  simp only [CollatzResearch.WordTrace]
  refine ⟨298969260722665542502859663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199312840481777028335239775 298969260722665542502859663)
  ·
    refine ⟨448453891083998313754289495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298969260722665542502859663 448453891083998313754289495)
    ·
      refine ⟨672680836625997470631434243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448453891083998313754289495 672680836625997470631434243)
      ·
        refine ⟨1009021254938996205947151365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 672680836625997470631434243 1009021254938996205947151365)
        ·
          refine ⟨189191485301061788615090881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1009021254938996205947151365 189191485301061788615090881)
          ·
            refine ⟨141893613975796341461318161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189191485301061788615090881 141893613975796341461318161)
            ·
              refine ⟨106420210481847256095988621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141893613975796341461318161 106420210481847256095988621)
              ·
                refine ⟨39907578930692721035995733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106420210481847256095988621 39907578930692721035995733)
                ·
                  refine ⟨467666940594055324640575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39907578930692721035995733 467666940594055324640575)
                  ·
                    rfl

theorem cell23_8197003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 8].length) (baseStart_8197003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197003 prefixEnd_8197003 := by exact prefixLift 8197003
  have htrace : WordTrace (prefixWord ++ tailWord_8197003) baseStart_8197003 baseEnd_8197003 := by
    simpa [prefixWord, tailWord_8197003, baseEnd_8197003] using wordTrace_append hprefix tailTrace_8197003
  have hstable : (prefixWord ++ tailWord_8197003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197003).length < 2 ^ (prefixWord ++ tailWord_8197003).sum := by decide
  have hdescent : baseEnd_8197003 < baseStart_8197003 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197031 : List Nat := [1, 1, 6, 1, 4, 1, 1, 1, 2, 1, 4]
def baseStart_8197031 : Nat := 118140960795 + 8197031 * 2 ^ 59
def prefixEnd_8197031 : Nat := 4983230072969 + 3 ^ 40 * 8197031 * 2
def baseEnd_8197031 : Nat := 4209016842804823812215047

theorem tailTrace_8197031 : CollatzResearch.WordTrace tailWord_8197031 prefixEnd_8197031 4209016842804823812215047 := by
  unfold tailWord_8197031
  simp only [CollatzResearch.WordTrace]
  refine ⟨298970281966564103284878947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199313521311042735523252631 298970281966564103284878947)
  ·
    refine ⟨448455422949846154927318421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298970281966564103284878947 448455422949846154927318421)
    ·
      refine ⟨21021347950774038512218051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 448455422949846154927318421 21021347950774038512218051)
      ·
        refine ⟨31532021926161057768327077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21021347950774038512218051 31532021926161057768327077)
        ·
          refine ⟨5912254111155198331561327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31532021926161057768327077 5912254111155198331561327)
          ·
            refine ⟨8868381166732797497341991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5912254111155198331561327 8868381166732797497341991)
            ·
              refine ⟨13302571750099196246012987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8868381166732797497341991 13302571750099196246012987)
              ·
                refine ⟨19953857625148794369019481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13302571750099196246012987 19953857625148794369019481)
                ·
                  refine ⟨14965393218861595776764611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19953857625148794369019481 14965393218861595776764611)
                  ·
                    refine ⟨22448089828292393665146917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14965393218861595776764611 22448089828292393665146917)
                    ·
                      refine ⟨4209016842804823812215047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22448089828292393665146917 4209016842804823812215047)
                      ·
                        rfl

theorem cell23_8197031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_8197031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197031 prefixEnd_8197031 := by exact prefixLift 8197031
  have htrace : WordTrace (prefixWord ++ tailWord_8197031) baseStart_8197031 baseEnd_8197031 := by
    simpa [prefixWord, tailWord_8197031, baseEnd_8197031] using wordTrace_append hprefix tailTrace_8197031
  have hstable : (prefixWord ++ tailWord_8197031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197031).length < 2 ^ (prefixWord ++ tailWord_8197031).sum := by decide
  have hdescent : baseEnd_8197031 < baseStart_8197031 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197041 : List Nat := [1, 2, 2, 4, 3, 1, 2, 3, 1, 4]
def baseStart_8197041 : Nat := 118140960795 + 8197041 * 2 ^ 59
def prefixEnd_8197041 : Nat := 4983230072969 + 3 ^ 40 * 8197041 * 2
def baseEnd_8197041 : Nat := 1403007325870456257696667

theorem tailTrace_8197041 : CollatzResearch.WordTrace tailWord_8197041 prefixEnd_8197041 1403007325870456257696667 := by
  unfold tailWord_8197041
  simp only [CollatzResearch.WordTrace]
  refine ⟨298970646696527874992742977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199313764464351916661828651 298970646696527874992742977)
  ·
    refine ⟨224227985022395906244557233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298970646696527874992742977 224227985022395906244557233)
    ·
      refine ⟨168170988766796929683417925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224227985022395906244557233 168170988766796929683417925)
      ·
        refine ⟨31532060393774424315640861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168170988766796929683417925 31532060393774424315640861)
        ·
          refine ⟨11824522647665409118365323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31532060393774424315640861 11824522647665409118365323)
          ·
            refine ⟨17736783971498113677547985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11824522647665409118365323 17736783971498113677547985)
            ·
              refine ⟨13302587978623585258160989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17736783971498113677547985 13302587978623585258160989)
              ·
                refine ⟨4988470491983844471810371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13302587978623585258160989 4988470491983844471810371)
                ·
                  refine ⟨7482705737975766707715557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4988470491983844471810371 7482705737975766707715557)
                  ·
                    refine ⟨1403007325870456257696667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7482705737975766707715557 1403007325870456257696667)
                    ·
                      rfl

theorem cell23_8197041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 3, 1, 4].length) (baseStart_8197041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197041 prefixEnd_8197041 := by exact prefixLift 8197041
  have htrace : WordTrace (prefixWord ++ tailWord_8197041) baseStart_8197041 baseEnd_8197041 := by
    simpa [prefixWord, tailWord_8197041, baseEnd_8197041] using wordTrace_append hprefix tailTrace_8197041
  have hstable : (prefixWord ++ tailWord_8197041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197041).length < 2 ^ (prefixWord ++ tailWord_8197041).sum := by decide
  have hdescent : baseEnd_8197041 < baseStart_8197041 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197074 : List Nat := [3, 2, 2, 3, 1, 1, 1, 2, 1, 5, 2]
def baseStart_8197074 : Nat := 118140960795 + 8197074 * 2 ^ 59
def prefixEnd_8197074 : Nat := 4983230072969 + 3 ^ 40 * 8197074 * 2
def baseEnd_8197074 : Nat := 4209038922472967143977349

theorem tailTrace_8197074 : CollatzResearch.WordTrace tailWord_8197074 prefixEnd_8197074 4209038922472967143977349 := by
  unfold tailWord_8197074
  simp only [CollatzResearch.WordTrace]
  refine ⟨74742962576352080407173569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199314566870272214419129517 74742962576352080407173569)
  ·
    refine ⟨56057221932264060305380177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74742962576352080407173569 56057221932264060305380177)
    ·
      refine ⟨42042916449198045229035133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56057221932264060305380177 42042916449198045229035133)
      ·
        refine ⟨15766093668449266960888175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42042916449198045229035133 15766093668449266960888175)
        ·
          refine ⟨23649140502673900441332263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15766093668449266960888175 23649140502673900441332263)
          ·
            refine ⟨35473710754010850661998395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23649140502673900441332263 35473710754010850661998395)
            ·
              refine ⟨53210566131016275992997593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35473710754010850661998395 53210566131016275992997593)
              ·
                refine ⟨39907924598262206994748195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53210566131016275992997593 39907924598262206994748195)
                ·
                  refine ⟨59861886897393310492122293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39907924598262206994748195 59861886897393310492122293)
                  ·
                    refine ⟨5612051896630622858636465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59861886897393310492122293 5612051896630622858636465)
                    ·
                      refine ⟨4209038922472967143977349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5612051896630622858636465 4209038922472967143977349)
                      ·
                        rfl

theorem cell23_8197074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_8197074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197074 prefixEnd_8197074 := by exact prefixLift 8197074
  have htrace : WordTrace (prefixWord ++ tailWord_8197074) baseStart_8197074 baseEnd_8197074 := by
    simpa [prefixWord, tailWord_8197074, baseEnd_8197074] using wordTrace_append hprefix tailTrace_8197074
  have hstable : (prefixWord ++ tailWord_8197074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197074).length < 2 ^ (prefixWord ++ tailWord_8197074).sum := by decide
  have hdescent : baseEnd_8197074 < baseStart_8197074 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197098 : List Nat := [3, 1, 3, 1, 2, 4, 1, 3, 1, 1, 3]
def baseStart_8197098 : Nat := 118140960795 + 8197098 * 2 ^ 59
def prefixEnd_8197098 : Nat := 4983230072969 + 3 ^ 40 * 8197098 * 2
def baseEnd_8197098 : Nat := 4209051246008675050077239

theorem tailTrace_8197098 : CollatzResearch.WordTrace tailWord_8197098 prefixEnd_8197098 4209051246008675050077239 := by
  unfold tailWord_8197098
  simp only [CollatzResearch.WordTrace]
  refine ⟨74743181414330343431891987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199315150438214249151711965 74743181414330343431891987)
  ·
    refine ⟨112114772121495515147837981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74743181414330343431891987 112114772121495515147837981)
    ·
      refine ⟨42043039545560818180439243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112114772121495515147837981 42043039545560818180439243)
      ·
        refine ⟨63064559318341227270658865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42043039545560818180439243 63064559318341227270658865)
        ·
          refine ⟨47298419488755920452994149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63064559318341227270658865 47298419488755920452994149)
          ·
            refine ⟨8868453654141735084936403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47298419488755920452994149 8868453654141735084936403)
            ·
              refine ⟨13302680481212602627404605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8868453654141735084936403 13302680481212602627404605)
              ·
                refine ⟨4988505180454725985276727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13302680481212602627404605 4988505180454725985276727)
                ·
                  refine ⟨7482757770682088977915091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4988505180454725985276727 7482757770682088977915091)
                  ·
                    refine ⟨11224136656023133466872637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7482757770682088977915091 11224136656023133466872637)
                    ·
                      refine ⟨4209051246008675050077239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11224136656023133466872637 4209051246008675050077239)
                      ·
                        rfl

theorem cell23_8197098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 3, 1, 1, 3].length) (baseStart_8197098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197098 prefixEnd_8197098 := by exact prefixLift 8197098
  have htrace : WordTrace (prefixWord ++ tailWord_8197098) baseStart_8197098 baseEnd_8197098 := by
    simpa [prefixWord, tailWord_8197098, baseEnd_8197098] using wordTrace_append hprefix tailTrace_8197098
  have hstable : (prefixWord ++ tailWord_8197098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197098).length < 2 ^ (prefixWord ++ tailWord_8197098).sum := by decide
  have hdescent : baseEnd_8197098 < baseStart_8197098 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197121 : List Nat := [1, 2, 4, 1, 2, 2, 3, 1, 3, 2, 2]
def baseStart_8197121 : Nat := 118140960795 + 8197121 * 2 ^ 59
def prefixEnd_8197121 : Nat := 4983230072969 + 3 ^ 40 * 8197121 * 2
def baseEnd_8197121 : Nat := 4209063056063728460089633

theorem tailTrace_8197121 : CollatzResearch.WordTrace tailWord_8197121 prefixEnd_8197121 4209063056063728460089633 := by
  unfold tailWord_8197121
  simp only [CollatzResearch.WordTrace]
  refine ⟨298973564536238048655655217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199315709690825365770436811 298973564536238048655655217)
  ·
    refine ⟨224230173402178536491741413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298973564536238048655655217 224230173402178536491741413)
    ·
      refine ⟨42043157512908475592201515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224230173402178536491741413 42043157512908475592201515)
      ·
        refine ⟨63064736269362713388302273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42043157512908475592201515 63064736269362713388302273)
        ·
          refine ⟨47298552202022035041226705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63064736269362713388302273 47298552202022035041226705)
          ·
            refine ⟨35473914151516526280920029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47298552202022035041226705 35473914151516526280920029)
            ·
              refine ⟨13302717806818697355345011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35473914151516526280920029 13302717806818697355345011)
              ·
                refine ⟨19954076710228046033017517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13302717806818697355345011 19954076710228046033017517)
                ·
                  refine ⟨7482778766335517262381569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19954076710228046033017517 7482778766335517262381569)
                  ·
                    refine ⟨5612084074751637946786177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7482778766335517262381569 5612084074751637946786177)
                    ·
                      refine ⟨4209063056063728460089633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5612084074751637946786177 4209063056063728460089633)
                      ·
                        rfl

theorem cell23_8197121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 3, 2, 2].length) (baseStart_8197121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197121 prefixEnd_8197121 := by exact prefixLift 8197121
  have htrace : WordTrace (prefixWord ++ tailWord_8197121) baseStart_8197121 baseEnd_8197121 := by
    simpa [prefixWord, tailWord_8197121, baseEnd_8197121] using wordTrace_append hprefix tailTrace_8197121
  have hstable : (prefixWord ++ tailWord_8197121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197121).length < 2 ^ (prefixWord ++ tailWord_8197121).sum := by decide
  have hdescent : baseEnd_8197121 < baseStart_8197121 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197131 : List Nat := [1, 1, 1, 1, 6, 4, 2, 1, 2, 4]
def baseStart_8197131 : Nat := 118140960795 + 8197131 * 2 ^ 59
def prefixEnd_8197131 : Nat := 4983230072969 + 3 ^ 40 * 8197131 * 2
def baseEnd_8197131 : Nat := 1403022730290091140321529

theorem tailTrace_8197131 : CollatzResearch.WordTrace tailWord_8197131 prefixEnd_8197131 1403022730290091140321529 := by
  unfold tailWord_8197131
  simp only [CollatzResearch.WordTrace]
  refine ⟨298973929266201820363519247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199315952844134546909012831 298973929266201820363519247)
  ·
    refine ⟨448460893899302730545278871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298973929266201820363519247 448460893899302730545278871)
    ·
      refine ⟨672691340848954095817918307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448460893899302730545278871 672691340848954095817918307)
      ·
        refine ⟨1009037011273431143726877461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 672691340848954095817918307 1009037011273431143726877461)
        ·
          refine ⟨47298609903442084862197381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1009037011273431143726877461 47298609903442084862197381)
          ·
            refine ⟨8868489356895390911662009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47298609903442084862197381 8868489356895390911662009)
            ·
              refine ⟨6651367017671543183746507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8868489356895390911662009 6651367017671543183746507)
              ·
                refine ⟨9977050526507314775619761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6651367017671543183746507 9977050526507314775619761)
                ·
                  refine ⟨7482787894880486081714821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9977050526507314775619761 7482787894880486081714821)
                  ·
                    refine ⟨1403022730290091140321529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7482787894880486081714821 1403022730290091140321529)
                    ·
                      rfl

theorem cell23_8197131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 1, 2, 4].length) (baseStart_8197131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197131 prefixEnd_8197131 := by exact prefixLift 8197131
  have htrace : WordTrace (prefixWord ++ tailWord_8197131) baseStart_8197131 baseEnd_8197131 := by
    simpa [prefixWord, tailWord_8197131, baseEnd_8197131] using wordTrace_append hprefix tailTrace_8197131
  have hstable : (prefixWord ++ tailWord_8197131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197131).length < 2 ^ (prefixWord ++ tailWord_8197131).sum := by decide
  have hdescent : baseEnd_8197131 < baseStart_8197131 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197138 : List Nat := [3, 2, 5, 1, 1, 1, 1, 1, 3, 1, 4]
def baseStart_8197138 : Nat := 118140960795 + 8197138 * 2 ^ 59
def prefixEnd_8197138 : Nat := 4983230072969 + 3 ^ 40 * 8197138 * 2
def baseEnd_8197138 : Nat := 4209071785234854893577055

theorem tailTrace_8197138 : CollatzResearch.WordTrace tailWord_8197138 prefixEnd_8197138 4209071785234854893577055 := by
  unfold tailWord_8197138
  simp only [CollatzResearch.WordTrace]
  refine ⟨74743546144294115139756017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199316123051450973706016045 74743546144294115139756017)
  ·
    refine ⟨56057659608220586354817013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74743546144294115139756017 56057659608220586354817013)
    ·
      refine ⟨5255405588270679970764095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56057659608220586354817013 5255405588270679970764095)
      ·
        refine ⟨7883108382406019956146143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5255405588270679970764095 7883108382406019956146143)
        ·
          refine ⟨11824662573609029934219215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7883108382406019956146143 11824662573609029934219215)
          ·
            refine ⟨17736993860413544901328823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11824662573609029934219215 17736993860413544901328823)
            ·
              refine ⟨26605490790620317351993235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17736993860413544901328823 26605490790620317351993235)
              ·
                refine ⟨39908236185930476027989853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26605490790620317351993235 39908236185930476027989853)
                ·
                  refine ⟨14965588569723928510496195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39908236185930476027989853 14965588569723928510496195)
                  ·
                    refine ⟨22448382854585892765744293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14965588569723928510496195 22448382854585892765744293)
                    ·
                      refine ⟨4209071785234854893577055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22448382854585892765744293 4209071785234854893577055)
                      ·
                        rfl

theorem cell23_8197138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_8197138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197138 prefixEnd_8197138 := by exact prefixLift 8197138
  have htrace : WordTrace (prefixWord ++ tailWord_8197138) baseStart_8197138 baseEnd_8197138 := by
    simpa [prefixWord, tailWord_8197138, baseEnd_8197138] using wordTrace_append hprefix tailTrace_8197138
  have hstable : (prefixWord ++ tailWord_8197138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197138).length < 2 ^ (prefixWord ++ tailWord_8197138).sum := by decide
  have hdescent : baseEnd_8197138 < baseStart_8197138 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197141 : List Nat := [1, 3, 2, 1, 4, 3, 1, 2, 1, 2, 3]
def baseStart_8197141 : Nat := 118140960795 + 8197141 * 2 ^ 59
def prefixEnd_8197141 : Nat := 4983230072969 + 3 ^ 40 * 8197141 * 2
def baseEnd_8197141 : Nat := 4209073325676818381839541

theorem tailTrace_8197141 : CollatzResearch.WordTrace tailWord_8197141 prefixEnd_8197141 4209073325676818381839541 := by
  unfold tailWord_8197141
  simp only [CollatzResearch.WordTrace]
  refine ⟨298974293996165592071383277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199316195997443728047588851 298974293996165592071383277)
  ·
    refine ⟨112115360248562097026768729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298974293996165592071383277 112115360248562097026768729)
    ·
      refine ⟨84086520186421572770076547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112115360248562097026768729 84086520186421572770076547)
      ·
        refine ⟨126129780279632359155114821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84086520186421572770076547 126129780279632359155114821)
        ·
          refine ⟨23649333802431067341584029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126129780279632359155114821 23649333802431067341584029)
          ·
            refine ⟨8868500175911650253094011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23649333802431067341584029 8868500175911650253094011)
            ·
              refine ⟨13302750263867475379641017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8868500175911650253094011 13302750263867475379641017)
              ·
                refine ⟨9977062697900606534730763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13302750263867475379641017 9977062697900606534730763)
                ·
                  refine ⟨14965594046850909802096145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9977062697900606534730763 14965594046850909802096145)
                  ·
                    refine ⟨11224195535138182351572109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14965594046850909802096145 11224195535138182351572109)
                    ·
                      refine ⟨4209073325676818381839541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11224195535138182351572109 4209073325676818381839541)
                      ·
                        rfl

theorem cell23_8197141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 2, 1, 2, 3].length) (baseStart_8197141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197141 prefixEnd_8197141 := by exact prefixLift 8197141
  have htrace : WordTrace (prefixWord ++ tailWord_8197141) baseStart_8197141 baseEnd_8197141 := by
    simpa [prefixWord, tailWord_8197141, baseEnd_8197141] using wordTrace_append hprefix tailTrace_8197141
  have hstable : (prefixWord ++ tailWord_8197141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197141).length < 2 ^ (prefixWord ++ tailWord_8197141).sum := by decide
  have hdescent : baseEnd_8197141 < baseStart_8197141 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197154 : List Nat := [3, 3, 1, 1, 1, 4, 1, 2, 1, 3, 3]
def baseStart_8197154 : Nat := 118140960795 + 8197154 * 2 ^ 59
def prefixEnd_8197154 : Nat := 4983230072969 + 3 ^ 40 * 8197154 * 2
def baseEnd_8197154 : Nat := 4209080000925326830976981

theorem tailTrace_8197154 : CollatzResearch.WordTrace tailWord_8197154 prefixEnd_8197154 4209080000925326830976981 := by
  unfold tailWord_8197154
  simp only [CollatzResearch.WordTrace]
  refine ⟨74743692036279623822901629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199316512096745663527737677 74743692036279623822901629)
  ·
    refine ⟨28028884513604858933588111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74743692036279623822901629 28028884513604858933588111)
    ·
      refine ⟨42043326770407288400382167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28028884513604858933588111 42043326770407288400382167)
      ·
        refine ⟨63064990155610932600573251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42043326770407288400382167 63064990155610932600573251)
        ·
          refine ⟨94597485233416398900859877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63064990155610932600573251 94597485233416398900859877)
          ·
            refine ⟨17737028481265574793911227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94597485233416398900859877 17737028481265574793911227)
            ·
              refine ⟨26605542721898362190866841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17737028481265574793911227 26605542721898362190866841)
              ·
                refine ⟨19954157041423771643150131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26605542721898362190866841 19954157041423771643150131)
                ·
                  refine ⟨29931235562135657464725197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19954157041423771643150131 29931235562135657464725197)
                  ·
                    refine ⟨11224213335800871549271949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29931235562135657464725197 11224213335800871549271949)
                    ·
                      refine ⟨4209080000925326830976981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11224213335800871549271949 4209080000925326830976981)
                      ·
                        rfl

theorem cell23_8197154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_8197154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197154 prefixEnd_8197154 := by exact prefixLift 8197154
  have htrace : WordTrace (prefixWord ++ tailWord_8197154) baseStart_8197154 baseEnd_8197154 := by
    simpa [prefixWord, tailWord_8197154, baseEnd_8197154] using wordTrace_append hprefix tailTrace_8197154
  have hstable : (prefixWord ++ tailWord_8197154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197154).length < 2 ^ (prefixWord ++ tailWord_8197154).sum := by decide
  have hdescent : baseEnd_8197154 < baseStart_8197154 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197172 : List Nat := [2, 5, 1, 2, 1, 1, 4, 2, 1, 2, 2]
def baseStart_8197172 : Nat := 118140960795 + 8197172 * 2 ^ 59
def prefixEnd_8197172 : Nat := 4983230072969 + 3 ^ 40 * 8197172 * 2
def baseEnd_8197172 : Nat := 4209089243577107760551899

theorem tailTrace_8197172 : CollatzResearch.WordTrace tailWord_8197172 prefixEnd_8197172 4209089243577107760551899 := by
  unfold tailWord_8197172
  simp only [CollatzResearch.WordTrace]
  refine ⟨149487712329526642182880885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199316949772702189577174513 149487712329526642182880885)
  ·
    refine ⟨14014473030893122704645083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149487712329526642182880885 14014473030893122704645083)
    ·
      refine ⟨21021709546339684056967625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14014473030893122704645083 21021709546339684056967625)
      ·
        refine ⟨15766282159754763042725719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21021709546339684056967625 15766282159754763042725719)
        ·
          refine ⟨23649423239632144564088579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15766282159754763042725719 23649423239632144564088579)
          ·
            refine ⟨35474134859448216846132869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23649423239632144564088579 35474134859448216846132869)
            ·
              refine ⟨6651400286146540658649913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35474134859448216846132869 6651400286146540658649913)
              ·
                refine ⟨4988550214609905493987435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6651400286146540658649913 4988550214609905493987435)
                ·
                  refine ⟨7482825321914858240981153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4988550214609905493987435 7482825321914858240981153)
                  ·
                    refine ⟨5612118991436143680735865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7482825321914858240981153 5612118991436143680735865)
                    ·
                      refine ⟨4209089243577107760551899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5612118991436143680735865 4209089243577107760551899)
                      ·
                        rfl

theorem cell23_8197172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_8197172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197172 prefixEnd_8197172 := by exact prefixLift 8197172
  have htrace : WordTrace (prefixWord ++ tailWord_8197172) baseStart_8197172 baseEnd_8197172 := by
    simpa [prefixWord, tailWord_8197172, baseEnd_8197172] using wordTrace_append hprefix tailTrace_8197172
  have hstable : (prefixWord ++ tailWord_8197172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197172).length < 2 ^ (prefixWord ++ tailWord_8197172).sum := by decide
  have hdescent : baseEnd_8197172 < baseStart_8197172 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197177 : List Nat := [1, 2, 1, 5, 2, 1, 1, 1, 2, 3, 4]
def baseStart_8197177 : Nat := 118140960795 + 8197177 * 2 ^ 59
def prefixEnd_8197177 : Nat := 4983230072969 + 3 ^ 40 * 8197177 * 2
def baseEnd_8197177 : Nat := 4209091810980380240989375

theorem tailTrace_8197177 : CollatzResearch.WordTrace tailWord_8197177 prefixEnd_8197177 4209091810980380240989375 := by
  unfold tailWord_8197177
  simp only [CollatzResearch.WordTrace]
  refine ⟨298975607024035170219693785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199317071349356780146462523 298975607024035170219693785)
  ·
    refine ⟨224231705268026377664770339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298975607024035170219693785 224231705268026377664770339)
    ·
      refine ⟨336347557902039566497155509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224231705268026377664770339 336347557902039566497155509)
      ·
        refine ⟨31532583553316209359108329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 336347557902039566497155509 31532583553316209359108329)
        ·
          refine ⟨23649437664987157019331247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31532583553316209359108329 23649437664987157019331247)
          ·
            refine ⟨35474156497480735528996871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23649437664987157019331247 35474156497480735528996871)
            ·
              refine ⟨53211234746221103293495307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35474156497480735528996871 53211234746221103293495307)
              ·
                refine ⟨79816852119331654940242961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53211234746221103293495307 79816852119331654940242961)
                ·
                  refine ⟨59862639089498741205182221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79816852119331654940242961 59862639089498741205182221)
                  ·
                    refine ⟨22448489658562027951943333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59862639089498741205182221 22448489658562027951943333)
                    ·
                      refine ⟨4209091810980380240989375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22448489658562027951943333 4209091810980380240989375)
                      ·
                        rfl

theorem cell23_8197177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_8197177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197177 prefixEnd_8197177 := by exact prefixLift 8197177
  have htrace : WordTrace (prefixWord ++ tailWord_8197177) baseStart_8197177 baseEnd_8197177 := by
    simpa [prefixWord, tailWord_8197177, baseEnd_8197177] using wordTrace_append hprefix tailTrace_8197177
  have hstable : (prefixWord ++ tailWord_8197177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197177).length < 2 ^ (prefixWord ++ tailWord_8197177).sum := by decide
  have hdescent : baseEnd_8197177 < baseStart_8197177 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197194 : List Nat := [3, 1, 2, 1, 1, 2, 3, 3, 1, 4, 2]
def baseStart_8197194 : Nat := 118140960795 + 8197194 * 2 ^ 59
def prefixEnd_8197194 : Nat := 4983230072969 + 3 ^ 40 * 8197194 * 2
def baseEnd_8197194 : Nat := 4209100540151506674476797

theorem tailTrace_8197194 : CollatzResearch.WordTrace tailWord_8197194 prefixEnd_8197194 4209100540151506674476797 := by
  unfold tailWord_8197194
  simp only [CollatzResearch.WordTrace]
  refine ⟨74744056766243395530765659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199317484709982388082041757 74744056766243395530765659)
  ·
    refine ⟨112116085149365093296148489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74744056766243395530765659 112116085149365093296148489)
    ·
      refine ⟨84087063862023819972111367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112116085149365093296148489 84087063862023819972111367)
      ·
        refine ⟨126130595793035729958167051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84087063862023819972111367 126130595793035729958167051)
        ·
          refine ⟨189195893689553594937250577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126130595793035729958167051 189195893689553594937250577)
          ·
            refine ⟨141896920267165196202937933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189195893689553594937250577 141896920267165196202937933)
            ·
              refine ⟨53211345100186948576101725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141896920267165196202937933 53211345100186948576101725)
              ·
                refine ⟨19954254412570105716038147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53211345100186948576101725 19954254412570105716038147)
                ·
                  refine ⟨29931381618855158574057221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19954254412570105716038147 29931381618855158574057221)
                  ·
                    refine ⟨5612134053535342232635729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29931381618855158574057221 5612134053535342232635729)
                    ·
                      refine ⟨4209100540151506674476797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5612134053535342232635729 4209100540151506674476797)
                      ·
                        rfl

theorem cell23_8197194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 1, 4, 2].length) (baseStart_8197194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197194 prefixEnd_8197194 := by exact prefixLift 8197194
  have htrace : WordTrace (prefixWord ++ tailWord_8197194) baseStart_8197194 baseEnd_8197194 := by
    simpa [prefixWord, tailWord_8197194, baseEnd_8197194] using wordTrace_append hprefix tailTrace_8197194
  have hstable : (prefixWord ++ tailWord_8197194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197194).length < 2 ^ (prefixWord ++ tailWord_8197194).sum := by decide
  have hdescent : baseEnd_8197194 < baseStart_8197194 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197234 : List Nat := [3, 2, 1, 2, 2, 1, 1, 6, 5]
def baseStart_8197234 : Nat := 118140960795 + 8197234 * 2 ^ 59
def prefixEnd_8197234 : Nat := 4983230072969 + 3 ^ 40 * 8197234 * 2
def baseEnd_8197234 : Nat := 467680119930854057552957

theorem tailTrace_8197234 : CollatzResearch.WordTrace tailWord_8197234 prefixEnd_8197234 467680119930854057552957 := by
  unfold tailWord_8197234
  simp only [CollatzResearch.WordTrace]
  refine ⟨74744421496207167238629689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199318457323219112636345837 74744421496207167238629689)
  ·
    refine ⟨56058316122155375428972267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74744421496207167238629689 56058316122155375428972267)
    ·
      refine ⟨84087474183233063143458401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56058316122155375428972267 84087474183233063143458401)
      ·
        refine ⟨63065605637424797357593801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84087474183233063143458401 63065605637424797357593801)
        ·
          refine ⟨47299204228068598018195351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63065605637424797357593801 47299204228068598018195351)
          ·
            refine ⟨70948806342102897027293027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47299204228068598018195351 70948806342102897027293027)
            ·
              refine ⟨106423209513154345540939541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70948806342102897027293027 106423209513154345540939541)
              ·
                refine ⟨4988587945929109947231541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 106423209513154345540939541 4988587945929109947231541)
                ·
                  refine ⟨467680119930854057552957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4988587945929109947231541 467680119930854057552957)
                  ·
                    rfl

theorem cell23_8197234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 6, 5].length) (baseStart_8197234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197234 prefixEnd_8197234 := by exact prefixLift 8197234
  have htrace : WordTrace (prefixWord ++ tailWord_8197234) baseStart_8197234 baseEnd_8197234 := by
    simpa [prefixWord, tailWord_8197234, baseEnd_8197234] using wordTrace_append hprefix tailTrace_8197234
  have hstable : (prefixWord ++ tailWord_8197234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197234).length < 2 ^ (prefixWord ++ tailWord_8197234).sum := by decide
  have hdescent : baseEnd_8197234 < baseStart_8197234 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197267 : List Nat := [1, 1, 1, 2, 1, 2, 6, 1, 1, 3, 4]
def baseStart_8197267 : Nat := 118140960795 + 8197267 * 2 ^ 59
def prefixEnd_8197267 : Nat := 4983230072969 + 3 ^ 40 * 8197267 * 2
def baseEnd_8197267 : Nat := 4209138024239284888863961

theorem tailTrace_8197267 : CollatzResearch.WordTrace tailWord_8197267 prefixEnd_8197267 4209138024239284888863961 := by
  unfold tailWord_8197267
  simp only [CollatzResearch.WordTrace]
  refine ⟨298978889593709115590470055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199319259729139410393646703 298978889593709115590470055)
  ·
    refine ⟨448468334390563673385705083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298978889593709115590470055 448468334390563673385705083)
    ·
      refine ⟨672702501585845510078557625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448468334390563673385705083 672702501585845510078557625)
      ·
        refine ⟨504526876189384132558918219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 672702501585845510078557625 504526876189384132558918219)
        ·
          refine ⟨756790314284076198838377329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504526876189384132558918219 756790314284076198838377329)
          ·
            refine ⟨567592735713057149128782997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 756790314284076198838377329 567592735713057149128782997)
            ·
              refine ⟨26605909486549553865411703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 567592735713057149128782997 26605909486549553865411703)
              ·
                refine ⟨39908864229824330798117555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26605909486549553865411703 39908864229824330798117555)
                ·
                  refine ⟨59863296344736496197176333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39908864229824330798117555 59863296344736496197176333)
                  ·
                    refine ⟨22448736129276186073941125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59863296344736496197176333 22448736129276186073941125)
                    ·
                      refine ⟨4209138024239284888863961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22448736129276186073941125 4209138024239284888863961)
                      ·
                        rfl

theorem cell23_8197267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 3, 4].length) (baseStart_8197267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197267 prefixEnd_8197267 := by exact prefixLift 8197267
  have htrace : WordTrace (prefixWord ++ tailWord_8197267) baseStart_8197267 baseEnd_8197267 := by
    simpa [prefixWord, tailWord_8197267, baseEnd_8197267] using wordTrace_append hprefix tailTrace_8197267
  have hstable : (prefixWord ++ tailWord_8197267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197267).length < 2 ^ (prefixWord ++ tailWord_8197267).sum := by decide
  have hdescent : baseEnd_8197267 < baseStart_8197267 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197284 : List Nat := [2, 3, 1, 2, 3, 1, 1, 1, 4, 1, 4]
def baseStart_8197284 : Nat := 118140960795 + 8197284 * 2 ^ 59
def prefixEnd_8197284 : Nat := 4983230072969 + 3 ^ 40 * 8197284 * 2
def baseEnd_8197284 : Nat := 4209146753410411322351383

theorem tailTrace_8197284 : CollatzResearch.WordTrace tailWord_8197284 prefixEnd_8197284 4209146753410411322351383 := by
  unfold tailWord_8197284
  simp only [CollatzResearch.WordTrace]
  refine ⟨149489754817323763746919453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199319673089765018329225937 149489754817323763746919453)
  ·
    refine ⟨56058658056496411405094795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149489754817323763746919453 56058658056496411405094795)
    ·
      refine ⟨84087987084744617107642193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56058658056496411405094795 84087987084744617107642193)
      ·
        refine ⟨63065990313558462830731645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84087987084744617107642193 63065990313558462830731645)
        ·
          refine ⟨23649746367584423561524367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63065990313558462830731645 23649746367584423561524367)
          ·
            refine ⟨35474619551376635342286551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23649746367584423561524367 35474619551376635342286551)
            ·
              refine ⟨53211929327064953013429827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35474619551376635342286551 53211929327064953013429827)
              ·
                refine ⟨79817893990597429520144741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53211929327064953013429827 79817893990597429520144741)
                ·
                  refine ⟨14965855123237018035027139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79817893990597429520144741 14965855123237018035027139)
                  ·
                    refine ⟨22448782684855527052540709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14965855123237018035027139 22448782684855527052540709)
                    ·
                      refine ⟨4209146753410411322351383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22448782684855527052540709 4209146753410411322351383)
                      ·
                        rfl

theorem cell23_8197284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_8197284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197284 prefixEnd_8197284 := by exact prefixLift 8197284
  have htrace : WordTrace (prefixWord ++ tailWord_8197284) baseStart_8197284 baseEnd_8197284 := by
    simpa [prefixWord, tailWord_8197284, baseEnd_8197284] using wordTrace_append hprefix tailTrace_8197284
  have hstable : (prefixWord ++ tailWord_8197284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197284).length < 2 ^ (prefixWord ++ tailWord_8197284).sum := by decide
  have hdescent : baseEnd_8197284 < baseStart_8197284 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197345 : List Nat := [1, 2, 3, 1, 3, 4, 2, 2, 1, 4]
def baseStart_8197345 : Nat := 118140960795 + 8197345 * 2 ^ 59
def prefixEnd_8197345 : Nat := 4983230072969 + 3 ^ 40 * 8197345 * 2
def baseEnd_8197345 : Nat := 1403059358576778527896201

theorem tailTrace_8197345 : CollatzResearch.WordTrace tailWord_8197345 prefixEnd_8197345 1403059358576778527896201 := by
  unfold tailWord_8197345
  simp only [CollatzResearch.WordTrace]
  refine ⟨298981734487426534911809489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199321156324951023274539659 298981734487426534911809489)
  ·
    refine ⟨224236300865569901183857117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298981734487426534911809489 224236300865569901183857117)
    ·
      refine ⟨84088612824588712943946419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224236300865569901183857117 84088612824588712943946419)
      ·
        refine ⟨126132919236883069415919629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84088612824588712943946419 126132919236883069415919629)
        ·
          refine ⟨47299844713831151030969861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126132919236883069415919629 47299844713831151030969861)
          ·
            refine ⟨8868720883843340818306849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47299844713831151030969861 8868720883843340818306849)
            ·
              refine ⟨6651540662882505613730137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8868720883843340818306849 6651540662882505613730137)
              ·
                refine ⟨4988655497161879210297603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6651540662882505613730137 4988655497161879210297603)
                ·
                  refine ⟨7482983245742818815446405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4988655497161879210297603 7482983245742818815446405)
                  ·
                    refine ⟨1403059358576778527896201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7482983245742818815446405 1403059358576778527896201)
                    ·
                      rfl

theorem cell23_8197345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 2, 1, 4].length) (baseStart_8197345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197345 prefixEnd_8197345 := by exact prefixLift 8197345
  have htrace : WordTrace (prefixWord ++ tailWord_8197345) baseStart_8197345 baseEnd_8197345 := by
    simpa [prefixWord, tailWord_8197345, baseEnd_8197345] using wordTrace_append hprefix tailTrace_8197345
  have hstable : (prefixWord ++ tailWord_8197345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197345).length < 2 ^ (prefixWord ++ tailWord_8197345).sum := by decide
  have hdescent : baseEnd_8197345 < baseStart_8197345 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197354 : List Nat := [3, 1, 3, 1, 1, 3, 1, 2, 3, 5]
def baseStart_8197354 : Nat := 118140960795 + 8197354 * 2 ^ 59
def prefixEnd_8197354 : Nat := 4983230072969 + 3 ^ 40 * 8197354 * 2
def baseEnd_8197354 : Nat := 1403060899018742016158687

theorem tailTrace_8197354 : CollatzResearch.WordTrace tailWord_8197354 prefixEnd_8197354 1403060899018742016158687 := by
  unfold tailWord_8197354
  simp only [CollatzResearch.WordTrace]
  refine ⟨74745515686098482362221779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199321375162929286299258077 74745515686098482362221779)
  ·
    refine ⟨112118273529147723543332669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74745515686098482362221779 112118273529147723543332669)
    ·
      refine ⟨42044352573430396328749751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112118273529147723543332669 42044352573430396328749751)
      ·
        refine ⟨63066528860145594493124627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42044352573430396328749751 63066528860145594493124627)
        ·
          refine ⟨94599793290218391739686941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63066528860145594493124627 94599793290218391739686941)
          ·
            refine ⟨35474922483831896902382603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94599793290218391739686941 35474922483831896902382603)
            ·
              refine ⟨53212383725747845353573905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35474922483831896902382603 53212383725747845353573905)
              ·
                refine ⟨39909287794310884015180429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53212383725747845353573905 39909287794310884015180429)
                ·
                  refine ⟨14965982922866581505692661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39909287794310884015180429 14965982922866581505692661)
                  ·
                    refine ⟨1403060899018742016158687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14965982922866581505692661 1403060899018742016158687)
                    ·
                      rfl

theorem cell23_8197354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_8197354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197354 prefixEnd_8197354 := by exact prefixLift 8197354
  have htrace : WordTrace (prefixWord ++ tailWord_8197354) baseStart_8197354 baseEnd_8197354 := by
    simpa [prefixWord, tailWord_8197354, baseEnd_8197354] using wordTrace_append hprefix tailTrace_8197354
  have hstable : (prefixWord ++ tailWord_8197354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197354).length < 2 ^ (prefixWord ++ tailWord_8197354).sum := by decide
  have hdescent : baseEnd_8197354 < baseStart_8197354 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197367 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 5, 6]
def baseStart_8197367 : Nat := 118140960795 + 8197367 * 2 ^ 59
def prefixEnd_8197367 : Nat := 4983230072969 + 3 ^ 40 * 8197367 * 2
def baseEnd_8197367 : Nat := 1403063124101578165871167

theorem tailTrace_8197367 : CollatzResearch.WordTrace tailWord_8197367 prefixEnd_8197367 1403063124101578165871167 := by
  unfold tailWord_8197367
  simp only [CollatzResearch.WordTrace]
  refine ⟨298982536893346832669110355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199321691262231221779406903 298982536893346832669110355)
  ·
    refine ⟨448473805340020249003665533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298982536893346832669110355 448473805340020249003665533)
    ·
      refine ⟨168177677002507593376374575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 448473805340020249003665533 168177677002507593376374575)
      ·
        refine ⟨252266515503761390064561863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168177677002507593376374575 252266515503761390064561863)
        ·
          refine ⟨378399773255642085096842795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252266515503761390064561863 378399773255642085096842795)
          ·
            refine ⟨567599659883463127645264193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378399773255642085096842795 567599659883463127645264193)
            ·
              refine ⟨425699744912597345733948145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 567599659883463127645264193 425699744912597345733948145)
              ·
                refine ⟨319274808684448009300461109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 425699744912597345733948145 319274808684448009300461109)
                ·
                  refine ⟨29932013314167000871918229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 319274808684448009300461109 29932013314167000871918229)
                  ·
                    refine ⟨1403063124101578165871167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29932013314167000871918229 1403063124101578165871167)
                    ·
                      rfl

theorem cell23_8197367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 6].length) (baseStart_8197367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197367 prefixEnd_8197367 := by exact prefixLift 8197367
  have htrace : WordTrace (prefixWord ++ tailWord_8197367) baseStart_8197367 baseEnd_8197367 := by
    simpa [prefixWord, tailWord_8197367, baseEnd_8197367] using wordTrace_append hprefix tailTrace_8197367
  have hstable : (prefixWord ++ tailWord_8197367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197367).length < 2 ^ (prefixWord ++ tailWord_8197367).sum := by decide
  have hdescent : baseEnd_8197367 < baseStart_8197367 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197388 : List Nat := [2, 2, 1, 2, 2, 5, 2, 1, 1, 5]
def baseStart_8197388 : Nat := 118140960795 + 8197388 * 2 ^ 59
def prefixEnd_8197388 : Nat := 4983230072969 + 3 ^ 40 * 8197388 * 2
def baseEnd_8197388 : Nat := 1403066718466159638483635

theorem tailTrace_8197388 : CollatzResearch.WordTrace tailWord_8197388 prefixEnd_8197388 1403066718466159638483635 := by
  unfold tailWord_8197388
  simp only [CollatzResearch.WordTrace]
  refine ⟨149491651413135376627812409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199322201884180502170416545 149491651413135376627812409)
  ·
    refine ⟨112118738559851532470859307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149491651413135376627812409 112118738559851532470859307)
    ·
      refine ⟨168178107839777298706288961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112118738559851532470859307 168178107839777298706288961)
      ·
        refine ⟨126133580879832974029716721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168178107839777298706288961 126133580879832974029716721)
        ·
          refine ⟨94600185659874730522287541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126133580879832974029716721 94600185659874730522287541)
          ·
            refine ⟨8868767405613255986464457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94600185659874730522287541 8868767405613255986464457)
            ·
              refine ⟨6651575554209941989848343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8868767405613255986464457 6651575554209941989848343)
              ·
                refine ⟨9977363331314912984772515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6651575554209941989848343 9977363331314912984772515)
                ·
                  refine ⟨14966044996972369477158773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9977363331314912984772515 14966044996972369477158773)
                  ·
                    refine ⟨1403066718466159638483635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14966044996972369477158773 1403066718466159638483635)
                    ·
                      rfl

theorem cell23_8197388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 1, 1, 5].length) (baseStart_8197388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197388 prefixEnd_8197388 := by exact prefixLift 8197388
  have htrace : WordTrace (prefixWord ++ tailWord_8197388) baseStart_8197388 baseEnd_8197388 := by
    simpa [prefixWord, tailWord_8197388, baseEnd_8197388] using wordTrace_append hprefix tailTrace_8197388
  have hstable : (prefixWord ++ tailWord_8197388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197388).length < 2 ^ (prefixWord ++ tailWord_8197388).sum := by decide
  have hdescent : baseEnd_8197388 < baseStart_8197388 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197404 : List Nat := [2, 2, 3, 1, 1, 1, 2, 2, 3, 2, 4]
def baseStart_8197404 : Nat := 118140960795 + 8197404 * 2 ^ 59
def prefixEnd_8197404 : Nat := 4983230072969 + 3 ^ 40 * 8197404 * 2
def baseEnd_8197404 : Nat := 4209208371088950852850831

theorem tailTrace_8197404 : CollatzResearch.WordTrace tailWord_8197404 prefixEnd_8197404 4209208371088950852850831 := by
  unfold tailWord_8197404
  simp only [CollatzResearch.WordTrace]
  refine ⟨149491943197106393994103633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199322590929475191992138177 149491943197106393994103633)
  ·
    refine ⟨112118957397829795495577725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149491943197106393994103633 112118957397829795495577725)
    ·
      refine ⟨42044609024186173310841647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112118957397829795495577725 42044609024186173310841647)
      ·
        refine ⟨63066913536279259966262471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42044609024186173310841647 63066913536279259966262471)
        ·
          refine ⟨94600370304418889949393707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63066913536279259966262471 94600370304418889949393707)
          ·
            refine ⟨141900555456628334924090561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94600370304418889949393707 141900555456628334924090561)
            ·
              refine ⟨106425416592471251193067921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141900555456628334924090561 106425416592471251193067921)
              ·
                refine ⟨79819062444353438394800941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106425416592471251193067921 79819062444353438394800941)
                ·
                  refine ⟨29932148416632539398050353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79819062444353438394800941 29932148416632539398050353)
                  ·
                    refine ⟨22449111312474404548537765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29932148416632539398050353 22449111312474404548537765)
                    ·
                      refine ⟨4209208371088950852850831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22449111312474404548537765 4209208371088950852850831)
                      ·
                        rfl

theorem cell23_8197404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_8197404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197404 prefixEnd_8197404 := by exact prefixLift 8197404
  have htrace : WordTrace (prefixWord ++ tailWord_8197404) baseStart_8197404 baseEnd_8197404 := by
    simpa [prefixWord, tailWord_8197404, baseEnd_8197404] using wordTrace_append hprefix tailTrace_8197404
  have hstable : (prefixWord ++ tailWord_8197404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197404).length < 2 ^ (prefixWord ++ tailWord_8197404).sum := by decide
  have hdescent : baseEnd_8197404 < baseStart_8197404 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197417 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 2, 3, 8]
def baseStart_8197417 : Nat := 118140960795 + 8197417 * 2 ^ 59
def prefixEnd_8197417 : Nat := 4983230072969 + 3 ^ 40 * 8197417 * 2
def baseEnd_8197417 : Nat := 4209215046337459301988271

theorem tailTrace_8197417 : CollatzResearch.WordTrace tailWord_8197417 prefixEnd_8197417 4209215046337459301988271 := by
  unfold tailWord_8197417
  simp only [CollatzResearch.WordTrace]
  refine ⟨298984360543165691208430505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199322907028777127472287003 298984360543165691208430505)
  ·
    refine ⟨224238270407374268406322879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298984360543165691208430505 224238270407374268406322879)
    ·
      refine ⟨336357405611061402609484319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224238270407374268406322879 336357405611061402609484319)
      ·
        refine ⟨504536108416592103914226479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336357405611061402609484319 504536108416592103914226479)
        ·
          refine ⟨756804162624888155871339719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504536108416592103914226479 756804162624888155871339719)
          ·
            refine ⟨1135206243937332233807009579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 756804162624888155871339719 1135206243937332233807009579)
            ·
              refine ⟨1702809365905998350710514369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1135206243937332233807009579 1702809365905998350710514369)
              ·
                refine ⟨1277107024429498763032885777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1702809365905998350710514369 1277107024429498763032885777)
                ·
                  refine ⟨957830268322124072274664333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1277107024429498763032885777 957830268322124072274664333)
                  ·
                    refine ⟨359186350620796527102999125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 957830268322124072274664333 359186350620796527102999125)
                    ·
                      refine ⟨4209215046337459301988271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 359186350620796527102999125 4209215046337459301988271)
                      ·
                        rfl

theorem cell23_8197417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 3, 8].length) (baseStart_8197417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197417 prefixEnd_8197417 := by exact prefixLift 8197417
  have htrace : WordTrace (prefixWord ++ tailWord_8197417) baseStart_8197417 baseEnd_8197417 := by
    simpa [prefixWord, tailWord_8197417, baseEnd_8197417] using wordTrace_append hprefix tailTrace_8197417
  have hstable : (prefixWord ++ tailWord_8197417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197417).length < 2 ^ (prefixWord ++ tailWord_8197417).sum := by decide
  have hdescent : baseEnd_8197417 < baseStart_8197417 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197418 : List Nat := [3, 1, 4, 2, 1, 3, 1, 1, 1, 6]
def baseStart_8197418 : Nat := 118140960795 + 8197418 * 2 ^ 59
def prefixEnd_8197418 : Nat := 4983230072969 + 3 ^ 40 * 8197418 * 2
def baseEnd_8197418 : Nat := 1403071853272704599358589

theorem tailTrace_8197418 : CollatzResearch.WordTrace tailWord_8197418 prefixEnd_8197418 1403071853272704599358589 := by
  unfold tailWord_8197418
  simp only [CollatzResearch.WordTrace]
  refine ⟨74746099254040517094804227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199322931344108045586144605 74746099254040517094804227)
  ·
    refine ⟨112119148881060775642206341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74746099254040517094804227 112119148881060775642206341)
    ·
      refine ⟨21022340415198895432913689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112119148881060775642206341 21022340415198895432913689)
      ·
        refine ⟨15766755311399171574685267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21022340415198895432913689 15766755311399171574685267)
        ·
          refine ⟨23650132967098757362027901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15766755311399171574685267 23650132967098757362027901)
          ·
            refine ⟨8868799862662034010760463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23650132967098757362027901 8868799862662034010760463)
            ·
              refine ⟨13303199793993051016140695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8868799862662034010760463 13303199793993051016140695)
              ·
                refine ⟨19954799690989576524211043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13303199793993051016140695 19954799690989576524211043)
                ·
                  refine ⟨29932199536484364786316565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19954799690989576524211043 29932199536484364786316565)
                  ·
                    refine ⟨1403071853272704599358589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29932199536484364786316565 1403071853272704599358589)
                    ·
                      rfl

theorem cell23_8197418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_8197418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197418 prefixEnd_8197418 := by exact prefixLift 8197418
  have htrace : WordTrace (prefixWord ++ tailWord_8197418) baseStart_8197418 baseEnd_8197418 := by
    simpa [prefixWord, tailWord_8197418, baseEnd_8197418] using wordTrace_append hprefix tailTrace_8197418
  have hstable : (prefixWord ++ tailWord_8197418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197418).length < 2 ^ (prefixWord ++ tailWord_8197418).sum := by decide
  have hdescent : baseEnd_8197418 < baseStart_8197418 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197454 : List Nat := [4, 1, 1, 1, 1, 1, 3, 2, 2, 2, 5]
def baseStart_8197454 : Nat := 118140960795 + 8197454 * 2 ^ 59
def prefixEnd_8197454 : Nat := 4983230072969 + 3 ^ 40 * 8197454 * 2
def baseEnd_8197454 : Nat := 4209234045121675657225601

theorem tailTrace_8197454 : CollatzResearch.WordTrace tailWord_8197454 prefixEnd_8197454 4209234045121675657225601 := by
  unfold tailWord_8197454
  simp only [CollatzResearch.WordTrace]
  refine ⟨37373213755503955815940927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199323806696021097685018277 37373213755503955815940927)
  ·
    refine ⟨56059820633255933723911391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37373213755503955815940927 56059820633255933723911391)
    ·
      refine ⟨84089730949883900585867087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56059820633255933723911391 84089730949883900585867087)
      ·
        refine ⟨126134596424825850878800631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84089730949883900585867087 126134596424825850878800631)
        ·
          refine ⟨189201894637238776318200947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126134596424825850878800631 189201894637238776318200947)
          ·
            refine ⟨283802841955858164477301421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189201894637238776318200947 283802841955858164477301421)
            ·
              refine ⟨106426065733446811678988033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 283802841955858164477301421 106426065733446811678988033)
              ·
                refine ⟨79819549300085108759241025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106426065733446811678988033 79819549300085108759241025)
                ·
                  refine ⟨59864661975063831569430769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79819549300085108759241025 59864661975063831569430769)
                  ·
                    refine ⟨44898496481297873677073077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59864661975063831569430769 44898496481297873677073077)
                    ·
                      refine ⟨4209234045121675657225601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44898496481297873677073077 4209234045121675657225601)
                      ·
                        rfl

theorem cell23_8197454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_8197454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197454 prefixEnd_8197454 := by exact prefixLift 8197454
  have htrace : WordTrace (prefixWord ++ tailWord_8197454) baseStart_8197454 baseEnd_8197454 := by
    simpa [prefixWord, tailWord_8197454, baseEnd_8197454] using wordTrace_append hprefix tailTrace_8197454
  have hstable : (prefixWord ++ tailWord_8197454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197454).length < 2 ^ (prefixWord ++ tailWord_8197454).sum := by decide
  have hdescent : baseEnd_8197454 < baseStart_8197454 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197458 : List Nat := [3, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3]
def baseStart_8197458 : Nat := 118140960795 + 8197458 * 2 ^ 59
def prefixEnd_8197458 : Nat := 4983230072969 + 3 ^ 40 * 8197458 * 2
def baseEnd_8197458 : Nat := 4209236099044293641575583

theorem tailTrace_8197458 : CollatzResearch.WordTrace tailWord_8197458 prefixEnd_8197458 4209236099044293641575583 := by
  unfold tailWord_8197458
  simp only [CollatzResearch.WordTrace]
  refine ⟨74746463984004288802668257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199323903957344770140448685 74746463984004288802668257)
  ·
    refine ⟨56059847988003216602001193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74746463984004288802668257 56059847988003216602001193)
    ·
      refine ⟨42044885991002412451500895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56059847988003216602001193 42044885991002412451500895)
      ·
        refine ⟨63067328986503618677251343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42044885991002412451500895 63067328986503618677251343)
        ·
          refine ⟨94600993479755428015877015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63067328986503618677251343 94600993479755428015877015)
          ·
            refine ⟨141901490219633142023815523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94600993479755428015877015 141901490219633142023815523)
            ·
              refine ⟨212852235329449713035723285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141901490219633142023815523 212852235329449713035723285)
              ·
                refine ⟨9977448531067955298549529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 212852235329449713035723285 9977448531067955298549529)
                ·
                  refine ⟨7483086398300966473912147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9977448531067955298549529 7483086398300966473912147)
                  ·
                    refine ⟨11224629597451449710868221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7483086398300966473912147 11224629597451449710868221)
                    ·
                      refine ⟨4209236099044293641575583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11224629597451449710868221 4209236099044293641575583)
                      ·
                        rfl

theorem cell23_8197458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_8197458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197458 prefixEnd_8197458 := by exact prefixLift 8197458
  have htrace : WordTrace (prefixWord ++ tailWord_8197458) baseStart_8197458 baseEnd_8197458 := by
    simpa [prefixWord, tailWord_8197458, baseEnd_8197458] using wordTrace_append hprefix tailTrace_8197458
  have hstable : (prefixWord ++ tailWord_8197458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197458).length < 2 ^ (prefixWord ++ tailWord_8197458).sum := by decide
  have hdescent : baseEnd_8197458 < baseStart_8197458 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197464 : List Nat := [2, 1, 2, 2, 1, 1, 4, 1, 2, 3, 4]
def baseStart_8197464 : Nat := 118140960795 + 8197464 * 2 ^ 59
def prefixEnd_8197464 : Nat := 4983230072969 + 3 ^ 40 * 8197464 * 2
def baseEnd_8197464 : Nat := 4209239179928220618100555

theorem tailTrace_8197464 : CollatzResearch.WordTrace tailWord_8197464 prefixEnd_8197464 4209239179928220618100555 := by
  unfold tailWord_8197464
  simp only [CollatzResearch.WordTrace]
  refine ⟨149493037386997709117695723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199324049849330278823594297 149493037386997709117695723)
  ·
    refine ⟨224239556080496563676543585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149493037386997709117695723 224239556080496563676543585)
    ·
      refine ⟨168179667060372422757407689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224239556080496563676543585 168179667060372422757407689)
      ·
        refine ⟨126134750295279317068055767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168179667060372422757407689 126134750295279317068055767)
        ·
          refine ⟨189202125442918975602083651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126134750295279317068055767 189202125442918975602083651)
          ·
            refine ⟨283803188164378463403125477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189202125442918975602083651 283803188164378463403125477)
            ·
              refine ⟨53213097780820961888086027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 283803188164378463403125477 53213097780820961888086027)
              ·
                refine ⟨79819646671231442832129041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53213097780820961888086027 79819646671231442832129041)
                ·
                  refine ⟨59864735003423582124096781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79819646671231442832129041 59864735003423582124096781)
                  ·
                    refine ⟨22449275626283843296536293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59864735003423582124096781 22449275626283843296536293)
                    ·
                      refine ⟨4209239179928220618100555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22449275626283843296536293 4209239179928220618100555)
                      ·
                        rfl

theorem cell23_8197464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_8197464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197464 prefixEnd_8197464 := by exact prefixLift 8197464
  have htrace : WordTrace (prefixWord ++ tailWord_8197464) baseStart_8197464 baseEnd_8197464 := by
    simpa [prefixWord, tailWord_8197464, baseEnd_8197464] using wordTrace_append hprefix tailTrace_8197464
  have hstable : (prefixWord ++ tailWord_8197464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197464).length < 2 ^ (prefixWord ++ tailWord_8197464).sum := by decide
  have hdescent : baseEnd_8197464 < baseStart_8197464 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197475 : List Nat := [1, 1, 1, 5, 2, 2, 4, 1, 2, 1, 3]
def baseStart_8197475 : Nat := 118140960795 + 8197475 * 2 ^ 59
def prefixEnd_8197475 : Nat := 4983230072969 + 3 ^ 40 * 8197475 * 2
def baseEnd_8197475 : Nat := 4209244828215420075063005

theorem tailTrace_8197475 : CollatzResearch.WordTrace tailWord_8197475 prefixEnd_8197475 4209244828215420075063005 := by
  unfold tailWord_8197475
  simp only [CollatzResearch.WordTrace]
  refine ⟨298986475976955567114041879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199324317317970378076027919 298986475976955567114041879)
  ·
    refine ⟨448479713965433350671062819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298986475976955567114041879 448479713965433350671062819)
    ·
      refine ⟨672719570948150026006594229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448479713965433350671062819 672719570948150026006594229)
      ·
        refine ⟨63067459776389064938118209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 672719570948150026006594229 63067459776389064938118209)
        ·
          refine ⟨47300594832291798703588657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63067459776389064938118209 47300594832291798703588657)
          ·
            refine ⟨35475446124218849027691493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47300594832291798703588657 35475446124218849027691493)
            ·
              refine ⟨6651646148291034192692155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35475446124218849027691493 6651646148291034192692155)
              ·
                refine ⟨9977469222436551289038233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6651646148291034192692155 9977469222436551289038233)
                ·
                  refine ⟨7483101916827413466778675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9977469222436551289038233 7483101916827413466778675)
                  ·
                    refine ⟨11224652875241120200168013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7483101916827413466778675 11224652875241120200168013)
                    ·
                      refine ⟨4209244828215420075063005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11224652875241120200168013 4209244828215420075063005)
                      ·
                        rfl

theorem cell23_8197475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 1, 2, 1, 3].length) (baseStart_8197475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197475 prefixEnd_8197475 := by exact prefixLift 8197475
  have htrace : WordTrace (prefixWord ++ tailWord_8197475) baseStart_8197475 baseEnd_8197475 := by
    simpa [prefixWord, tailWord_8197475, baseEnd_8197475] using wordTrace_append hprefix tailTrace_8197475
  have hstable : (prefixWord ++ tailWord_8197475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197475).length < 2 ^ (prefixWord ++ tailWord_8197475).sum := by decide
  have hdescent : baseEnd_8197475 < baseStart_8197475 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
