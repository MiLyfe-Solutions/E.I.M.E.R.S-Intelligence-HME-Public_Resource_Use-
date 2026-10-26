import V185TrunkScan23Chunk1122

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6652023 : List Nat := [1, 1, 3, 1, 1, 6, 1, 2, 2, 1, 4]
def baseStart_6652023 : Nat := 118140960795 + 6652023 * 2 ^ 59
def prefixEnd_6652023 : Nat := 4983230072969 + 3 ^ 40 * 6652023 * 2
def baseEnd_6652023 : Nat := 3415685123763132663120409

theorem tailTrace_6652023 : CollatzResearch.WordTrace tailWord_6652023 prefixEnd_6652023 3415685123763132663120409 := by
  unfold tailWord_6652023
  simp only [CollatzResearch.WordTrace]
  refine ⟨242619210779864220925952723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161746140519909480617301815 242619210779864220925952723)
  ·
    refine ⟨363928816169796331388929085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242619210779864220925952723 363928816169796331388929085)
    ·
      refine ⟨136473306063673624270848407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 363928816169796331388929085 136473306063673624270848407)
      ·
        refine ⟨204709959095510436406272611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136473306063673624270848407 204709959095510436406272611)
        ·
          refine ⟨307064938643265654609408917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204709959095510436406272611 307064938643265654609408917)
          ·
            refine ⟨14393668998903077559816043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 307064938643265654609408917 14393668998903077559816043)
            ·
              refine ⟨21590503498354616339724065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14393668998903077559816043 21590503498354616339724065)
              ·
                refine ⟨16192877623765962254793049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21590503498354616339724065 16192877623765962254793049)
                ·
                  refine ⟨12144658217824471691094787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16192877623765962254793049 12144658217824471691094787)
                  ·
                    refine ⟨18216987326736707536642181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12144658217824471691094787 18216987326736707536642181)
                    ·
                      refine ⟨3415685123763132663120409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18216987326736707536642181 3415685123763132663120409)
                      ·
                        rfl

theorem cell23_6652023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 2, 1, 4].length) (baseStart_6652023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6652023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6652023 prefixEnd_6652023 := by exact prefixLift 6652023
  have htrace : WordTrace (prefixWord ++ tailWord_6652023) baseStart_6652023 baseEnd_6652023 := by
    simpa [prefixWord, tailWord_6652023, baseEnd_6652023] using wordTrace_append hprefix tailTrace_6652023
  have hstable : (prefixWord ++ tailWord_6652023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6652023).length < 2 ^ (prefixWord ++ tailWord_6652023).sum := by decide
  have hdescent : baseEnd_6652023 < baseStart_6652023 := by decide
  rcases family_descends (prefixWord ++ tailWord_6652023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6652026 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 2, 8, 3]
def baseStart_6652026 : Nat := 118140960795 + 6652026 * 2 ^ 59
def prefixEnd_6652026 : Nat := 4983230072969 + 3 ^ 40 * 6652026 * 2
def baseEnd_6652026 : Nat := 3415686664205096151382895

theorem tailTrace_6652026 : CollatzResearch.WordTrace tailWord_6652026 prefixEnd_6652026 3415686664205096151382895 := by
  unfold tailWord_6652026
  simp only [CollatzResearch.WordTrace]
  refine ⟨60654830049713338109577983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161746213465902234958874621 60654830049713338109577983)
  ·
    refine ⟨90982245074570007164366975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60654830049713338109577983 90982245074570007164366975)
    ·
      refine ⟨136473367611855010746550463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90982245074570007164366975 136473367611855010746550463)
      ·
        refine ⟨204710051417782516119825695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136473367611855010746550463 204710051417782516119825695)
        ·
          refine ⟨307065077126673774179738543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204710051417782516119825695 307065077126673774179738543)
          ·
            refine ⟨460597615690010661269607815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307065077126673774179738543 460597615690010661269607815)
            ·
              refine ⟨690896423535015991904411723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 460597615690010661269607815 690896423535015991904411723)
              ·
                refine ⟨1036344635302523987856617585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 690896423535015991904411723 1036344635302523987856617585)
                ·
                  refine ⟨777258476476892990892463189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1036344635302523987856617585 777258476476892990892463189)
                  ·
                    refine ⟨9108497771213589737021053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 777258476476892990892463189 9108497771213589737021053)
                    ·
                      refine ⟨3415686664205096151382895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9108497771213589737021053 3415686664205096151382895)
                      ·
                        rfl

theorem cell23_6652026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 2, 8, 3].length) (baseStart_6652026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6652026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6652026 prefixEnd_6652026 := by exact prefixLift 6652026
  have htrace : WordTrace (prefixWord ++ tailWord_6652026) baseStart_6652026 baseEnd_6652026 := by
    simpa [prefixWord, tailWord_6652026, baseEnd_6652026] using wordTrace_append hprefix tailTrace_6652026
  have hstable : (prefixWord ++ tailWord_6652026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6652026).length < 2 ^ (prefixWord ++ tailWord_6652026).sum := by decide
  have hdescent : baseEnd_6652026 < baseStart_6652026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6652026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6652060 : List Nat := [2, 2, 3, 2, 1, 1, 4, 1, 2, 2, 3]
def baseStart_6652060 : Nat := 118140960795 + 6652060 * 2 ^ 59
def prefixEnd_6652060 : Nat := 4983230072969 + 3 ^ 40 * 6652060 * 2
def baseEnd_6652060 : Nat := 3415704122547349018357739

theorem tailTrace_6652060 : CollatzResearch.WordTrace tailWord_6652060 prefixEnd_6652060 3415704122547349018357739 := by
  unfold tailWord_6652060
  simp only [CollatzResearch.WordTrace]
  refine ⟨121310280140365088122524817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161747040187153450830033089 121310280140365088122524817)
  ·
    refine ⟨90982710105273816091893613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121310280140365088122524817 90982710105273816091893613)
    ·
      refine ⟨34118516289477681034460105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90982710105273816091893613 34118516289477681034460105)
      ·
        refine ⟨25588887217108260775845079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34118516289477681034460105 25588887217108260775845079)
        ·
          refine ⟨38383330825662391163767619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25588887217108260775845079 38383330825662391163767619)
          ·
            refine ⟨57574996238493586745651429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38383330825662391163767619 57574996238493586745651429)
            ·
              refine ⟨10795311794717547514809643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57574996238493586745651429 10795311794717547514809643)
              ·
                refine ⟨16192967692076321272214465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10795311794717547514809643 16192967692076321272214465)
                ·
                  refine ⟨12144725769057240954160849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16192967692076321272214465 12144725769057240954160849)
                  ·
                    refine ⟨9108544326792930715620637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12144725769057240954160849 9108544326792930715620637)
                    ·
                      refine ⟨3415704122547349018357739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9108544326792930715620637 3415704122547349018357739)
                      ·
                        rfl

theorem cell23_6652060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_6652060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6652060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6652060 prefixEnd_6652060 := by exact prefixLift 6652060
  have htrace : WordTrace (prefixWord ++ tailWord_6652060) baseStart_6652060 baseEnd_6652060 := by
    simpa [prefixWord, tailWord_6652060, baseEnd_6652060] using wordTrace_append hprefix tailTrace_6652060
  have hstable : (prefixWord ++ tailWord_6652060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6652060).length < 2 ^ (prefixWord ++ tailWord_6652060).sum := by decide
  have hdescent : baseEnd_6652060 < baseStart_6652060 := by decide
  rcases family_descends (prefixWord ++ tailWord_6652060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6652083 : List Nat := [1, 1, 1, 2, 3, 2, 1, 2, 3, 5, 2]
def baseStart_6652083 : Nat := 118140960795 + 6652083 * 2 ^ 59
def prefixEnd_6652083 : Nat := 4983230072969 + 3 ^ 40 * 6652083 * 2
def baseEnd_6652083 : Nat := 3415715932602402428370133

theorem tailTrace_6652083 : CollatzResearch.WordTrace tailWord_6652083 prefixEnd_6652083 3415715932602402428370133 := by
  unfold tailWord_6652083
  simp only [CollatzResearch.WordTrace]
  refine ⟨242621399159646851173136903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161747599439764567448757935 242621399159646851173136903)
  ·
    refine ⟨363932098739470276759705355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242621399159646851173136903 363932098739470276759705355)
    ·
      refine ⟨545898148109205415139558033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363932098739470276759705355 545898148109205415139558033)
      ·
        refine ⟨409423611081904061354668525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 545898148109205415139558033 409423611081904061354668525)
        ·
          refine ⟨153533854155714023008000697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 409423611081904061354668525 153533854155714023008000697)
          ·
            refine ⟨115150390616785517256000523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153533854155714023008000697 115150390616785517256000523)
            ·
              refine ⟨172725585925178275884000785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115150390616785517256000523 172725585925178275884000785)
              ·
                refine ⟨129544189443883706913000589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172725585925178275884000785 129544189443883706913000589)
                ·
                  refine ⟨48579071041456390092375221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129544189443883706913000589 48579071041456390092375221)
                  ·
                    refine ⟨4554287910136536571160177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48579071041456390092375221 4554287910136536571160177)
                    ·
                      refine ⟨3415715932602402428370133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4554287910136536571160177 3415715932602402428370133)
                      ·
                        rfl

theorem cell23_6652083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 5, 2].length) (baseStart_6652083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6652083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6652083 prefixEnd_6652083 := by exact prefixLift 6652083
  have htrace : WordTrace (prefixWord ++ tailWord_6652083) baseStart_6652083 baseEnd_6652083 := by
    simpa [prefixWord, tailWord_6652083, baseEnd_6652083] using wordTrace_append hprefix tailTrace_6652083
  have hstable : (prefixWord ++ tailWord_6652083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6652083).length < 2 ^ (prefixWord ++ tailWord_6652083).sum := by decide
  have hdescent : baseEnd_6652083 < baseStart_6652083 := by decide
  rcases family_descends (prefixWord ++ tailWord_6652083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6652113 : List Nat := [1, 2, 2, 1, 2, 2, 4, 1, 3, 1, 4]
def baseStart_6652113 : Nat := 118140960795 + 6652113 * 2 ^ 59
def prefixEnd_6652113 : Nat := 4983230072969 + 3 ^ 40 * 6652113 * 2
def baseEnd_6652113 : Nat := 3415731337022037310994995

theorem tailTrace_6652113 : CollatzResearch.WordTrace tailWord_6652113 prefixEnd_6652113 3415731337022037310994995 := by
  unfold tailWord_6652113
  simp only [CollatzResearch.WordTrace]
  refine ⟨242622493349538166296728993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161748328899692110864485995 242622493349538166296728993)
  ·
    refine ⟨181966870012153624722546745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242622493349538166296728993 181966870012153624722546745)
    ·
      refine ⟨136475152509115218541910059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181966870012153624722546745 136475152509115218541910059)
      ·
        refine ⟨204712728763672827812865089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136475152509115218541910059 204712728763672827812865089)
        ·
          refine ⟨153534546572754620859648817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204712728763672827812865089 153534546572754620859648817)
          ·
            refine ⟨115150909929565965644736613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153534546572754620859648817 115150909929565965644736613)
            ·
              refine ⟨21590795611793618558388115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115150909929565965644736613 21590795611793618558388115)
              ·
                refine ⟨32386193417690427837582173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21590795611793618558388115 32386193417690427837582173)
                ·
                  refine ⟨12144822531633910439093315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32386193417690427837582173 12144822531633910439093315)
                  ·
                    refine ⟨18217233797450865658639973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12144822531633910439093315 18217233797450865658639973)
                    ·
                      refine ⟨3415731337022037310994995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18217233797450865658639973 3415731337022037310994995)
                      ·
                        rfl

theorem cell23_6652113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 3, 1, 4].length) (baseStart_6652113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6652113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6652113 prefixEnd_6652113 := by exact prefixLift 6652113
  have htrace : WordTrace (prefixWord ++ tailWord_6652113) baseStart_6652113 baseEnd_6652113 := by
    simpa [prefixWord, tailWord_6652113, baseEnd_6652113] using wordTrace_append hprefix tailTrace_6652113
  have hstable : (prefixWord ++ tailWord_6652113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6652113).length < 2 ^ (prefixWord ++ tailWord_6652113).sum := by decide
  have hdescent : baseEnd_6652113 < baseStart_6652113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6652113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6652117 : List Nat := [1, 3, 2, 4, 2, 1, 1, 1, 1, 5, 2]
def baseStart_6652117 : Nat := 118140960795 + 6652117 * 2 ^ 59
def prefixEnd_6652117 : Nat := 4983230072969 + 3 ^ 40 * 6652117 * 2
def baseEnd_6652117 : Nat := 3415733390944655295344977

theorem tailTrace_6652117 : CollatzResearch.WordTrace tailWord_6652117 prefixEnd_6652117 3415733390944655295344977 := by
  unfold tailWord_6652117
  simp only [CollatzResearch.WordTrace]
  refine ⟨242622639241523674979874605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161748426161015783319916403 242622639241523674979874605)
  ·
    refine ⟨90983489715571378117452977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242622639241523674979874605 90983489715571378117452977)
    ·
      refine ⟨68237617286678533588089733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90983489715571378117452977 68237617286678533588089733)
      ·
        refine ⟨12794553241252225047766825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68237617286678533588089733 12794553241252225047766825)
        ·
          refine ⟨9595914930939168785825119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12794553241252225047766825 9595914930939168785825119)
          ·
            refine ⟨14393872396408753178737679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9595914930939168785825119 14393872396408753178737679)
            ·
              refine ⟨21590808594613129768106519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14393872396408753178737679 21590808594613129768106519)
              ·
                refine ⟨32386212891919694652159779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21590808594613129768106519 32386212891919694652159779)
                ·
                  refine ⟨48579319337879541978239669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32386212891919694652159779 48579319337879541978239669)
                  ·
                    refine ⟨4554311187926207060459969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48579319337879541978239669 4554311187926207060459969)
                    ·
                      refine ⟨3415733390944655295344977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4554311187926207060459969 3415733390944655295344977)
                      ·
                        rfl

theorem cell23_6652117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_6652117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6652117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6652117 prefixEnd_6652117 := by exact prefixLift 6652117
  have htrace : WordTrace (prefixWord ++ tailWord_6652117) baseStart_6652117 baseEnd_6652117 := by
    simpa [prefixWord, tailWord_6652117, baseEnd_6652117] using wordTrace_append hprefix tailTrace_6652117
  have hstable : (prefixWord ++ tailWord_6652117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6652117).length < 2 ^ (prefixWord ++ tailWord_6652117).sum := by decide
  have hdescent : baseEnd_6652117 < baseStart_6652117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6652117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6652147 : List Nat := [1, 1, 1, 2, 2, 4, 4, 1, 3, 2, 2]
def baseStart_6652147 : Nat := 118140960795 + 6652147 * 2 ^ 59
def prefixEnd_6652147 : Nat := 4983230072969 + 3 ^ 40 * 6652147 * 2
def baseEnd_6652147 : Nat := 3415748795364290177969839

theorem tailTrace_6652147 : CollatzResearch.WordTrace tailWord_6652147 prefixEnd_6652147 3415748795364290177969839 := by
  unfold tailWord_6652147
  simp only [CollatzResearch.WordTrace]
  refine ⟨242623733431414990103466695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161749155620943326735644463 242623733431414990103466695)
  ·
    refine ⟨363935600147122485155200043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242623733431414990103466695 363935600147122485155200043)
    ·
      refine ⟨545903400220683727732800065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363935600147122485155200043 545903400220683727732800065)
      ·
        refine ⟨409427550165512795799600049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 545903400220683727732800065 409427550165512795799600049)
        ·
          refine ⟨307070662624134596849700037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 409427550165512795799600049 307070662624134596849700037)
          ·
            refine ⟨57575749242025236909318757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 307070662624134596849700037 57575749242025236909318757)
            ·
              refine ⟨10795452982879731920497267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57575749242025236909318757 10795452982879731920497267)
              ·
                refine ⟨16193179474319597880745901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10795452982879731920497267 16193179474319597880745901)
                ·
                  refine ⟨6072442302869849205279713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16193179474319597880745901 6072442302869849205279713)
                  ·
                    refine ⟨4554331727152386903959785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6072442302869849205279713 4554331727152386903959785)
                    ·
                      refine ⟨3415748795364290177969839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4554331727152386903959785 3415748795364290177969839)
                      ·
                        rfl

theorem cell23_6652147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 3, 2, 2].length) (baseStart_6652147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6652147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6652147 prefixEnd_6652147 := by exact prefixLift 6652147
  have htrace : WordTrace (prefixWord ++ tailWord_6652147) baseStart_6652147 baseEnd_6652147 := by
    simpa [prefixWord, tailWord_6652147, baseEnd_6652147] using wordTrace_append hprefix tailTrace_6652147
  have hstable : (prefixWord ++ tailWord_6652147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6652147).length < 2 ^ (prefixWord ++ tailWord_6652147).sum := by decide
  have hdescent : baseEnd_6652147 < baseStart_6652147 := by decide
  rcases family_descends (prefixWord ++ tailWord_6652147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6652150 : List Nat := [5, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3]
def baseStart_6652150 : Nat := 118140960795 + 6652150 * 2 ^ 59
def prefixEnd_6652150 : Nat := 4983230072969 + 3 ^ 40 * 6652150 * 2
def baseEnd_6652150 : Nat := 3415750335806253666232325

theorem tailTrace_6652150 : CollatzResearch.WordTrace tailWord_6652150 prefixEnd_6652150 3415750335806253666232325 := by
  unfold tailWord_6652150
  simp only [CollatzResearch.WordTrace]
  refine ⟨15163990178150257600989119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161749228566936081077217269 15163990178150257600989119)
  ·
    refine ⟨22745985267225386401483679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15163990178150257600989119 22745985267225386401483679)
    ·
      refine ⟨34118977900838079602225519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22745985267225386401483679 34118977900838079602225519)
      ·
        refine ⟨51178466851257119403338279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34118977900838079602225519 51178466851257119403338279)
        ·
          refine ⟨76767700276885679105007419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51178466851257119403338279 76767700276885679105007419)
          ·
            refine ⟨115151550415328518657511129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76767700276885679105007419 115151550415328518657511129)
            ·
              refine ⟨86363662811496388993133347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115151550415328518657511129 86363662811496388993133347)
              ·
                refine ⟨129545494217244583489700021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86363662811496388993133347 129545494217244583489700021)
                ·
                  refine ⟨12144890082866679702159377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 129545494217244583489700021 12144890082866679702159377)
                  ·
                    refine ⟨9108667562150009776619533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12144890082866679702159377 9108667562150009776619533)
                    ·
                      refine ⟨3415750335806253666232325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9108667562150009776619533 3415750335806253666232325)
                      ·
                        rfl

theorem cell23_6652150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_6652150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6652150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6652150 prefixEnd_6652150 := by exact prefixLift 6652150
  have htrace : WordTrace (prefixWord ++ tailWord_6652150) baseStart_6652150 baseEnd_6652150 := by
    simpa [prefixWord, tailWord_6652150, baseEnd_6652150] using wordTrace_append hprefix tailTrace_6652150
  have hstable : (prefixWord ++ tailWord_6652150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6652150).length < 2 ^ (prefixWord ++ tailWord_6652150).sum := by decide
  have hdescent : baseEnd_6652150 < baseStart_6652150 := by decide
  rcases family_descends (prefixWord ++ tailWord_6652150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6652213 : List Nat := [1, 3, 3, 1, 2, 1, 2, 1, 1, 8]
def baseStart_6652213 : Nat := 118140960795 + 6652213 * 2 ^ 59
def prefixEnd_6652213 : Nat := 4983230072969 + 3 ^ 40 * 6652213 * 2
def baseEnd_6652213 : Nat := 1138594228362495639914845

theorem tailTrace_6652213 : CollatzResearch.WordTrace tailWord_6652213 prefixEnd_6652213 1138594228362495639914845 := by
  unfold tailWord_6652213
  simp only [CollatzResearch.WordTrace]
  refine ⟨242626140649175883375369293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161750760432783922250246195 242626140649175883375369293)
  ·
    refine ⟨90984802743440956265763485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242626140649175883375369293 90984802743440956265763485)
    ·
      refine ⟨34119301028790358599661307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90984802743440956265763485 34119301028790358599661307)
      ·
        refine ⟨51178951543185537899491961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34119301028790358599661307 51178951543185537899491961)
        ·
          refine ⟨38384213657389153424618971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51178951543185537899491961 38384213657389153424618971)
          ·
            refine ⟨57576320486083730136928457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38384213657389153424618971 57576320486083730136928457)
            ·
              refine ⟨43182240364562797602696343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57576320486083730136928457 43182240364562797602696343)
              ·
                refine ⟨64773360546844196404044515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43182240364562797602696343 64773360546844196404044515)
                ·
                  refine ⟨97160040820266294606066773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64773360546844196404044515 97160040820266294606066773)
                  ·
                    refine ⟨1138594228362495639914845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 97160040820266294606066773 1138594228362495639914845)
                    ·
                      rfl

theorem cell23_6652213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_6652213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6652213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6652213 prefixEnd_6652213 := by exact prefixLift 6652213
  have htrace : WordTrace (prefixWord ++ tailWord_6652213) baseStart_6652213 baseEnd_6652213 := by
    simpa [prefixWord, tailWord_6652213, baseEnd_6652213] using wordTrace_append hprefix tailTrace_6652213
  have hstable : (prefixWord ++ tailWord_6652213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6652213).length < 2 ^ (prefixWord ++ tailWord_6652213).sum := by decide
  have hdescent : baseEnd_6652213 < baseStart_6652213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6652213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6652223 : List Nat := [1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 5]
def baseStart_6652223 : Nat := 118140960795 + 6652223 * 2 ^ 59
def prefixEnd_6652223 : Nat := 4983230072969 + 3 ^ 40 * 6652223 * 2
def baseEnd_6652223 : Nat := 3415787819894031880619489

theorem tailTrace_6652223 : CollatzResearch.WordTrace tailWord_6652223 prefixEnd_6652223 3415787819894031880619489 := by
  unfold tailWord_6652223
  simp only [CollatzResearch.WordTrace]
  refine ⟨242626505379139655083233323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161751003586093103388822215 242626505379139655083233323)
  ·
    refine ⟨363939758068709482624849985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242626505379139655083233323 363939758068709482624849985)
    ·
      refine ⟨272954818551532111968637489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363939758068709482624849985 272954818551532111968637489)
      ·
        refine ⟨204716113913649083976478117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272954818551532111968637489 204716113913649083976478117)
        ·
          refine ⟨38384271358809203245589647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 204716113913649083976478117 38384271358809203245589647)
          ·
            refine ⟨57576407038213804868384471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38384271358809203245589647 57576407038213804868384471)
            ·
              refine ⟨86364610557320707302576707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57576407038213804868384471 86364610557320707302576707)
              ·
                refine ⟨129546915835981060953865061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86364610557320707302576707 129546915835981060953865061)
                ·
                  refine ⟨24290046719246448928849699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 129546915835981060953865061 24290046719246448928849699)
                  ·
                    refine ⟨36435070078869673393274549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24290046719246448928849699 36435070078869673393274549)
                    ·
                      refine ⟨3415787819894031880619489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36435070078869673393274549 3415787819894031880619489)
                      ·
                        rfl

theorem cell23_6652223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 5].length) (baseStart_6652223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6652223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6652223 prefixEnd_6652223 := by exact prefixLift 6652223
  have htrace : WordTrace (prefixWord ++ tailWord_6652223) baseStart_6652223 baseEnd_6652223 := by
    simpa [prefixWord, tailWord_6652223, baseEnd_6652223] using wordTrace_append hprefix tailTrace_6652223
  have hstable : (prefixWord ++ tailWord_6652223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6652223).length < 2 ^ (prefixWord ++ tailWord_6652223).sum := by decide
  have hdescent : baseEnd_6652223 < baseStart_6652223 := by decide
  rcases family_descends (prefixWord ++ tailWord_6652223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6652233 : List Nat := [1, 2, 1, 1, 2, 3, 1, 2, 4, 2, 4]
def baseStart_6652233 : Nat := 118140960795 + 6652233 * 2 ^ 59
def prefixEnd_6652233 : Nat := 4983230072969 + 3 ^ 40 * 6652233 * 2
def baseEnd_6652233 : Nat := 3415792954700576841494443

theorem tailTrace_6652233 : CollatzResearch.WordTrace tailWord_6652233 prefixEnd_6652233 3415792954700576841494443 := by
  unfold tailWord_6652233
  simp only [CollatzResearch.WordTrace]
  refine ⟨242626870109103426791097353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161751246739402284527398235 242626870109103426791097353)
  ·
    refine ⟨181970152581827570093323015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242626870109103426791097353 181970152581827570093323015)
    ·
      refine ⟨272955228872741355139984523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181970152581827570093323015 272955228872741355139984523)
      ·
        refine ⟨409432843309112032709976785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272955228872741355139984523 409432843309112032709976785)
        ·
          refine ⟨307074632481834024532482589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 409432843309112032709976785 307074632481834024532482589)
          ·
            refine ⟨115152987180687759199680971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 307074632481834024532482589 115152987180687759199680971)
            ·
              refine ⟨172729480771031638799521457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115152987180687759199680971 172729480771031638799521457)
              ·
                refine ⟨129547110578273729099641093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172729480771031638799521457 129547110578273729099641093)
                ·
                  refine ⟨24290083233426324206182705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 129547110578273729099641093 24290083233426324206182705)
                  ·
                    refine ⟨18217562425069743154637029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24290083233426324206182705 18217562425069743154637029)
                    ·
                      refine ⟨3415792954700576841494443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18217562425069743154637029 3415792954700576841494443)
                      ·
                        rfl

theorem cell23_6652233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 2, 4].length) (baseStart_6652233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6652233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6652233 prefixEnd_6652233 := by exact prefixLift 6652233
  have htrace : WordTrace (prefixWord ++ tailWord_6652233) baseStart_6652233 baseEnd_6652233 := by
    simpa [prefixWord, tailWord_6652233, baseEnd_6652233] using wordTrace_append hprefix tailTrace_6652233
  have hstable : (prefixWord ++ tailWord_6652233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6652233).length < 2 ^ (prefixWord ++ tailWord_6652233).sum := by decide
  have hdescent : baseEnd_6652233 < baseStart_6652233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6652233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6652273 : List Nat := [1, 2, 2, 2, 1, 2, 1, 4, 1, 7]
def baseStart_6652273 : Nat := 118140960795 + 6652273 * 2 ^ 59
def prefixEnd_6652273 : Nat := 4983230072969 + 3 ^ 40 * 6652273 * 2
def baseEnd_6652273 : Nat := 1138604497975585561664753

theorem tailTrace_6652273 : CollatzResearch.WordTrace tailWord_6652273 prefixEnd_6652273 1138604497975585561664753 := by
  unfold tailWord_6652273
  simp only [CollatzResearch.WordTrace]
  refine ⟨242628329028958513622553473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161752219352639009081702315 242628329028958513622553473)
  ·
    refine ⟨181971246771718885216915105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242628329028958513622553473 181971246771718885216915105)
    ·
      refine ⟨136478435078789163912686329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181971246771718885216915105 136478435078789163912686329)
      ·
        refine ⟨102358826309091872934514747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136478435078789163912686329 102358826309091872934514747)
        ·
          refine ⟨153538239463637809401772121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102358826309091872934514747 153538239463637809401772121)
          ·
            refine ⟨115153679597728357051329091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153538239463637809401772121 115153679597728357051329091)
            ·
              refine ⟨172730519396592535576993637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115153679597728357051329091 172730519396592535576993637)
              ·
                refine ⟨32386972386861100420686307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 172730519396592535576993637 32386972386861100420686307)
                ·
                  refine ⟨48580458580291650631029461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32386972386861100420686307 48580458580291650631029461)
                  ·
                    refine ⟨1138604497975585561664753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48580458580291650631029461 1138604497975585561664753)
                    ·
                      rfl

theorem cell23_6652273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 7].length) (baseStart_6652273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6652273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6652273 prefixEnd_6652273 := by exact prefixLift 6652273
  have htrace : WordTrace (prefixWord ++ tailWord_6652273) baseStart_6652273 baseEnd_6652273 := by
    simpa [prefixWord, tailWord_6652273, baseEnd_6652273] using wordTrace_append hprefix tailTrace_6652273
  have hstable : (prefixWord ++ tailWord_6652273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6652273).length < 2 ^ (prefixWord ++ tailWord_6652273).sum := by decide
  have hdescent : baseEnd_6652273 < baseStart_6652273 := by decide
  rcases family_descends (prefixWord ++ tailWord_6652273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6652337 : List Nat := [1, 2, 2, 4, 1, 2, 2, 2, 3, 4]
def baseStart_6652337 : Nat := 118140960795 + 6652337 * 2 ^ 59
def prefixEnd_6652337 : Nat := 4983230072969 + 3 ^ 40 * 6652337 * 2
def baseEnd_6652337 : Nat := 1138615452229548144864655

theorem tailTrace_6652337 : CollatzResearch.WordTrace tailWord_6652337 prefixEnd_6652337 1138615452229548144864655 := by
  unfold tailWord_6652337
  simp only [CollatzResearch.WordTrace]
  refine ⟨242630663300726652552883265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161753775533817768368588843 242630663300726652552883265)
  ·
    refine ⟨181972997475544989414662449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242630663300726652552883265 181972997475544989414662449)
    ·
      refine ⟨136479748106658742060996837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181972997475544989414662449 136479748106658742060996837)
      ·
        refine ⟨25589952769998514136436907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136479748106658742060996837 25589952769998514136436907)
        ·
          refine ⟨38384929154997771204655361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25589952769998514136436907 38384929154997771204655361)
          ·
            refine ⟨28788696866248328403491521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38384929154997771204655361 28788696866248328403491521)
            ·
              refine ⟨21591522649686246302618641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28788696866248328403491521 21591522649686246302618641)
              ·
                refine ⟨16193641987264684726963981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21591522649686246302618641 16193641987264684726963981)
                ·
                  refine ⟨6072615745224256772611493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16193641987264684726963981 6072615745224256772611493)
                  ·
                    refine ⟨1138615452229548144864655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6072615745224256772611493 1138615452229548144864655)
                    ·
                      rfl

theorem cell23_6652337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 3, 4].length) (baseStart_6652337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6652337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6652337 prefixEnd_6652337 := by exact prefixLift 6652337
  have htrace : WordTrace (prefixWord ++ tailWord_6652337) baseStart_6652337 baseEnd_6652337 := by
    simpa [prefixWord, tailWord_6652337, baseEnd_6652337] using wordTrace_append hprefix tailTrace_6652337
  have hstable : (prefixWord ++ tailWord_6652337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6652337).length < 2 ^ (prefixWord ++ tailWord_6652337).sum := by decide
  have hdescent : baseEnd_6652337 < baseStart_6652337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6652337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6652350 : List Nat := [4, 2, 1, 1, 1, 1, 3, 2, 8]
def baseStart_6652350 : Nat := 118140960795 + 6652350 * 2 ^ 59
def prefixEnd_6652350 : Nat := 4983230072969 + 3 ^ 40 * 6652350 * 2
def baseEnd_6652350 : Nat := 379539225770794764859045

theorem tailTrace_6652350 : CollatzResearch.WordTrace tailWord_6652350 prefixEnd_6652350 379539225770794764859045 := by
  unfold tailWord_6652350
  simp only [CollatzResearch.WordTrace]
  refine ⟨30328892181209944471638313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161754091633119703848737669 30328892181209944471638313)
  ·
    refine ⟨22746669135907458353728735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30328892181209944471638313 22746669135907458353728735)
    ·
      refine ⟨34120003703861187530593103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22746669135907458353728735 34120003703861187530593103)
      ·
        refine ⟨51180005555791781295889655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34120003703861187530593103 51180005555791781295889655)
        ·
          refine ⟨76770008333687671943834483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51180005555791781295889655 76770008333687671943834483)
          ·
            refine ⟨115155012500531507915751725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76770008333687671943834483 115155012500531507915751725)
            ·
              refine ⟨43183129687699315468406897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115155012500531507915751725 43183129687699315468406897)
              ·
                refine ⟨32387347265774486601305173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43183129687699315468406897 32387347265774486601305173)
                ·
                  refine ⟨379539225770794764859045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32387347265774486601305173 379539225770794764859045)
                  ·
                    rfl

theorem cell23_6652350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 8].length) (baseStart_6652350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6652350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6652350 prefixEnd_6652350 := by exact prefixLift 6652350
  have htrace : WordTrace (prefixWord ++ tailWord_6652350) baseStart_6652350 baseEnd_6652350 := by
    simpa [prefixWord, tailWord_6652350, baseEnd_6652350] using wordTrace_append hprefix tailTrace_6652350
  have hstable : (prefixWord ++ tailWord_6652350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6652350).length < 2 ^ (prefixWord ++ tailWord_6652350).sum := by decide
  have hdescent : baseEnd_6652350 < baseStart_6652350 := by decide
  rcases family_descends (prefixWord ++ tailWord_6652350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6652364 : List Nat := [2, 2, 1, 4, 3, 1, 1, 2, 2, 2, 3]
def baseStart_6652364 : Nat := 118140960795 + 6652364 * 2 ^ 59
def prefixEnd_6652364 : Nat := 4983230072969 + 3 ^ 40 * 6652364 * 2
def baseEnd_6652364 : Nat := 3415860220666315828956341

theorem tailTrace_6652364 : CollatzResearch.WordTrace tailWord_6652364 prefixEnd_6652364 3415860220666315828956341 := by
  unfold tailWord_6652364
  simp only [CollatzResearch.WordTrace]
  refine ⟨121315824035814418082058073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161754432047752557442744097 121315824035814418082058073)
  ·
    refine ⟨90986868026860813561543555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121315824035814418082058073 90986868026860813561543555)
    ·
      refine ⟨136480302040291220342315333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90986868026860813561543555 136480302040291220342315333)
      ·
        refine ⟨25590056632554603814184125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136480302040291220342315333 25590056632554603814184125)
        ·
          refine ⟨9596271237207976430319047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25590056632554603814184125 9596271237207976430319047)
          ·
            refine ⟨14394406855811964645478571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9596271237207976430319047 14394406855811964645478571)
            ·
              refine ⟨21591610283717946968217857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14394406855811964645478571 21591610283717946968217857)
              ·
                refine ⟨16193707712788460226163393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21591610283717946968217857 16193707712788460226163393)
                ·
                  refine ⟨12145280784591345169622545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16193707712788460226163393 12145280784591345169622545)
                  ·
                    refine ⟨9108960588443508877216909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12145280784591345169622545 9108960588443508877216909)
                    ·
                      refine ⟨3415860220666315828956341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9108960588443508877216909 3415860220666315828956341)
                      ·
                        rfl

theorem cell23_6652364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_6652364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6652364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6652364 prefixEnd_6652364 := by exact prefixLift 6652364
  have htrace : WordTrace (prefixWord ++ tailWord_6652364) baseStart_6652364 baseEnd_6652364 := by
    simpa [prefixWord, tailWord_6652364, baseEnd_6652364] using wordTrace_append hprefix tailTrace_6652364
  have hstable : (prefixWord ++ tailWord_6652364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6652364).length < 2 ^ (prefixWord ++ tailWord_6652364).sum := by decide
  have hdescent : baseEnd_6652364 < baseStart_6652364 := by decide
  rcases family_descends (prefixWord ++ tailWord_6652364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6652422 : List Nat := [6, 2, 1, 1, 1, 1, 4, 2, 1, 4]
def baseStart_6652422 : Nat := 118140960795 + 6652422 * 2 ^ 59
def prefixEnd_6652422 : Nat := 4983230072969 + 3 ^ 40 * 6652422 * 2
def baseEnd_6652422 : Nat := 1138630000848092200677025

theorem tailTrace_6652422 : CollatzResearch.WordTrace tailWord_6652422 prefixEnd_6652422 1138630000848092200677025 := by
  unfold tailWord_6652422
  simp only [CollatzResearch.WordTrace]
  refine ⟨7582305109544334752178985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 161755842336945808046485013 7582305109544334752178985)
  ·
    refine ⟨5686728832158251064134239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7582305109544334752178985 5686728832158251064134239)
    ·
      refine ⟨8530093248237376596201359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5686728832158251064134239 8530093248237376596201359)
      ·
        refine ⟨12795139872356064894302039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8530093248237376596201359 12795139872356064894302039)
        ·
          refine ⟨19192709808534097341453059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12795139872356064894302039 19192709808534097341453059)
          ·
            refine ⟨28789064712801146012179589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19192709808534097341453059 28789064712801146012179589)
            ·
              refine ⟨5397949633650214877283673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28789064712801146012179589 5397949633650214877283673)
              ·
                refine ⟨4048462225237661157962755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5397949633650214877283673 4048462225237661157962755)
                ·
                  refine ⟨6072693337856491736944133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4048462225237661157962755 6072693337856491736944133)
                  ·
                    refine ⟨1138630000848092200677025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6072693337856491736944133 1138630000848092200677025)
                    ·
                      rfl

theorem cell23_6652422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_6652422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6652422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6652422 prefixEnd_6652422 := by exact prefixLift 6652422
  have htrace : WordTrace (prefixWord ++ tailWord_6652422) baseStart_6652422 baseEnd_6652422 := by
    simpa [prefixWord, tailWord_6652422, baseEnd_6652422] using wordTrace_append hprefix tailTrace_6652422
  have hstable : (prefixWord ++ tailWord_6652422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6652422).length < 2 ^ (prefixWord ++ tailWord_6652422).sum := by decide
  have hdescent : baseEnd_6652422 < baseStart_6652422 := by decide
  rcases family_descends (prefixWord ++ tailWord_6652422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6652428 : List Nat := [2, 2, 1, 2, 4, 1, 4, 2, 1, 1, 3]
def baseStart_6652428 : Nat := 118140960795 + 6652428 * 2 ^ 59
def prefixEnd_6652428 : Nat := 4983230072969 + 3 ^ 40 * 6652428 * 2
def baseEnd_6652428 : Nat := 3415893083428203578556047

theorem tailTrace_6652428 : CollatzResearch.WordTrace tailWord_6652428 prefixEnd_6652428 3415893083428203578556047 := by
  unfold tailWord_6652428
  simp only [CollatzResearch.WordTrace]
  refine ⟨121316991171698487547222969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161755988228931316729630625 121316991171698487547222969)
  ·
    refine ⟨90987743378773865660417227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121316991171698487547222969 90987743378773865660417227)
    ·
      refine ⟨136481615068160798490625841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90987743378773865660417227 136481615068160798490625841)
      ·
        refine ⟨102361211301120598867969381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136481615068160798490625841 102361211301120598867969381)
        ·
          refine ⟨19192727118960112287744259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102361211301120598867969381 19192727118960112287744259)
          ·
            refine ⟨28789090678440168431616389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19192727118960112287744259 28789090678440168431616389)
            ·
              refine ⟨5397954502207531580928073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28789090678440168431616389 5397954502207531580928073)
              ·
                refine ⟨4048465876655648685696055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5397954502207531580928073 4048465876655648685696055)
                ·
                  refine ⟨6072698814983473028544083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4048465876655648685696055 6072698814983473028544083)
                  ·
                    refine ⟨9109048222475209542816125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6072698814983473028544083 9109048222475209542816125)
                    ·
                      refine ⟨3415893083428203578556047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9109048222475209542816125 3415893083428203578556047)
                      ·
                        rfl

theorem cell23_6652428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 2, 1, 1, 3].length) (baseStart_6652428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6652428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6652428 prefixEnd_6652428 := by exact prefixLift 6652428
  have htrace : WordTrace (prefixWord ++ tailWord_6652428) baseStart_6652428 baseEnd_6652428 := by
    simpa [prefixWord, tailWord_6652428, baseEnd_6652428] using wordTrace_append hprefix tailTrace_6652428
  have hstable : (prefixWord ++ tailWord_6652428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6652428).length < 2 ^ (prefixWord ++ tailWord_6652428).sum := by decide
  have hdescent : baseEnd_6652428 < baseStart_6652428 := by decide
  rcases family_descends (prefixWord ++ tailWord_6652428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6652437 : List Nat := [1, 3, 2, 1, 3, 1, 1, 1, 5, 2, 3]
def baseStart_6652437 : Nat := 118140960795 + 6652437 * 2 ^ 59
def prefixEnd_6652437 : Nat := 4983230072969 + 3 ^ 40 * 6652437 * 2
def baseEnd_6652437 : Nat := 3415897704754094043343505

theorem tailTrace_6652437 : CollatzResearch.WordTrace tailWord_6652437 prefixEnd_6652437 3415897704754094043343505 := by
  unfold tailWord_6652437
  simp only [CollatzResearch.WordTrace]
  refine ⟨242634310600364369631523565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161756207066909579754349043 242634310600364369631523565)
  ·
    refine ⟨90987866475136638611821337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242634310600364369631523565 90987866475136638611821337)
    ·
      refine ⟨68240899856352478958866003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90987866475136638611821337 68240899856352478958866003)
      ·
        refine ⟨102361349784528718438299005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68240899856352478958866003 102361349784528718438299005)
        ·
          refine ⟨38385506169198269414362127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102361349784528718438299005 38385506169198269414362127)
          ·
            refine ⟨57578259253797404121543191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38385506169198269414362127 57578259253797404121543191)
            ·
              refine ⟨86367388880696106182314787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57578259253797404121543191 86367388880696106182314787)
              ·
                refine ⟨129551083321044159273472181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86367388880696106182314787 129551083321044159273472181)
                ·
                  refine ⟨12145414061347889931888017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 129551083321044159273472181 12145414061347889931888017)
                  ·
                    refine ⟨9109060546010917448916013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12145414061347889931888017 9109060546010917448916013)
                    ·
                      refine ⟨3415897704754094043343505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9109060546010917448916013 3415897704754094043343505)
                      ·
                        rfl

theorem cell23_6652437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 5, 2, 3].length) (baseStart_6652437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6652437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6652437 prefixEnd_6652437 := by exact prefixLift 6652437
  have htrace : WordTrace (prefixWord ++ tailWord_6652437) baseStart_6652437 baseEnd_6652437 := by
    simpa [prefixWord, tailWord_6652437, baseEnd_6652437] using wordTrace_append hprefix tailTrace_6652437
  have hstable : (prefixWord ++ tailWord_6652437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6652437).length < 2 ^ (prefixWord ++ tailWord_6652437).sum := by decide
  have hdescent : baseEnd_6652437 < baseStart_6652437 := by decide
  rcases family_descends (prefixWord ++ tailWord_6652437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6652444 : List Nat := [2, 2, 3, 1, 2, 2, 2, 3, 2, 4]
def baseStart_6652444 : Nat := 118140960795 + 6652444 * 2 ^ 59
def prefixEnd_6652444 : Nat := 4983230072969 + 3 ^ 40 * 6652444 * 2
def baseEnd_6652444 : Nat := 1138633766372891838651991

theorem tailTrace_6652444 : CollatzResearch.WordTrace tailWord_6652444 prefixEnd_6652444 1138633766372891838651991 := by
  unfold tailWord_6652444
  simp only [CollatzResearch.WordTrace]
  refine ⟨121317282955669504913514193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161756377274226006551352257 121317282955669504913514193)
  ·
    refine ⟨90987962216752128685135645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121317282955669504913514193 90987962216752128685135645)
    ·
      refine ⟨34120485831282048256925867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90987962216752128685135645 34120485831282048256925867)
      ·
        refine ⟨51180728746923072385388801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34120485831282048256925867 51180728746923072385388801)
        ·
          refine ⟨38385546560192304289041601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51180728746923072385388801 38385546560192304289041601)
          ·
            refine ⟨28789159920144228216781201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38385546560192304289041601 28789159920144228216781201)
            ·
              refine ⟨21591869940108171162585901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28789159920144228216781201 21591869940108171162585901)
              ·
                refine ⟨8096951227540564185969713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21591869940108171162585901 8096951227540564185969713)
                ·
                  refine ⟨6072713420655423139477285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8096951227540564185969713 6072713420655423139477285)
                  ·
                    refine ⟨1138633766372891838651991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6072713420655423139477285 1138633766372891838651991)
                    ·
                      rfl

theorem cell23_6652444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_6652444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6652444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6652444 prefixEnd_6652444 := by exact prefixLift 6652444
  have htrace : WordTrace (prefixWord ++ tailWord_6652444) baseStart_6652444 baseEnd_6652444 := by
    simpa [prefixWord, tailWord_6652444, baseEnd_6652444] using wordTrace_append hprefix tailTrace_6652444
  have hstable : (prefixWord ++ tailWord_6652444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6652444).length < 2 ^ (prefixWord ++ tailWord_6652444).sum := by decide
  have hdescent : baseEnd_6652444 < baseStart_6652444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6652444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6652451 : List Nat := [1, 1, 1, 4, 4, 2, 1, 2, 3, 2, 2]
def baseStart_6652451 : Nat := 118140960795 + 6652451 * 2 ^ 59
def prefixEnd_6652451 : Nat := 4983230072969 + 3 ^ 40 * 6652451 * 2
def baseEnd_6652451 : Nat := 3415904893483256988568441

theorem tailTrace_6652451 : CollatzResearch.WordTrace tailWord_6652451 prefixEnd_6652451 3415904893483256988568441 := by
  unfold tailWord_6652451
  simp only [CollatzResearch.WordTrace]
  refine ⟨242634821222313650022533207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161756547481542433348355471 242634821222313650022533207)
  ·
    refine ⟨363952231833470475033799811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242634821222313650022533207 363952231833470475033799811)
    ·
      refine ⟨545928347750205712550699717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363952231833470475033799811 545928347750205712550699717)
      ·
        refine ⟨102361565203163571103256197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 545928347750205712550699717 102361565203163571103256197)
        ·
          refine ⟨19192793475593169581860537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102361565203163571103256197 19192793475593169581860537)
          ·
            refine ⟨14394595106694877186395403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19192793475593169581860537 14394595106694877186395403)
            ·
              refine ⟨21591892660042315779593105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14394595106694877186395403 21591892660042315779593105)
              ·
                refine ⟨16193919495031736834694829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21591892660042315779593105 16193919495031736834694829)
                ·
                  refine ⟨6072719810636901313010561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16193919495031736834694829 6072719810636901313010561)
                  ·
                    refine ⟨4554539857977675984757921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6072719810636901313010561 4554539857977675984757921)
                    ·
                      refine ⟨3415904893483256988568441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4554539857977675984757921 3415904893483256988568441)
                      ·
                        rfl

theorem cell23_6652451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 3, 2, 2].length) (baseStart_6652451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6652451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6652451 prefixEnd_6652451 := by exact prefixLift 6652451
  have htrace : WordTrace (prefixWord ++ tailWord_6652451) baseStart_6652451 baseEnd_6652451 := by
    simpa [prefixWord, tailWord_6652451, baseEnd_6652451] using wordTrace_append hprefix tailTrace_6652451
  have hstable : (prefixWord ++ tailWord_6652451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6652451).length < 2 ^ (prefixWord ++ tailWord_6652451).sum := by decide
  have hdescent : baseEnd_6652451 < baseStart_6652451 := by decide
  rcases family_descends (prefixWord ++ tailWord_6652451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6652455 : List Nat := [1, 1, 7, 2, 1, 2, 1, 1, 2, 3, 2]
def baseStart_6652455 : Nat := 118140960795 + 6652455 * 2 ^ 59
def prefixEnd_6652455 : Nat := 4983230072969 + 3 ^ 40 * 6652455 * 2
def baseEnd_6652455 : Nat := 3415906947405874972918423

theorem tailTrace_6652455 : CollatzResearch.WordTrace tailWord_6652455 prefixEnd_6652455 3415906947405874972918423 := by
  unfold tailWord_6652455
  simp only [CollatzResearch.WordTrace]
  refine ⟨242634967114299158705678819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161756644742866105803785879 242634967114299158705678819)
  ·
    refine ⟨363952450671448738058518229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242634967114299158705678819 363952450671448738058518229)
    ·
      refine ⟨8530135562612079798246521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 363952450671448738058518229 8530135562612079798246521)
      ·
        refine ⟨6397601671959059848684891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8530135562612079798246521 6397601671959059848684891)
        ·
          refine ⟨9596402507938589773027337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6397601671959059848684891 9596402507938589773027337)
          ·
            refine ⟨7197301880953942329770503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9596402507938589773027337 7197301880953942329770503)
            ·
              refine ⟨10795952821430913494655755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7197301880953942329770503 10795952821430913494655755)
              ·
                refine ⟨16193929232146370241983633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10795952821430913494655755 16193929232146370241983633)
                ·
                  refine ⟨12145446924109777681487725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16193929232146370241983633 12145446924109777681487725)
                  ·
                    refine ⟨4554542596541166630557897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12145446924109777681487725 4554542596541166630557897)
                    ·
                      refine ⟨3415906947405874972918423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4554542596541166630557897 3415906947405874972918423)
                      ·
                        rfl

theorem cell23_6652455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_6652455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6652455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6652455 prefixEnd_6652455 := by exact prefixLift 6652455
  have htrace : WordTrace (prefixWord ++ tailWord_6652455) baseStart_6652455 baseEnd_6652455 := by
    simpa [prefixWord, tailWord_6652455, baseEnd_6652455] using wordTrace_append hprefix tailTrace_6652455
  have hstable : (prefixWord ++ tailWord_6652455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6652455).length < 2 ^ (prefixWord ++ tailWord_6652455).sum := by decide
  have hdescent : baseEnd_6652455 < baseStart_6652455 := by decide
  rcases family_descends (prefixWord ++ tailWord_6652455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6652467 : List Nat := [1, 1, 1, 2, 4, 2, 1, 4, 1, 3, 3]
def baseStart_6652467 : Nat := 118140960795 + 6652467 * 2 ^ 59
def prefixEnd_6652467 : Nat := 4983230072969 + 3 ^ 40 * 6652467 * 2
def baseEnd_6652467 : Nat := 3415913109173728925968367

theorem tailTrace_6652467 : CollatzResearch.WordTrace tailWord_6652467 prefixEnd_6652467 3415913109173728925968367 := by
  unfold tailWord_6652467
  simp only [CollatzResearch.WordTrace]
  refine ⟨242635404790255684755115655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161756936526837123170077103 242635404790255684755115655)
  ·
    refine ⟨363953107185383527132673483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242635404790255684755115655 363953107185383527132673483)
    ·
      refine ⟨545929660778075290699010225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363953107185383527132673483 545929660778075290699010225)
      ·
        refine ⟨409447245583556468024257669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 545929660778075290699010225 409447245583556468024257669)
        ·
          refine ⟨76771358546916837754548313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 409447245583556468024257669 76771358546916837754548313)
          ·
            refine ⟨57578518910187628315911235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76771358546916837754548313 57578518910187628315911235)
            ·
              refine ⟨86367778365281442473866853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57578518910187628315911235 86367778365281442473866853)
              ·
                refine ⟨16193958443490270463850035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86367778365281442473866853 16193958443490270463850035)
                ·
                  refine ⟨24290937665235405695775053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16193958443490270463850035 24290937665235405695775053)
                  ·
                    refine ⟨9109101624463277135915645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24290937665235405695775053 9109101624463277135915645)
                    ·
                      refine ⟨3415913109173728925968367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9109101624463277135915645 3415913109173728925968367)
                      ·
                        rfl

theorem cell23_6652467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 3, 3].length) (baseStart_6652467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6652467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6652467 prefixEnd_6652467 := by exact prefixLift 6652467
  have htrace : WordTrace (prefixWord ++ tailWord_6652467) baseStart_6652467 baseEnd_6652467 := by
    simpa [prefixWord, tailWord_6652467, baseEnd_6652467] using wordTrace_append hprefix tailTrace_6652467
  have hstable : (prefixWord ++ tailWord_6652467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6652467).length < 2 ^ (prefixWord ++ tailWord_6652467).sum := by decide
  have hdescent : baseEnd_6652467 < baseStart_6652467 := by decide
  rcases family_descends (prefixWord ++ tailWord_6652467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6652468 : List Nat := [2, 5, 1, 3, 1, 1, 1, 3, 1, 1, 4]
def baseStart_6652468 : Nat := 118140960795 + 6652468 * 2 ^ 59
def prefixEnd_6652468 : Nat := 4983230072969 + 3 ^ 40 * 6652468 * 2
def baseEnd_6652468 : Nat := 3415913622654383422055863

theorem tailTrace_6652468 : CollatzResearch.WordTrace tailWord_6652468 prefixEnd_6652468 3415913622654383422055863 := by
  unfold tailWord_6652468
  simp only [CollatzResearch.WordTrace]
  refine ⟨121317720631626030962951029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161756960842168041283934705 121317720631626030962951029)
  ·
    refine ⟨11373536309214940402776659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 121317720631626030962951029 11373536309214940402776659)
    ·
      refine ⟨17060304463822410604164989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11373536309214940402776659 17060304463822410604164989)
      ·
        refine ⟨6397614173933403976561871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17060304463822410604164989 6397614173933403976561871)
        ·
          refine ⟨9596421260900105964842807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6397614173933403976561871 9596421260900105964842807)
          ·
            refine ⟨14394631891350158947264211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9596421260900105964842807 14394631891350158947264211)
            ·
              refine ⟨21591947837025238420896317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14394631891350158947264211 21591947837025238420896317)
              ·
                refine ⟨8096980438884464407836119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21591947837025238420896317 8096980438884464407836119)
                ·
                  refine ⟨12145470658326696611754179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8096980438884464407836119 12145470658326696611754179)
                  ·
                    refine ⟨18218205987490044917631269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12145470658326696611754179 18218205987490044917631269)
                    ·
                      refine ⟨3415913622654383422055863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18218205987490044917631269 3415913622654383422055863)
                      ·
                        rfl

theorem cell23_6652468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_6652468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6652468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6652468 prefixEnd_6652468 := by exact prefixLift 6652468
  have htrace : WordTrace (prefixWord ++ tailWord_6652468) baseStart_6652468 baseEnd_6652468 := by
    simpa [prefixWord, tailWord_6652468, baseEnd_6652468] using wordTrace_append hprefix tailTrace_6652468
  have hstable : (prefixWord ++ tailWord_6652468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6652468).length < 2 ^ (prefixWord ++ tailWord_6652468).sum := by decide
  have hdescent : baseEnd_6652468 < baseStart_6652468 := by decide
  rcases family_descends (prefixWord ++ tailWord_6652468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6652494 : List Nat := [4, 1, 1, 1, 1, 2, 2, 1, 5, 3, 2]
def baseStart_6652494 : Nat := 118140960795 + 6652494 * 2 ^ 59
def prefixEnd_6652494 : Nat := 4983230072969 + 3 ^ 40 * 6652494 * 2
def baseEnd_6652494 : Nat := 3415926973151400320330743

theorem tailTrace_6652494 : CollatzResearch.WordTrace tailWord_6652494 prefixEnd_6652494 3415926973151400320330743 := by
  unfold tailWord_6652494
  simp only [CollatzResearch.WordTrace]
  refine ⟨30329548695144733545793567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161757593040771912244232357 30329548695144733545793567)
  ·
    refine ⟨45494323042717100318690351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30329548695144733545793567 45494323042717100318690351)
    ·
      refine ⟨68241484564075650478035527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45494323042717100318690351 68241484564075650478035527)
      ·
        refine ⟨102362226846113475717053291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68241484564075650478035527 102362226846113475717053291)
        ·
          refine ⟨153543340269170213575579937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102362226846113475717053291 153543340269170213575579937)
          ·
            refine ⟨115157505201877660181684953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153543340269170213575579937 115157505201877660181684953)
            ·
              refine ⟨86368128901408245136263715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115157505201877660181684953 86368128901408245136263715)
              ·
                refine ⟨129552193352112367704395573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86368128901408245136263715 129552193352112367704395573)
                ·
                  refine ⟨12145518126760534472287085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 129552193352112367704395573 12145518126760534472287085)
                  ·
                    refine ⟨4554569297535200427107657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12145518126760534472287085 4554569297535200427107657)
                    ·
                      refine ⟨3415926973151400320330743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4554569297535200427107657 3415926973151400320330743)
                      ·
                        rfl

theorem cell23_6652494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 5, 3, 2].length) (baseStart_6652494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6652494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6652494 prefixEnd_6652494 := by exact prefixLift 6652494
  have htrace : WordTrace (prefixWord ++ tailWord_6652494) baseStart_6652494 baseEnd_6652494 := by
    simpa [prefixWord, tailWord_6652494, baseEnd_6652494] using wordTrace_append hprefix tailTrace_6652494
  have hstable : (prefixWord ++ tailWord_6652494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6652494).length < 2 ^ (prefixWord ++ tailWord_6652494).sum := by decide
  have hdescent : baseEnd_6652494 < baseStart_6652494 := by decide
  rcases family_descends (prefixWord ++ tailWord_6652494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6652524 : List Nat := [2, 2, 1, 1, 3, 1, 2, 4, 1, 4, 2]
def baseStart_6652524 : Nat := 118140960795 + 6652524 * 2 ^ 59
def prefixEnd_6652524 : Nat := 4983230072969 + 3 ^ 40 * 6652524 * 2
def baseEnd_6652524 : Nat := 3415942377571035202955605

theorem tailTrace_6652524 : CollatzResearch.WordTrace tailWord_6652524 prefixEnd_6652524 3415942377571035202955605 := by
  unfold tailWord_6652524
  simp only [CollatzResearch.WordTrace]
  refine ⟨121318741875524591744970313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161758322500699455659960417 121318741875524591744970313)
  ·
    refine ⟨90989056406643443808727735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121318741875524591744970313 90989056406643443808727735)
    ·
      refine ⟨136483584609965165713091603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90989056406643443808727735 136483584609965165713091603)
      ·
        refine ⟨204725376914947748569637405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136483584609965165713091603 204725376914947748569637405)
        ·
          refine ⟨76772016343105405713614027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204725376914947748569637405 76772016343105405713614027)
          ·
            refine ⟨115158024514658108570421041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76772016343105405713614027 115158024514658108570421041)
            ·
              refine ⟨86368518385993581427815781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115158024514658108570421041 86368518385993581427815781)
              ·
                refine ⟨16194097197373796517715459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86368518385993581427815781 16194097197373796517715459)
                ·
                  refine ⟨24291145796060694776573189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16194097197373796517715459 24291145796060694776573189)
                  ·
                    refine ⟨4554589836761380270607473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24291145796060694776573189 4554589836761380270607473)
                    ·
                      refine ⟨3415942377571035202955605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4554589836761380270607473 3415942377571035202955605)
                      ·
                        rfl

theorem cell23_6652524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 4, 2].length) (baseStart_6652524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6652524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6652524 prefixEnd_6652524 := by exact prefixLift 6652524
  have htrace : WordTrace (prefixWord ++ tailWord_6652524) baseStart_6652524 baseEnd_6652524 := by
    simpa [prefixWord, tailWord_6652524, baseEnd_6652524] using wordTrace_append hprefix tailTrace_6652524
  have hstable : (prefixWord ++ tailWord_6652524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6652524).length < 2 ^ (prefixWord ++ tailWord_6652524).sum := by decide
  have hdescent : baseEnd_6652524 < baseStart_6652524 := by decide
  rcases family_descends (prefixWord ++ tailWord_6652524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6652547 : List Nat := [1, 1, 1, 3, 3, 1, 5, 1, 7]
def baseStart_6652547 : Nat := 118140960795 + 6652547 * 2 ^ 59
def prefixEnd_6652547 : Nat := 4983230072969 + 3 ^ 40 * 6652547 * 2
def baseEnd_6652547 : Nat := 379550465291787623663111

theorem tailTrace_6652547 : CollatzResearch.WordTrace tailWord_6652547 prefixEnd_6652547 379550465291787623663111 := by
  unfold tailWord_6652547
  simp only [CollatzResearch.WordTrace]
  refine ⟨242638322629965858418027895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161758881753310572278685263 242638322629965858418027895)
  ·
    refine ⟨363957483944948787627041843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242638322629965858418027895 363957483944948787627041843)
    ·
      refine ⟨545936225917423181440562765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363957483944948787627041843 545936225917423181440562765)
      ·
        refine ⟨204726084719033693040211037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 545936225917423181440562765 204726084719033693040211037)
        ·
          refine ⟨76772281769637634890079139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204726084719033693040211037 76772281769637634890079139)
          ·
            refine ⟨115158422654456452335118709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76772281769637634890079139 115158422654456452335118709)
            ·
              refine ⟨10796102123855292406417379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 115158422654456452335118709 10796102123855292406417379)
              ·
                refine ⟨16194153185782938609626069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10796102123855292406417379 16194153185782938609626069)
                ·
                  refine ⟨379550465291787623663111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16194153185782938609626069 379550465291787623663111)
                  ·
                    rfl

theorem cell23_6652547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 7].length) (baseStart_6652547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6652547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6652547 prefixEnd_6652547 := by exact prefixLift 6652547
  have htrace : WordTrace (prefixWord ++ tailWord_6652547) baseStart_6652547 baseEnd_6652547 := by
    simpa [prefixWord, tailWord_6652547, baseEnd_6652547] using wordTrace_append hprefix tailTrace_6652547
  have hstable : (prefixWord ++ tailWord_6652547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6652547).length < 2 ^ (prefixWord ++ tailWord_6652547).sum := by decide
  have hdescent : baseEnd_6652547 < baseStart_6652547 := by decide
  rcases family_descends (prefixWord ++ tailWord_6652547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6652558 : List Nat := [4, 1, 1, 3, 1, 1, 3, 3, 2, 2, 2]
def baseStart_6652558 : Nat := 118140960795 + 6652558 * 2 ^ 59
def prefixEnd_6652558 : Nat := 4983230072969 + 3 ^ 40 * 6652558 * 2
def baseEnd_6652558 : Nat := 3415959835913288069930449

theorem tailTrace_6652558 : CollatzResearch.WordTrace tailWord_6652558 prefixEnd_6652558 3415959835913288069930449 := by
  unfold tailWord_6652558
  simp only [CollatzResearch.WordTrace]
  refine ⟨30329840479115750912084791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161759149221950671531118885 30329840479115750912084791)
  ·
    refine ⟨45494760718673626368127187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30329840479115750912084791 45494760718673626368127187)
    ·
      refine ⟨68242141078010439552190781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45494760718673626368127187 68242141078010439552190781)
      ·
        refine ⟨25590802904253914832071543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68242141078010439552190781 25590802904253914832071543)
        ·
          refine ⟨38386204356380872248107315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25590802904253914832071543 38386204356380872248107315)
          ·
            refine ⟨57579306534571308372160973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38386204356380872248107315 57579306534571308372160973)
            ·
              refine ⟨21592239950464240639560365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57579306534571308372160973 21592239950464240639560365)
              ·
                refine ⟨8097089981424090239835137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21592239950464240639560365 8097089981424090239835137)
                ·
                  refine ⟨6072817486068067679876353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8097089981424090239835137 6072817486068067679876353)
                  ·
                    refine ⟨4554613114551050759907265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6072817486068067679876353 4554613114551050759907265)
                    ·
                      refine ⟨3415959835913288069930449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4554613114551050759907265 3415959835913288069930449)
                      ·
                        rfl

theorem cell23_6652558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_6652558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6652558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6652558 prefixEnd_6652558 := by exact prefixLift 6652558
  have htrace : WordTrace (prefixWord ++ tailWord_6652558) baseStart_6652558 baseEnd_6652558 := by
    simpa [prefixWord, tailWord_6652558, baseEnd_6652558] using wordTrace_append hprefix tailTrace_6652558
  have hstable : (prefixWord ++ tailWord_6652558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6652558).length < 2 ^ (prefixWord ++ tailWord_6652558).sum := by decide
  have hdescent : baseEnd_6652558 < baseStart_6652558 := by decide
  rcases family_descends (prefixWord ++ tailWord_6652558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6652628 : List Nat := [2, 4, 1, 3, 2, 2, 1, 1, 2, 5]
def baseStart_6652628 : Nat := 118140960795 + 6652628 * 2 ^ 59
def prefixEnd_6652628 : Nat := 4983230072969 + 3 ^ 40 * 6652628 * 2
def baseEnd_6652628 : Nat := 1138665259853034265351709

theorem tailTrace_6652628 : CollatzResearch.WordTrace tailWord_6652628 prefixEnd_6652628 1138665259853034265351709 := by
  unfold tailWord_6652628
  simp only [CollatzResearch.WordTrace]
  refine ⟨121320638471336204625863269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161760851295114939501151025 121320638471336204625863269)
  ·
    refine ⟨22747619713375538367349363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121320638471336204625863269 22747619713375538367349363)
    ·
      refine ⟨34121429570063307551024045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22747619713375538367349363 34121429570063307551024045)
      ·
        refine ⟨12795536088773740331634017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34121429570063307551024045 12795536088773740331634017)
        ·
          refine ⟨9596652066580305248725513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12795536088773740331634017 9596652066580305248725513)
          ·
            refine ⟨7197489049935228936544135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9596652066580305248725513 7197489049935228936544135)
            ·
              refine ⟨10796233574902843404816203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7197489049935228936544135 10796233574902843404816203)
              ·
                refine ⟨16194350362354265107224305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10796233574902843404816203 16194350362354265107224305)
                ·
                  refine ⟨12145762771765698830418229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16194350362354265107224305 12145762771765698830418229)
                  ·
                    refine ⟨1138665259853034265351709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12145762771765698830418229 1138665259853034265351709)
                    ·
                      rfl

theorem cell23_6652628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_6652628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6652628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6652628 prefixEnd_6652628 := by exact prefixLift 6652628
  have htrace : WordTrace (prefixWord ++ tailWord_6652628) baseStart_6652628 baseEnd_6652628 := by
    simpa [prefixWord, tailWord_6652628, baseEnd_6652628] using wordTrace_append hprefix tailTrace_6652628
  have hstable : (prefixWord ++ tailWord_6652628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6652628).length < 2 ^ (prefixWord ++ tailWord_6652628).sum := by decide
  have hdescent : baseEnd_6652628 < baseStart_6652628 := by decide
  rcases family_descends (prefixWord ++ tailWord_6652628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6652631 : List Nat := [1, 1, 3, 2, 1, 6, 1, 1, 2, 1, 4]
def baseStart_6652631 : Nat := 118140960795 + 6652631 * 2 ^ 59
def prefixEnd_6652631 : Nat := 4983230072969 + 3 ^ 40 * 6652631 * 2
def baseEnd_6652631 : Nat := 3415997320001066284317613

theorem tailTrace_6652631 : CollatzResearch.WordTrace tailWord_6652631 prefixEnd_6652631 3415997320001066284317613 := by
  unfold tailWord_6652631
  simp only [CollatzResearch.WordTrace]
  refine ⟨242641386361661540764085747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161760924241107693842723831 242641386361661540764085747)
  ·
    refine ⟨363962079542492311146128621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242641386361661540764085747 363962079542492311146128621)
    ·
      refine ⟨136485779828434616679798233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 363962079542492311146128621 136485779828434616679798233)
      ·
        refine ⟨102364334871325962509848675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136485779828434616679798233 102364334871325962509848675)
        ·
          refine ⟨153546502306988943764773013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102364334871325962509848675 153546502306988943764773013)
          ·
            refine ⟨7197492295640106738973735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 153546502306988943764773013 7197492295640106738973735)
            ·
              refine ⟨10796238443460160108460603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7197492295640106738973735 10796238443460160108460603)
              ·
                refine ⟨16194357665190240162690905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10796238443460160108460603 16194357665190240162690905)
                ·
                  refine ⟨12145768248892680122018179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16194357665190240162690905 12145768248892680122018179)
                  ·
                    refine ⟨18218652373339020183027269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12145768248892680122018179 18218652373339020183027269)
                    ·
                      refine ⟨3415997320001066284317613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18218652373339020183027269 3415997320001066284317613)
                      ·
                        rfl

theorem cell23_6652631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 2, 1, 4].length) (baseStart_6652631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6652631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6652631 prefixEnd_6652631 := by exact prefixLift 6652631
  have htrace : WordTrace (prefixWord ++ tailWord_6652631) baseStart_6652631 baseEnd_6652631 := by
    simpa [prefixWord, tailWord_6652631, baseEnd_6652631] using wordTrace_append hprefix tailTrace_6652631
  have hstable : (prefixWord ++ tailWord_6652631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6652631).length < 2 ^ (prefixWord ++ tailWord_6652631).sum := by decide
  have hdescent : baseEnd_6652631 < baseStart_6652631 := by decide
  rcases family_descends (prefixWord ++ tailWord_6652631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6652634 : List Nat := [3, 1, 1, 2, 2, 2, 3, 1, 1, 4, 3]
def baseStart_6652634 : Nat := 118140960795 + 6652634 * 2 ^ 59
def prefixEnd_6652634 : Nat := 4983230072969 + 3 ^ 40 * 6652634 * 2
def baseEnd_6652634 : Nat := 3415998860443029772580099

theorem tailTrace_6652634 : CollatzResearch.WordTrace tailWord_6652634 prefixEnd_6652634 3415998860443029772580099 := by
  unfold tailWord_6652634
  simp only [CollatzResearch.WordTrace]
  refine ⟨60660373945162668069111239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161760997187100448184296637 60660373945162668069111239)
  ·
    refine ⟨90990560917744002103666859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60660373945162668069111239 90990560917744002103666859)
    ·
      refine ⟨136485841376616003155500289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90990560917744002103666859 136485841376616003155500289)
      ·
        refine ⟨102364381032462002366625217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136485841376616003155500289 102364381032462002366625217)
        ·
          refine ⟨76773285774346501774968913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102364381032462002366625217 76773285774346501774968913)
          ·
            refine ⟨57579964330759876331226685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76773285774346501774968913 57579964330759876331226685)
            ·
              refine ⟨21592486624034953624210007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57579964330759876331226685 21592486624034953624210007)
              ·
                refine ⟨32388729936052430436315011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21592486624034953624210007 32388729936052430436315011)
                ·
                  refine ⟨48583094904078645654472517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32388729936052430436315011 48583094904078645654472517)
                  ·
                    refine ⟨9109330294514746060213597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48583094904078645654472517 9109330294514746060213597)
                    ·
                      refine ⟨3415998860443029772580099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9109330294514746060213597 3415998860443029772580099)
                      ·
                        rfl

theorem cell23_6652634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 1, 4, 3].length) (baseStart_6652634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6652634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6652634 prefixEnd_6652634 := by exact prefixLift 6652634
  have htrace : WordTrace (prefixWord ++ tailWord_6652634) baseStart_6652634 baseEnd_6652634 := by
    simpa [prefixWord, tailWord_6652634, baseEnd_6652634] using wordTrace_append hprefix tailTrace_6652634
  have hstable : (prefixWord ++ tailWord_6652634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6652634).length < 2 ^ (prefixWord ++ tailWord_6652634).sum := by decide
  have hdescent : baseEnd_6652634 < baseStart_6652634 := by decide
  rcases family_descends (prefixWord ++ tailWord_6652634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6652654 : List Nat := [4, 1, 2, 1, 1, 4, 1, 1, 8]
def baseStart_6652654 : Nat := 118140960795 + 6652654 * 2 ^ 59
def prefixEnd_6652654 : Nat := 4983230072969 + 3 ^ 40 * 6652654 * 2
def baseEnd_6652654 : Nat := 379556570006235521592223

theorem tailTrace_6652654 : CollatzResearch.WordTrace tailWord_6652654 prefixEnd_6652654 379556570006235521592223 := by
  unfold tailWord_6652654
  simp only [CollatzResearch.WordTrace]
  refine ⟨30330278155072276961521627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161761483493718810461448677 30330278155072276961521627)
  ·
    refine ⟨45495417232608415442282441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30330278155072276961521627 45495417232608415442282441)
    ·
      refine ⟨34121562924456311581711831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45495417232608415442282441 34121562924456311581711831)
      ·
        refine ⟨51182344386684467372567747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34121562924456311581711831 51182344386684467372567747)
        ·
          refine ⟨76773516580026701058851621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51182344386684467372567747 76773516580026701058851621)
          ·
            refine ⟨14395034358755006448534679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76773516580026701058851621 14395034358755006448534679)
            ·
              refine ⟨21592551538132509672802019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14395034358755006448534679 21592551538132509672802019)
              ·
                refine ⟨32388827307198764509203029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21592551538132509672802019 32388827307198764509203029)
                ·
                  refine ⟨379556570006235521592223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32388827307198764509203029 379556570006235521592223)
                  ·
                    rfl

theorem cell23_6652654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 8].length) (baseStart_6652654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6652654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6652654 prefixEnd_6652654 := by exact prefixLift 6652654
  have htrace : WordTrace (prefixWord ++ tailWord_6652654) baseStart_6652654 baseEnd_6652654 := by
    simpa [prefixWord, tailWord_6652654, baseEnd_6652654] using wordTrace_append hprefix tailTrace_6652654
  have hstable : (prefixWord ++ tailWord_6652654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6652654).length < 2 ^ (prefixWord ++ tailWord_6652654).sum := by decide
  have hdescent : baseEnd_6652654 < baseStart_6652654 := by decide
  rcases family_descends (prefixWord ++ tailWord_6652654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6652657 : List Nat := [1, 2, 2, 2, 2, 2, 1, 1, 1, 1, 8]
def baseStart_6652657 : Nat := 118140960795 + 6652657 * 2 ^ 59
def prefixEnd_6652657 : Nat := 4983230072969 + 3 ^ 40 * 6652657 * 2
def baseEnd_6652657 : Nat := 3416010670498083182592493

theorem tailTrace_6652657 : CollatzResearch.WordTrace tailWord_6652657 prefixEnd_6652657 3416010670498083182592493 := by
  unfold tailWord_6652657
  simp only [CollatzResearch.WordTrace]
  refine ⟨242642334659567347204532225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161761556439711564803021483 242642334659567347204532225)
  ·
    refine ⟨181981750994675510403399169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242642334659567347204532225 181981750994675510403399169)
    ·
      refine ⟨136486313246006632802549377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181981750994675510403399169 136486313246006632802549377)
      ·
        refine ⟨102364734934504974601912033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136486313246006632802549377 102364734934504974601912033)
        ·
          refine ⟨76773551200878730951434025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102364734934504974601912033 76773551200878730951434025)
          ·
            refine ⟨57580163400659048213575519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76773551200878730951434025 57580163400659048213575519)
            ·
              refine ⟨86370245100988572320363279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57580163400659048213575519 86370245100988572320363279)
              ·
                refine ⟨129555367651482858480544919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86370245100988572320363279 129555367651482858480544919)
                ·
                  refine ⟨194333051477224287720817379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129555367651482858480544919 194333051477224287720817379)
                  ·
                    refine ⟨291499577215836431581226069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 194333051477224287720817379 291499577215836431581226069)
                    ·
                      refine ⟨3416010670498083182592493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 291499577215836431581226069 3416010670498083182592493)
                      ·
                        rfl

theorem cell23_6652657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_6652657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6652657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6652657 prefixEnd_6652657 := by exact prefixLift 6652657
  have htrace : WordTrace (prefixWord ++ tailWord_6652657) baseStart_6652657 baseEnd_6652657 := by
    simpa [prefixWord, tailWord_6652657, baseEnd_6652657] using wordTrace_append hprefix tailTrace_6652657
  have hstable : (prefixWord ++ tailWord_6652657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6652657).length < 2 ^ (prefixWord ++ tailWord_6652657).sum := by decide
  have hdescent : baseEnd_6652657 < baseStart_6652657 := by decide
  rcases family_descends (prefixWord ++ tailWord_6652657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6652658 : List Nat := [3, 2, 1, 3, 1, 2, 2, 4, 1, 4]
def baseStart_6652658 : Nat := 118140960795 + 6652658 * 2 ^ 59
def prefixEnd_6652658 : Nat := 4983230072969 + 3 ^ 40 * 6652658 * 2
def baseEnd_6652658 : Nat := 1138670394659579226226663

theorem tailTrace_6652658 : CollatzResearch.WordTrace tailWord_6652658 prefixEnd_6652658 1138670394659579226226663 := by
  unfold tailWord_6652658
  simp only [CollatzResearch.WordTrace]
  refine ⟨60660592783140931093829657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161761580755042482916879085 60660592783140931093829657)
  ·
    refine ⟨45495444587355698320372243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60660592783140931093829657 45495444587355698320372243)
    ·
      refine ⟨68243166881033547480558365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45495444587355698320372243 68243166881033547480558365)
      ·
        refine ⟨25591187580387580305209387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68243166881033547480558365 25591187580387580305209387)
        ·
          refine ⟨38386781370581370457814081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25591187580387580305209387 38386781370581370457814081)
          ·
            refine ⟨28790086027936027843360561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38386781370581370457814081 28790086027936027843360561)
            ·
              refine ⟨21592564520952020882520421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28790086027936027843360561 21592564520952020882520421)
              ·
                refine ⟨4048605847678503915472579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21592564520952020882520421 4048605847678503915472579)
                ·
                  refine ⟨6072908771517755873208869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4048605847678503915472579 6072908771517755873208869)
                  ·
                    refine ⟨1138670394659579226226663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6072908771517755873208869 1138670394659579226226663)
                    ·
                      rfl

theorem cell23_6652658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 4, 1, 4].length) (baseStart_6652658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6652658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6652658 prefixEnd_6652658 := by exact prefixLift 6652658
  have htrace : WordTrace (prefixWord ++ tailWord_6652658) baseStart_6652658 baseEnd_6652658 := by
    simpa [prefixWord, tailWord_6652658, baseEnd_6652658] using wordTrace_append hprefix tailTrace_6652658
  have hstable : (prefixWord ++ tailWord_6652658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6652658).length < 2 ^ (prefixWord ++ tailWord_6652658).sum := by decide
  have hdescent : baseEnd_6652658 < baseStart_6652658 := by decide
  rcases family_descends (prefixWord ++ tailWord_6652658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6652677 : List Nat := [1, 3, 1, 1, 2, 1, 1, 3, 2, 1, 7]
def baseStart_6652677 : Nat := 118140960795 + 6652677 * 2 ^ 59
def prefixEnd_6652677 : Nat := 4983230072969 + 3 ^ 40 * 6652677 * 2
def baseEnd_6652677 : Nat := 3416020940111173104342401

theorem tailTrace_6652677 : CollatzResearch.WordTrace tailWord_6652677 prefixEnd_6652677 3416020940111173104342401 := by
  unfold tailWord_6652677
  simp only [CollatzResearch.WordTrace]
  refine ⟨242643064119494890620260285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161762042746329927080173523 242643064119494890620260285)
  ·
    refine ⟨90991149044810583982597607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242643064119494890620260285 90991149044810583982597607)
    ·
      refine ⟨136486723567215875973896411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90991149044810583982597607 136486723567215875973896411)
      ·
        refine ⟨204730085350823813960844617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136486723567215875973896411 204730085350823813960844617)
        ·
          refine ⟨153547564013117860470633463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204730085350823813960844617 153547564013117860470633463)
          ·
            refine ⟨230321346019676790705950195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153547564013117860470633463 230321346019676790705950195)
            ·
              refine ⟨345482019029515186058925293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230321346019676790705950195 345482019029515186058925293)
              ·
                refine ⟨129555757136068194772096985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 345482019029515186058925293 129555757136068194772096985)
                ·
                  refine ⟨97166817852051146079072739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129555757136068194772096985 97166817852051146079072739)
                  ·
                    refine ⟨145750226778076719118609109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 97166817852051146079072739 145750226778076719118609109)
                    ·
                      refine ⟨3416020940111173104342401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 145750226778076719118609109 3416020940111173104342401)
                      ·
                        rfl

theorem cell23_6652677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 1, 7].length) (baseStart_6652677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6652677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6652677 prefixEnd_6652677 := by exact prefixLift 6652677
  have htrace : WordTrace (prefixWord ++ tailWord_6652677) baseStart_6652677 baseEnd_6652677 := by
    simpa [prefixWord, tailWord_6652677, baseEnd_6652677] using wordTrace_append hprefix tailTrace_6652677
  have hstable : (prefixWord ++ tailWord_6652677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6652677).length < 2 ^ (prefixWord ++ tailWord_6652677).sum := by decide
  have hdescent : baseEnd_6652677 < baseStart_6652677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6652677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6652681 : List Nat := [1, 2, 1, 1, 3, 2, 4, 2, 3, 1, 3]
def baseStart_6652681 : Nat := 118140960795 + 6652681 * 2 ^ 59
def prefixEnd_6652681 : Nat := 4983230072969 + 3 ^ 40 * 6652681 * 2
def baseEnd_6652681 : Nat := 3416022994033791088692383

theorem tailTrace_6652681 : CollatzResearch.WordTrace tailWord_6652681 prefixEnd_6652681 3416022994033791088692383 := by
  unfold tailWord_6652681
  simp only [CollatzResearch.WordTrace]
  refine ⟨242643210011480399303405897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161762140007653599535603931 242643210011480399303405897)
  ·
    refine ⟨181982407508610299477554423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242643210011480399303405897 181982407508610299477554423)
    ·
      refine ⟨272973611262915449216331635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181982407508610299477554423 272973611262915449216331635)
      ·
        refine ⟨409460416894373173824497453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272973611262915449216331635 409460416894373173824497453)
        ·
          refine ⟨153547656335389940184186545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 409460416894373173824497453 153547656335389940184186545)
          ·
            refine ⟨115160742251542455138139909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153547656335389940184186545 115160742251542455138139909)
            ·
              refine ⟨21592639172164210338401233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115160742251542455138139909 21592639172164210338401233)
              ·
                refine ⟨16194479379123157753800925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21592639172164210338401233 16194479379123157753800925)
                ·
                  refine ⟨6072929767171184157675347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16194479379123157753800925 6072929767171184157675347)
                  ·
                    refine ⟨9109394650756776236513021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6072929767171184157675347 9109394650756776236513021)
                    ·
                      refine ⟨3416022994033791088692383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9109394650756776236513021 3416022994033791088692383)
                      ·
                        rfl

theorem cell23_6652681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 3, 1, 3].length) (baseStart_6652681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6652681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6652681 prefixEnd_6652681 := by exact prefixLift 6652681
  have htrace : WordTrace (prefixWord ++ tailWord_6652681) baseStart_6652681 baseEnd_6652681 := by
    simpa [prefixWord, tailWord_6652681, baseEnd_6652681] using wordTrace_append hprefix tailTrace_6652681
  have hstable : (prefixWord ++ tailWord_6652681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6652681).length < 2 ^ (prefixWord ++ tailWord_6652681).sum := by decide
  have hdescent : baseEnd_6652681 < baseStart_6652681 := by decide
  rcases family_descends (prefixWord ++ tailWord_6652681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6652691 : List Nat := [1, 1, 1, 2, 1, 3, 4, 3, 2, 3, 2]
def baseStart_6652691 : Nat := 118140960795 + 6652691 * 2 ^ 59
def prefixEnd_6652691 : Nat := 4983230072969 + 3 ^ 40 * 6652691 * 2
def baseEnd_6652691 : Nat := 3416028128840336049567337

theorem tailTrace_6652691 : CollatzResearch.WordTrace tailWord_6652691 prefixEnd_6652691 3416028128840336049567337 := by
  unfold tailWord_6652691
  simp only [CollatzResearch.WordTrace]
  refine ⟨242643574741444171011269927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161762383160962780674179951 242643574741444171011269927)
  ·
    refine ⟨363965362112166256516904891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242643574741444171011269927 363965362112166256516904891)
    ·
      refine ⟨545948043168249384775357337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363965362112166256516904891 545948043168249384775357337)
      ·
        refine ⟨409461032376187038581518003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 545948043168249384775357337 409461032376187038581518003)
        ·
          refine ⟨614191548564280557872277005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409461032376187038581518003 614191548564280557872277005)
          ·
            refine ⟨230321830711605209202103877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 614191548564280557872277005 230321830711605209202103877)
            ·
              refine ⟨43185343258425976725394477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 230321830711605209202103877 43185343258425976725394477)
              ·
                refine ⟨16194503721909741272022929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43185343258425976725394477 16194503721909741272022929)
                ·
                  refine ⟨12145877791432305954017197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16194503721909741272022929 12145877791432305954017197)
                  ·
                    refine ⟨4554704171787114732756449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12145877791432305954017197 4554704171787114732756449)
                    ·
                      refine ⟨3416028128840336049567337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4554704171787114732756449 3416028128840336049567337)
                      ·
                        rfl

theorem cell23_6652691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 2, 3, 2].length) (baseStart_6652691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6652691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6652691 prefixEnd_6652691 := by exact prefixLift 6652691
  have htrace : WordTrace (prefixWord ++ tailWord_6652691) baseStart_6652691 baseEnd_6652691 := by
    simpa [prefixWord, tailWord_6652691, baseEnd_6652691] using wordTrace_append hprefix tailTrace_6652691
  have hstable : (prefixWord ++ tailWord_6652691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6652691).length < 2 ^ (prefixWord ++ tailWord_6652691).sum := by decide
  have hdescent : baseEnd_6652691 < baseStart_6652691 := by decide
  rcases family_descends (prefixWord ++ tailWord_6652691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6652741 : List Nat := [1, 3, 1, 1, 1, 2, 2, 6, 1, 2, 3]
def baseStart_6652741 : Nat := 118140960795 + 6652741 * 2 ^ 59
def prefixEnd_6652741 : Nat := 4983230072969 + 3 ^ 40 * 6652741 * 2
def baseEnd_6652741 : Nat := 3416053802873060853942107

theorem tailTrace_6652741 : CollatzResearch.WordTrace tailWord_6652741 prefixEnd_6652741 3416053802873060853942107 := by
  unfold tailWord_6652741
  simp only [CollatzResearch.WordTrace]
  refine ⟨242645398391263029550590077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161763598927508686367060051 242645398391263029550590077)
  ·
    refine ⟨90992024396723636081471279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242645398391263029550590077 90992024396723636081471279)
    ·
      refine ⟨136488036595085454122206919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90992024396723636081471279 136488036595085454122206919)
      ·
        refine ⟨204732054892628181183310379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136488036595085454122206919 204732054892628181183310379)
        ·
          refine ⟨307098082338942271774965569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204732054892628181183310379 307098082338942271774965569)
          ·
            refine ⟨230323561754206703831224177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 307098082338942271774965569 230323561754206703831224177)
            ·
              refine ⟨172742671315655027873418133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230323561754206703831224177 172742671315655027873418133)
              ·
                refine ⟨8097312717921329431566475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 172742671315655027873418133 8097312717921329431566475)
                ·
                  refine ⟨12145969076881994147349713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8097312717921329431566475 12145969076881994147349713)
                  ·
                    refine ⟨9109476807661495610512285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12145969076881994147349713 9109476807661495610512285)
                    ·
                      refine ⟨3416053802873060853942107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9109476807661495610512285 3416053802873060853942107)
                      ·
                        rfl

theorem cell23_6652741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 6, 1, 2, 3].length) (baseStart_6652741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6652741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6652741 prefixEnd_6652741 := by exact prefixLift 6652741
  have htrace : WordTrace (prefixWord ++ tailWord_6652741) baseStart_6652741 baseEnd_6652741 := by
    simpa [prefixWord, tailWord_6652741, baseEnd_6652741] using wordTrace_append hprefix tailTrace_6652741
  have hstable : (prefixWord ++ tailWord_6652741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6652741).length < 2 ^ (prefixWord ++ tailWord_6652741).sum := by decide
  have hdescent : baseEnd_6652741 < baseStart_6652741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6652741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6652772 : List Nat := [2, 3, 1, 1, 4, 2, 1, 4, 1, 2, 2]
def baseStart_6652772 : Nat := 118140960795 + 6652772 * 2 ^ 59
def prefixEnd_6652772 : Nat := 4983230072969 + 3 ^ 40 * 6652772 * 2
def baseEnd_6652772 : Nat := 3416069720773350232654465

theorem tailTrace_6652772 : CollatzResearch.WordTrace tailWord_6652772 prefixEnd_6652772 3416069720773350232654465 := by
  unfold tailWord_6652772
  simp only [CollatzResearch.WordTrace]
  refine ⟨121323264527075360922484285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161764352702767147896645713 121323264527075360922484285)
  ·
    refine ⟨45496224197653260345931607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121323264527075360922484285 45496224197653260345931607)
    ·
      refine ⟨68244336296479890518897411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45496224197653260345931607 68244336296479890518897411)
      ·
        refine ⟨102366504444719835778346117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68244336296479890518897411 102366504444719835778346117)
        ·
          refine ⟨19193719583384969208439897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102366504444719835778346117 19193719583384969208439897)
          ·
            refine ⟨14395289687538726906329923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19193719583384969208439897 14395289687538726906329923)
            ·
              refine ⟨21592934531308090359494885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14395289687538726906329923 21592934531308090359494885)
              ·
                refine ⟨4048675224620266942405291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21592934531308090359494885 4048675224620266942405291)
                ·
                  refine ⟨6073012836930400413607937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4048675224620266942405291 6073012836930400413607937)
                  ·
                    refine ⟨4554759627697800310205953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6073012836930400413607937 4554759627697800310205953)
                    ·
                      refine ⟨3416069720773350232654465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4554759627697800310205953 3416069720773350232654465)
                      ·
                        rfl

theorem cell23_6652772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 4, 1, 2, 2].length) (baseStart_6652772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6652772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6652772 prefixEnd_6652772 := by exact prefixLift 6652772
  have htrace : WordTrace (prefixWord ++ tailWord_6652772) baseStart_6652772 baseEnd_6652772 := by
    simpa [prefixWord, tailWord_6652772, baseEnd_6652772] using wordTrace_append hprefix tailTrace_6652772
  have hstable : (prefixWord ++ tailWord_6652772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6652772).length < 2 ^ (prefixWord ++ tailWord_6652772).sum := by decide
  have hdescent : baseEnd_6652772 < baseStart_6652772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6652772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6652794 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 4, 3, 4]
def baseStart_6652794 : Nat := 118140960795 + 6652794 * 2 ^ 59
def prefixEnd_6652794 : Nat := 4983230072969 + 3 ^ 40 * 6652794 * 2
def baseEnd_6652794 : Nat := 3416081017347749146579363

theorem tailTrace_6652794 : CollatzResearch.WordTrace tailWord_6652794 prefixEnd_6652794 3416081017347749146579363 := by
  unfold tailWord_6652794
  simp only [CollatzResearch.WordTrace]
  refine ⟨60661832865017754900567359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161764887640047346401512957 60661832865017754900567359)
  ·
    refine ⟨90992749297526632350851039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60661832865017754900567359 90992749297526632350851039)
    ·
      refine ⟨136489123946289948526276559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90992749297526632350851039 136489123946289948526276559)
      ·
        refine ⟨204733685919434922789414839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136489123946289948526276559 204733685919434922789414839)
        ·
          refine ⟨307100528879152384184122259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204733685919434922789414839 307100528879152384184122259)
          ·
            refine ⟨460650793318728576276183389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307100528879152384184122259 460650793318728576276183389)
            ·
              refine ⟨172744047494523216103568771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 460650793318728576276183389 172744047494523216103568771)
              ·
                refine ⟨259116071241784824155353157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172744047494523216103568771 259116071241784824155353157)
                ·
                  refine ⟨48584263357834654529128717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 259116071241784824155353157 48584263357834654529128717)
                  ·
                    refine ⟨18219098759187995448423269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48584263357834654529128717 18219098759187995448423269)
                    ·
                      refine ⟨3416081017347749146579363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18219098759187995448423269 3416081017347749146579363)
                      ·
                        rfl

theorem cell23_6652794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 4, 3, 4].length) (baseStart_6652794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6652794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6652794 prefixEnd_6652794 := by exact prefixLift 6652794
  have htrace : WordTrace (prefixWord ++ tailWord_6652794) baseStart_6652794 baseEnd_6652794 := by
    simpa [prefixWord, tailWord_6652794, baseEnd_6652794] using wordTrace_append hprefix tailTrace_6652794
  have hstable : (prefixWord ++ tailWord_6652794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6652794).length < 2 ^ (prefixWord ++ tailWord_6652794).sum := by decide
  have hdescent : baseEnd_6652794 < baseStart_6652794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6652794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6652804 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 3, 8]
def baseStart_6652804 : Nat := 118140960795 + 6652804 * 2 ^ 59
def prefixEnd_6652804 : Nat := 4983230072969 + 3 ^ 40 * 6652804 * 2
def baseEnd_6652804 : Nat := 1138695384051431369151439

theorem tailTrace_6652804 : CollatzResearch.WordTrace tailWord_6652804 prefixEnd_6652804 1138695384051431369151439 := by
  unfold tailWord_6652804
  simp only [CollatzResearch.WordTrace]
  refine ⟨121323848095017395655066733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161765130793356527540088977 121323848095017395655066733)
  ·
    refine ⟨45496443035631523370650025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121323848095017395655066733 45496443035631523370650025)
    ·
      refine ⟨34122332276723642527987519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45496443035631523370650025 34122332276723642527987519)
      ·
        refine ⟨51183498415085463791981279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34122332276723642527987519 51183498415085463791981279)
        ·
          refine ⟨76775247622628195687971919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51183498415085463791981279 76775247622628195687971919)
          ·
            refine ⟨115162871433942293531957879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76775247622628195687971919 115162871433942293531957879)
            ·
              refine ⟨172744307150913440297936819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115162871433942293531957879 172744307150913440297936819)
              ·
                refine ⟨259116460726370160446905229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172744307150913440297936819 259116460726370160446905229)
                ·
                  refine ⟨97168672772388810167589461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 259116460726370160446905229 97168672772388810167589461)
                  ·
                    refine ⟨1138695384051431369151439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 97168672772388810167589461 1138695384051431369151439)
                    ·
                      rfl

theorem cell23_6652804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_6652804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6652804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6652804 prefixEnd_6652804 := by exact prefixLift 6652804
  have htrace : WordTrace (prefixWord ++ tailWord_6652804) baseStart_6652804 baseEnd_6652804 := by
    simpa [prefixWord, tailWord_6652804, baseEnd_6652804] using wordTrace_append hprefix tailTrace_6652804
  have hstable : (prefixWord ++ tailWord_6652804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6652804).length < 2 ^ (prefixWord ++ tailWord_6652804).sum := by decide
  have hdescent : baseEnd_6652804 < baseStart_6652804 := by decide
  rcases family_descends (prefixWord ++ tailWord_6652804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6652881 : List Nat := [1, 2, 2, 1, 2, 1, 5, 2, 2, 5]
def baseStart_6652881 : Nat := 118140960795 + 6652881 * 2 ^ 59
def prefixEnd_6652881 : Nat := 4983230072969 + 3 ^ 40 * 6652881 * 2
def baseEnd_6652881 : Nat := 1138708563388230102063821

theorem tailTrace_6652881 : CollatzResearch.WordTrace tailWord_6652881 prefixEnd_6652881 1138708563388230102063821 := by
  unfold tailWord_6652881
  simp only [CollatzResearch.WordTrace]
  refine ⟨242650504610755833460686497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161767003073837222307124331 242650504610755833460686497)
  ·
    refine ⟨181987878458066875095514873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242650504610755833460686497 181987878458066875095514873)
    ·
      refine ⟨136490908843550156321636155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181987878458066875095514873 136490908843550156321636155)
      ·
        refine ⟨204736363265325234482454233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136490908843550156321636155 204736363265325234482454233)
        ·
          refine ⟨153552272448993925861840675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204736363265325234482454233 153552272448993925861840675)
          ·
            refine ⟨230328408673490888792761013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153552272448993925861840675 230328408673490888792761013)
            ·
              refine ⟨21593288313139770824321345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 230328408673490888792761013 21593288313139770824321345)
              ·
                refine ⟨16194966234854828118241009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21593288313139770824321345 16194966234854828118241009)
                ·
                  refine ⟨12146224676141121088680757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16194966234854828118241009 12146224676141121088680757)
                  ·
                    refine ⟨1138708563388230102063821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12146224676141121088680757 1138708563388230102063821)
                    ·
                      rfl

theorem cell23_6652881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 2, 5].length) (baseStart_6652881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6652881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6652881 prefixEnd_6652881 := by exact prefixLift 6652881
  have htrace : WordTrace (prefixWord ++ tailWord_6652881) baseStart_6652881 baseEnd_6652881 := by
    simpa [prefixWord, tailWord_6652881, baseEnd_6652881] using wordTrace_append hprefix tailTrace_6652881
  have hstable : (prefixWord ++ tailWord_6652881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6652881).length < 2 ^ (prefixWord ++ tailWord_6652881).sum := by decide
  have hdescent : baseEnd_6652881 < baseStart_6652881 := by decide
  rcases family_descends (prefixWord ++ tailWord_6652881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6652885 : List Nat := [1, 3, 2, 3, 4, 1, 1, 1, 7]
def baseStart_6652885 : Nat := 118140960795 + 6652885 * 2 ^ 59
def prefixEnd_6652885 : Nat := 4983230072969 + 3 ^ 40 * 6652885 * 2
def baseEnd_6652885 : Nat := 379569749343034254504605

theorem tailTrace_6652885 : CollatzResearch.WordTrace tailWord_6652885 prefixEnd_6652885 379569749343034254504605 := by
  unfold tailWord_6652885
  simp only [CollatzResearch.WordTrace]
  refine ⟨242650650502741342143832109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161767100335160894762554739 242650650502741342143832109)
  ·
    refine ⟨90993993938528003303937041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242650650502741342143832109 90993993938528003303937041)
    ·
      refine ⟨68245495453896002477952781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90993993938528003303937041 68245495453896002477952781)
      ·
        refine ⟨25592060795211000929232293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68245495453896002477952781 25592060795211000929232293)
        ·
          refine ⟨4798511399102062674231055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25592060795211000929232293 4798511399102062674231055)
          ·
            refine ⟨7197767098653094011346583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4798511399102062674231055 7197767098653094011346583)
            ·
              refine ⟨10796650647979641017019875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7197767098653094011346583 10796650647979641017019875)
              ·
                refine ⟨16194975971969461525529813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10796650647979641017019875 16194975971969461525529813)
                ·
                  refine ⟨379569749343034254504605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16194975971969461525529813 379569749343034254504605)
                  ·
                    rfl

theorem cell23_6652885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 7].length) (baseStart_6652885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6652885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6652885 prefixEnd_6652885 := by exact prefixLift 6652885
  have htrace : WordTrace (prefixWord ++ tailWord_6652885) baseStart_6652885 baseEnd_6652885 := by
    simpa [prefixWord, tailWord_6652885, baseEnd_6652885] using wordTrace_append hprefix tailTrace_6652885
  have hstable : (prefixWord ++ tailWord_6652885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6652885).length < 2 ^ (prefixWord ++ tailWord_6652885).sum := by decide
  have hdescent : baseEnd_6652885 < baseStart_6652885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6652885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6652971 : List Nat := [1, 1, 1, 1, 2, 1, 5, 3, 3, 5]
def baseStart_6652971 : Nat := 118140960795 + 6652971 * 2 ^ 59
def prefixEnd_6652971 : Nat := 4983230072969 + 3 ^ 40 * 6652971 * 2
def baseEnd_6652971 : Nat := 1138723967807864984688683

theorem tailTrace_6652971 : CollatzResearch.WordTrace tailWord_6652971 prefixEnd_6652971 1138723967807864984688683 := by
  unfold tailWord_6652971
  simp only [CollatzResearch.WordTrace]
  refine ⟨242653787180429778831462767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161769191453619852554308511 242653787180429778831462767)
  ·
    refine ⟨363980680770644668247194151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242653787180429778831462767 363980680770644668247194151)
    ·
      refine ⟨545971021155967002370791227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363980680770644668247194151 545971021155967002370791227)
      ·
        refine ⟨818956531733950503556186841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 545971021155967002370791227 818956531733950503556186841)
        ·
          refine ⟨614217398800462877667140131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 818956531733950503556186841 614217398800462877667140131)
          ·
            refine ⟨921326098200694316500710197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 614217398800462877667140131 921326098200694316500710197)
            ·
              refine ⟨86374321706315092171941581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 921326098200694316500710197 86374321706315092171941581)
              ·
                refine ⟨32390370639868159564478093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86374321706315092171941581 32390370639868159564478093)
                ·
                  refine ⟨12146388989950559836679285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32390370639868159564478093 12146388989950559836679285)
                  ·
                    refine ⟨1138723967807864984688683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12146388989950559836679285 1138723967807864984688683)
                    ·
                      rfl

theorem cell23_6652971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 3, 5].length) (baseStart_6652971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6652971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6652971 prefixEnd_6652971 := by exact prefixLift 6652971
  have htrace : WordTrace (prefixWord ++ tailWord_6652971) baseStart_6652971 baseEnd_6652971 := by
    simpa [prefixWord, tailWord_6652971, baseEnd_6652971] using wordTrace_append hprefix tailTrace_6652971
  have hstable : (prefixWord ++ tailWord_6652971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6652971).length < 2 ^ (prefixWord ++ tailWord_6652971).sum := by decide
  have hdescent : baseEnd_6652971 < baseStart_6652971 := by decide
  rcases family_descends (prefixWord ++ tailWord_6652971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6652981 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 2, 4, 5]
def baseStart_6652981 : Nat := 118140960795 + 6652981 * 2 ^ 59
def prefixEnd_6652981 : Nat := 4983230072969 + 3 ^ 40 * 6652981 * 2
def baseEnd_6652981 : Nat := 3416177038230139914941003

theorem tailTrace_6652981 : CollatzResearch.WordTrace tailWord_6652981 prefixEnd_6652981 3416177038230139914941003 := by
  unfold tailWord_6652981
  simp only [CollatzResearch.WordTrace]
  refine ⟨242654151910393550539326797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161769434606929033692884531 242654151910393550539326797)
  ·
    refine ⟨90995306966397581452247549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242654151910393550539326797 90995306966397581452247549)
    ·
      refine ⟨34123240112399093044592831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90995306966397581452247549 34123240112399093044592831)
      ·
        refine ⟨51184860168598639566889247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34123240112399093044592831 51184860168598639566889247)
        ·
          refine ⟨76777290252897959350333871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51184860168598639566889247 76777290252897959350333871)
          ·
            refine ⟨115165935379346939025500807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76777290252897959350333871 115165935379346939025500807)
            ·
              refine ⟨172748903069020408538251211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115165935379346939025500807 172748903069020408538251211)
              ·
                refine ⟨259123354603530612807376817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172748903069020408538251211 259123354603530612807376817)
                ·
                  refine ⟨194342515952647959605532613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 259123354603530612807376817 194342515952647959605532613)
                  ·
                    refine ⟨36439221741121492426037365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 194342515952647959605532613 36439221741121492426037365)
                    ·
                      refine ⟨3416177038230139914941003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36439221741121492426037365 3416177038230139914941003)
                      ·
                        rfl

theorem cell23_6652981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_6652981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6652981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6652981 prefixEnd_6652981 := by exact prefixLift 6652981
  have htrace : WordTrace (prefixWord ++ tailWord_6652981) baseStart_6652981 baseEnd_6652981 := by
    simpa [prefixWord, tailWord_6652981, baseEnd_6652981] using wordTrace_append hprefix tailTrace_6652981
  have hstable : (prefixWord ++ tailWord_6652981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6652981).length < 2 ^ (prefixWord ++ tailWord_6652981).sum := by decide
  have hdescent : baseEnd_6652981 < baseStart_6652981 := by decide
  rcases family_descends (prefixWord ++ tailWord_6652981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6653002 : List Nat := [3, 1, 2, 1, 1, 2, 4, 4, 1, 1, 3]
def baseStart_6653002 : Nat := 118140960795 + 6653002 * 2 ^ 59
def prefixEnd_6653002 : Nat := 4983230072969 + 3 ^ 40 * 6653002 * 2
def baseEnd_6653002 : Nat := 3416187821323884332778407

theorem tailTrace_6653002 : CollatzResearch.WordTrace tailWord_6653002 prefixEnd_6653002 3416187821323884332778407 := by
  unfold tailWord_6653002
  simp only [CollatzResearch.WordTrace]
  refine ⟨60663729460829367781460315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161769945228878314083894173 60663729460829367781460315)
  ·
    refine ⟨90995594191244051672190473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60663729460829367781460315 90995594191244051672190473)
    ·
      refine ⟨68246695643433038754142855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90995594191244051672190473 68246695643433038754142855)
      ·
        refine ⟨102370043465149558131214283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68246695643433038754142855 102370043465149558131214283)
        ·
          refine ⟨153555065197724337196821425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102370043465149558131214283 153555065197724337196821425)
          ·
            refine ⟨115166298898293252897616069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153555065197724337196821425 115166298898293252897616069)
            ·
              refine ⟨21593681043429984918303013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115166298898293252897616069 21593681043429984918303013)
              ·
                refine ⟨4048815195643122172181815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21593681043429984918303013 4048815195643122172181815)
                ·
                  refine ⟨6073222793464683258272723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4048815195643122172181815 6073222793464683258272723)
                  ·
                    refine ⟨9109834190197024887409085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6073222793464683258272723 9109834190197024887409085)
                    ·
                      refine ⟨3416187821323884332778407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9109834190197024887409085 3416187821323884332778407)
                      ·
                        rfl

theorem cell23_6653002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 4, 1, 1, 3].length) (baseStart_6653002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6653002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6653002 prefixEnd_6653002 := by exact prefixLift 6653002
  have htrace : WordTrace (prefixWord ++ tailWord_6653002) baseStart_6653002 baseEnd_6653002 := by
    simpa [prefixWord, tailWord_6653002, baseEnd_6653002] using wordTrace_append hprefix tailTrace_6653002
  have hstable : (prefixWord ++ tailWord_6653002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6653002).length < 2 ^ (prefixWord ++ tailWord_6653002).sum := by decide
  have hdescent : baseEnd_6653002 < baseStart_6653002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6653002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6653011 : List Nat := [1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 5]
def baseStart_6653011 : Nat := 118140960795 + 6653011 * 2 ^ 59
def prefixEnd_6653011 : Nat := 4983230072969 + 3 ^ 40 * 6653011 * 2
def baseEnd_6653011 : Nat := 3416192442649774797565865

theorem tailTrace_6653011 : CollatzResearch.WordTrace tailWord_6653011 prefixEnd_6653011 3416192442649774797565865 := by
  unfold tailWord_6653011
  simp only [CollatzResearch.WordTrace]
  refine ⟨242655246100284865662918887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161770164066856577108612591 242655246100284865662918887)
  ·
    refine ⟨363982869150427298494378331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242655246100284865662918887 363982869150427298494378331)
    ·
      refine ⟨545974303725640947741567497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363982869150427298494378331 545974303725640947741567497)
      ·
        refine ⟨409480727794230710806175623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 545974303725640947741567497 409480727794230710806175623)
        ·
          refine ⟨614221091691346066209263435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409480727794230710806175623 614221091691346066209263435)
          ·
            refine ⟨921331637537019099313895153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 614221091691346066209263435 921331637537019099313895153)
            ·
              refine ⟨690998728152764324485421365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 921331637537019099313895153 690998728152764324485421365)
              ·
                refine ⟨64781130764321655420508253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 690998728152764324485421365 64781130764321655420508253)
                ·
                  refine ⟨24292924036620620782690595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64781130764321655420508253 24292924036620620782690595)
                  ·
                    refine ⟨36439386054930931174035893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24292924036620620782690595 36439386054930931174035893)
                    ·
                      refine ⟨3416192442649774797565865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36439386054930931174035893 3416192442649774797565865)
                      ·
                        rfl

theorem cell23_6653011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 5].length) (baseStart_6653011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6653011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6653011 prefixEnd_6653011 := by exact prefixLift 6653011
  have htrace : WordTrace (prefixWord ++ tailWord_6653011) baseStart_6653011 baseEnd_6653011 := by
    simpa [prefixWord, tailWord_6653011, baseEnd_6653011] using wordTrace_append hprefix tailTrace_6653011
  have hstable : (prefixWord ++ tailWord_6653011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6653011).length < 2 ^ (prefixWord ++ tailWord_6653011).sum := by decide
  have hdescent : baseEnd_6653011 < baseStart_6653011 := by decide
  rcases family_descends (prefixWord ++ tailWord_6653011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6653081 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 10]
def baseStart_6653081 : Nat := 118140960795 + 6653081 * 2 ^ 59
def prefixEnd_6653081 : Nat := 4983230072969 + 3 ^ 40 * 6653081 * 2
def baseEnd_6653081 : Nat := 3416228386295589523690543

theorem tailTrace_6653081 : CollatzResearch.WordTrace tailWord_6653081 prefixEnd_6653081 3416228386295589523690543 := by
  unfold tailWord_6653081
  simp only [CollatzResearch.WordTrace]
  refine ⟨242657799210031267617967097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161771866140020845078644731 242657799210031267617967097)
  ·
    refine ⟨181993349407523450713475323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242657799210031267617967097 181993349407523450713475323)
    ·
      refine ⟨272990024111285176070212985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181993349407523450713475323 272990024111285176070212985)
      ·
        refine ⟨204742518083463882052659739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272990024111285176070212985 204742518083463882052659739)
        ·
          refine ⟨307113777125195823078989609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204742518083463882052659739 307113777125195823078989609)
          ·
            refine ⟨230335332843896867309242207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 307113777125195823078989609 230335332843896867309242207)
            ·
              refine ⟨345502999265845300963863311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230335332843896867309242207 345502999265845300963863311)
              ·
                refine ⟨518254498898767951445794967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 345502999265845300963863311 518254498898767951445794967)
                ·
                  refine ⟨777381748348151927168692451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 518254498898767951445794967 777381748348151927168692451)
                  ·
                    refine ⟨1166072622522227890753038677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 777381748348151927168692451 1166072622522227890753038677)
                    ·
                      refine ⟨3416228386295589523690543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1166072622522227890753038677 3416228386295589523690543)
                      ·
                        rfl

theorem cell23_6653081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 10].length) (baseStart_6653081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6653081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6653081 prefixEnd_6653081 := by exact prefixLift 6653081
  have htrace : WordTrace (prefixWord ++ tailWord_6653081) baseStart_6653081 baseEnd_6653081 := by
    simpa [prefixWord, tailWord_6653081, baseEnd_6653081] using wordTrace_append hprefix tailTrace_6653081
  have hstable : (prefixWord ++ tailWord_6653081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6653081).length < 2 ^ (prefixWord ++ tailWord_6653081).sum := by decide
  have hdescent : baseEnd_6653081 < baseStart_6653081 := by decide
  rcases family_descends (prefixWord ++ tailWord_6653081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6653110 : List Nat := [5, 1, 3, 2, 1, 1, 1, 4, 1, 2, 2]
def baseStart_6653110 : Nat := 118140960795 + 6653110 * 2 ^ 59
def prefixEnd_6653110 : Nat := 4983230072969 + 3 ^ 40 * 6653110 * 2
def baseEnd_6653110 : Nat := 3416243277234569910227911

theorem tailTrace_6653110 : CollatzResearch.WordTrace tailWord_6653110 prefixEnd_6653110 3416243277234569910227911 := by
  unfold tailWord_6653110
  simp only [CollatzResearch.WordTrace]
  refine ⟨15166178557932887848173299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161772571284617470380515189 15166178557932887848173299)
  ·
    refine ⟨22749267836899331772259949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15166178557932887848173299 22749267836899331772259949)
    ·
      refine ⟨8530975438837249414597481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22749267836899331772259949 8530975438837249414597481)
      ·
        refine ⟨6398231579127937060948111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8530975438837249414597481 6398231579127937060948111)
        ·
          refine ⟨9597347368691905591422167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6398231579127937060948111 9597347368691905591422167)
          ·
            refine ⟨14396021053037858387133251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9597347368691905591422167 14396021053037858387133251)
            ·
              refine ⟨21594031579556787580699877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14396021053037858387133251 21594031579556787580699877)
              ·
                refine ⟨4048880921166897671381227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21594031579556787580699877 4048880921166897671381227)
                ·
                  refine ⟨6073321381750346507071841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4048880921166897671381227 6073321381750346507071841)
                  ·
                    refine ⟨4554991036312759880303881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6073321381750346507071841 4554991036312759880303881)
                    ·
                      refine ⟨3416243277234569910227911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4554991036312759880303881 3416243277234569910227911)
                      ·
                        rfl

theorem cell23_6653110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_6653110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6653110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6653110 prefixEnd_6653110 := by exact prefixLift 6653110
  have htrace : WordTrace (prefixWord ++ tailWord_6653110) baseStart_6653110 baseEnd_6653110 := by
    simpa [prefixWord, tailWord_6653110, baseEnd_6653110] using wordTrace_append hprefix tailTrace_6653110
  have hstable : (prefixWord ++ tailWord_6653110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6653110).length < 2 ^ (prefixWord ++ tailWord_6653110).sum := by decide
  have hdescent : baseEnd_6653110 < baseStart_6653110 := by decide
  rcases family_descends (prefixWord ++ tailWord_6653110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6653128 : List Nat := [2, 1, 3, 1, 2, 1, 3, 1, 1, 4, 4]
def baseStart_6653128 : Nat := 118140960795 + 6653128 * 2 ^ 59
def prefixEnd_6653128 : Nat := 4983230072969 + 3 ^ 40 * 6653128 * 2
def baseEnd_6653128 : Nat := 3416252519886350839802827

theorem tailTrace_6653128 : CollatzResearch.WordTrace tailWord_6653128 prefixEnd_6653128 3416252519886350839802827 := by
  unfold tailWord_6653128
  simp only [CollatzResearch.WordTrace]
  refine ⟨121329756720430497322464019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161773008960573996429952025 121329756720430497322464019)
  ·
    refine ⟨181994635080645745983696029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121329756720430497322464019 181994635080645745983696029)
    ·
      refine ⟨68247988155242154743886011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181994635080645745983696029 68247988155242154743886011)
      ·
        refine ⟨102371982232863232115829017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68247988155242154743886011 102371982232863232115829017)
        ·
          refine ⟨76778986674647424086871763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102371982232863232115829017 76778986674647424086871763)
          ·
            refine ⟨115168480011971136130307645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76778986674647424086871763 115168480011971136130307645)
            ·
              refine ⟨43188180004489176048865367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115168480011971136130307645 43188180004489176048865367)
              ·
                refine ⟨64782270006733764073298051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43188180004489176048865367 64782270006733764073298051)
                ·
                  refine ⟨97173405010100646109947077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64782270006733764073298051 97173405010100646109947077)
                  ·
                    refine ⟨18220013439393871145615077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 97173405010100646109947077 18220013439393871145615077)
                    ·
                      refine ⟨3416252519886350839802827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18220013439393871145615077 3416252519886350839802827)
                      ·
                        rfl

theorem cell23_6653128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_6653128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6653128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6653128 prefixEnd_6653128 := by exact prefixLift 6653128
  have htrace : WordTrace (prefixWord ++ tailWord_6653128) baseStart_6653128 baseEnd_6653128 := by
    simpa [prefixWord, tailWord_6653128, baseEnd_6653128] using wordTrace_append hprefix tailTrace_6653128
  have hstable : (prefixWord ++ tailWord_6653128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6653128).length < 2 ^ (prefixWord ++ tailWord_6653128).sum := by decide
  have hdescent : baseEnd_6653128 < baseStart_6653128 := by decide
  rcases family_descends (prefixWord ++ tailWord_6653128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6653178 : List Nat := [3, 1, 1, 1, 1, 4, 2, 1, 1, 1, 7]
def baseStart_6653178 : Nat := 118140960795 + 6653178 * 2 ^ 59
def prefixEnd_6653178 : Nat := 4983230072969 + 3 ^ 40 * 6653178 * 2
def baseEnd_6653178 : Nat := 3416278193919075644177597

theorem tailTrace_6653178 : CollatzResearch.WordTrace tailWord_6653178 prefixEnd_6653178 3416278193919075644177597 := by
  unfold tailWord_6653178
  simp only [CollatzResearch.WordTrace]
  refine ⟨60665334272669963296062047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161774224727119902122832125 60665334272669963296062047)
  ·
    refine ⟨90998001409004944944093071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60665334272669963296062047 90998001409004944944093071)
    ·
      refine ⟨136497002113507417416139607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90998001409004944944093071 136497002113507417416139607)
      ·
        refine ⟨204745503170261126124209411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136497002113507417416139607 204745503170261126124209411)
        ·
          refine ⟨307118254755391689186314117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204745503170261126124209411 307118254755391689186314117)
          ·
            refine ⟨57584672766635941722433897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 307118254755391689186314117 57584672766635941722433897)
            ·
              refine ⟨43188504574976956291825423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57584672766635941722433897 43188504574976956291825423)
              ·
                refine ⟨64782756862465434437738135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43188504574976956291825423 64782756862465434437738135)
                ·
                  refine ⟨97174135293698151656607203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64782756862465434437738135 97174135293698151656607203)
                  ·
                    refine ⟨145761202940547227484910805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 97174135293698151656607203 145761202940547227484910805)
                    ·
                      refine ⟨3416278193919075644177597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 145761202940547227484910805 3416278193919075644177597)
                      ·
                        rfl

theorem cell23_6653178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 1, 1, 7].length) (baseStart_6653178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6653178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6653178 prefixEnd_6653178 := by exact prefixLift 6653178
  have htrace : WordTrace (prefixWord ++ tailWord_6653178) baseStart_6653178 baseEnd_6653178 := by
    simpa [prefixWord, tailWord_6653178, baseEnd_6653178] using wordTrace_append hprefix tailTrace_6653178
  have hstable : (prefixWord ++ tailWord_6653178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6653178).length < 2 ^ (prefixWord ++ tailWord_6653178).sum := by decide
  have hdescent : baseEnd_6653178 < baseStart_6653178 := by decide
  rcases family_descends (prefixWord ++ tailWord_6653178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6653182 : List Nat := [4, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3]
def baseStart_6653182 : Nat := 118140960795 + 6653182 * 2 ^ 59
def prefixEnd_6653182 : Nat := 4983230072969 + 3 ^ 40 * 6653182 * 2
def baseEnd_6653182 : Nat := 3416280247841693628527579

theorem tailTrace_6653182 : CollatzResearch.WordTrace tailWord_6653182 prefixEnd_6653182 3416280247841693628527579 := by
  unfold tailWord_6653182
  simp only [CollatzResearch.WordTrace]
  refine ⟨30332685372833170233424225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161774321988443574578262533 30332685372833170233424225)
  ·
    refine ⟨22749514029624877675068169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30332685372833170233424225 22749514029624877675068169)
    ·
      refine ⟨17062135522218658256301127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22749514029624877675068169 17062135522218658256301127)
      ·
        refine ⟨25593203283327987384451691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17062135522218658256301127 25593203283327987384451691)
        ·
          refine ⟨38389804924991981076677537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25593203283327987384451691 38389804924991981076677537)
          ·
            refine ⟨28792353693743985807508153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38389804924991981076677537 28792353693743985807508153)
            ·
              refine ⟨21594265270307989355631115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28792353693743985807508153 21594265270307989355631115)
              ·
                refine ⟨32391397905461984033446673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21594265270307989355631115 32391397905461984033446673)
                ·
                  refine ⟨24293548429096488025085005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32391397905461984033446673 24293548429096488025085005)
                  ·
                    refine ⟨9110080660911183009406877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24293548429096488025085005 9110080660911183009406877)
                    ·
                      refine ⟨3416280247841693628527579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9110080660911183009406877 3416280247841693628527579)
                      ·
                        rfl

theorem cell23_6653182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_6653182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6653182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6653182 prefixEnd_6653182 := by exact prefixLift 6653182
  have htrace : WordTrace (prefixWord ++ tailWord_6653182) baseStart_6653182 baseEnd_6653182 := by
    simpa [prefixWord, tailWord_6653182, baseEnd_6653182] using wordTrace_append hprefix tailTrace_6653182
  have hstable : (prefixWord ++ tailWord_6653182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6653182).length < 2 ^ (prefixWord ++ tailWord_6653182).sum := by decide
  have hdescent : baseEnd_6653182 < baseStart_6653182 := by decide
  rcases family_descends (prefixWord ++ tailWord_6653182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6653205 : List Nat := [1, 3, 2, 1, 2, 1, 1, 5, 2, 1, 4]
def baseStart_6653205 : Nat := 118140960795 + 6653205 * 2 ^ 59
def prefixEnd_6653205 : Nat := 4983230072969 + 3 ^ 40 * 6653205 * 2
def baseEnd_6653205 : Nat := 3416292057896747038539973

theorem tailTrace_6653205 : CollatzResearch.WordTrace tailWord_6653205 prefixEnd_6653205 3416292057896747038539973 := by
  unfold tailWord_6653205
  simp only [CollatzResearch.WordTrace]
  refine ⟨242662321861582036795481069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161774881241054691196987379 242662321861582036795481069)
  ·
    refine ⟨90998370698093263798305401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242662321861582036795481069 90998370698093263798305401)
    ·
      refine ⟨68248778023569947848729051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90998370698093263798305401 68248778023569947848729051)
      ·
        refine ⟨102373167035354921773093577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68248778023569947848729051 102373167035354921773093577)
        ·
          refine ⟨76779875276516191329820183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102373167035354921773093577 76779875276516191329820183)
          ·
            refine ⟨115169812914774286994730275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76779875276516191329820183 115169812914774286994730275)
            ·
              refine ⟨172754719372161430492095413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115169812914774286994730275 172754719372161430492095413)
              ·
                refine ⟨16195754941140134108633945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 172754719372161430492095413 16195754941140134108633945)
                ·
                  refine ⟨12146816205855100581475459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16195754941140134108633945 12146816205855100581475459)
                  ·
                    refine ⟨18220224308782650872213189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12146816205855100581475459 18220224308782650872213189)
                    ·
                      refine ⟨3416292057896747038539973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18220224308782650872213189 3416292057896747038539973)
                      ·
                        rfl

theorem cell23_6653205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_6653205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6653205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6653205 prefixEnd_6653205 := by exact prefixLift 6653205
  have htrace : WordTrace (prefixWord ++ tailWord_6653205) baseStart_6653205 baseEnd_6653205 := by
    simpa [prefixWord, tailWord_6653205, baseEnd_6653205] using wordTrace_append hprefix tailTrace_6653205
  have hstable : (prefixWord ++ tailWord_6653205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6653205).length < 2 ^ (prefixWord ++ tailWord_6653205).sum := by decide
  have hdescent : baseEnd_6653205 < baseStart_6653205 := by decide
  rcases family_descends (prefixWord ++ tailWord_6653205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6653295 : List Nat := [1, 1, 2, 1, 3, 1, 3, 1, 5, 1, 4]
def baseStart_6653295 : Nat := 118140960795 + 6653295 * 2 ^ 59
def prefixEnd_6653295 : Nat := 4983230072969 + 3 ^ 40 * 6653295 * 2
def baseEnd_6653295 : Nat := 3416338271155651686414559

theorem tailTrace_6653295 : CollatzResearch.WordTrace tailWord_6653295 prefixEnd_6653295 3416338271155651686414559 := by
  unfold tailWord_6653295
  simp only [CollatzResearch.WordTrace]
  refine ⟨242665604431255982166257339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161777069620837321444171559 242665604431255982166257339)
  ·
    refine ⟨363998406646883973249386009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242665604431255982166257339 363998406646883973249386009)
    ·
      refine ⟨272998804985162979937039507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 363998406646883973249386009 272998804985162979937039507)
      ·
        refine ⟨409498207477744469905559261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272998804985162979937039507 409498207477744469905559261)
        ·
          refine ⟨153561827804154176214584723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 409498207477744469905559261 153561827804154176214584723)
          ·
            refine ⟨230342741706231264321877085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153561827804154176214584723 230342741706231264321877085)
            ·
              refine ⟨86378528139836724120703907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 230342741706231264321877085 86378528139836724120703907)
              ·
                refine ⟨129567792209755086181055861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86378528139836724120703907 129567792209755086181055861)
                ·
                  refine ⟨12146980519664539329473987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 129567792209755086181055861 12146980519664539329473987)
                  ·
                    refine ⟨18220470779496808994210981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12146980519664539329473987 18220470779496808994210981)
                    ·
                      refine ⟨3416338271155651686414559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18220470779496808994210981 3416338271155651686414559)
                      ·
                        rfl

theorem cell23_6653295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 5, 1, 4].length) (baseStart_6653295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6653295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6653295 prefixEnd_6653295 := by exact prefixLift 6653295
  have htrace : WordTrace (prefixWord ++ tailWord_6653295) baseStart_6653295 baseEnd_6653295 := by
    simpa [prefixWord, tailWord_6653295, baseEnd_6653295] using wordTrace_append hprefix tailTrace_6653295
  have hstable : (prefixWord ++ tailWord_6653295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6653295).length < 2 ^ (prefixWord ++ tailWord_6653295).sum := by decide
  have hdescent : baseEnd_6653295 < baseStart_6653295 := by decide
  rcases family_descends (prefixWord ++ tailWord_6653295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6653305 : List Nat := [1, 2, 1, 3, 2, 1, 3, 3, 1, 6]
def baseStart_6653305 : Nat := 118140960795 + 6653305 * 2 ^ 59
def prefixEnd_6653305 : Nat := 4983230072969 + 3 ^ 40 * 6653305 * 2
def baseEnd_6653305 : Nat := 1138781135320732215763171

theorem tailTrace_6653305 : CollatzResearch.WordTrace tailWord_6653305 prefixEnd_6653305 1138781135320732215763171 := by
  unfold tailWord_6653305
  simp only [CollatzResearch.WordTrace]
  refine ⟨242665969161219753874121369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161777312774146502582747579 242665969161219753874121369)
  ·
    refine ⟨181999476870914815405591027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242665969161219753874121369 181999476870914815405591027)
    ·
      refine ⟨272999215306372223108386541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181999476870914815405591027 272999215306372223108386541)
      ·
        refine ⟨102374705739889583665644953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 272999215306372223108386541 102374705739889583665644953)
        ·
          refine ⟨76781029304917187749233715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102374705739889583665644953 76781029304917187749233715)
          ·
            refine ⟨115171543957375781623850573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76781029304917187749233715 115171543957375781623850573)
            ·
              refine ⟨43189328984015918108943965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115171543957375781623850573 43189328984015918108943965)
              ·
                refine ⟨16195998369005969290853987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43189328984015918108943965 16195998369005969290853987)
                ·
                  refine ⟨24293997553508953936280981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16195998369005969290853987 24293997553508953936280981)
                  ·
                    refine ⟨1138781135320732215763171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24293997553508953936280981 1138781135320732215763171)
                    ·
                      rfl

theorem cell23_6653305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 6].length) (baseStart_6653305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6653305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6653305 prefixEnd_6653305 := by exact prefixLift 6653305
  have htrace : WordTrace (prefixWord ++ tailWord_6653305) baseStart_6653305 baseEnd_6653305 := by
    simpa [prefixWord, tailWord_6653305, baseEnd_6653305] using wordTrace_append hprefix tailTrace_6653305
  have hstable : (prefixWord ++ tailWord_6653305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6653305).length < 2 ^ (prefixWord ++ tailWord_6653305).sum := by decide
  have hdescent : baseEnd_6653305 < baseStart_6653305 := by decide
  rcases family_descends (prefixWord ++ tailWord_6653305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6653310 : List Nat := [4, 2, 3, 2, 2, 1, 1, 1, 2, 2, 3]
def baseStart_6653310 : Nat := 118140960795 + 6653310 * 2 ^ 59
def prefixEnd_6653310 : Nat := 4983230072969 + 3 ^ 40 * 6653310 * 2
def baseEnd_6653310 : Nat := 3416345973365469127726991

theorem tailTrace_6653310 : CollatzResearch.WordTrace tailWord_6653310 prefixEnd_6653310 3416345973365469127726991 := by
  unfold tailWord_6653310
  simp only [CollatzResearch.WordTrace]
  refine ⟨30333268940775204966006673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161777434350801093152035589 30333268940775204966006673)
  ·
    refine ⟨22749951705581403724505005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30333268940775204966006673 22749951705581403724505005)
    ·
      refine ⟨8531231889593026396689377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22749951705581403724505005 8531231889593026396689377)
      ·
        refine ⟨6398423917194769797517033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8531231889593026396689377 6398423917194769797517033)
        ·
          refine ⟨4798817937896077348137775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6398423917194769797517033 4798817937896077348137775)
          ·
            refine ⟨7198226906844116022206663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4798817937896077348137775 7198226906844116022206663)
            ·
              refine ⟨10797340360266174033309995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7198226906844116022206663 10797340360266174033309995)
              ·
                refine ⟨16196010540399261049964993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10797340360266174033309995 16196010540399261049964993)
                ·
                  refine ⟨12147007905299445787473745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16196010540399261049964993 12147007905299445787473745)
                  ·
                    refine ⟨9110255928974584340605309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12147007905299445787473745 9110255928974584340605309)
                    ·
                      refine ⟨3416345973365469127726991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9110255928974584340605309 3416345973365469127726991)
                      ·
                        rfl

theorem cell23_6653310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_6653310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6653310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6653310 prefixEnd_6653310 := by exact prefixLift 6653310
  have htrace : WordTrace (prefixWord ++ tailWord_6653310) baseStart_6653310 baseEnd_6653310 := by
    simpa [prefixWord, tailWord_6653310, baseEnd_6653310] using wordTrace_append hprefix tailTrace_6653310
  have hstable : (prefixWord ++ tailWord_6653310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6653310).length < 2 ^ (prefixWord ++ tailWord_6653310).sum := by decide
  have hdescent : baseEnd_6653310 < baseStart_6653310 := by decide
  rcases family_descends (prefixWord ++ tailWord_6653310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6653316 : List Nat := [2, 3, 2, 1, 1, 5, 1, 1, 2, 3, 2]
def baseStart_6653316 : Nat := 118140960795 + 6653316 * 2 ^ 59
def prefixEnd_6653316 : Nat := 4983230072969 + 3 ^ 40 * 6653316 * 2
def baseEnd_6653316 : Nat := 3416349054249396104251963

theorem tailTrace_6653316 : CollatzResearch.WordTrace tailWord_6653316 prefixEnd_6653316 3416349054249396104251963 := by
  unfold tailWord_6653316
  simp only [CollatzResearch.WordTrace]
  refine ⟨121333185182089951376385901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161777580242786601835181201 121333185182089951376385901)
  ·
    refine ⟨45499944443283731766144713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121333185182089951376385901 45499944443283731766144713)
    ·
      refine ⟨34124958332462798824608535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45499944443283731766144713 34124958332462798824608535)
      ·
        refine ⟨51187437498694198236912803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34124958332462798824608535 51187437498694198236912803)
        ·
          refine ⟨76781156248041297355369205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51187437498694198236912803 76781156248041297355369205)
          ·
            refine ⟨7198233398253871627065863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76781156248041297355369205 7198233398253871627065863)
            ·
              refine ⟨10797350097380807440598795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7198233398253871627065863 10797350097380807440598795)
              ·
                refine ⟨16196025146071211160898193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10797350097380807440598795 16196025146071211160898193)
                ·
                  refine ⟨12147018859553408370673645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16196025146071211160898193 12147018859553408370673645)
                  ·
                    refine ⟨4555132072332528139002617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12147018859553408370673645 4555132072332528139002617)
                    ·
                      refine ⟨3416349054249396104251963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4555132072332528139002617 3416349054249396104251963)
                      ·
                        rfl

theorem cell23_6653316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 2, 3, 2].length) (baseStart_6653316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6653316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6653316 prefixEnd_6653316 := by exact prefixLift 6653316
  have htrace : WordTrace (prefixWord ++ tailWord_6653316) baseStart_6653316 baseEnd_6653316 := by
    simpa [prefixWord, tailWord_6653316, baseEnd_6653316] using wordTrace_append hprefix tailTrace_6653316
  have hstable : (prefixWord ++ tailWord_6653316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6653316).length < 2 ^ (prefixWord ++ tailWord_6653316).sum := by decide
  have hdescent : baseEnd_6653316 < baseStart_6653316 := by decide
  rcases family_descends (prefixWord ++ tailWord_6653316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6653346 : List Nat := [3, 3, 1, 2, 1, 2, 1, 3, 3, 2, 2]
def baseStart_6653346 : Nat := 118140960795 + 6653346 * 2 ^ 59
def prefixEnd_6653346 : Nat := 4983230072969 + 3 ^ 40 * 6653346 * 2
def baseEnd_6653346 : Nat := 3416364458669030986876825

theorem tailTrace_6653346 : CollatzResearch.WordTrace tailWord_6653346 prefixEnd_6653346 3416364458669030986876825 := by
  unfold tailWord_6653346
  simp only [CollatzResearch.WordTrace]
  refine ⟨60666866138517804469090973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161778309702714145250909261 60666866138517804469090973)
  ·
    refine ⟨22750074801944176675909115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60666866138517804469090973 22750074801944176675909115)
    ·
      refine ⟨34125112202916265013863673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22750074801944176675909115 34125112202916265013863673)
      ·
        refine ⟨25593834152187198760397755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34125112202916265013863673 25593834152187198760397755)
        ·
          refine ⟨38390751228280798140596633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25593834152187198760397755 38390751228280798140596633)
          ·
            refine ⟨28793063421210598605447475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38390751228280798140596633 28793063421210598605447475)
            ·
              refine ⟨43189595131815897908171213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28793063421210598605447475 43189595131815897908171213)
              ·
                refine ⟨16196098174430961715564205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43189595131815897908171213 16196098174430961715564205)
                ·
                  refine ⟨6073536815411610643336577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16196098174430961715564205 6073536815411610643336577)
                  ·
                    refine ⟨4555152611558707982502433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6073536815411610643336577 4555152611558707982502433)
                    ·
                      refine ⟨3416364458669030986876825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4555152611558707982502433 3416364458669030986876825)
                      ·
                        rfl

theorem cell23_6653346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_6653346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6653346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6653346 prefixEnd_6653346 := by exact prefixLift 6653346
  have htrace : WordTrace (prefixWord ++ tailWord_6653346) baseStart_6653346 baseEnd_6653346 := by
    simpa [prefixWord, tailWord_6653346, baseEnd_6653346] using wordTrace_append hprefix tailTrace_6653346
  have hstable : (prefixWord ++ tailWord_6653346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6653346).length < 2 ^ (prefixWord ++ tailWord_6653346).sum := by decide
  have hdescent : baseEnd_6653346 < baseStart_6653346 := by decide
  rcases family_descends (prefixWord ++ tailWord_6653346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6653362 : List Nat := [3, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3]
def baseStart_6653362 : Nat := 118140960795 + 6653362 * 2 ^ 59
def prefixEnd_6653362 : Nat := 4983230072969 + 3 ^ 40 * 6653362 * 2
def baseEnd_6653362 : Nat := 3416372674359502924276751

theorem tailTrace_6653362 : CollatzResearch.WordTrace tailWord_6653362 prefixEnd_6653362 3416372674359502924276751 := by
  unfold tailWord_6653362
  simp only [CollatzResearch.WordTrace]
  refine ⟨60667012030503313152236585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161778698748008835072630893 60667012030503313152236585)
  ·
    refine ⟨45500259022877484864177439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60667012030503313152236585 45500259022877484864177439)
    ·
      refine ⟨68250388534316227296266159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45500259022877484864177439 68250388534316227296266159)
      ·
        refine ⟨102375582801474340944399239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68250388534316227296266159 102375582801474340944399239)
        ·
          refine ⟨153563374202211511416598859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102375582801474340944399239 153563374202211511416598859)
          ·
            refine ⟨230345061303317267124898289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153563374202211511416598859 230345061303317267124898289)
            ·
              refine ⟨172758795977487950343673717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230345061303317267124898289 172758795977487950343673717)
              ·
                refine ⟨16196137122889495344719411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 172758795977487950343673717 16196137122889495344719411)
                ·
                  refine ⟨24294205684334243017079117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16196137122889495344719411 24294205684334243017079117)
                  ·
                    refine ⟨9110327131625341131404669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24294205684334243017079117 9110327131625341131404669)
                    ·
                      refine ⟨3416372674359502924276751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9110327131625341131404669 3416372674359502924276751)
                      ·
                        rfl

theorem cell23_6653362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3].length) (baseStart_6653362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6653362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6653362 prefixEnd_6653362 := by exact prefixLift 6653362
  have htrace : WordTrace (prefixWord ++ tailWord_6653362) baseStart_6653362 baseEnd_6653362 := by
    simpa [prefixWord, tailWord_6653362, baseEnd_6653362] using wordTrace_append hprefix tailTrace_6653362
  have hstable : (prefixWord ++ tailWord_6653362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6653362).length < 2 ^ (prefixWord ++ tailWord_6653362).sum := by decide
  have hdescent : baseEnd_6653362 < baseStart_6653362 := by decide
  rcases family_descends (prefixWord ++ tailWord_6653362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6653369 : List Nat := [1, 2, 1, 4, 4, 2, 2, 7]
def baseStart_6653369 : Nat := 118140960795 + 6653369 * 2 ^ 59
def prefixEnd_6653369 : Nat := 4983230072969 + 3 ^ 40 * 6653369 * 2
def baseEnd_6653369 : Nat := 126532454397188310995897

theorem tailTrace_6653369 : CollatzResearch.WordTrace tailWord_6653369 prefixEnd_6653369 126532454397188310995897 := by
  unfold tailWord_6653369
  simp only [CollatzResearch.WordTrace]
  refine ⟨242668303432987892804451161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161778868955325261869634107 242668303432987892804451161)
  ·
    refine ⟨182001227574740919603338371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242668303432987892804451161 182001227574740919603338371)
    ·
      refine ⟨273001841362111379405007557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182001227574740919603338371 273001841362111379405007557)
      ·
        refine ⟨51187845255395883638438917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 273001841362111379405007557 51187845255395883638438917)
        ·
          refine ⟨9597720985386728182207297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51187845255395883638438917 9597720985386728182207297)
          ·
            refine ⟨7198290739040046136655473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9597720985386728182207297 7198290739040046136655473)
            ·
              refine ⟨5398718054280034602491605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7198290739040046136655473 5398718054280034602491605)
              ·
                refine ⟨126532454397188310995897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5398718054280034602491605 126532454397188310995897)
                ·
                  rfl

theorem cell23_6653369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 7].length) (baseStart_6653369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6653369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6653369 prefixEnd_6653369 := by exact prefixLift 6653369
  have htrace : WordTrace (prefixWord ++ tailWord_6653369) baseStart_6653369 baseEnd_6653369 := by
    simpa [prefixWord, tailWord_6653369, baseEnd_6653369] using wordTrace_append hprefix tailTrace_6653369
  have hstable : (prefixWord ++ tailWord_6653369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6653369).length < 2 ^ (prefixWord ++ tailWord_6653369).sum := by decide
  have hdescent : baseEnd_6653369 < baseStart_6653369 := by decide
  rcases family_descends (prefixWord ++ tailWord_6653369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6653380 : List Nat := [2, 3, 3, 2, 1, 1, 3, 3, 1, 2, 2]
def baseStart_6653380 : Nat := 118140960795 + 6653380 * 2 ^ 59
def prefixEnd_6653380 : Nat := 4983230072969 + 3 ^ 40 * 6653380 * 2
def baseEnd_6653380 : Nat := 3416381917011283853851669

theorem tailTrace_6653380 : CollatzResearch.WordTrace tailWord_6653380 prefixEnd_6653380 3416381917011283853851669 := by
  unfold tailWord_6653380
  simp only [CollatzResearch.WordTrace]
  refine ⟨121334352317974020841550797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161779136423965361122067729 121334352317974020841550797)
  ·
    refine ⟨45500382119240257815581549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121334352317974020841550797 45500382119240257815581549)
    ·
      refine ⟨17062643294715096680843081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45500382119240257815581549 17062643294715096680843081)
      ·
        refine ⟨12796982471036322510632311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17062643294715096680843081 12796982471036322510632311)
        ·
          refine ⟨19195473706554483765948467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12796982471036322510632311 19195473706554483765948467)
          ·
            refine ⟨28793210559831725648922701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19195473706554483765948467 28793210559831725648922701)
            ·
              refine ⟨10797453959936897118346013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28793210559831725648922701 10797453959936897118346013)
              ·
                refine ⟨4049045234976336419379755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10797453959936897118346013 4049045234976336419379755)
                ·
                  refine ⟨6073567852464504629069633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4049045234976336419379755 6073567852464504629069633)
                  ·
                    refine ⟨4555175889348378471802225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6073567852464504629069633 4555175889348378471802225)
                    ·
                      refine ⟨3416381917011283853851669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4555175889348378471802225 3416381917011283853851669)
                      ·
                        rfl

theorem cell23_6653380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_6653380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6653380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6653380 prefixEnd_6653380 := by exact prefixLift 6653380
  have htrace : WordTrace (prefixWord ++ tailWord_6653380) baseStart_6653380 baseEnd_6653380 := by
    simpa [prefixWord, tailWord_6653380, baseEnd_6653380] using wordTrace_append hprefix tailTrace_6653380
  have hstable : (prefixWord ++ tailWord_6653380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6653380).length < 2 ^ (prefixWord ++ tailWord_6653380).sum := by decide
  have hdescent : baseEnd_6653380 < baseStart_6653380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6653380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6653385 : List Nat := [1, 2, 1, 1, 2, 1, 3, 2, 1, 5, 4]
def baseStart_6653385 : Nat := 118140960795 + 6653385 * 2 ^ 59
def prefixEnd_6653385 : Nat := 4983230072969 + 3 ^ 40 * 6653385 * 2
def baseEnd_6653385 : Nat := 3416384484414556334289145

theorem tailTrace_6653385 : CollatzResearch.WordTrace tailWord_6653385 prefixEnd_6653385 3416384484414556334289145 := by
  unfold tailWord_6653385
  simp only [CollatzResearch.WordTrace]
  refine ⟨242668887000929927537033609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161779258000619951691355739 242668887000929927537033609)
  ·
    refine ⟨182001665250697445652775207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242668887000929927537033609 182001665250697445652775207)
    ·
      refine ⟨273002497876046168479162811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182001665250697445652775207 273002497876046168479162811)
      ·
        refine ⟨409503746814069252718744217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273002497876046168479162811 409503746814069252718744217)
        ·
          refine ⟨307127810110551939539058163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 409503746814069252718744217 307127810110551939539058163)
          ·
            refine ⟨460691715165827909308587245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307127810110551939539058163 460691715165827909308587245)
            ·
              refine ⟨172759393187185465990720217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 460691715165827909308587245 172759393187185465990720217)
              ·
                refine ⟨129569544890389099493040163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172759393187185465990720217 129569544890389099493040163)
                ·
                  refine ⟨194354317335583649239560245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129569544890389099493040163 194354317335583649239560245)
                  ·
                    refine ⟨18220717250210967116208773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 194354317335583649239560245 18220717250210967116208773)
                    ·
                      refine ⟨3416384484414556334289145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18220717250210967116208773 3416384484414556334289145)
                      ·
                        rfl

theorem cell23_6653385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 5, 4].length) (baseStart_6653385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6653385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6653385 prefixEnd_6653385 := by exact prefixLift 6653385
  have htrace : WordTrace (prefixWord ++ tailWord_6653385) baseStart_6653385 baseEnd_6653385 := by
    simpa [prefixWord, tailWord_6653385, baseEnd_6653385] using wordTrace_append hprefix tailTrace_6653385
  have hstable : (prefixWord ++ tailWord_6653385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6653385).length < 2 ^ (prefixWord ++ tailWord_6653385).sum := by decide
  have hdescent : baseEnd_6653385 < baseStart_6653385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6653385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6653413 : List Nat := [1, 3, 1, 5, 1, 1, 4, 1, 2, 1, 3]
def baseStart_6653413 : Nat := 118140960795 + 6653413 * 2 ^ 59
def prefixEnd_6653413 : Nat := 4983230072969 + 3 ^ 40 * 6653413 * 2
def baseEnd_6653413 : Nat := 3416398861872882224739017

theorem tailTrace_6653413 : CollatzResearch.WordTrace tailWord_6653413 prefixEnd_6653413 3416398861872882224739017 := by
  unfold tailWord_6653413
  simp only [CollatzResearch.WordTrace]
  refine ⟨242669908244828488319052893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161779938829885658879368595 242669908244828488319052893)
  ·
    refine ⟨91001215591810683119644835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242669908244828488319052893 91001215591810683119644835)
    ·
      refine ⟨136501823387716024679467253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91001215591810683119644835 136501823387716024679467253)
      ·
        refine ⟨12797045942598377313700055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 136501823387716024679467253 12797045942598377313700055)
        ·
          refine ⟨19195568913897565970550083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12797045942598377313700055 19195568913897565970550083)
          ·
            refine ⟨28793353370846348955825125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19195568913897565970550083 28793353370846348955825125)
            ·
              refine ⟨5398753757033690429217211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28793353370846348955825125 5398753757033690429217211)
              ·
                refine ⟨8098130635550535643825817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5398753757033690429217211 8098130635550535643825817)
                ·
                  refine ⟨6073597976662901732869363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8098130635550535643825817 6073597976662901732869363)
                  ·
                    refine ⟨9110396964994352599304045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6073597976662901732869363 9110396964994352599304045)
                    ·
                      refine ⟨3416398861872882224739017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9110396964994352599304045 3416398861872882224739017)
                      ·
                        rfl

theorem cell23_6653413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_6653413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6653413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6653413 prefixEnd_6653413 := by exact prefixLift 6653413
  have htrace : WordTrace (prefixWord ++ tailWord_6653413) baseStart_6653413 baseEnd_6653413 := by
    simpa [prefixWord, tailWord_6653413, baseEnd_6653413] using wordTrace_append hprefix tailTrace_6653413
  have hstable : (prefixWord ++ tailWord_6653413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6653413).length < 2 ^ (prefixWord ++ tailWord_6653413).sum := by decide
  have hdescent : baseEnd_6653413 < baseStart_6653413 := by decide
  rcases family_descends (prefixWord ++ tailWord_6653413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6653419 : List Nat := [1, 1, 1, 1, 2, 3, 2, 2, 6, 2, 2]
def baseStart_6653419 : Nat := 118140960795 + 6653419 * 2 ^ 59
def prefixEnd_6653419 : Nat := 4983230072969 + 3 ^ 40 * 6653419 * 2
def baseEnd_6653419 : Nat := 3416401942756809201263989

theorem tailTrace_6653419 : CollatzResearch.WordTrace tailWord_6653419 prefixEnd_6653419 3416401942756809201263989 := by
  unfold tailWord_6653419
  simp only [CollatzResearch.WordTrace]
  refine ⟨242670127082806751343771311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161780084721871167562514207 242670127082806751343771311)
  ·
    refine ⟨364005190624210127015656967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242670127082806751343771311 364005190624210127015656967)
    ·
      refine ⟨546007785936315190523485451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364005190624210127015656967 546007785936315190523485451)
      ·
        refine ⟨819011678904472785785228177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 546007785936315190523485451 819011678904472785785228177)
        ·
          refine ⟨614258759178354589338921133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 819011678904472785785228177 614258759178354589338921133)
          ·
            refine ⟨230347034691882971002095425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 614258759178354589338921133 230347034691882971002095425)
            ·
              refine ⟨172760276018912228251571569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230347034691882971002095425 172760276018912228251571569)
              ·
                refine ⟨129570207014184171188678677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172760276018912228251571569 129570207014184171188678677)
                ·
                  refine ⟨6073603453789883024469313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 129570207014184171188678677 6073603453789883024469313)
                  ·
                    refine ⟨4555202590342412268351985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6073603453789883024469313 4555202590342412268351985)
                    ·
                      refine ⟨3416401942756809201263989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4555202590342412268351985 3416401942756809201263989)
                      ·
                        rfl

theorem cell23_6653419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 6, 2, 2].length) (baseStart_6653419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6653419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6653419 prefixEnd_6653419 := by exact prefixLift 6653419
  have htrace : WordTrace (prefixWord ++ tailWord_6653419) baseStart_6653419 baseEnd_6653419 := by
    simpa [prefixWord, tailWord_6653419, baseEnd_6653419] using wordTrace_append hprefix tailTrace_6653419
  have hstable : (prefixWord ++ tailWord_6653419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6653419).length < 2 ^ (prefixWord ++ tailWord_6653419).sum := by decide
  have hdescent : baseEnd_6653419 < baseStart_6653419 := by decide
  rcases family_descends (prefixWord ++ tailWord_6653419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6653422 : List Nat := [4, 1, 2, 1, 2, 1, 1, 1, 4, 1, 5]
def baseStart_6653422 : Nat := 118140960795 + 6653422 * 2 ^ 59
def prefixEnd_6653422 : Nat := 4983230072969 + 3 ^ 40 * 6653422 * 2
def baseEnd_6653422 : Nat := 3416403483198772689526475

theorem tailTrace_6653422 : CollatzResearch.WordTrace tailWord_6653422 prefixEnd_6653422 3416403483198772689526475 := by
  unfold tailWord_6653422
  simp only [CollatzResearch.WordTrace]
  refine ⟨30333779562724485357016315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161780157667863921904087013 30333779562724485357016315)
  ·
    refine ⟨45500669344086728035524473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30333779562724485357016315 45500669344086728035524473)
    ·
      refine ⟨34125502008065046026643355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45500669344086728035524473 34125502008065046026643355)
      ·
        refine ⟨51188253012097569039965033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34125502008065046026643355 51188253012097569039965033)
        ·
          refine ⟨38391189759073176779973775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51188253012097569039965033 38391189759073176779973775)
          ·
            refine ⟨57586784638609765169960663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38391189759073176779973775 57586784638609765169960663)
            ·
              refine ⟨86380176957914647754940995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57586784638609765169960663 86380176957914647754940995)
              ·
                refine ⟨129570265436871971632411493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86380176957914647754940995 129570265436871971632411493)
                ·
                  refine ⟨24294424769413494681077155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 129570265436871971632411493 24294424769413494681077155)
                  ·
                    refine ⟨36441637154120242021615733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24294424769413494681077155 36441637154120242021615733)
                    ·
                      refine ⟨3416403483198772689526475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36441637154120242021615733 3416403483198772689526475)
                      ·
                        rfl

theorem cell23_6653422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_6653422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6653422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6653422 prefixEnd_6653422 := by exact prefixLift 6653422
  have htrace : WordTrace (prefixWord ++ tailWord_6653422) baseStart_6653422 baseEnd_6653422 := by
    simpa [prefixWord, tailWord_6653422, baseEnd_6653422] using wordTrace_append hprefix tailTrace_6653422
  have hstable : (prefixWord ++ tailWord_6653422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6653422).length < 2 ^ (prefixWord ++ tailWord_6653422).sum := by decide
  have hdescent : baseEnd_6653422 < baseStart_6653422 := by decide
  rcases family_descends (prefixWord ++ tailWord_6653422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6653459 : List Nat := [1, 1, 1, 2, 1, 7, 1, 4, 5]
def baseStart_6653459 : Nat := 118140960795 + 6653459 * 2 ^ 59
def prefixEnd_6653459 : Nat := 4983230072969 + 3 ^ 40 * 6653459 * 2
def baseEnd_6653459 : Nat := 379602497998109893862645

theorem tailTrace_6653459 : CollatzResearch.WordTrace tailWord_6653459 prefixEnd_6653459 379602497998109893862645 := by
  unfold tailWord_6653459
  simp only [CollatzResearch.WordTrace]
  refine ⟨242671586002661838175227431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161781057335107892116818287 242671586002661838175227431)
  ·
    refine ⟨364007379003992757262841147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242671586002661838175227431 364007379003992757262841147)
    ·
      refine ⟨546011068505989135894261721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364007379003992757262841147 546011068505989135894261721)
      ·
        refine ⟨409508301379491851920696291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 546011068505989135894261721 409508301379491851920696291)
        ·
          refine ⟨614262452069237777881044437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409508301379491851920696291 614262452069237777881044437)
          ·
            refine ⟨14396776220372760419086979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 614262452069237777881044437 14396776220372760419086979)
            ·
              refine ⟨21595164330559140628630469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14396776220372760419086979 21595164330559140628630469)
              ·
                refine ⟨4049093311979838867868213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21595164330559140628630469 4049093311979838867868213)
                ·
                  refine ⟨379602497998109893862645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4049093311979838867868213 379602497998109893862645)
                  ·
                    rfl

theorem cell23_6653459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 4, 5].length) (baseStart_6653459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6653459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6653459 prefixEnd_6653459 := by exact prefixLift 6653459
  have htrace : WordTrace (prefixWord ++ tailWord_6653459) baseStart_6653459 baseEnd_6653459 := by
    simpa [prefixWord, tailWord_6653459, baseEnd_6653459] using wordTrace_append hprefix tailTrace_6653459
  have hstable : (prefixWord ++ tailWord_6653459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6653459).length < 2 ^ (prefixWord ++ tailWord_6653459).sum := by decide
  have hdescent : baseEnd_6653459 < baseStart_6653459 := by decide
  rcases family_descends (prefixWord ++ tailWord_6653459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6653469 : List Nat := [1, 4, 2, 2, 1, 1, 3, 1, 2, 3, 3]
def baseStart_6653469 : Nat := 118140960795 + 6653469 * 2 ^ 59
def prefixEnd_6653469 : Nat := 4983230072969 + 3 ^ 40 * 6653469 * 2
def baseEnd_6653469 : Nat := 3416427616789534005638759

theorem tailTrace_6653469 : CollatzResearch.WordTrace tailWord_6653469 prefixEnd_6653469 3416427616789534005638759 := by
  unfold tailWord_6653469
  simp only [CollatzResearch.WordTrace]
  refine ⟨242671950732625609883091461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161781300488417073255394307 242671950732625609883091461)
  ·
    refine ⟨45500990762367301853079649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 242671950732625609883091461 45500990762367301853079649)
    ·
      refine ⟨34125743071775476389809737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45500990762367301853079649 34125743071775476389809737)
      ·
        refine ⟨25594307303831607292357303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34125743071775476389809737 25594307303831607292357303)
        ·
          refine ⟨38391460955747410938535955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25594307303831607292357303 38391460955747410938535955)
          ·
            refine ⟨57587191433621116407803933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38391460955747410938535955 57587191433621116407803933)
            ·
              refine ⟨21595196787607918652926475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57587191433621116407803933 21595196787607918652926475)
              ·
                refine ⟨32392795181411877979389713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21595196787607918652926475 32392795181411877979389713)
                ·
                  refine ⟨24294596386058908484542285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32392795181411877979389713 24294596386058908484542285)
                  ·
                    refine ⟨9110473644772090681703357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24294596386058908484542285 9110473644772090681703357)
                    ·
                      refine ⟨3416427616789534005638759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9110473644772090681703357 3416427616789534005638759)
                      ·
                        rfl

theorem cell23_6653469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_6653469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6653469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6653469 prefixEnd_6653469 := by exact prefixLift 6653469
  have htrace : WordTrace (prefixWord ++ tailWord_6653469) baseStart_6653469 baseEnd_6653469 := by
    simpa [prefixWord, tailWord_6653469, baseEnd_6653469] using wordTrace_append hprefix tailTrace_6653469
  have hstable : (prefixWord ++ tailWord_6653469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6653469).length < 2 ^ (prefixWord ++ tailWord_6653469).sum := by decide
  have hdescent : baseEnd_6653469 < baseStart_6653469 := by decide
  rcases family_descends (prefixWord ++ tailWord_6653469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6653509 : List Nat := [1, 3, 1, 1, 1, 4, 1, 1, 4, 4, 2]
def baseStart_6653509 : Nat := 118140960795 + 6653509 * 2 ^ 59
def prefixEnd_6653509 : Nat := 4983230072969 + 3 ^ 40 * 6653509 * 2
def baseEnd_6653509 : Nat := 3416448156015713849138575

theorem tailTrace_6653509 : CollatzResearch.WordTrace tailWord_6653509 prefixEnd_6653509 3416448156015713849138575 := by
  unfold tailWord_6653509
  simp only [CollatzResearch.WordTrace]
  refine ⟨242673409652480696714547581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161782273101653797809698387 242673409652480696714547581)
  ·
    refine ⟨91002528619680261267955343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242673409652480696714547581 91002528619680261267955343)
    ·
      refine ⟨136503792929520391901933015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91002528619680261267955343 136503792929520391901933015)
      ·
        refine ⟨204755689394280587852899523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136503792929520391901933015 204755689394280587852899523)
        ·
          refine ⟨307133534091420881779349285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204755689394280587852899523 307133534091420881779349285)
          ·
            refine ⟨57587537642141415333627991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 307133534091420881779349285 57587537642141415333627991)
            ·
              refine ⟨86381306463212123000441987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57587537642141415333627991 86381306463212123000441987)
              ·
                refine ⟨129571959694818184500662981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86381306463212123000441987 129571959694818184500662981)
                ·
                  refine ⟨24294742442778409593874309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 129571959694818184500662981 24294742442778409593874309)
                  ·
                    refine ⟨4555264208020951798851433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24294742442778409593874309 4555264208020951798851433)
                    ·
                      refine ⟨3416448156015713849138575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4555264208020951798851433 3416448156015713849138575)
                      ·
                        rfl

theorem cell23_6653509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 4, 2].length) (baseStart_6653509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6653509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6653509 prefixEnd_6653509 := by exact prefixLift 6653509
  have htrace : WordTrace (prefixWord ++ tailWord_6653509) baseStart_6653509 baseEnd_6653509 := by
    simpa [prefixWord, tailWord_6653509, baseEnd_6653509] using wordTrace_append hprefix tailTrace_6653509
  have hstable : (prefixWord ++ tailWord_6653509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6653509).length < 2 ^ (prefixWord ++ tailWord_6653509).sum := by decide
  have hdescent : baseEnd_6653509 < baseStart_6653509 := by decide
  rcases family_descends (prefixWord ++ tailWord_6653509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6653596 : List Nat := [2, 2, 3, 2, 3, 1, 1, 1, 3, 5]
def baseStart_6653596 : Nat := 118140960795 + 6653596 * 2 ^ 59
def prefixEnd_6653596 : Nat := 4983230072969 + 3 ^ 40 * 6653596 * 2
def baseEnd_6653596 : Nat := 1138830942944218336250225

theorem tailTrace_6653596 : CollatzResearch.WordTrace tailWord_6653596 prefixEnd_6653596 1138830942944218336250225 := by
  unfold tailWord_6653596
  simp only [CollatzResearch.WordTrace]
  refine ⟨121338291401582755286482321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161784388535443673715309761 121338291401582755286482321)
  ·
    refine ⟨91003718551187066464861741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121338291401582755286482321 91003718551187066464861741)
    ·
      refine ⟨34126394456695149924323153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91003718551187066464861741 34126394456695149924323153)
      ·
        refine ⟨25594795842521362443242365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34126394456695149924323153 25594795842521362443242365)
        ·
          refine ⟨9598048440945510916215887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25594795842521362443242365 9598048440945510916215887)
          ·
            refine ⟨14397072661418266374323831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9598048440945510916215887 14397072661418266374323831)
            ·
              refine ⟨21595608992127399561485747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14397072661418266374323831 21595608992127399561485747)
              ·
                refine ⟨32393413488191099342228621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21595608992127399561485747 32393413488191099342228621)
                ·
                  refine ⟨12147530058071662253335733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32393413488191099342228621 12147530058071662253335733)
                  ·
                    refine ⟨1138830942944218336250225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12147530058071662253335733 1138830942944218336250225)
                    ·
                      rfl

theorem cell23_6653596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_6653596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6653596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6653596 prefixEnd_6653596 := by exact prefixLift 6653596
  have htrace : WordTrace (prefixWord ++ tailWord_6653596) baseStart_6653596 baseEnd_6653596 := by
    simpa [prefixWord, tailWord_6653596, baseEnd_6653596] using wordTrace_append hprefix tailTrace_6653596
  have hstable : (prefixWord ++ tailWord_6653596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6653596).length < 2 ^ (prefixWord ++ tailWord_6653596).sum := by decide
  have hdescent : baseEnd_6653596 < baseStart_6653596 := by decide
  rcases family_descends (prefixWord ++ tailWord_6653596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6653612 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 6]
def baseStart_6653612 : Nat := 118140960795 + 6653612 * 2 ^ 59
def prefixEnd_6653612 : Nat := 4983230072969 + 3 ^ 40 * 6653612 * 2
def baseEnd_6653612 : Nat := 3416501044523126946150601

theorem tailTrace_6653612 : CollatzResearch.WordTrace tailWord_6653612 prefixEnd_6653612 3416501044523126946150601 := by
  unfold tailWord_6653612
  simp only [CollatzResearch.WordTrace]
  refine ⟨121338583185553772652773545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161784777580738363537031393 121338583185553772652773545)
  ·
    refine ⟨91003937389165329489580159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121338583185553772652773545 91003937389165329489580159)
    ·
      refine ⟨136505906083747994234370239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91003937389165329489580159 136505906083747994234370239)
      ·
        refine ⟨204758859125621991351555359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136505906083747994234370239 204758859125621991351555359)
        ·
          refine ⟨307138288688432987027333039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204758859125621991351555359 307138288688432987027333039)
          ·
            refine ⟨460707433032649480540999559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307138288688432987027333039 460707433032649480540999559)
            ·
              refine ⟨691061149548974220811499339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 460707433032649480540999559 691061149548974220811499339)
              ·
                refine ⟨1036591724323461331217249009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 691061149548974220811499339 1036591724323461331217249009)
                ·
                  refine ⟨777443793242595998412936757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1036591724323461331217249009 777443793242595998412936757)
                  ·
                    refine ⟨72885355616493374851212821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 777443793242595998412936757 72885355616493374851212821)
                    ·
                      refine ⟨3416501044523126946150601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72885355616493374851212821 3416501044523126946150601)
                      ·
                        rfl

theorem cell23_6653612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 6].length) (baseStart_6653612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6653612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6653612 prefixEnd_6653612 := by exact prefixLift 6653612
  have htrace : WordTrace (prefixWord ++ tailWord_6653612) baseStart_6653612 baseEnd_6653612 := by
    simpa [prefixWord, tailWord_6653612, baseEnd_6653612] using wordTrace_append hprefix tailTrace_6653612
  have hstable : (prefixWord ++ tailWord_6653612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6653612).length < 2 ^ (prefixWord ++ tailWord_6653612).sum := by decide
  have hdescent : baseEnd_6653612 < baseStart_6653612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6653612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6653613 : List Nat := [1, 5, 2, 1, 1, 1, 5, 1, 1, 5]
def baseStart_6653613 : Nat := 118140960795 + 6653613 * 2 ^ 59
def prefixEnd_6653613 : Nat := 4983230072969 + 3 ^ 40 * 6653613 * 2
def baseEnd_6653613 : Nat := 1138833852667927147412699

theorem tailTrace_6653613 : CollatzResearch.WordTrace tailWord_6653613 prefixEnd_6653613 1138833852667927147412699 := by
  unfold tailWord_6653613
  simp only [CollatzResearch.WordTrace]
  refine ⟨242677202844103922476333493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161784801896069281650888995 242677202844103922476333493)
  ·
    refine ⟨22750987766634742732156265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 242677202844103922476333493 22750987766634742732156265)
    ·
      refine ⟨17063240824976057049117199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22750987766634742732156265 17063240824976057049117199)
      ·
        refine ⟨25594861237464085573675799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17063240824976057049117199 25594861237464085573675799)
        ·
          refine ⟨38392291856196128360513699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25594861237464085573675799 38392291856196128360513699)
          ·
            refine ⟨57588437784294192540770549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38392291856196128360513699 57588437784294192540770549)
            ·
              refine ⟨5398916042277580550697239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57588437784294192540770549 5398916042277580550697239)
              ·
                refine ⟨8098374063416370826045859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5398916042277580550697239 8098374063416370826045859)
                ·
                  refine ⟨12147561095124556239068789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8098374063416370826045859 12147561095124556239068789)
                  ·
                    refine ⟨1138833852667927147412699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12147561095124556239068789 1138833852667927147412699)
                    ·
                      rfl

theorem cell23_6653613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_6653613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6653613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6653613 prefixEnd_6653613 := by exact prefixLift 6653613
  have htrace : WordTrace (prefixWord ++ tailWord_6653613) baseStart_6653613 baseEnd_6653613 := by
    simpa [prefixWord, tailWord_6653613, baseEnd_6653613] using wordTrace_append hprefix tailTrace_6653613
  have hstable : (prefixWord ++ tailWord_6653613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6653613).length < 2 ^ (prefixWord ++ tailWord_6653613).sum := by decide
  have hdescent : baseEnd_6653613 < baseStart_6653613 := by decide
  rcases family_descends (prefixWord ++ tailWord_6653613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6653626 : List Nat := [3, 1, 1, 1, 2, 4, 1, 4, 2, 4]
def baseStart_6653626 : Nat := 118140960795 + 6653626 * 2 ^ 59
def prefixEnd_6653626 : Nat := 4983230072969 + 3 ^ 40 * 6653626 * 2
def baseEnd_6653626 : Nat := 1138836077750763297125179

theorem tailTrace_6653626 : CollatzResearch.WordTrace tailWord_6653626 prefixEnd_6653626 1138836077750763297125179 := by
  unfold tailWord_6653626
  simp only [CollatzResearch.WordTrace]
  refine ⟨60669419248264206424139183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161785117995371217131037821 60669419248264206424139183)
  ·
    refine ⟨91004128872396309636208775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60669419248264206424139183 91004128872396309636208775)
    ·
      refine ⟨136506193308594464454313163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91004128872396309636208775 136506193308594464454313163)
      ·
        refine ⟨204759289962891696681469745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136506193308594464454313163 204759289962891696681469745)
        ·
          refine ⟨153569467472168772511102309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204759289962891696681469745 153569467472168772511102309)
          ·
            refine ⟨28794275151031644845831683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153569467472168772511102309 28794275151031644845831683)
            ·
              refine ⟨43191412726547467268747525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28794275151031644845831683 43191412726547467268747525)
              ·
                refine ⟨8098389886227650112890161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43191412726547467268747525 8098389886227650112890161)
                ·
                  refine ⟨6073792414670737584667621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8098389886227650112890161 6073792414670737584667621)
                  ·
                    refine ⟨1138836077750763297125179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6073792414670737584667621 1138836077750763297125179)
                    ·
                      rfl

theorem cell23_6653626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 4, 2, 4].length) (baseStart_6653626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6653626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6653626 prefixEnd_6653626 := by exact prefixLift 6653626
  have htrace : WordTrace (prefixWord ++ tailWord_6653626) baseStart_6653626 baseEnd_6653626 := by
    simpa [prefixWord, tailWord_6653626, baseEnd_6653626] using wordTrace_append hprefix tailTrace_6653626
  have hstable : (prefixWord ++ tailWord_6653626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6653626).length < 2 ^ (prefixWord ++ tailWord_6653626).sum := by decide
  have hdescent : baseEnd_6653626 < baseStart_6653626 := by decide
  rcases family_descends (prefixWord ++ tailWord_6653626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6653629 : List Nat := [1, 4, 1, 2, 1, 2, 1, 2, 3, 2, 4]
def baseStart_6653629 : Nat := 118140960795 + 6653629 * 2 ^ 59
def prefixEnd_6653629 : Nat := 4983230072969 + 3 ^ 40 * 6653629 * 2
def baseEnd_6653629 : Nat := 3416509773694253379638023

theorem tailTrace_6653629 : CollatzResearch.WordTrace tailWord_6653629 prefixEnd_6653629 3416509773694253379638023 := by
  unfold tailWord_6653629
  simp only [CollatzResearch.WordTrace]
  refine ⟨242677786412045957208915941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161785190941363971472610627 242677786412045957208915941)
  ·
    refine ⟨45502084952258616976671739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 242677786412045957208915941 45502084952258616976671739)
    ·
      refine ⟨68253127428387925465007609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45502084952258616976671739 68253127428387925465007609)
      ·
        refine ⟨51189845571290944098755707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68253127428387925465007609 51189845571290944098755707)
        ·
          refine ⟨76784768356936416148133561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51189845571290944098755707 76784768356936416148133561)
          ·
            refine ⟨57588576267702312111100171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76784768356936416148133561 57588576267702312111100171)
            ·
              refine ⟨86382864401553468166650257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57588576267702312111100171 86382864401553468166650257)
              ·
                refine ⟨64787148301165101124987693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86382864401553468166650257 64787148301165101124987693)
                ·
                  refine ⟨24295180612936912921870385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64787148301165101124987693 24295180612936912921870385)
                  ·
                    refine ⟨18221385459702684691402789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24295180612936912921870385 18221385459702684691402789)
                    ·
                      refine ⟨3416509773694253379638023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18221385459702684691402789 3416509773694253379638023)
                      ·
                        rfl

theorem cell23_6653629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_6653629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6653629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6653629 prefixEnd_6653629 := by exact prefixLift 6653629
  have htrace : WordTrace (prefixWord ++ tailWord_6653629) baseStart_6653629 baseEnd_6653629 := by
    simpa [prefixWord, tailWord_6653629, baseEnd_6653629] using wordTrace_append hprefix tailTrace_6653629
  have hstable : (prefixWord ++ tailWord_6653629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6653629).length < 2 ^ (prefixWord ++ tailWord_6653629).sum := by decide
  have hdescent : baseEnd_6653629 < baseStart_6653629 := by decide
  rcases family_descends (prefixWord ++ tailWord_6653629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6653636 : List Nat := [2, 3, 3, 1, 1, 1, 1, 1, 5, 2, 3]
def baseStart_6653636 : Nat := 118140960795 + 6653636 * 2 ^ 59
def prefixEnd_6653636 : Nat := 4983230072969 + 3 ^ 40 * 6653636 * 2
def baseEnd_6653636 : Nat := 3416513368058834852250491

theorem tailTrace_6653636 : CollatzResearch.WordTrace tailWord_6653636 prefixEnd_6653636 3416513368058834852250491 := by
  unfold tailWord_6653636
  simp only [CollatzResearch.WordTrace]
  refine ⟨121339020861510298702210381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161785361148680398269613841 121339020861510298702210381)
  ·
    refine ⟨45502132823066362013328893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121339020861510298702210381 45502132823066362013328893)
    ·
      refine ⟨17063299808649885754998335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45502132823066362013328893 17063299808649885754998335)
      ·
        refine ⟨25594949712974828632497503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17063299808649885754998335 25594949712974828632497503)
        ·
          refine ⟨38392424569462242948746255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25594949712974828632497503 38392424569462242948746255)
          ·
            refine ⟨57588636854193364423119383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38392424569462242948746255 57588636854193364423119383)
            ·
              refine ⟨86382955281290046634679075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57588636854193364423119383 86382955281290046634679075)
              ·
                refine ⟨129574432921935069952018613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86382955281290046634679075 129574432921935069952018613)
                ·
                  refine ⟨12147603086431412808001745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 129574432921935069952018613 12147603086431412808001745)
                  ·
                    refine ⟨9110702314823559606001309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12147603086431412808001745 9110702314823559606001309)
                    ·
                      refine ⟨3416513368058834852250491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9110702314823559606001309 3416513368058834852250491)
                      ·
                        rfl

theorem cell23_6653636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_6653636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6653636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6653636 prefixEnd_6653636 := by exact prefixLift 6653636
  have htrace : WordTrace (prefixWord ++ tailWord_6653636) baseStart_6653636 baseEnd_6653636 := by
    simpa [prefixWord, tailWord_6653636, baseEnd_6653636] using wordTrace_append hprefix tailTrace_6653636
  have hstable : (prefixWord ++ tailWord_6653636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6653636).length < 2 ^ (prefixWord ++ tailWord_6653636).sum := by decide
  have hdescent : baseEnd_6653636 < baseStart_6653636 := by decide
  rcases family_descends (prefixWord ++ tailWord_6653636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6653646 : List Nat := [4, 1, 1, 1, 3, 1, 4, 1, 1, 2, 4]
def baseStart_6653646 : Nat := 118140960795 + 6653646 * 2 ^ 59
def prefixEnd_6653646 : Nat := 4983230072969 + 3 ^ 40 * 6653646 * 2
def baseEnd_6653646 : Nat := 3416518502865379813125445

theorem tailTrace_6653646 : CollatzResearch.WordTrace tailWord_6653646 prefixEnd_6653646 3416518502865379813125445 := by
  unfold tailWord_6653646
  simp only [CollatzResearch.WordTrace]
  refine ⟨30334800806623046139035599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161785604301989579408189861 30334800806623046139035599)
  ·
    refine ⟨45502201209934569208553399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30334800806623046139035599 45502201209934569208553399)
    ·
      refine ⟨68253301814901853812830099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45502201209934569208553399 68253301814901853812830099)
      ·
        refine ⟨102379952722352780719245149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68253301814901853812830099 102379952722352780719245149)
        ·
          refine ⟨38392482270882292769716931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102379952722352780719245149 38392482270882292769716931)
          ·
            refine ⟨57588723406323439154575397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38392482270882292769716931 57588723406323439154575397)
            ·
              refine ⟨10797885638685644841482887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57588723406323439154575397 10797885638685644841482887)
              ·
                refine ⟨16196828458028467262224331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10797885638685644841482887 16196828458028467262224331)
                ·
                  refine ⟨24295242687042700893336497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16196828458028467262224331 24295242687042700893336497)
                  ·
                    refine ⟨18221432015282025670002373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24295242687042700893336497 18221432015282025670002373)
                    ·
                      refine ⟨3416518502865379813125445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18221432015282025670002373 3416518502865379813125445)
                      ·
                        rfl

theorem cell23_6653646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 1, 2, 4].length) (baseStart_6653646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6653646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6653646 prefixEnd_6653646 := by exact prefixLift 6653646
  have htrace : WordTrace (prefixWord ++ tailWord_6653646) baseStart_6653646 baseEnd_6653646 := by
    simpa [prefixWord, tailWord_6653646, baseEnd_6653646] using wordTrace_append hprefix tailTrace_6653646
  have hstable : (prefixWord ++ tailWord_6653646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6653646).length < 2 ^ (prefixWord ++ tailWord_6653646).sum := by decide
  have hdescent : baseEnd_6653646 < baseStart_6653646 := by decide
  rcases family_descends (prefixWord ++ tailWord_6653646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6653650 : List Nat := [3, 2, 2, 2, 2, 2, 1, 2, 3, 2, 2]
def baseStart_6653650 : Nat := 118140960795 + 6653650 * 2 ^ 59
def prefixEnd_6653650 : Nat := 4983230072969 + 3 ^ 40 * 6653650 * 2
def baseEnd_6653650 : Nat := 3416520556787997797475427

theorem tailTrace_6653650 : CollatzResearch.WordTrace tailWord_6653650 prefixEnd_6653650 3416520556787997797475427 := by
  unfold tailWord_6653650
  simp only [CollatzResearch.WordTrace]
  refine ⟨60669638086242469448857601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161785701563313251863620269 60669638086242469448857601)
  ·
    refine ⟨45502228564681852086643201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60669638086242469448857601 45502228564681852086643201)
    ·
      refine ⟨34126671423511389064982401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45502228564681852086643201 34126671423511389064982401)
      ·
        refine ⟨25595003567633541798736801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34126671423511389064982401 25595003567633541798736801)
        ·
          refine ⟨19196252675725156349052601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25595003567633541798736801 19196252675725156349052601)
          ·
            refine ⟨14397189506793867261789451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19196252675725156349052601 14397189506793867261789451)
            ·
              refine ⟨21595784260190800892684177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14397189506793867261789451 21595784260190800892684177)
              ·
                refine ⟨16196838195143100669513133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21595784260190800892684177 16196838195143100669513133)
                ·
                  refine ⟨6073814323178662751067425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16196838195143100669513133 6073814323178662751067425)
                  ·
                    refine ⟨4555360742383997063300569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6073814323178662751067425 4555360742383997063300569)
                    ·
                      refine ⟨3416520556787997797475427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4555360742383997063300569 3416520556787997797475427)
                      ·
                        rfl

theorem cell23_6653650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_6653650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6653650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6653650 prefixEnd_6653650 := by exact prefixLift 6653650
  have htrace : WordTrace (prefixWord ++ tailWord_6653650) baseStart_6653650 baseEnd_6653650 := by
    simpa [prefixWord, tailWord_6653650, baseEnd_6653650] using wordTrace_append hprefix tailTrace_6653650
  have hstable : (prefixWord ++ tailWord_6653650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6653650).length < 2 ^ (prefixWord ++ tailWord_6653650).sum := by decide
  have hdescent : baseEnd_6653650 < baseStart_6653650 := by decide
  rcases family_descends (prefixWord ++ tailWord_6653650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6653654 : List Nat := [5, 2, 1, 3, 1, 2, 1, 1, 2, 3, 2]
def baseStart_6653654 : Nat := 118140960795 + 6653654 * 2 ^ 59
def prefixEnd_6653654 : Nat := 4983230072969 + 3 ^ 40 * 6653654 * 2
def baseEnd_6653654 : Nat := 3416522610710615781825409

theorem tailTrace_6653654 : CollatzResearch.WordTrace tailWord_6653654 prefixEnd_6653654 3416522610710615781825409 := by
  unfold tailWord_6653654
  simp only [CollatzResearch.WordTrace]
  refine ⟨15167418639809711654911001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161785798824636924319050677 15167418639809711654911001)
  ·
    refine ⟨11375563979857283741183251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15167418639809711654911001 11375563979857283741183251)
    ·
      refine ⟨17063345969785925611774877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11375563979857283741183251 17063345969785925611774877)
      ·
        refine ⟨6398754738669722104415579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17063345969785925611774877 6398754738669722104415579)
        ·
          refine ⟨9598132108004583156623369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6398754738669722104415579 9598132108004583156623369)
          ·
            refine ⟨7198599081003437367467527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9598132108004583156623369 7198599081003437367467527)
            ·
              refine ⟨10797898621505156051201291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7198599081003437367467527 10797898621505156051201291)
              ·
                refine ⟨16196847932257734076801937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10797898621505156051201291 16196847932257734076801937)
                ·
                  refine ⟨12147635949193300557601453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16196847932257734076801937 12147635949193300557601453)
                  ·
                    refine ⟨4555363480947487709100545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12147635949193300557601453 4555363480947487709100545)
                    ·
                      refine ⟨3416522610710615781825409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4555363480947487709100545 3416522610710615781825409)
                      ·
                        rfl

theorem cell23_6653654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_6653654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6653654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6653654 prefixEnd_6653654 := by exact prefixLift 6653654
  have htrace : WordTrace (prefixWord ++ tailWord_6653654) baseStart_6653654 baseEnd_6653654 := by
    simpa [prefixWord, tailWord_6653654, baseEnd_6653654] using wordTrace_append hprefix tailTrace_6653654
  have hstable : (prefixWord ++ tailWord_6653654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6653654).length < 2 ^ (prefixWord ++ tailWord_6653654).sum := by decide
  have hdescent : baseEnd_6653654 < baseStart_6653654 := by decide
  rcases family_descends (prefixWord ++ tailWord_6653654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6653667 : List Nat := [1, 1, 1, 7, 3, 1, 2, 1, 1, 1, 4]
def baseStart_6653667 : Nat := 118140960795 + 6653667 * 2 ^ 59
def prefixEnd_6653667 : Nat := 4983230072969 + 3 ^ 40 * 6653667 * 2
def baseEnd_6653667 : Nat := 3416529285959124230962849

theorem tailTrace_6653667 : CollatzResearch.WordTrace tailWord_6653667 prefixEnd_6653667 3416529285959124230962849 := by
  unfold tailWord_6653667
  simp only [CollatzResearch.WordTrace]
  refine ⟨242679172385908289698799255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161786114923938859799199503 242679172385908289698799255)
  ·
    refine ⟨364018758578862434548198883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242679172385908289698799255 364018758578862434548198883)
    ·
      refine ⟨546028137868293651822298325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364018758578862434548198883 546028137868293651822298325)
      ·
        refine ⟨12797534481288132464585117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 546028137868293651822298325 12797534481288132464585117)
        ·
          refine ⟨4799075430483049674219419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12797534481288132464585117 4799075430483049674219419)
          ·
            refine ⟨7198613145724574511329129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4799075430483049674219419 7198613145724574511329129)
            ·
              refine ⟨5398959859293430883496847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7198613145724574511329129 5398959859293430883496847)
              ·
                refine ⟨8098439788940146325245271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5398959859293430883496847 8098439788940146325245271)
                ·
                  refine ⟨12147659683410219487867907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8098439788940146325245271 12147659683410219487867907)
                  ·
                    refine ⟨18221489525115329231801861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12147659683410219487867907 18221489525115329231801861)
                    ·
                      refine ⟨3416529285959124230962849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18221489525115329231801861 3416529285959124230962849)
                      ·
                        rfl

theorem cell23_6653667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_6653667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6653667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6653667 prefixEnd_6653667 := by exact prefixLift 6653667
  have htrace : WordTrace (prefixWord ++ tailWord_6653667) baseStart_6653667 baseEnd_6653667 := by
    simpa [prefixWord, tailWord_6653667, baseEnd_6653667] using wordTrace_append hprefix tailTrace_6653667
  have hstable : (prefixWord ++ tailWord_6653667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6653667).length < 2 ^ (prefixWord ++ tailWord_6653667).sum := by decide
  have hdescent : baseEnd_6653667 < baseStart_6653667 := by decide
  rcases family_descends (prefixWord ++ tailWord_6653667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6653683 : List Nat := [1, 1, 1, 2, 2, 3, 5, 2, 2, 1, 3]
def baseStart_6653683 : Nat := 118140960795 + 6653683 * 2 ^ 59
def prefixEnd_6653683 : Nat := 4983230072969 + 3 ^ 40 * 6653683 * 2
def baseEnd_6653683 : Nat := 3416537501649596168362775

theorem tailTrace_6653683 : CollatzResearch.WordTrace tailWord_6653683 prefixEnd_6653683 3416537501649596168362775 := by
  unfold tailWord_6653683
  simp only [CollatzResearch.WordTrace]
  refine ⟨242679755953850324431381703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161786503969233549620921135 242679755953850324431381703)
  ·
    refine ⟨364019633930775486647072555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242679755953850324431381703 364019633930775486647072555)
    ·
      refine ⟨546029450896163229970608833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364019633930775486647072555 546029450896163229970608833)
      ·
        refine ⟨409522088172122422477956625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 546029450896163229970608833 409522088172122422477956625)
        ·
          refine ⟨307141566129091816858467469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 409522088172122422477956625 307141566129091816858467469)
          ·
            refine ⟨115178087298409431321925301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 307141566129091816858467469 115178087298409431321925301)
            ·
              refine ⟨10797945684225884186430497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 115178087298409431321925301 10797945684225884186430497)
              ·
                refine ⟨8098459263169413139822873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10797945684225884186430497 8098459263169413139822873)
                ·
                  refine ⟨6073844447377059854867155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8098459263169413139822873 6073844447377059854867155)
                  ·
                    refine ⟨9110766671065589782300733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6073844447377059854867155 9110766671065589782300733)
                    ·
                      refine ⟨3416537501649596168362775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9110766671065589782300733 3416537501649596168362775)
                      ·
                        rfl

theorem cell23_6653683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 2, 2, 1, 3].length) (baseStart_6653683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6653683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6653683 prefixEnd_6653683 := by exact prefixLift 6653683
  have htrace : WordTrace (prefixWord ++ tailWord_6653683) baseStart_6653683 baseEnd_6653683 := by
    simpa [prefixWord, tailWord_6653683, baseEnd_6653683] using wordTrace_append hprefix tailTrace_6653683
  have hstable : (prefixWord ++ tailWord_6653683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6653683).length < 2 ^ (prefixWord ++ tailWord_6653683).sum := by decide
  have hdescent : baseEnd_6653683 < baseStart_6653683 := by decide
  rcases family_descends (prefixWord ++ tailWord_6653683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6653684 : List Nat := [2, 6, 1, 1, 1, 2, 2, 1, 3, 2, 2]
def baseStart_6653684 : Nat := 118140960795 + 6653684 * 2 ^ 59
def prefixEnd_6653684 : Nat := 4983230072969 + 3 ^ 40 * 6653684 * 2
def baseEnd_6653684 : Nat := 3416538015130250664450271

theorem tailTrace_6653684 : CollatzResearch.WordTrace tailWord_6653684 prefixEnd_6653684 3416538015130250664450271 := by
  unfold tailWord_6653684
  simp only [CollatzResearch.WordTrace]
  refine ⟨121339896213423350801084053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161786528284564467734778737 121339896213423350801084053)
  ·
    refine ⟨5687807635004219568800815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 121339896213423350801084053 5687807635004219568800815)
    ·
      refine ⟨8531711452506329353201223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5687807635004219568800815 8531711452506329353201223)
      ·
        refine ⟨12797567178759494029801835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8531711452506329353201223 12797567178759494029801835)
        ·
          refine ⟨19196350768139241044702753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12797567178759494029801835 19196350768139241044702753)
          ·
            refine ⟨14397263076104430783527065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19196350768139241044702753 14397263076104430783527065)
            ·
              refine ⟨10797947307078323087645299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14397263076104430783527065 10797947307078323087645299)
              ·
                refine ⟨16196920960617484631467949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10797947307078323087645299 16196920960617484631467949)
                ·
                  refine ⟨6073845360231556736800481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16196920960617484631467949 6073845360231556736800481)
                  ·
                    refine ⟨4555384020173667552600361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6073845360231556736800481 4555384020173667552600361)
                    ·
                      refine ⟨3416538015130250664450271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4555384020173667552600361 3416538015130250664450271)
                      ·
                        rfl

theorem cell23_6653684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_6653684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6653684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6653684 prefixEnd_6653684 := by exact prefixLift 6653684
  have htrace : WordTrace (prefixWord ++ tailWord_6653684) baseStart_6653684 baseEnd_6653684 := by
    simpa [prefixWord, tailWord_6653684, baseEnd_6653684] using wordTrace_append hprefix tailTrace_6653684
  have hstable : (prefixWord ++ tailWord_6653684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6653684).length < 2 ^ (prefixWord ++ tailWord_6653684).sum := by decide
  have hdescent : baseEnd_6653684 < baseStart_6653684 := by decide
  rcases family_descends (prefixWord ++ tailWord_6653684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6653699 : List Nat := [1, 1, 1, 3, 2, 2, 4, 1, 2, 6]
def baseStart_6653699 : Nat := 118140960795 + 6653699 * 2 ^ 59
def prefixEnd_6653699 : Nat := 4983230072969 + 3 ^ 40 * 6653699 * 2
def baseEnd_6653699 : Nat := 1138848572446689368587567

theorem tailTrace_6653699 : CollatzResearch.WordTrace tailWord_6653699 prefixEnd_6653699 1138848572446689368587567 := by
  unfold tailWord_6653699
  simp only [CollatzResearch.WordTrace]
  refine ⟨242680339521792359163964151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161786893014528239442642767 242680339521792359163964151)
  ·
    refine ⟨364020509282688538745946227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242680339521792359163964151 364020509282688538745946227)
    ·
      refine ⟨546030763924032808118919341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364020509282688538745946227 546030763924032808118919341)
      ·
        refine ⟨204761536471512303044594753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 546030763924032808118919341 204761536471512303044594753)
        ·
          refine ⟨153571152353634227283446065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204761536471512303044594753 153571152353634227283446065)
          ·
            refine ⟨115178364265225670462584549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153571152353634227283446065 115178364265225670462584549)
            ·
              refine ⟨21595943299729813211734603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115178364265225670462584549 21595943299729813211734603)
              ·
                refine ⟨32393914949594719817601905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21595943299729813211734603 32393914949594719817601905)
                ·
                  refine ⟨24295436212196039863201429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32393914949594719817601905 24295436212196039863201429)
                  ·
                    refine ⟨1138848572446689368587567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24295436212196039863201429 1138848572446689368587567)
                    ·
                      rfl

theorem cell23_6653699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 6].length) (baseStart_6653699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6653699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6653699 prefixEnd_6653699 := by exact prefixLift 6653699
  have htrace : WordTrace (prefixWord ++ tailWord_6653699) baseStart_6653699 baseEnd_6653699 := by
    simpa [prefixWord, tailWord_6653699, baseEnd_6653699] using wordTrace_append hprefix tailTrace_6653699
  have hstable : (prefixWord ++ tailWord_6653699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6653699).length < 2 ^ (prefixWord ++ tailWord_6653699).sum := by decide
  have hdescent : baseEnd_6653699 < baseStart_6653699 := by decide
  rcases family_descends (prefixWord ++ tailWord_6653699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6653746 : List Nat := [3, 2, 1, 1, 3, 2, 3, 1, 7]
def baseStart_6653746 : Nat := 118140960795 + 6653746 * 2 ^ 59
def prefixEnd_6653746 : Nat := 4983230072969 + 3 ^ 40 * 6653746 * 2
def baseEnd_6653746 : Nat := 379618872325647713541665

theorem tailTrace_6653746 : CollatzResearch.WordTrace tailWord_6653746 prefixEnd_6653746 379618872325647713541665 := by
  unfold tailWord_6653746
  simp only [CollatzResearch.WordTrace]
  refine ⟨60670513438155521547731273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161788035835081390793950061 60670513438155521547731273)
  ·
    refine ⟨45502885078616641160798455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60670513438155521547731273 45502885078616641160798455)
    ·
      refine ⟨68254327617924961741197683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45502885078616641160798455 68254327617924961741197683)
      ·
        refine ⟨102381491426887442611796525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68254327617924961741197683 102381491426887442611796525)
        ·
          refine ⟨38393059285082790979423697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102381491426887442611796525 38393059285082790979423697)
          ·
            refine ⟨28794794463812093234567773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38393059285082790979423697 28794794463812093234567773)
            ·
              refine ⟨10798047923929534962962915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28794794463812093234567773 10798047923929534962962915)
              ·
                refine ⟨16197071885894302444444373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10798047923929534962962915 16197071885894302444444373)
                ·
                  refine ⟨379618872325647713541665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16197071885894302444444373 379618872325647713541665)
                  ·
                    rfl

theorem cell23_6653746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 7].length) (baseStart_6653746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6653746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6653746 prefixEnd_6653746 := by exact prefixLift 6653746
  have htrace : WordTrace (prefixWord ++ tailWord_6653746) baseStart_6653746 baseEnd_6653746 := by
    simpa [prefixWord, tailWord_6653746, baseEnd_6653746] using wordTrace_append hprefix tailTrace_6653746
  have hstable : (prefixWord ++ tailWord_6653746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6653746).length < 2 ^ (prefixWord ++ tailWord_6653746).sum := by decide
  have hdescent : baseEnd_6653746 < baseStart_6653746 := by decide
  rcases family_descends (prefixWord ++ tailWord_6653746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6653756 : List Nat := [2, 2, 2, 2, 1, 1, 2, 3, 2, 3, 3]
def baseStart_6653756 : Nat := 118140960795 + 6653756 * 2 ^ 59
def prefixEnd_6653756 : Nat := 4983230072969 + 3 ^ 40 * 6653756 * 2
def baseEnd_6653756 : Nat := 3416574985737374382749939

theorem tailTrace_6653756 : CollatzResearch.WordTrace tailWord_6653756 prefixEnd_6653756 3416574985737374382749939 := by
  unfold tailWord_6653756
  simp only [CollatzResearch.WordTrace]
  refine ⟨121341209241292928949394561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161788278988390571932526081 121341209241292928949394561)
  ·
    refine ⟨91005906930969696712045921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121341209241292928949394561 91005906930969696712045921)
    ·
      refine ⟨68254430198227272534034441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91005906930969696712045921 68254430198227272534034441)
      ·
        refine ⟨51190822648670454400525831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68254430198227272534034441 51190822648670454400525831)
        ·
          refine ⟨76786233973005681600788747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51190822648670454400525831 76786233973005681600788747)
          ·
            refine ⟨115179350959508522401183121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76786233973005681600788747 115179350959508522401183121)
            ·
              refine ⟨86384513219631391800887341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115179350959508522401183121 86384513219631391800887341)
              ·
                refine ⟨32394192457361771925332753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86384513219631391800887341 32394192457361771925332753)
                ·
                  refine ⟨24295644343021328943999565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32394192457361771925332753 24295644343021328943999565)
                  ·
                    refine ⟨9110866628632998353999837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24295644343021328943999565 9110866628632998353999837)
                    ·
                      refine ⟨3416574985737374382749939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9110866628632998353999837 3416574985737374382749939)
                      ·
                        rfl

theorem cell23_6653756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_6653756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6653756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6653756 prefixEnd_6653756 := by exact prefixLift 6653756
  have htrace : WordTrace (prefixWord ++ tailWord_6653756) baseStart_6653756 baseEnd_6653756 := by
    simpa [prefixWord, tailWord_6653756, baseEnd_6653756] using wordTrace_append hprefix tailTrace_6653756
  have hstable : (prefixWord ++ tailWord_6653756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6653756).length < 2 ^ (prefixWord ++ tailWord_6653756).sum := by decide
  have hdescent : baseEnd_6653756 < baseStart_6653756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6653756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6653757 : List Nat := [1, 4, 1, 4, 1, 2, 1, 3, 2, 2, 2]
def baseStart_6653757 : Nat := 118140960795 + 6653757 * 2 ^ 59
def prefixEnd_6653757 : Nat := 4983230072969 + 3 ^ 40 * 6653757 * 2
def baseEnd_6653757 : Nat := 3416575499218028878837435

theorem tailTrace_6653757 : CollatzResearch.WordTrace tailWord_6653757 prefixEnd_6653757 3416575499218028878837435 := by
  unfold tailWord_6653757
  simp only [CollatzResearch.WordTrace]
  refine ⟨242682454955582235069575525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161788303303721490046383683 242682454955582235069575525)
  ·
    refine ⟨45502960304171669075545411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 242682454955582235069575525 45502960304171669075545411)
    ·
      refine ⟨68254440456257503613318117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45502960304171669075545411 68254440456257503613318117)
      ·
        refine ⟨12797707585548281927497147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68254440456257503613318117 12797707585548281927497147)
        ·
          refine ⟨19196561378322422891245721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12797707585548281927497147 19196561378322422891245721)
          ·
            refine ⟨14397421033741817168434291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19196561378322422891245721 14397421033741817168434291)
            ·
              refine ⟨21596131550612725752651437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14397421033741817168434291 21596131550612725752651437)
              ·
                refine ⟨8098549331479772157244289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21596131550612725752651437 8098549331479772157244289)
                ·
                  refine ⟨6073911998609829117933217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8098549331479772157244289 6073911998609829117933217)
                  ·
                    refine ⟨4555433998957371838449913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6073911998609829117933217 4555433998957371838449913)
                    ·
                      refine ⟨3416575499218028878837435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4555433998957371838449913 3416575499218028878837435)
                      ·
                        rfl

theorem cell23_6653757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_6653757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6653757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6653757 prefixEnd_6653757 := by exact prefixLift 6653757
  have htrace : WordTrace (prefixWord ++ tailWord_6653757) baseStart_6653757 baseEnd_6653757 := by
    simpa [prefixWord, tailWord_6653757, baseEnd_6653757] using wordTrace_append hprefix tailTrace_6653757
  have hstable : (prefixWord ++ tailWord_6653757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6653757).length < 2 ^ (prefixWord ++ tailWord_6653757).sum := by decide
  have hdescent : baseEnd_6653757 < baseStart_6653757 := by decide
  rcases family_descends (prefixWord ++ tailWord_6653757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6653769 : List Nat := [1, 2, 1, 1, 2, 4, 1, 2, 1, 1, 7]
def baseStart_6653769 : Nat := 118140960795 + 6653769 * 2 ^ 59
def prefixEnd_6653769 : Nat := 4983230072969 + 3 ^ 40 * 6653769 * 2
def baseEnd_6653769 : Nat := 3416581660985882831887379

theorem tailTrace_6653769 : CollatzResearch.WordTrace tailWord_6653769 prefixEnd_6653769 3416581660985882831887379 := by
  unfold tailWord_6653769
  simp only [CollatzResearch.WordTrace]
  refine ⟨242682892631538761119012361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161788595087692507412674907 242682892631538761119012361)
  ·
    refine ⟨182012169473654070839259271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242682892631538761119012361 182012169473654070839259271)
    ·
      refine ⟨273018254210481106258888907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182012169473654070839259271 273018254210481106258888907)
      ·
        refine ⟨409527381315721659388333361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273018254210481106258888907 409527381315721659388333361)
        ·
          refine ⟨307145535986791244541250021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 409527381315721659388333361 307145535986791244541250021)
          ·
            refine ⟨57589787997523358351484379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 307145535986791244541250021 57589787997523358351484379)
            ·
              refine ⟨86384681996285037527226569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57589787997523358351484379 86384681996285037527226569)
              ·
                refine ⟨64788511497213778145419927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86384681996285037527226569 64788511497213778145419927)
                ·
                  refine ⟨97182767245820667218129891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64788511497213778145419927 97182767245820667218129891)
                  ·
                    refine ⟨145774150868731000827194837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 97182767245820667218129891 145774150868731000827194837)
                    ·
                      refine ⟨3416581660985882831887379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 145774150868731000827194837 3416581660985882831887379)
                      ·
                        rfl

theorem cell23_6653769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 1, 7].length) (baseStart_6653769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6653769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6653769 prefixEnd_6653769 := by exact prefixLift 6653769
  have htrace : WordTrace (prefixWord ++ tailWord_6653769) baseStart_6653769 baseEnd_6653769 := by
    simpa [prefixWord, tailWord_6653769, baseEnd_6653769] using wordTrace_append hprefix tailTrace_6653769
  have hstable : (prefixWord ++ tailWord_6653769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6653769).length < 2 ^ (prefixWord ++ tailWord_6653769).sum := by decide
  have hdescent : baseEnd_6653769 < baseStart_6653769 := by decide
  rcases family_descends (prefixWord ++ tailWord_6653769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6653819 : List Nat := [1, 1, 1, 1, 1, 5, 1, 2, 10]
def baseStart_6653819 : Nat := 118140960795 + 6653819 * 2 ^ 59
def prefixEnd_6653819 : Nat := 4983230072969 + 3 ^ 40 * 6653819 * 2
def baseEnd_6653819 : Nat := 379623037224289737362461

theorem tailTrace_6653819 : CollatzResearch.WordTrace tailWord_6653819 prefixEnd_6653819 379623037224289737362461 := by
  unfold tailWord_6653819
  simp only [CollatzResearch.WordTrace]
  refine ⟨242684716281357619658332511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161789810854238413105555007 242684716281357619658332511)
  ·
    refine ⟨364027074422036429487498767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242684716281357619658332511 364027074422036429487498767)
    ·
      refine ⟨546040611633054644231248151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364027074422036429487498767 546040611633054644231248151)
      ·
        refine ⟨819060917449581966346872227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 546040611633054644231248151 819060917449581966346872227)
        ·
          refine ⟨1228591376174372949520308341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 819060917449581966346872227 1228591376174372949520308341)
          ·
            refine ⟨115180441516347464017528907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1228591376174372949520308341 115180441516347464017528907)
            ·
              refine ⟨172770662274521196026293361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115180441516347464017528907 172770662274521196026293361)
              ·
                refine ⟨129577996705890897019720021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172770662274521196026293361 129577996705890897019720021)
                ·
                  refine ⟨379623037224289737362461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 129577996705890897019720021 379623037224289737362461)
                  ·
                    rfl

theorem cell23_6653819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 10].length) (baseStart_6653819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6653819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6653819 prefixEnd_6653819 := by exact prefixLift 6653819
  have htrace : WordTrace (prefixWord ++ tailWord_6653819) baseStart_6653819 baseEnd_6653819 := by
    simpa [prefixWord, tailWord_6653819, baseEnd_6653819] using wordTrace_append hprefix tailTrace_6653819
  have hstable : (prefixWord ++ tailWord_6653819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6653819).length < 2 ^ (prefixWord ++ tailWord_6653819).sum := by decide
  have hdescent : baseEnd_6653819 < baseStart_6653819 := by decide
  rcases family_descends (prefixWord ++ tailWord_6653819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6653853 : List Nat := [1, 4, 2, 1, 2, 2, 3, 2, 6]
def baseStart_6653853 : Nat := 118140960795 + 6653853 * 2 ^ 59
def prefixEnd_6653853 : Nat := 4983230072969 + 3 ^ 40 * 6653853 * 2
def baseEnd_6653853 : Nat := 379624977040095611470777

theorem tailTrace_6653853 : CollatzResearch.WordTrace tailWord_6653853 prefixEnd_6653853 379624977040095611470777 := by
  unfold tailWord_6653853
  simp only [CollatzResearch.WordTrace]
  refine ⟨242685956363234443465070213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161790637575489628976713475 242685956363234443465070213)
  ·
    refine ⟨45503616818106458149700665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 242685956363234443465070213 45503616818106458149700665)
    ·
      refine ⟨34127712613579843612275499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45503616818106458149700665 34127712613579843612275499)
      ·
        refine ⟨51191568920369765418413249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34127712613579843612275499 51191568920369765418413249)
        ·
          refine ⟨38393676690277324063809937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51191568920369765418413249 38393676690277324063809937)
          ·
            refine ⟨28795257517707993047857453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38393676690277324063809937 28795257517707993047857453)
            ·
              refine ⟨10798221569140497392946545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28795257517707993047857453 10798221569140497392946545)
              ·
                refine ⟨8098666176855373044709909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10798221569140497392946545 8098666176855373044709909)
                ·
                  refine ⟨379624977040095611470777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8098666176855373044709909 379624977040095611470777)
                  ·
                    rfl

theorem cell23_6653853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 2, 6].length) (baseStart_6653853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6653853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6653853 prefixEnd_6653853 := by exact prefixLift 6653853
  have htrace : WordTrace (prefixWord ++ tailWord_6653853) baseStart_6653853 baseEnd_6653853 := by
    simpa [prefixWord, tailWord_6653853, baseEnd_6653853] using wordTrace_append hprefix tailTrace_6653853
  have hstable : (prefixWord ++ tailWord_6653853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6653853).length < 2 ^ (prefixWord ++ tailWord_6653853).sum := by decide
  have hdescent : baseEnd_6653853 < baseStart_6653853 := by decide
  rcases family_descends (prefixWord ++ tailWord_6653853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6653903 : List Nat := [1, 1, 2, 1, 1, 5, 1, 5, 1, 1, 4]
def baseStart_6653903 : Nat := 118140960795 + 6653903 * 2 ^ 59
def prefixEnd_6653903 : Nat := 4983230072969 + 3 ^ 40 * 6653903 * 2
def baseEnd_6653903 : Nat := 3416650467393585307611763

theorem tailTrace_6653903 : CollatzResearch.WordTrace tailWord_6653903 prefixEnd_6653903 3416650467393585307611763 := by
  unfold tailWord_6653903
  simp only [CollatzResearch.WordTrace]
  refine ⟨242687780013053302004390363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161791853342035534669593575 242687780013053302004390363)
  ·
    refine ⟨364031670019579953006585545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242687780013053302004390363 364031670019579953006585545)
    ·
      refine ⟨273023752514684964754939159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364031670019579953006585545 273023752514684964754939159)
      ·
        refine ⟨409535628772027447132408739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273023752514684964754939159 409535628772027447132408739)
        ·
          refine ⟨614303443158041170698613109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409535628772027447132408739 614303443158041170698613109)
          ·
            refine ⟨57590947796066359752994979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 614303443158041170698613109 57590947796066359752994979)
            ·
              refine ⟨86386421694099539629492469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57590947796066359752994979 86386421694099539629492469)
              ·
                refine ⟨8098727033821831840264919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86386421694099539629492469 8098727033821831840264919)
                ·
                  refine ⟨12148090550732747760397379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8098727033821831840264919 12148090550732747760397379)
                  ·
                    refine ⟨18222135826099121640596069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12148090550732747760397379 18222135826099121640596069)
                    ·
                      refine ⟨3416650467393585307611763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18222135826099121640596069 3416650467393585307611763)
                      ·
                        rfl

theorem cell23_6653903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 5, 1, 1, 4].length) (baseStart_6653903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6653903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6653903 prefixEnd_6653903 := by exact prefixLift 6653903
  have htrace : WordTrace (prefixWord ++ tailWord_6653903) baseStart_6653903 baseEnd_6653903 := by
    simpa [prefixWord, tailWord_6653903, baseEnd_6653903] using wordTrace_append hprefix tailTrace_6653903
  have hstable : (prefixWord ++ tailWord_6653903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6653903).length < 2 ^ (prefixWord ++ tailWord_6653903).sum := by decide
  have hdescent : baseEnd_6653903 < baseStart_6653903 := by decide
  rcases family_descends (prefixWord ++ tailWord_6653903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6653914 : List Nat := [3, 1, 1, 2, 6, 1, 1, 1, 3, 1, 3]
def baseStart_6653914 : Nat := 118140960795 + 6653914 * 2 ^ 59
def prefixEnd_6653914 : Nat := 4983230072969 + 3 ^ 40 * 6653914 * 2
def baseEnd_6653914 : Nat := 3416656115680784764574213

theorem tailTrace_6653914 : CollatzResearch.WordTrace tailWord_6653914 prefixEnd_6653914 3416656115680784764574213 := by
  unfold tailWord_6653914
  simp only [CollatzResearch.WordTrace]
  refine ⟨60672045304003362720760199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161792120810675633922027197 60672045304003362720760199)
  ·
    refine ⟨91008067956005044081140299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60672045304003362720760199 91008067956005044081140299)
    ·
      refine ⟨136512101934007566121710449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91008067956005044081140299 136512101934007566121710449)
      ·
        refine ⟨102384076450505674591282837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136512101934007566121710449 102384076450505674591282837)
        ·
          refine ⟨4799253583617453496466383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 102384076450505674591282837 4799253583617453496466383)
          ·
            refine ⟨7198880375426180244699575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4799253583617453496466383 7198880375426180244699575)
            ·
              refine ⟨10798320563139270367049363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7198880375426180244699575 10798320563139270367049363)
              ·
                refine ⟨16197480844708905550574045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10798320563139270367049363 16197480844708905550574045)
                ·
                  refine ⟨6074055316765839581465267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16197480844708905550574045 6074055316765839581465267)
                  ·
                    refine ⟨9111082975148759372197901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6074055316765839581465267 9111082975148759372197901)
                    ·
                      refine ⟨3416656115680784764574213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9111082975148759372197901 3416656115680784764574213)
                      ·
                        rfl

theorem cell23_6653914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 3, 1, 3].length) (baseStart_6653914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6653914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6653914 prefixEnd_6653914 := by exact prefixLift 6653914
  have htrace : WordTrace (prefixWord ++ tailWord_6653914) baseStart_6653914 baseEnd_6653914 := by
    simpa [prefixWord, tailWord_6653914, baseEnd_6653914] using wordTrace_append hprefix tailTrace_6653914
  have hstable : (prefixWord ++ tailWord_6653914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6653914).length < 2 ^ (prefixWord ++ tailWord_6653914).sum := by decide
  have hdescent : baseEnd_6653914 < baseStart_6653914 := by decide
  rcases family_descends (prefixWord ++ tailWord_6653914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6653923 : List Nat := [1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 5]
def baseStart_6653923 : Nat := 118140960795 + 6653923 * 2 ^ 59
def prefixEnd_6653923 : Nat := 4983230072969 + 3 ^ 40 * 6653923 * 2
def baseEnd_6653923 : Nat := 3416660737006675229361671

theorem tailTrace_6653923 : CollatzResearch.WordTrace tailWord_6653923 prefixEnd_6653923 3416660737006675229361671 := by
  unfold tailWord_6653923
  simp only [CollatzResearch.WordTrace]
  refine ⟨242688509472980845420118423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161792339648653896946745615 242688509472980845420118423)
  ·
    refine ⟨364032764209471268130177635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242688509472980845420118423 364032764209471268130177635)
    ·
      refine ⟨546049146314206902195266453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364032764209471268130177635 546049146314206902195266453)
      ·
        refine ⟨25596053733478448540403115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 546049146314206902195266453 25596053733478448540403115)
        ·
          refine ⟨38394080600217672810604673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25596053733478448540403115 38394080600217672810604673)
          ·
            refine ⟨28795560450163254607953505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38394080600217672810604673 28795560450163254607953505)
            ·
              refine ⟨21596670337622440955965129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28795560450163254607953505 21596670337622440955965129)
              ·
                refine ⟨16197502753216830716973847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21596670337622440955965129 16197502753216830716973847)
                ·
                  refine ⟨24296254129825246075460771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16197502753216830716973847 24296254129825246075460771)
                  ·
                    refine ⟨36444381194737869113191157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24296254129825246075460771 36444381194737869113191157)
                    ·
                      refine ⟨3416660737006675229361671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36444381194737869113191157 3416660737006675229361671)
                      ·
                        rfl

theorem cell23_6653923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_6653923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6653923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6653923 prefixEnd_6653923 := by exact prefixLift 6653923
  have htrace : WordTrace (prefixWord ++ tailWord_6653923) baseStart_6653923 baseEnd_6653923 := by
    simpa [prefixWord, tailWord_6653923, baseEnd_6653923] using wordTrace_append hprefix tailTrace_6653923
  have hstable : (prefixWord ++ tailWord_6653923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6653923).length < 2 ^ (prefixWord ++ tailWord_6653923).sum := by decide
  have hdescent : baseEnd_6653923 < baseStart_6653923 := by decide
  rcases family_descends (prefixWord ++ tailWord_6653923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6653930 : List Nat := [3, 1, 3, 1, 2, 1, 3, 3, 2, 4]
def baseStart_6653930 : Nat := 118140960795 + 6653930 * 2 ^ 59
def prefixEnd_6653930 : Nat := 4983230072969 + 3 ^ 40 * 6653930 * 2
def baseEnd_6653930 : Nat := 1138888110457085567324713

theorem tailTrace_6653930 : CollatzResearch.WordTrace tailWord_6653930 prefixEnd_6653930 1138888110457085567324713 := by
  unfold tailWord_6653930
  simp only [CollatzResearch.WordTrace]
  refine ⟨60672191195988871403905811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161792509855970323743748829 60672191195988871403905811)
  ·
    refine ⟨91008286793983307105858717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60672191195988871403905811 91008286793983307105858717)
    ·
      refine ⟨34128107547743740164697019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91008286793983307105858717 34128107547743740164697019)
      ·
        refine ⟨51192161321615610247045529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34128107547743740164697019 51192161321615610247045529)
        ·
          refine ⟨38394120991211707685284147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51192161321615610247045529 38394120991211707685284147)
          ·
            refine ⟨57591181486817561527926221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38394120991211707685284147 57591181486817561527926221)
            ·
              refine ⟨21596693057556585572972333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57591181486817561527926221 21596693057556585572972333)
              ·
                refine ⟨8098759896583719589864625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21596693057556585572972333 8098759896583719589864625)
                ·
                  refine ⟨6074069922437789692398469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8098759896583719589864625 6074069922437789692398469)
                  ·
                    refine ⟨1138888110457085567324713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6074069922437789692398469 1138888110457085567324713)
                    ·
                      rfl

theorem cell23_6653930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_6653930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6653930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6653930 prefixEnd_6653930 := by exact prefixLift 6653930
  have htrace : WordTrace (prefixWord ++ tailWord_6653930) baseStart_6653930 baseEnd_6653930 := by
    simpa [prefixWord, tailWord_6653930, baseEnd_6653930] using wordTrace_append hprefix tailTrace_6653930
  have hstable : (prefixWord ++ tailWord_6653930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6653930).length < 2 ^ (prefixWord ++ tailWord_6653930).sum := by decide
  have hdescent : baseEnd_6653930 < baseStart_6653930 := by decide
  rcases family_descends (prefixWord ++ tailWord_6653930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6653937 : List Nat := [1, 2, 2, 2, 5, 2, 1, 2, 1, 1, 4]
def baseStart_6653937 : Nat := 118140960795 + 6653937 * 2 ^ 59
def prefixEnd_6653937 : Nat := 4983230072969 + 3 ^ 40 * 6653937 * 2
def baseEnd_6653937 : Nat := 3416667925735838174586607

theorem tailTrace_6653937 : CollatzResearch.WordTrace tailWord_6653937 prefixEnd_6653937 3416667925735838174586607 := by
  unfold tailWord_6653937
  simp only [CollatzResearch.WordTrace]
  refine ⟨242689020094930125811128065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161792680063286750540752043 242689020094930125811128065)
  ·
    refine ⟨182016765071197594358346049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242689020094930125811128065 182016765071197594358346049)
    ·
      refine ⟨136512573803398195768759537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182016765071197594358346049 136512573803398195768759537)
      ·
        refine ⟨102384430352548646826569653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136512573803398195768759537 102384430352548646826569653)
        ·
          refine ⟨9598540345551435639990905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102384430352548646826569653 9598540345551435639990905)
          ·
            refine ⟨7198905259163576729993179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9598540345551435639990905 7198905259163576729993179)
            ·
              refine ⟨10798357888745365094989769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7198905259163576729993179 10798357888745365094989769)
              ·
                refine ⟨8098768416559023821242327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10798357888745365094989769 8098768416559023821242327)
                ·
                  refine ⟨12148152624838535731863491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8098768416559023821242327 12148152624838535731863491)
                  ·
                    refine ⟨18222228937257803597795237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12148152624838535731863491 18222228937257803597795237)
                    ·
                      refine ⟨3416667925735838174586607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18222228937257803597795237 3416667925735838174586607)
                      ·
                        rfl

theorem cell23_6653937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 2, 1, 1, 4].length) (baseStart_6653937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6653937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6653937 prefixEnd_6653937 := by exact prefixLift 6653937
  have htrace : WordTrace (prefixWord ++ tailWord_6653937) baseStart_6653937 baseEnd_6653937 := by
    simpa [prefixWord, tailWord_6653937, baseEnd_6653937] using wordTrace_append hprefix tailTrace_6653937
  have hstable : (prefixWord ++ tailWord_6653937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6653937).length < 2 ^ (prefixWord ++ tailWord_6653937).sum := by decide
  have hdescent : baseEnd_6653937 < baseStart_6653937 := by decide
  rcases family_descends (prefixWord ++ tailWord_6653937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6653950 : List Nat := [4, 2, 2, 2, 1, 1, 1, 1, 3, 2, 4]
def baseStart_6653950 : Nat := 118140960795 + 6653950 * 2 ^ 59
def prefixEnd_6653950 : Nat := 4983230072969 + 3 ^ 40 * 6653950 * 2
def baseEnd_6653950 : Nat := 3416674600984346623724047

theorem tailTrace_6653950 : CollatzResearch.WordTrace tailWord_6653950 prefixEnd_6653950 3416674600984346623724047 := by
  unfold tailWord_6653950
  simp only [CollatzResearch.WordTrace]
  refine ⟨30336186780485378628918913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161792996162588686020900869 30336186780485378628918913)
  ·
    refine ⟨22752140085364033971689185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30336186780485378628918913 22752140085364033971689185)
    ·
      refine ⟨17064105064023025478766889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22752140085364033971689185 17064105064023025478766889)
      ·
        refine ⟨12798078798017269109075167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17064105064023025478766889 12798078798017269109075167)
        ·
          refine ⟨19197118197025903663612751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12798078798017269109075167 19197118197025903663612751)
          ·
            refine ⟨28795677295538855495419127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19197118197025903663612751 28795677295538855495419127)
            ·
              refine ⟨43193515943308283243128691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28795677295538855495419127 43193515943308283243128691)
              ·
                refine ⟨64790273914962424864693037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43193515943308283243128691 64790273914962424864693037)
                ·
                  refine ⟨24296352718110909324259889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64790273914962424864693037 24296352718110909324259889)
                  ·
                    refine ⟨18222264538583181993194917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24296352718110909324259889 18222264538583181993194917)
                    ·
                      refine ⟨3416674600984346623724047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18222264538583181993194917 3416674600984346623724047)
                      ·
                        rfl

theorem cell23_6653950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_6653950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6653950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6653950 prefixEnd_6653950 := by exact prefixLift 6653950
  have htrace : WordTrace (prefixWord ++ tailWord_6653950) baseStart_6653950 baseEnd_6653950 := by
    simpa [prefixWord, tailWord_6653950, baseEnd_6653950] using wordTrace_append hprefix tailTrace_6653950
  have hstable : (prefixWord ++ tailWord_6653950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6653950).length < 2 ^ (prefixWord ++ tailWord_6653950).sum := by decide
  have hdescent : baseEnd_6653950 < baseStart_6653950 := by decide
  rcases family_descends (prefixWord ++ tailWord_6653950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6653957 : List Nat := [1, 3, 1, 1, 2, 5, 3, 1, 1, 2, 3]
def baseStart_6653957 : Nat := 118140960795 + 6653957 * 2 ^ 59
def prefixEnd_6653957 : Nat := 4983230072969 + 3 ^ 40 * 6653957 * 2
def baseEnd_6653957 : Nat := 3416678195348928096336515

theorem tailTrace_6653957 : CollatzResearch.WordTrace tailWord_6653957 prefixEnd_6653957 3416678195348928096336515 := by
  unfold tailWord_6653957
  simp only [CollatzResearch.WordTrace]
  refine ⟨242689749554857669226856125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161793166369905112817904083 242689749554857669226856125)
  ·
    refine ⟨91008656083071625960071047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242689749554857669226856125 91008656083071625960071047)
    ·
      refine ⟨136512984124607438940106571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91008656083071625960071047 136512984124607438940106571)
      ·
        refine ⟨204769476186911158410159857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136512984124607438940106571 204769476186911158410159857)
        ·
          refine ⟨153577107140183368807619893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204769476186911158410159857 153577107140183368807619893)
          ·
            refine ⟨14397853794392190825714365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 153577107140183368807619893 14397853794392190825714365)
            ·
              refine ⟨5399195172897071559642887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14397853794392190825714365 5399195172897071559642887)
              ·
                refine ⟨8098792759345607339464331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5399195172897071559642887 8098792759345607339464331)
                ·
                  refine ⟨12148189139018411009196497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8098792759345607339464331 12148189139018411009196497)
                  ·
                    refine ⟨9111141854263808256897373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12148189139018411009196497 9111141854263808256897373)
                    ·
                      refine ⟨3416678195348928096336515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9111141854263808256897373 3416678195348928096336515)
                      ·
                        rfl

theorem cell23_6653957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 1, 1, 2, 3].length) (baseStart_6653957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6653957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6653957 prefixEnd_6653957 := by exact prefixLift 6653957
  have htrace : WordTrace (prefixWord ++ tailWord_6653957) baseStart_6653957 baseEnd_6653957 := by
    simpa [prefixWord, tailWord_6653957, baseEnd_6653957] using wordTrace_append hprefix tailTrace_6653957
  have hstable : (prefixWord ++ tailWord_6653957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6653957).length < 2 ^ (prefixWord ++ tailWord_6653957).sum := by decide
  have hdescent : baseEnd_6653957 < baseStart_6653957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6653957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654013 : List Nat := [1, 4, 1, 3, 1, 1, 2, 1, 1, 3, 5]
def baseStart_6654013 : Nat := 118140960795 + 6654013 * 2 ^ 59
def prefixEnd_6654013 : Nat := 4983230072969 + 3 ^ 40 * 6654013 * 2
def baseEnd_6654013 : Nat := 3416706950265579877236257

theorem tailTrace_6654013 : CollatzResearch.WordTrace tailWord_6654013 prefixEnd_6654013 3416706950265579877236257 := by
  unfold tailWord_6654013
  simp only [CollatzResearch.WordTrace]
  refine ⟨242691792042654790790894693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161794528028436527193929795 242691792042654790790894693)
  ·
    refine ⟨45504711007997773273292755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 242691792042654790790894693 45504711007997773273292755)
    ·
      refine ⟨68257066511996659909939133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45504711007997773273292755 68257066511996659909939133)
      ·
        refine ⟨25596399941998747466227175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68257066511996659909939133 25596399941998747466227175)
        ·
          refine ⟨38394599912998121199340763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25596399941998747466227175 38394599912998121199340763)
          ·
            refine ⟨57591899869497181799011145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38394599912998121199340763 57591899869497181799011145)
            ·
              refine ⟨43193924902122886349258359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57591899869497181799011145 43193924902122886349258359)
              ·
                refine ⟨64790887353184329523887539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43193924902122886349258359 64790887353184329523887539)
                ·
                  refine ⟨97186331029776494285831309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64790887353184329523887539 97186331029776494285831309)
                  ·
                    refine ⟨36444874136166185357186741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 97186331029776494285831309 36444874136166185357186741)
                    ·
                      refine ⟨3416706950265579877236257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36444874136166185357186741 3416706950265579877236257)
                      ·
                        rfl

theorem cell23_6654013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_6654013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654013 prefixEnd_6654013 := by exact prefixLift 6654013
  have htrace : WordTrace (prefixWord ++ tailWord_6654013) baseStart_6654013 baseEnd_6654013 := by
    simpa [prefixWord, tailWord_6654013, baseEnd_6654013] using wordTrace_append hprefix tailTrace_6654013
  have hstable : (prefixWord ++ tailWord_6654013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654013).length < 2 ^ (prefixWord ++ tailWord_6654013).sum := by decide
  have hdescent : baseEnd_6654013 < baseStart_6654013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654023 : List Nat := [1, 1, 4, 1, 3, 1, 1, 1, 4, 2, 4]
def baseStart_6654023 : Nat := 118140960795 + 6654023 * 2 ^ 59
def prefixEnd_6654023 : Nat := 4983230072969 + 3 ^ 40 * 6654023 * 2
def baseEnd_6654023 : Nat := 3416712085072124838111211

theorem tailTrace_6654023 : CollatzResearch.WordTrace tailWord_6654023 prefixEnd_6654023 3416712085072124838111211 := by
  unfold tailWord_6654023
  simp only [CollatzResearch.WordTrace]
  refine ⟨242692156772618562498758723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161794771181745708332505815 242692156772618562498758723)
  ·
    refine ⟨364038235158927843748138085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242692156772618562498758723 364038235158927843748138085)
    ·
      refine ⟨68257169092298970702775891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 364038235158927843748138085 68257169092298970702775891)
      ·
        refine ⟨102385753638448456054163837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68257169092298970702775891 102385753638448456054163837)
        ·
          refine ⟨38394657614418171020311439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102385753638448456054163837 38394657614418171020311439)
          ·
            refine ⟨57591986421627256530467159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38394657614418171020311439 57591986421627256530467159)
            ·
              refine ⟨86387979632440884795700739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57591986421627256530467159 86387979632440884795700739)
              ·
                refine ⟨129581969448661327193551109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86387979632440884795700739 129581969448661327193551109)
                ·
                  refine ⟨24296619271623998848790833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 129581969448661327193551109 24296619271623998848790833)
                  ·
                    refine ⟨18222464453717999136593125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24296619271623998848790833 18222464453717999136593125)
                    ·
                      refine ⟨3416712085072124838111211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18222464453717999136593125 3416712085072124838111211)
                      ·
                        rfl

theorem cell23_6654023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_6654023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654023 prefixEnd_6654023 := by exact prefixLift 6654023
  have htrace : WordTrace (prefixWord ++ tailWord_6654023) baseStart_6654023 baseEnd_6654023 := by
    simpa [prefixWord, tailWord_6654023, baseEnd_6654023] using wordTrace_append hprefix tailTrace_6654023
  have hstable : (prefixWord ++ tailWord_6654023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654023).length < 2 ^ (prefixWord ++ tailWord_6654023).sum := by decide
  have hdescent : baseEnd_6654023 < baseStart_6654023 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654038 : List Nat := [5, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3]
def baseStart_6654038 : Nat := 118140960795 + 6654038 * 2 ^ 59
def prefixEnd_6654038 : Nat := 4983230072969 + 3 ^ 40 * 6654038 * 2
def baseEnd_6654038 : Nat := 3416719787281942279423643

theorem tailTrace_6654038 : CollatzResearch.WordTrace tailWord_6654038 prefixEnd_6654038 3416719787281942279423643 := by
  unfold tailWord_6654038
  simp only [CollatzResearch.WordTrace]
  refine ⟨15168293991722763753784673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161795135911709480040369845 15168293991722763753784673)
  ·
    refine ⟨11376220493792072815338505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15168293991722763753784673 11376220493792072815338505)
    ·
      refine ⟨8532165370344054611503879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11376220493792072815338505 8532165370344054611503879)
      ·
        refine ⟨12798248055516081917255819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8532165370344054611503879 12798248055516081917255819)
        ·
          refine ⟨19197372083274122875883729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12798248055516081917255819 19197372083274122875883729)
          ·
            refine ⟨14398029062455592156912797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19197372083274122875883729 14398029062455592156912797)
            ·
              refine ⟨5399260898420847058842299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14398029062455592156912797 5399260898420847058842299)
              ·
                refine ⟨8098891347631270588263449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5399260898420847058842299 8098891347631270588263449)
                ·
                  refine ⟨6074168510723452941197587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8098891347631270588263449 6074168510723452941197587)
                  ·
                    refine ⟨9111252766085179411796381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6074168510723452941197587 9111252766085179411796381)
                    ·
                      refine ⟨3416719787281942279423643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9111252766085179411796381 3416719787281942279423643)
                      ·
                        rfl

theorem cell23_6654038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_6654038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654038 prefixEnd_6654038 := by exact prefixLift 6654038
  have htrace : WordTrace (prefixWord ++ tailWord_6654038) baseStart_6654038 baseEnd_6654038 := by
    simpa [prefixWord, tailWord_6654038, baseEnd_6654038] using wordTrace_append hprefix tailTrace_6654038
  have hstable : (prefixWord ++ tailWord_6654038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654038).length < 2 ^ (prefixWord ++ tailWord_6654038).sum := by decide
  have hdescent : baseEnd_6654038 < baseStart_6654038 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654044 : List Nat := [2, 2, 4, 1, 1, 4, 1, 1, 1, 4, 2]
def baseStart_6654044 : Nat := 118140960795 + 6654044 * 2 ^ 59
def prefixEnd_6654044 : Nat := 4983230072969 + 3 ^ 40 * 6654044 * 2
def baseEnd_6654044 : Nat := 3416722868165869255948615

theorem tailTrace_6654044 : CollatzResearch.WordTrace tailWord_6654044 prefixEnd_6654044 3416722868165869255948615 := by
  unfold tailWord_6654044
  simp only [CollatzResearch.WordTrace]
  refine ⟨121346461352771241542636593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161795281803694988723515457 121346461352771241542636593)
  ·
    refine ⟨91009846014578431156977445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121346461352771241542636593 91009846014578431156977445)
    ·
      refine ⟨17064346127733455841933271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91009846014578431156977445 17064346127733455841933271)
      ·
        refine ⟨25596519191600183762899907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17064346127733455841933271 25596519191600183762899907)
        ·
          refine ⟨38394778787400275644349861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25596519191600183762899907 38394778787400275644349861)
          ·
            refine ⟨7199021022637551683315599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38394778787400275644349861 7199021022637551683315599)
            ·
              refine ⟨10798531533956327524973399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7199021022637551683315599 10798531533956327524973399)
              ·
                refine ⟨16197797300934491287460099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10798531533956327524973399 16197797300934491287460099)
                ·
                  refine ⟨24296695951401736931190149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16197797300934491287460099 24296695951401736931190149)
                  ·
                    refine ⟨4555630490887825674598153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24296695951401736931190149 4555630490887825674598153)
                    ·
                      refine ⟨3416722868165869255948615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4555630490887825674598153 3416722868165869255948615)
                      ·
                        rfl

theorem cell23_6654044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_6654044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654044 prefixEnd_6654044 := by exact prefixLift 6654044
  have htrace : WordTrace (prefixWord ++ tailWord_6654044) baseStart_6654044 baseEnd_6654044 := by
    simpa [prefixWord, tailWord_6654044, baseEnd_6654044] using wordTrace_append hprefix tailTrace_6654044
  have hstable : (prefixWord ++ tailWord_6654044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654044).length < 2 ^ (prefixWord ++ tailWord_6654044).sum := by decide
  have hdescent : baseEnd_6654044 < baseStart_6654044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654063 : List Nat := [1, 1, 2, 1, 3, 4, 2, 1, 1, 7]
def baseStart_6654063 : Nat := 118140960795 + 6654063 * 2 ^ 59
def prefixEnd_6654063 : Nat := 4983230072969 + 3 ^ 40 * 6654063 * 2
def baseEnd_6654063 : Nat := 1138910874766101560537009

theorem tailTrace_6654063 : CollatzResearch.WordTrace tailWord_6654063 prefixEnd_6654063 1138910874766101560537009 := by
  unfold tailWord_6654063
  simp only [CollatzResearch.WordTrace]
  refine ⟨242693615692473649330214843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161795743794982432886809895 242693615692473649330214843)
  ·
    refine ⟨364040423538710473995322265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242693615692473649330214843 364040423538710473995322265)
    ·
      refine ⟨273030317654032855496491699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364040423538710473995322265 273030317654032855496491699)
      ·
        refine ⟨409545476481049283244737549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273030317654032855496491699 409545476481049283244737549)
        ·
          refine ⟨153579553680393481216776581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 409545476481049283244737549 153579553680393481216776581)
          ·
            refine ⟨28796166315073777728145609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153579553680393481216776581 28796166315073777728145609)
            ·
              refine ⟨21597124736305333296109207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28796166315073777728145609 21597124736305333296109207)
              ·
                refine ⟨32395687104457999944163811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21597124736305333296109207 32395687104457999944163811)
                ·
                  refine ⟨48593530656686999916245717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32395687104457999944163811 48593530656686999916245717)
                  ·
                    refine ⟨1138910874766101560537009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48593530656686999916245717 1138910874766101560537009)
                    ·
                      rfl

theorem cell23_6654063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 7].length) (baseStart_6654063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654063 prefixEnd_6654063 := by exact prefixLift 6654063
  have htrace : WordTrace (prefixWord ++ tailWord_6654063) baseStart_6654063 baseEnd_6654063 := by
    simpa [prefixWord, tailWord_6654063, baseEnd_6654063] using wordTrace_append hprefix tailTrace_6654063
  have hstable : (prefixWord ++ tailWord_6654063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654063).length < 2 ^ (prefixWord ++ tailWord_6654063).sum := by decide
  have hdescent : baseEnd_6654063 < baseStart_6654063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654090 : List Nat := [3, 1, 2, 3, 1, 3, 1, 1, 1, 2, 5]
def baseStart_6654090 : Nat := 118140960795 + 6654090 * 2 ^ 59
def prefixEnd_6654090 : Nat := 4983230072969 + 3 ^ 40 * 6654090 * 2
def baseEnd_6654090 : Nat := 3416746488275976075973403

theorem tailTrace_6654090 : CollatzResearch.WordTrace tailWord_6654090 prefixEnd_6654090 3416746488275976075973403 := by
  unfold tailWord_6654090
  simp only [CollatzResearch.WordTrace]
  refine ⟨60673650115843958235361931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161796400308917221960965149 60673650115843958235361931)
  ·
    refine ⟨91010475173765937353042897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60673650115843958235361931 91010475173765937353042897)
    ·
      refine ⟨68257856380324453014782173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91010475173765937353042897 68257856380324453014782173)
      ·
        refine ⟨25596696142621669880543315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68257856380324453014782173 25596696142621669880543315)
        ·
          refine ⟨38395044213932504820814973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25596696142621669880543315 38395044213932504820814973)
          ·
            refine ⟨14398141580224689307805615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38395044213932504820814973 14398141580224689307805615)
            ·
              refine ⟨21597212370337033961708423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14398141580224689307805615 21597212370337033961708423)
              ·
                refine ⟨32395818555505550942562635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21597212370337033961708423 32395818555505550942562635)
                ·
                  refine ⟨48593727833258326413843953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32395818555505550942562635 48593727833258326413843953)
                  ·
                    refine ⟨36445295874943744810382965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48593727833258326413843953 36445295874943744810382965)
                    ·
                      refine ⟨3416746488275976075973403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36445295874943744810382965 3416746488275976075973403)
                      ·
                        rfl

theorem cell23_6654090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_6654090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654090 prefixEnd_6654090 := by exact prefixLift 6654090
  have htrace : WordTrace (prefixWord ++ tailWord_6654090) baseStart_6654090 baseEnd_6654090 := by
    simpa [prefixWord, tailWord_6654090, baseEnd_6654090] using wordTrace_append hprefix tailTrace_6654090
  have hstable : (prefixWord ++ tailWord_6654090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654090).length < 2 ^ (prefixWord ++ tailWord_6654090).sum := by decide
  have hdescent : baseEnd_6654090 < baseStart_6654090 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654127 : List Nat := [1, 1, 2, 1, 2, 3, 1, 7, 1, 4]
def baseStart_6654127 : Nat := 118140960795 + 6654127 * 2 ^ 59
def prefixEnd_6654127 : Nat := 4983230072969 + 3 ^ 40 * 6654127 * 2
def baseEnd_6654127 : Nat := 1138921829020064143736911

theorem tailTrace_6654127 : CollatzResearch.WordTrace tailWord_6654127 prefixEnd_6654127 1138921829020064143736911 := by
  unfold tailWord_6654127
  simp only [CollatzResearch.WordTrace]
  refine ⟨242695949964241788260544635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161797299976161192173696423 242695949964241788260544635)
  ·
    refine ⟨364043924946362682390816953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242695949964241788260544635 364043924946362682390816953)
    ·
      refine ⟨273032943709772011793112715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364043924946362682390816953 273032943709772011793112715)
      ·
        refine ⟨409549415564658017689669073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273032943709772011793112715 409549415564658017689669073)
        ·
          refine ⟨307162061673493513267251805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 409549415564658017689669073 307162061673493513267251805)
          ·
            refine ⟨115185773127560067475219427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 307162061673493513267251805 115185773127560067475219427)
            ·
              refine ⟨172778659691340101212829141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115185773127560067475219427 172778659691340101212829141)
              ·
                refine ⟨4049499836515783622175683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 172778659691340101212829141 4049499836515783622175683)
                ·
                  refine ⟨6074249754773675433263525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4049499836515783622175683 6074249754773675433263525)
                  ·
                    refine ⟨1138921829020064143736911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6074249754773675433263525 1138921829020064143736911)
                    ·
                      rfl

theorem cell23_6654127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 7, 1, 4].length) (baseStart_6654127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654127 prefixEnd_6654127 := by exact prefixLift 6654127
  have htrace : WordTrace (prefixWord ++ tailWord_6654127) baseStart_6654127 baseEnd_6654127 := by
    simpa [prefixWord, tailWord_6654127, baseEnd_6654127] using wordTrace_append hprefix tailTrace_6654127
  have hstable : (prefixWord ++ tailWord_6654127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654127).length < 2 ^ (prefixWord ++ tailWord_6654127).sum := by decide
  have hdescent : baseEnd_6654127 < baseStart_6654127 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654143 : List Nat := [1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 6]
def baseStart_6654143 : Nat := 118140960795 + 6654143 * 2 ^ 59
def prefixEnd_6654143 : Nat := 4983230072969 + 3 ^ 40 * 6654143 * 2
def baseEnd_6654143 : Nat := 3416773702750664368610659

theorem tailTrace_6654143 : CollatzResearch.WordTrace tailWord_6654143 prefixEnd_6654143 3416773702750664368610659 := by
  unfold tailWord_6654143
  simp only [CollatzResearch.WordTrace]
  refine ⟨242696533532183822993127083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161797689021455881995418055 242696533532183822993127083)
  ·
    refine ⟨364044800298275734489690625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242696533532183822993127083 364044800298275734489690625)
    ·
      refine ⟨273033600223706800867267969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364044800298275734489690625 273033600223706800867267969)
      ·
        refine ⟨204775200167780100650450977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273033600223706800867267969 204775200167780100650450977)
        ·
          refine ⟨153581400125835075487838233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204775200167780100650450977 153581400125835075487838233)
          ·
            refine ⟨115186050094376306615878675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153581400125835075487838233 115186050094376306615878675)
            ·
              refine ⟨172779075141564459923818013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115186050094376306615878675 172779075141564459923818013)
              ·
                refine ⟨64792153178086672471431755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 172779075141564459923818013 64792153178086672471431755)
                ·
                  refine ⟨97188229767130008707147633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64792153178086672471431755 97188229767130008707147633)
                  ·
                    refine ⟨72891172325347506530360725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 97188229767130008707147633 72891172325347506530360725)
                    ·
                      refine ⟨3416773702750664368610659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72891172325347506530360725 3416773702750664368610659)
                      ·
                        rfl

theorem cell23_6654143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 6].length) (baseStart_6654143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654143 prefixEnd_6654143 := by exact prefixLift 6654143
  have htrace : WordTrace (prefixWord ++ tailWord_6654143) baseStart_6654143 baseEnd_6654143 := by
    simpa [prefixWord, tailWord_6654143, baseEnd_6654143] using wordTrace_append hprefix tailTrace_6654143
  have hstable : (prefixWord ++ tailWord_6654143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654143).length < 2 ^ (prefixWord ++ tailWord_6654143).sum := by decide
  have hdescent : baseEnd_6654143 < baseStart_6654143 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654144 : List Nat := [2, 1, 1, 2, 5, 2, 1, 4, 1, 4]
def baseStart_6654144 : Nat := 118140960795 + 6654144 * 2 ^ 59
def prefixEnd_6654144 : Nat := 4983230072969 + 3 ^ 40 * 6654144 * 2
def baseEnd_6654144 : Nat := 1138924738743772954899385

theorem tailTrace_6654144 : CollatzResearch.WordTrace tailWord_6654144 prefixEnd_6654144 1138924738743772954899385 := by
  unfold tailWord_6654144
  simp only [CollatzResearch.WordTrace]
  refine ⟨121348285002590100081956743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161797713336786800109275657 121348285002590100081956743)
  ·
    refine ⟨182022427503885150122935115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121348285002590100081956743 182022427503885150122935115)
    ·
      refine ⟨273033641255827725184402673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182022427503885150122935115 273033641255827725184402673)
      ·
        refine ⟨204775230941870793888302005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273033641255827725184402673 204775230941870793888302005)
        ·
          refine ⟨19197677900800386927028313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 204775230941870793888302005 19197677900800386927028313)
          ·
            refine ⟨14398258425600290195271235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19197677900800386927028313 14398258425600290195271235)
            ·
              refine ⟨21597387638400435292906853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14398258425600290195271235 21597387638400435292906853)
              ·
                refine ⟨4049510182200081617420035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21597387638400435292906853 4049510182200081617420035)
                ·
                  refine ⟨6074265273300122426130053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4049510182200081617420035 6074265273300122426130053)
                  ·
                    refine ⟨1138924738743772954899385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6074265273300122426130053 1138924738743772954899385)
                    ·
                      rfl

theorem cell23_6654144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 4, 1, 4].length) (baseStart_6654144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654144 prefixEnd_6654144 := by exact prefixLift 6654144
  have htrace : WordTrace (prefixWord ++ tailWord_6654144) baseStart_6654144 baseEnd_6654144 := by
    simpa [prefixWord, tailWord_6654144, baseEnd_6654144] using wordTrace_append hprefix tailTrace_6654144
  have hstable : (prefixWord ++ tailWord_6654144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654144).length < 2 ^ (prefixWord ++ tailWord_6654144).sum := by decide
  have hdescent : baseEnd_6654144 < baseStart_6654144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654170 : List Nat := [3, 1, 1, 2, 2, 1, 4, 1, 3, 5]
def baseStart_6654170 : Nat := 118140960795 + 6654170 * 2 ^ 59
def prefixEnd_6654170 : Nat := 4983230072969 + 3 ^ 40 * 6654170 * 2
def baseEnd_6654170 : Nat := 1138929188909445254324345

theorem tailTrace_6654170 : CollatzResearch.WordTrace tailWord_6654170 prefixEnd_6654170 1138929188909445254324345 := by
  unfold tailWord_6654170
  simp only [CollatzResearch.WordTrace]
  refine ⟨60674379575771501651089991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161798345535390671069573309 60674379575771501651089991)
  ·
    refine ⟨91011569363657252476634987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60674379575771501651089991 91011569363657252476634987)
    ·
      refine ⟨136517354045485878714952481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91011569363657252476634987 136517354045485878714952481)
      ·
        refine ⟨102388015534114409036214361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136517354045485878714952481 102388015534114409036214361)
        ·
          refine ⟨76791011650585806777160771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102388015534114409036214361 76791011650585806777160771)
          ·
            refine ⟨115186517475878710165741157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76791011650585806777160771 115186517475878710165741157)
            ·
              refine ⟨21597472026727258156076467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115186517475878710165741157 21597472026727258156076467)
              ·
                refine ⟨32396208040090887234114701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21597472026727258156076467 32396208040090887234114701)
                ·
                  refine ⟨12148578015034082712793013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32396208040090887234114701 12148578015034082712793013)
                  ·
                    refine ⟨1138929188909445254324345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12148578015034082712793013 1138929188909445254324345)
                    ·
                      rfl

theorem cell23_6654170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 3, 5].length) (baseStart_6654170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654170 prefixEnd_6654170 := by exact prefixLift 6654170
  have htrace : WordTrace (prefixWord ++ tailWord_6654170) baseStart_6654170 baseEnd_6654170 := by
    simpa [prefixWord, tailWord_6654170, baseEnd_6654170] using wordTrace_append hprefix tailTrace_6654170
  have hstable : (prefixWord ++ tailWord_6654170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654170).length < 2 ^ (prefixWord ++ tailWord_6654170).sum := by decide
  have hdescent : baseEnd_6654170 < baseStart_6654170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654177 : List Nat := [1, 2, 3, 1, 3, 1, 3, 1, 1, 5, 2]
def baseStart_6654177 : Nat := 118140960795 + 6654177 * 2 ^ 59
def prefixEnd_6654177 : Nat := 4983230072969 + 3 ^ 40 * 6654177 * 2
def baseEnd_6654177 : Nat := 3416791161092917235585503

theorem tailTrace_6654177 : CollatzResearch.WordTrace tailWord_6654177 prefixEnd_6654177 3416791161092917235585503 := by
  unfold tailWord_6654177
  simp only [CollatzResearch.WordTrace]
  refine ⟨242697773614060646799864785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161798515742707097866576523 242697773614060646799864785)
  ·
    refine ⟨182023330210545485099898589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242697773614060646799864785 182023330210545485099898589)
    ·
      refine ⟨68258748828954556912461971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182023330210545485099898589 68258748828954556912461971)
      ·
        refine ⟨102388123243431835368692957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68258748828954556912461971 102388123243431835368692957)
        ·
          refine ⟨38395546216286938263259859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102388123243431835368692957 38395546216286938263259859)
          ·
            refine ⟨57593319324430407394889789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38395546216286938263259859 57593319324430407394889789)
            ·
              refine ⟨21597494746661402773083671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57593319324430407394889789 21597494746661402773083671)
              ·
                refine ⟨32396242119992104159625507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21597494746661402773083671 32396242119992104159625507)
                ·
                  refine ⟨48594363179988156239438261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32396242119992104159625507 48594363179988156239438261)
                  ·
                    refine ⟨4555721548123889647447337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48594363179988156239438261 4555721548123889647447337)
                    ·
                      refine ⟨3416791161092917235585503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4555721548123889647447337 3416791161092917235585503)
                      ·
                        rfl

theorem cell23_6654177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 5, 2].length) (baseStart_6654177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654177 prefixEnd_6654177 := by exact prefixLift 6654177
  have htrace : WordTrace (prefixWord ++ tailWord_6654177) baseStart_6654177 baseEnd_6654177 := by
    simpa [prefixWord, tailWord_6654177, baseEnd_6654177] using wordTrace_append hprefix tailTrace_6654177
  have hstable : (prefixWord ++ tailWord_6654177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654177).length < 2 ^ (prefixWord ++ tailWord_6654177).sum := by decide
  have hdescent : baseEnd_6654177 < baseStart_6654177 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654217 : List Nat := [1, 2, 1, 1, 3, 6, 1, 1, 1, 6]
def baseStart_6654217 : Nat := 118140960795 + 6654217 * 2 ^ 59
def prefixEnd_6654217 : Nat := 4983230072969 + 3 ^ 40 * 6654217 * 2
def baseEnd_6654217 : Nat := 1138937233439699026361773

theorem tailTrace_6654217 : CollatzResearch.WordTrace tailWord_6654217 prefixEnd_6654217 1138937233439699026361773 := by
  unfold tailWord_6654217
  simp only [CollatzResearch.WordTrace]
  refine ⟨242699232533915733631320905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161799488355943822420880603 242699232533915733631320905)
  ·
    refine ⟨182024424400436800223490679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242699232533915733631320905 182024424400436800223490679)
    ·
      refine ⟨273036636600655200335236019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182024424400436800223490679 273036636600655200335236019)
      ·
        refine ⟨409554954900982800502854029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273036636600655200335236019 409554954900982800502854029)
        ·
          refine ⟨153583108087868550188570261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 409554954900982800502854029 153583108087868550188570261)
          ·
            refine ⟨7199208191618838290089231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 153583108087868550188570261 7199208191618838290089231)
            ·
              refine ⟨10798812287428257435133847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7199208191618838290089231 10798812287428257435133847)
              ·
                refine ⟨16198218431142386152700771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10798812287428257435133847 16198218431142386152700771)
                ·
                  refine ⟨24297327646713579229051157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16198218431142386152700771 24297327646713579229051157)
                  ·
                    refine ⟨1138937233439699026361773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24297327646713579229051157 1138937233439699026361773)
                    ·
                      rfl

theorem cell23_6654217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 6].length) (baseStart_6654217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654217 prefixEnd_6654217 := by exact prefixLift 6654217
  have htrace : WordTrace (prefixWord ++ tailWord_6654217) baseStart_6654217 baseEnd_6654217 := by
    simpa [prefixWord, tailWord_6654217, baseEnd_6654217] using wordTrace_append hprefix tailTrace_6654217
  have hstable : (prefixWord ++ tailWord_6654217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654217).length < 2 ^ (prefixWord ++ tailWord_6654217).sum := by decide
  have hdescent : baseEnd_6654217 < baseStart_6654217 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654220 : List Nat := [2, 2, 1, 2, 2, 2, 3, 1, 1, 1, 6]
def baseStart_6654220 : Nat := 118140960795 + 6654220 * 2 ^ 59
def prefixEnd_6654220 : Nat := 4983230072969 + 3 ^ 40 * 6654220 * 2
def baseEnd_6654220 : Nat := 3416813240761060567347805

theorem tailTrace_6654220 : CollatzResearch.WordTrace tailWord_6654220 prefixEnd_6654220 3416813240761060567347805 := by
  unfold tailWord_6654220
  simp only [CollatzResearch.WordTrace]
  refine ⟨121349670976452432571840057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161799561301936576762453409 121349670976452432571840057)
  ·
    refine ⟨91012253232339324428880043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121349670976452432571840057 91012253232339324428880043)
    ·
      refine ⟨136518379848508986643320065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91012253232339324428880043 136518379848508986643320065)
      ·
        refine ⟨102388784886381739982490049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136518379848508986643320065 102388784886381739982490049)
        ·
          refine ⟨76791588664786304986867537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102388784886381739982490049 76791588664786304986867537)
          ·
            refine ⟨57593691498589728740150653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76791588664786304986867537 57593691498589728740150653)
            ·
              refine ⟨21597634311971148277556495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57593691498589728740150653 21597634311971148277556495)
              ·
                refine ⟨32396451467956722416334743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21597634311971148277556495 32396451467956722416334743)
                ·
                  refine ⟨48594677201935083624502115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32396451467956722416334743 48594677201935083624502115)
                  ·
                    refine ⟨72892015802902625436753173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48594677201935083624502115 72892015802902625436753173)
                    ·
                      refine ⟨3416813240761060567347805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72892015802902625436753173 3416813240761060567347805)
                      ·
                        rfl

theorem cell23_6654220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_6654220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654220 prefixEnd_6654220 := by exact prefixLift 6654220
  have htrace : WordTrace (prefixWord ++ tailWord_6654220) baseStart_6654220 baseEnd_6654220 := by
    simpa [prefixWord, tailWord_6654220, baseEnd_6654220] using wordTrace_append hprefix tailTrace_6654220
  have hstable : (prefixWord ++ tailWord_6654220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654220).length < 2 ^ (prefixWord ++ tailWord_6654220).sum := by decide
  have hdescent : baseEnd_6654220 < baseStart_6654220 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654244 : List Nat := [2, 3, 1, 3, 1, 2, 2, 3, 1, 2, 3]
def baseStart_6654244 : Nat := 118140960795 + 6654244 * 2 ^ 59
def prefixEnd_6654244 : Nat := 4983230072969 + 3 ^ 40 * 6654244 * 2
def baseEnd_6654244 : Nat := 3416825564296768473447695

theorem tailTrace_6654244 : CollatzResearch.WordTrace tailWord_6654244 prefixEnd_6654244 3416825564296768473447695 := by
  unfold tailWord_6654244
  simp only [CollatzResearch.WordTrace]
  refine ⟨121350108652408958621276893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161800144869878611495035857 121350108652408958621276893)
  ·
    refine ⟨45506290744653359482978835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121350108652408958621276893 45506290744653359482978835)
    ·
      refine ⟨68259436116980039224468253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45506290744653359482978835 68259436116980039224468253)
      ·
        refine ⟨25597288543867514709175595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68259436116980039224468253 25597288543867514709175595)
        ·
          refine ⟨38395932815801272063763393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25597288543867514709175595 38395932815801272063763393)
          ·
            refine ⟨28796949611850954047822545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38395932815801272063763393 28796949611850954047822545)
            ·
              refine ⟨21597712208888215535866909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28796949611850954047822545 21597712208888215535866909)
              ·
                refine ⟨8099142078333080825950091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21597712208888215535866909 8099142078333080825950091)
                ·
                  refine ⟨12148713117499621238925137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8099142078333080825950091 12148713117499621238925137)
                  ·
                    refine ⟨9111534838124715929193853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12148713117499621238925137 9111534838124715929193853)
                    ·
                      refine ⟨3416825564296768473447695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9111534838124715929193853 3416825564296768473447695)
                      ·
                        rfl

theorem cell23_6654244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_6654244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654244 prefixEnd_6654244 := by exact prefixLift 6654244
  have htrace : WordTrace (prefixWord ++ tailWord_6654244) baseStart_6654244 baseEnd_6654244 := by
    simpa [prefixWord, tailWord_6654244, baseEnd_6654244] using wordTrace_append hprefix tailTrace_6654244
  have hstable : (prefixWord ++ tailWord_6654244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654244).length < 2 ^ (prefixWord ++ tailWord_6654244).sum := by decide
  have hdescent : baseEnd_6654244 < baseStart_6654244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654258 : List Nat := [3, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2]
def baseStart_6654258 : Nat := 118140960795 + 6654258 * 2 ^ 59
def prefixEnd_6654258 : Nat := 4983230072969 + 3 ^ 40 * 6654258 * 2
def baseEnd_6654258 : Nat := 3416832753025931418672631

theorem tailTrace_6654258 : CollatzResearch.WordTrace tailWord_6654258 prefixEnd_6654258 3416832753025931418672631 := by
  unfold tailWord_6654258
  simp only [CollatzResearch.WordTrace]
  refine ⟨60675181981691799408390857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161800485284511465089042285 60675181981691799408390857)
  ·
    refine ⟨45506386486268849556293143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60675181981691799408390857 45506386486268849556293143)
    ·
      refine ⟨68259579729403274334439715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45506386486268849556293143 68259579729403274334439715)
      ·
        refine ⟨102389369594104911501659573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68259579729403274334439715 102389369594104911501659573)
        ·
          refine ⟨9599003399447335453280585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102389369594104911501659573 9599003399447335453280585)
          ·
            refine ⟨7199252549585501589960439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9599003399447335453280585 7199252549585501589960439)
            ·
              refine ⟨10798878824378252384940659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7199252549585501589960439 10798878824378252384940659)
              ·
                refine ⟨16198318236567378577410989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10798878824378252384940659 16198318236567378577410989)
                ·
                  refine ⟨6074369338712766966529121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16198318236567378577410989 6074369338712766966529121)
                  ·
                    refine ⟨4555777004034575224896841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6074369338712766966529121 4555777004034575224896841)
                    ·
                      refine ⟨3416832753025931418672631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4555777004034575224896841 3416832753025931418672631)
                      ·
                        rfl

theorem cell23_6654258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2].length) (baseStart_6654258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654258 prefixEnd_6654258 := by exact prefixLift 6654258
  have htrace : WordTrace (prefixWord ++ tailWord_6654258) baseStart_6654258 baseEnd_6654258 := by
    simpa [prefixWord, tailWord_6654258, baseEnd_6654258] using wordTrace_append hprefix tailTrace_6654258
  have hstable : (prefixWord ++ tailWord_6654258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654258).length < 2 ^ (prefixWord ++ tailWord_6654258).sum := by decide
  have hdescent : baseEnd_6654258 < baseStart_6654258 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654284 : List Nat := [2, 2, 1, 3, 2, 1, 3, 1, 3, 3, 2]
def baseStart_6654284 : Nat := 118140960795 + 6654284 * 2 ^ 59
def prefixEnd_6654284 : Nat := 4983230072969 + 3 ^ 40 * 6654284 * 2
def baseEnd_6654284 : Nat := 3416846103522948316947511

theorem tailTrace_6654284 : CollatzResearch.WordTrace tailWord_6654284 prefixEnd_6654284 3416846103522948316947511 := by
  unfold tailWord_6654284
  simp only [CollatzResearch.WordTrace]
  refine ⟨121350838112336502037004953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161801117483115336049339937 121350838112336502037004953)
  ·
    refine ⟨91013128584252376527753715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121350838112336502037004953 91013128584252376527753715)
    ·
      refine ⟨136519692876378564791630573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91013128584252376527753715 136519692876378564791630573)
      ·
        refine ⟨51194884828641961796861465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136519692876378564791630573 51194884828641961796861465)
        ·
          refine ⟨38396163621481471347646099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51194884828641961796861465 38396163621481471347646099)
          ·
            refine ⟨57594245432222207021469149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38396163621481471347646099 57594245432222207021469149)
            ·
              refine ⟨21597842037083327633050931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57594245432222207021469149 21597842037083327633050931)
              ·
                refine ⟨32396763055624991449576397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21597842037083327633050931 32396763055624991449576397)
                ·
                  refine ⟨12148786145859371793591149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32396763055624991449576397 12148786145859371793591149)
                  ·
                    refine ⟨4555794804697264422596681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12148786145859371793591149 4555794804697264422596681)
                    ·
                      refine ⟨3416846103522948316947511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4555794804697264422596681 3416846103522948316947511)
                      ·
                        rfl

theorem cell23_6654284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 3, 3, 2].length) (baseStart_6654284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654284 prefixEnd_6654284 := by exact prefixLift 6654284
  have htrace : WordTrace (prefixWord ++ tailWord_6654284) baseStart_6654284 baseEnd_6654284 := by
    simpa [prefixWord, tailWord_6654284, baseEnd_6654284] using wordTrace_append hprefix tailTrace_6654284
  have hstable : (prefixWord ++ tailWord_6654284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654284).length < 2 ^ (prefixWord ++ tailWord_6654284).sum := by decide
  have hdescent : baseEnd_6654284 < baseStart_6654284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654302 : List Nat := [4, 4, 2, 1, 1, 1, 2, 2, 2, 4]
def baseStart_6654302 : Nat := 118140960795 + 6654302 * 2 ^ 59
def prefixEnd_6654302 : Nat := 4983230072969 + 3 ^ 40 * 6654302 * 2
def baseEnd_6654302 : Nat := 1138951782058243082174143

theorem tailTrace_6654302 : CollatzResearch.WordTrace tailWord_6654302 prefixEnd_6654302 1138951782058243082174143 := by
  unfold tailWord_6654302
  simp only [CollatzResearch.WordTrace]
  refine ⟨30337791592325974143520645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161801555159071862098776773 30337791592325974143520645)
  ·
    refine ⟨5688335923561120151910121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30337791592325974143520645 5688335923561120151910121)
    ·
      refine ⟨4266251942670840113932591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5688335923561120151910121 4266251942670840113932591)
      ·
        refine ⟨6399377914006260170898887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4266251942670840113932591 6399377914006260170898887)
        ·
          refine ⟨9599066871009390256348331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6399377914006260170898887 9599066871009390256348331)
          ·
            refine ⟨14398600306514085384522497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9599066871009390256348331 14398600306514085384522497)
            ·
              refine ⟨10798950229885564038391873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14398600306514085384522497 10798950229885564038391873)
              ·
                refine ⟨8099212672414173028793905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10798950229885564038391873 8099212672414173028793905)
                ·
                  refine ⟨6074409504310629771595429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8099212672414173028793905 6074409504310629771595429)
                  ·
                    refine ⟨1138951782058243082174143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6074409504310629771595429 1138951782058243082174143)
                    ·
                      rfl

theorem cell23_6654302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_6654302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654302 prefixEnd_6654302 := by exact prefixLift 6654302
  have htrace : WordTrace (prefixWord ++ tailWord_6654302) baseStart_6654302 baseEnd_6654302 := by
    simpa [prefixWord, tailWord_6654302, baseEnd_6654302] using wordTrace_append hprefix tailTrace_6654302
  have hstable : (prefixWord ++ tailWord_6654302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654302).length < 2 ^ (prefixWord ++ tailWord_6654302).sum := by decide
  have hdescent : baseEnd_6654302 < baseStart_6654302 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654317 : List Nat := [1, 5, 1, 1, 1, 2, 1, 1, 1, 6, 3]
def baseStart_6654317 : Nat := 118140960795 + 6654317 * 2 ^ 59
def prefixEnd_6654317 : Nat := 4983230072969 + 3 ^ 40 * 6654317 * 2
def baseEnd_6654317 : Nat := 3416863048384546687834859

theorem tailTrace_6654317 : CollatzResearch.WordTrace tailWord_6654317 prefixEnd_6654317 3416863048384546687834859 := by
  unfold tailWord_6654317
  simp only [CollatzResearch.WordTrace]
  refine ⟨242702879833553450709961205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161801919889035633806640803 242702879833553450709961205)
  ·
    refine ⟨22753394984395636004058863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 242702879833553450709961205 22753394984395636004058863)
    ·
      refine ⟨34130092476593454006088295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22753394984395636004058863 34130092476593454006088295)
      ·
        refine ⟨51195138714890181009132443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34130092476593454006088295 51195138714890181009132443)
        ·
          refine ⟨76792708072335271513698665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51195138714890181009132443 76792708072335271513698665)
          ·
            refine ⟨57594531054251453635273999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76792708072335271513698665 57594531054251453635273999)
            ·
              refine ⟨86391796581377180452910999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57594531054251453635273999 86391796581377180452910999)
              ·
                refine ⟨129587694872065770679366499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86391796581377180452910999 129587694872065770679366499)
                ·
                  refine ⟨194381542308098656019049749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129587694872065770679366499 194381542308098656019049749)
                  ·
                    refine ⟨9111634795692124500892957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 194381542308098656019049749 9111634795692124500892957)
                    ·
                      refine ⟨3416863048384546687834859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9111634795692124500892957 3416863048384546687834859)
                      ·
                        rfl

theorem cell23_6654317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_6654317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654317 prefixEnd_6654317 := by exact prefixLift 6654317
  have htrace : WordTrace (prefixWord ++ tailWord_6654317) baseStart_6654317 baseEnd_6654317 := by
    simpa [prefixWord, tailWord_6654317, baseEnd_6654317] using wordTrace_append hprefix tailTrace_6654317
  have hstable : (prefixWord ++ tailWord_6654317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654317).length < 2 ^ (prefixWord ++ tailWord_6654317).sum := by decide
  have hdescent : baseEnd_6654317 < baseStart_6654317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654331 : List Nat := [1, 1, 1, 1, 1, 7, 2, 3, 2, 2, 2]
def baseStart_6654331 : Nat := 118140960795 + 6654331 * 2 ^ 59
def prefixEnd_6654331 : Nat := 4983230072969 + 3 ^ 40 * 6654331 * 2
def baseEnd_6654331 : Nat := 3416870237113709633059795

theorem tailTrace_6654331 : CollatzResearch.WordTrace tailWord_6654331 prefixEnd_6654331 3416870237113709633059795 := by
  unfold tailWord_6654331
  simp only [CollatzResearch.WordTrace]
  refine ⟨242703390455502731100970847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161802260303668487400647231 242703390455502731100970847)
  ·
    refine ⟨364055085683254096651456271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242703390455502731100970847 364055085683254096651456271)
    ·
      refine ⟨546082628524881144977184407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364055085683254096651456271 546082628524881144977184407)
      ·
        refine ⟨819123942787321717465776611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 546082628524881144977184407 819123942787321717465776611)
        ·
          refine ⟨1228685914180982576198664917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 819123942787321717465776611 1228685914180982576198664917)
          ·
            refine ⟨28797326113616779129656209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1228685914180982576198664917 28797326113616779129656209)
            ·
              refine ⟨21597994585212584347242157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28797326113616779129656209 21597994585212584347242157)
              ·
                refine ⟨8099247969454719130215809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21597994585212584347242157 8099247969454719130215809)
                ·
                  refine ⟨6074435977091039347661857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8099247969454719130215809 6074435977091039347661857)
                  ·
                    refine ⟨4555826982818279510746393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6074435977091039347661857 4555826982818279510746393)
                    ·
                      refine ⟨3416870237113709633059795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4555826982818279510746393 3416870237113709633059795)
                      ·
                        rfl

theorem cell23_6654331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 3, 2, 2, 2].length) (baseStart_6654331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654331 prefixEnd_6654331 := by exact prefixLift 6654331
  have htrace : WordTrace (prefixWord ++ tailWord_6654331) baseStart_6654331 baseEnd_6654331 := by
    simpa [prefixWord, tailWord_6654331, baseEnd_6654331] using wordTrace_append hprefix tailTrace_6654331
  have hstable : (prefixWord ++ tailWord_6654331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654331).length < 2 ^ (prefixWord ++ tailWord_6654331).sum := by decide
  have hdescent : baseEnd_6654331 < baseStart_6654331 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654337 : List Nat := [1, 2, 4, 3, 1, 1, 1, 1, 9]
def baseStart_6654337 : Nat := 118140960795 + 6654337 * 2 ^ 59
def prefixEnd_6654337 : Nat := 4983230072969 + 3 ^ 40 * 6654337 * 2
def baseEnd_6654337 : Nat := 379652590888626289953863

theorem tailTrace_6654337 : CollatzResearch.WordTrace tailWord_6654337 prefixEnd_6654337 379652590888626289953863 := by
  unfold tailWord_6654337
  simp only [CollatzResearch.WordTrace]
  refine ⟨242703609293480994125689265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161802406195653996083792843 242703609293480994125689265)
  ·
    refine ⟨182027706970110745594266949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242703609293480994125689265 182027706970110745594266949)
    ·
      refine ⟨34130195056895764798925053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182027706970110745594266949 34130195056895764798925053)
      ·
        refine ⟨12798823146335911799596895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34130195056895764798925053 12798823146335911799596895)
        ·
          refine ⟨19198234719503867699395343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12798823146335911799596895 19198234719503867699395343)
          ·
            refine ⟨28797352079255801549093015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19198234719503867699395343 28797352079255801549093015)
            ·
              refine ⟨43196028118883702323639523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28797352079255801549093015 43196028118883702323639523)
              ·
                refine ⟨64794042178325553485459285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43196028118883702323639523 64794042178325553485459285)
                ·
                  refine ⟨379652590888626289953863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 64794042178325553485459285 379652590888626289953863)
                  ·
                    rfl

theorem cell23_6654337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 9].length) (baseStart_6654337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654337 prefixEnd_6654337 := by exact prefixLift 6654337
  have htrace : WordTrace (prefixWord ++ tailWord_6654337) baseStart_6654337 baseEnd_6654337 := by
    simpa [prefixWord, tailWord_6654337, baseEnd_6654337] using wordTrace_append hprefix tailTrace_6654337
  have hstable : (prefixWord ++ tailWord_6654337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654337).length < 2 ^ (prefixWord ++ tailWord_6654337).sum := by decide
  have hdescent : baseEnd_6654337 < baseStart_6654337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654365 : List Nat := [1, 4, 2, 1, 4, 2, 1, 2, 2, 2, 2]
def baseStart_6654365 : Nat := 118140960795 + 6654365 * 2 ^ 59
def prefixEnd_6654365 : Nat := 4983230072969 + 3 ^ 40 * 6654365 * 2
def baseEnd_6654365 : Nat := 3416887695455962500034639

theorem tailTrace_6654365 : CollatzResearch.WordTrace tailWord_6654365 prefixEnd_6654365 3416887695455962500034639 := by
  unfold tailWord_6654365
  simp only [CollatzResearch.WordTrace]
  refine ⟨242704630537379554907708549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161803087024919703271805699 242704630537379554907708549)
  ·
    refine ⟨45507118225758666545195353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 242704630537379554907708549 45507118225758666545195353)
    ·
      refine ⟨34130338669318999908896515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45507118225758666545195353 34130338669318999908896515)
      ·
        refine ⟨51195508003978499863344773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34130338669318999908896515 51195508003978499863344773)
        ·
          refine ⟨9599157750745968724377145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51195508003978499863344773 9599157750745968724377145)
          ·
            refine ⟨7199368313059476543282859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9599157750745968724377145 7199368313059476543282859)
            ·
              refine ⟨10799052469589214814924289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7199368313059476543282859 10799052469589214814924289)
              ·
                refine ⟨8099289352191911111193217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10799052469589214814924289 8099289352191911111193217)
                ·
                  refine ⟨6074467014143933333394913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8099289352191911111193217 6074467014143933333394913)
                  ·
                    refine ⟨4555850260607950000046185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6074467014143933333394913 4555850260607950000046185)
                    ·
                      refine ⟨3416887695455962500034639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4555850260607950000046185 3416887695455962500034639)
                      ·
                        rfl

theorem cell23_6654365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 2, 2, 2, 2].length) (baseStart_6654365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654365 prefixEnd_6654365 := by exact prefixLift 6654365
  have htrace : WordTrace (prefixWord ++ tailWord_6654365) baseStart_6654365 baseEnd_6654365 := by
    simpa [prefixWord, tailWord_6654365, baseEnd_6654365] using wordTrace_append hprefix tailTrace_6654365
  have hstable : (prefixWord ++ tailWord_6654365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654365).length < 2 ^ (prefixWord ++ tailWord_6654365).sum := by decide
  have hdescent : baseEnd_6654365 < baseStart_6654365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654367 : List Nat := [1, 1, 2, 5, 1, 1, 2, 1, 4, 5]
def baseStart_6654367 : Nat := 118140960795 + 6654367 * 2 ^ 59
def prefixEnd_6654367 : Nat := 4983230072969 + 3 ^ 40 * 6654367 * 2
def baseEnd_6654367 : Nat := 1138962907472423830736543

theorem tailTrace_6654367 : CollatzResearch.WordTrace tailWord_6654367 prefixEnd_6654367 1138962907472423830736543 := by
  unfold tailWord_6654367
  simp only [CollatzResearch.WordTrace]
  refine ⟨242704703483372309249281355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161803135655581539499520903 242704703483372309249281355)
  ·
    refine ⟨364057055225058463873922033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242704703483372309249281355 364057055225058463873922033)
    ·
      refine ⟨273042791418793847905441525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364057055225058463873922033 273042791418793847905441525)
      ·
        refine ⟨25597761695511923241135143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 273042791418793847905441525 25597761695511923241135143)
        ·
          refine ⟨38396642543267884861702715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25597761695511923241135143 38396642543267884861702715)
          ·
            refine ⟨57594963814901827292554073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38396642543267884861702715 57594963814901827292554073)
            ·
              refine ⟨43196222861176370469415555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57594963814901827292554073 43196222861176370469415555)
              ·
                refine ⟨64794334291764555704123333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43196222861176370469415555 64794334291764555704123333)
                ·
                  refine ⟨12148937679705854194523125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64794334291764555704123333 12148937679705854194523125)
                  ·
                    refine ⟨1138962907472423830736543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12148937679705854194523125 1138962907472423830736543)
                    ·
                      rfl

theorem cell23_6654367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 4, 5].length) (baseStart_6654367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654367 prefixEnd_6654367 := by exact prefixLift 6654367
  have htrace : WordTrace (prefixWord ++ tailWord_6654367) baseStart_6654367 baseEnd_6654367 := by
    simpa [prefixWord, tailWord_6654367, baseEnd_6654367] using wordTrace_append hprefix tailTrace_6654367
  have hstable : (prefixWord ++ tailWord_6654367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654367).length < 2 ^ (prefixWord ++ tailWord_6654367).sum := by decide
  have hdescent : baseEnd_6654367 < baseStart_6654367 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654431 : List Nat := [1, 1, 2, 3, 3, 4, 1, 1, 3, 4]
def baseStart_6654431 : Nat := 118140960795 + 6654431 * 2 ^ 59
def prefixEnd_6654431 : Nat := 4983230072969 + 3 ^ 40 * 6654431 * 2
def baseEnd_6654431 : Nat := 1138973861726386413936445

theorem tailTrace_6654431 : CollatzResearch.WordTrace tailWord_6654431 prefixEnd_6654431 1138973861726386413936445 := by
  unfold tailWord_6654431
  simp only [CollatzResearch.WordTrace]
  refine ⟨242707037755140448179611147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161804691836760298786407431 242707037755140448179611147)
  ·
    refine ⟨364060556632710672269416721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242707037755140448179611147 364060556632710672269416721)
    ·
      refine ⟨273045417474533004202062541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364060556632710672269416721 273045417474533004202062541)
      ·
        refine ⟨102392031552949876575773453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273045417474533004202062541 102392031552949876575773453)
        ·
          refine ⟨38397011832356203715915045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102392031552949876575773453 38397011832356203715915045)
          ·
            refine ⟨7199439718566788196734071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38397011832356203715915045 7199439718566788196734071)
            ·
              refine ⟨10799159577850182295101107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7199439718566788196734071 10799159577850182295101107)
              ·
                refine ⟨16198739366775273442651661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10799159577850182295101107 16198739366775273442651661)
                ·
                  refine ⟨6074527262540727540994373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16198739366775273442651661 6074527262540727540994373)
                  ·
                    refine ⟨1138973861726386413936445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6074527262540727540994373 1138973861726386413936445)
                    ·
                      rfl

theorem cell23_6654431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 3, 4].length) (baseStart_6654431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654431 prefixEnd_6654431 := by exact prefixLift 6654431
  have htrace : WordTrace (prefixWord ++ tailWord_6654431) baseStart_6654431 baseEnd_6654431 := by
    simpa [prefixWord, tailWord_6654431, baseEnd_6654431] using wordTrace_append hprefix tailTrace_6654431
  have hstable : (prefixWord ++ tailWord_6654431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654431).length < 2 ^ (prefixWord ++ tailWord_6654431).sum := by decide
  have hdescent : baseEnd_6654431 < baseStart_6654431 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654507 : List Nat := [1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 6]
def baseStart_6654507 : Nat := 118140960795 + 6654507 * 2 ^ 59
def prefixEnd_6654507 : Nat := 4983230072969 + 3 ^ 40 * 6654507 * 2
def baseEnd_6654507 : Nat := 3416960609708900944458985

theorem tailTrace_6654507 : CollatzResearch.WordTrace tailWord_6654507 prefixEnd_6654507 3416960609708900944458985 := by
  unfold tailWord_6654507
  simp only [CollatzResearch.WordTrace]
  refine ⟨242709809702865113159377775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161806539801910075439585183 242709809702865113159377775)
  ·
    refine ⟨364064714554297669739066663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242709809702865113159377775 364064714554297669739066663)
    ·
      refine ⟨546097071831446504608599995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364064714554297669739066663 546097071831446504608599995)
      ·
        refine ⟨819145607747169756912899993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 546097071831446504608599995 819145607747169756912899993)
        ·
          refine ⟨614359205810377317684674995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 819145607747169756912899993 614359205810377317684674995)
          ·
            refine ⟨921538808715565976527012493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 614359205810377317684674995 921538808715565976527012493)
            ·
              refine ⟨345577053268337241197629685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 921538808715565976527012493 345577053268337241197629685)
              ·
                refine ⟨32397848743906616362277783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 345577053268337241197629685 32397848743906616362277783)
                ·
                  refine ⟨48596773115859924543416675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32397848743906616362277783 48596773115859924543416675)
                  ·
                    refine ⟨72895159673789886815125013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48596773115859924543416675 72895159673789886815125013)
                    ·
                      refine ⟨3416960609708900944458985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72895159673789886815125013 3416960609708900944458985)
                      ·
                        rfl

theorem cell23_6654507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 6].length) (baseStart_6654507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654507 prefixEnd_6654507 := by exact prefixLift 6654507
  have htrace : WordTrace (prefixWord ++ tailWord_6654507) baseStart_6654507 baseEnd_6654507 := by
    simpa [prefixWord, tailWord_6654507, baseEnd_6654507] using wordTrace_append hprefix tailTrace_6654507
  have hstable : (prefixWord ++ tailWord_6654507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654507).length < 2 ^ (prefixWord ++ tailWord_6654507).sum := by decide
  have hdescent : baseEnd_6654507 < baseStart_6654507 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654509 : List Nat := [1, 5, 4, 1, 2, 1, 1, 1, 2, 2, 3]
def baseStart_6654509 : Nat := 118140960795 + 6654509 * 2 ^ 59
def prefixEnd_6654509 : Nat := 4983230072969 + 3 ^ 40 * 6654509 * 2
def baseEnd_6654509 : Nat := 3416961636670209936633977

theorem tailTrace_6654509 : CollatzResearch.WordTrace tailWord_6654509 prefixEnd_6654509 3416961636670209936633977 := by
  unfold tailWord_6654509
  simp only [CollatzResearch.WordTrace]
  refine ⟨242709882648857867500950581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161806588432571911667300387 242709882648857867500950581)
  ·
    refine ⟨22754051498330425078214117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 242709882648857867500950581 22754051498330425078214117)
    ·
      refine ⟨4266384655936954702165147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22754051498330425078214117 4266384655936954702165147)
      ·
        refine ⟨6399576983905432053247721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4266384655936954702165147 6399576983905432053247721)
        ·
          refine ⟨4799682737929074039935791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6399576983905432053247721 4799682737929074039935791)
          ·
            refine ⟨7199524106893611059903687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4799682737929074039935791 7199524106893611059903687)
            ·
              refine ⟨10799286160340416589855531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7199524106893611059903687 10799286160340416589855531)
              ·
                refine ⟨16198929240510624884783297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10799286160340416589855531 16198929240510624884783297)
                ·
                  refine ⟨12149196930382968663587473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16198929240510624884783297 12149196930382968663587473)
                  ·
                    refine ⟨9111897697787226497690605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12149196930382968663587473 9111897697787226497690605)
                    ·
                      refine ⟨3416961636670209936633977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9111897697787226497690605 3416961636670209936633977)
                      ·
                        rfl

theorem cell23_6654509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_6654509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654509 prefixEnd_6654509 := by exact prefixLift 6654509
  have htrace : WordTrace (prefixWord ++ tailWord_6654509) baseStart_6654509 baseEnd_6654509 := by
    simpa [prefixWord, tailWord_6654509, baseEnd_6654509] using wordTrace_append hprefix tailTrace_6654509
  have hstable : (prefixWord ++ tailWord_6654509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654509).length < 2 ^ (prefixWord ++ tailWord_6654509).sum := by decide
  have hdescent : baseEnd_6654509 < baseStart_6654509 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654537 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 4, 2, 6]
def baseStart_6654537 : Nat := 118140960795 + 6654537 * 2 ^ 59
def prefixEnd_6654537 : Nat := 4983230072969 + 3 ^ 40 * 6654537 * 2
def baseEnd_6654537 : Nat := 3416976014128535827083847

theorem tailTrace_6654537 : CollatzResearch.WordTrace tailWord_6654537 prefixEnd_6654537 3416976014128535827083847 := by
  unfold tailWord_6654537
  simp only [CollatzResearch.WordTrace]
  refine ⟨242710903892756428282969865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161807269261837618855313243 242710903892756428282969865)
  ·
    refine ⟨182033177919567321212227399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242710903892756428282969865 182033177919567321212227399)
    ·
      refine ⟨273049766879350981818341099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182033177919567321212227399 273049766879350981818341099)
      ·
        refine ⟨409574650319026472727511649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273049766879350981818341099 409574650319026472727511649)
        ·
          refine ⟨307180987739269854545633737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 409574650319026472727511649 307180987739269854545633737)
          ·
            refine ⟨230385740804452390909225303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 307180987739269854545633737 230385740804452390909225303)
            ·
              refine ⟨345578611206678586363837955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230385740804452390909225303 345578611206678586363837955)
              ·
                refine ⟨518367916810017879545756933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 345578611206678586363837955 518367916810017879545756933)
                ·
                  refine ⟨97193984401878352414829425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 518367916810017879545756933 97193984401878352414829425)
                  ·
                    refine ⟨72895488301408764311122069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 97193984401878352414829425 72895488301408764311122069)
                    ·
                      refine ⟨3416976014128535827083847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72895488301408764311122069 3416976014128535827083847)
                      ·
                        rfl

theorem cell23_6654537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 2, 6].length) (baseStart_6654537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654537 prefixEnd_6654537 := by exact prefixLift 6654537
  have htrace : WordTrace (prefixWord ++ tailWord_6654537) baseStart_6654537 baseEnd_6654537 := by
    simpa [prefixWord, tailWord_6654537, baseEnd_6654537] using wordTrace_append hprefix tailTrace_6654537
  have hstable : (prefixWord ++ tailWord_6654537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654537).length < 2 ^ (prefixWord ++ tailWord_6654537).sum := by decide
  have hdescent : baseEnd_6654537 < baseStart_6654537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654538 : List Nat := [3, 1, 2, 1, 1, 6, 1, 2, 2, 4]
def baseStart_6654538 : Nat := 118140960795 + 6654538 * 2 ^ 59
def prefixEnd_6654538 : Nat := 4983230072969 + 3 ^ 40 * 6654538 * 2
def baseEnd_6654538 : Nat := 1138992175869730107723781

theorem tailTrace_6654538 : CollatzResearch.WordTrace tailWord_6654538 prefixEnd_6654538 1138992175869730107723781 := by
  unfold tailWord_6654538
  simp only [CollatzResearch.WordTrace]
  refine ⟨60677735091438201363439067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161807293577168536969170845 60677735091438201363439067)
  ·
    refine ⟨91016602637157302045158601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60677735091438201363439067 91016602637157302045158601)
    ·
      refine ⟨68262451977867976533868951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91016602637157302045158601 68262451977867976533868951)
      ·
        refine ⟨102393677966801964800803427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68262451977867976533868951 102393677966801964800803427)
        ·
          refine ⟨153590516950202947201205141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102393677966801964800803427 153590516950202947201205141)
          ·
            refine ⟨7199555482040763150056491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 153590516950202947201205141 7199555482040763150056491)
            ·
              refine ⟨10799333223061144725084737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7199555482040763150056491 10799333223061144725084737)
              ·
                refine ⟨8099499917295858543813553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10799333223061144725084737 8099499917295858543813553)
                ·
                  refine ⟨6074624937971893907860165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8099499917295858543813553 6074624937971893907860165)
                  ·
                    refine ⟨1138992175869730107723781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6074624937971893907860165 1138992175869730107723781)
                    ·
                      rfl

theorem cell23_6654538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 2, 2, 4].length) (baseStart_6654538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654538 prefixEnd_6654538 := by exact prefixLift 6654538
  have htrace : WordTrace (prefixWord ++ tailWord_6654538) baseStart_6654538 baseEnd_6654538 := by
    simpa [prefixWord, tailWord_6654538, baseEnd_6654538] using wordTrace_append hprefix tailTrace_6654538
  have hstable : (prefixWord ++ tailWord_6654538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654538).length < 2 ^ (prefixWord ++ tailWord_6654538).sum := by decide
  have hdescent : baseEnd_6654538 < baseStart_6654538 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654545 : List Nat := [1, 2, 2, 1, 3, 3, 2, 4, 1, 2, 2]
def baseStart_6654545 : Nat := 118140960795 + 6654545 * 2 ^ 59
def prefixEnd_6654545 : Nat := 4983230072969 + 3 ^ 40 * 6654545 * 2
def baseEnd_6654545 : Nat := 3416980121973771795783811

theorem tailTrace_6654545 : CollatzResearch.WordTrace tailWord_6654545 prefixEnd_6654545 3416980121973771795783811 := by
  unfold tailWord_6654545
  simp only [CollatzResearch.WordTrace]
  refine ⟨242711195676727445649261089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161807463784484963766174059 242711195676727445649261089)
  ·
    refine ⟨182033396757545584236945817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242711195676727445649261089 182033396757545584236945817)
    ·
      refine ⟨136525047568159188177709363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182033396757545584236945817 136525047568159188177709363)
      ·
        refine ⟨204787571352238782266564045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136525047568159188177709363 204787571352238782266564045)
        ·
          refine ⟨76795339257089543349961517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204787571352238782266564045 76795339257089543349961517)
          ·
            refine ⟨28798252221408578756235569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76795339257089543349961517 28798252221408578756235569)
            ·
              refine ⟨21598689166056434067176677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28798252221408578756235569 21598689166056434067176677)
              ·
                refine ⟨4049754218635581387595627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21598689166056434067176677 4049754218635581387595627)
                ·
                  refine ⟨6074631327953372081393441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4049754218635581387595627 6074631327953372081393441)
                  ·
                    refine ⟨4555973495965029061045081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6074631327953372081393441 4555973495965029061045081)
                    ·
                      refine ⟨3416980121973771795783811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4555973495965029061045081 3416980121973771795783811)
                      ·
                        rfl

theorem cell23_6654545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 4, 1, 2, 2].length) (baseStart_6654545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654545 prefixEnd_6654545 := by exact prefixLift 6654545
  have htrace : WordTrace (prefixWord ++ tailWord_6654545) baseStart_6654545 baseEnd_6654545 := by
    simpa [prefixWord, tailWord_6654545, baseEnd_6654545] using wordTrace_append hprefix tailTrace_6654545
  have hstable : (prefixWord ++ tailWord_6654545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654545).length < 2 ^ (prefixWord ++ tailWord_6654545).sum := by decide
  have hdescent : baseEnd_6654545 < baseStart_6654545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654561 : List Nat := [1, 2, 3, 1, 1, 4, 3, 1, 1, 3, 3]
def baseStart_6654561 : Nat := 118140960795 + 6654561 * 2 ^ 59
def prefixEnd_6654561 : Nat := 4983230072969 + 3 ^ 40 * 6654561 * 2
def baseEnd_6654561 : Nat := 3416988337664243733183737

theorem tailTrace_6654561 : CollatzResearch.WordTrace tailWord_6654561 prefixEnd_6654561 3416988337664243733183737 := by
  unfold tailWord_6654561
  simp only [CollatzResearch.WordTrace]
  refine ⟨242711779244669480381843537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161807852829779653587895691 242711779244669480381843537)
  ·
    refine ⟨182033834433502110286382653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242711779244669480381843537 182033834433502110286382653)
    ·
      refine ⟨68262687912563291357393495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182033834433502110286382653 68262687912563291357393495)
      ·
        refine ⟨102394031868844937036090243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68262687912563291357393495 102394031868844937036090243)
        ·
          refine ⟨153591047803267405554135365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102394031868844937036090243 153591047803267405554135365)
          ·
            refine ⟨28798321463112638541400381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153591047803267405554135365 28798321463112638541400381)
            ·
              refine ⟨10799370548667239453025143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28798321463112638541400381 10799370548667239453025143)
              ·
                refine ⟨16199055823000859179537715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10799370548667239453025143 16199055823000859179537715)
                ·
                  refine ⟨24298583734501288769306573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16199055823000859179537715 24298583734501288769306573)
                  ·
                    refine ⟨9111968900437983288489965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24298583734501288769306573 9111968900437983288489965)
                    ·
                      refine ⟨3416988337664243733183737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9111968900437983288489965 3416988337664243733183737)
                      ·
                        rfl

theorem cell23_6654561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 3, 3].length) (baseStart_6654561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654561 prefixEnd_6654561 := by exact prefixLift 6654561
  have htrace : WordTrace (prefixWord ++ tailWord_6654561) baseStart_6654561 baseEnd_6654561 := by
    simpa [prefixWord, tailWord_6654561, baseEnd_6654561] using wordTrace_append hprefix tailTrace_6654561
  have hstable : (prefixWord ++ tailWord_6654561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654561).length < 2 ^ (prefixWord ++ tailWord_6654561).sum := by decide
  have hdescent : baseEnd_6654561 < baseStart_6654561 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654568 : List Nat := [2, 1, 4, 3, 2, 2, 2, 7]
def baseStart_6654568 : Nat := 118140960795 + 6654568 * 2 ^ 59
def prefixEnd_6654568 : Nat := 4983230072969 + 3 ^ 40 * 6654568 * 2
def baseEnd_6654568 : Nat := 126555256741808340955415

theorem tailTrace_6654568 : CollatzResearch.WordTrace tailWord_6654568 prefixEnd_6654568 126555256741808340955415 := by
  unfold tailWord_6654568
  simp only [CollatzResearch.WordTrace]
  refine ⟨121356017277822060288674179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161808023037096080384898905 121356017277822060288674179)
  ·
    refine ⟨182034025916733090433011269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121356017277822060288674179 182034025916733090433011269)
    ·
      refine ⟨34131379859387454456189613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182034025916733090433011269 34131379859387454456189613)
      ·
        refine ⟨12799267447270295421071105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34131379859387454456189613 12799267447270295421071105)
        ·
          refine ⟨9599450585452721565803329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12799267447270295421071105 9599450585452721565803329)
          ·
            refine ⟨7199587939089541174352497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9599450585452721565803329 7199587939089541174352497)
            ·
              refine ⟨5399690954317155880764373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7199587939089541174352497 5399690954317155880764373)
              ·
                refine ⟨126555256741808340955415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5399690954317155880764373 126555256741808340955415)
                ·
                  rfl

theorem cell23_6654568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 7].length) (baseStart_6654568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654568 prefixEnd_6654568 := by exact prefixLift 6654568
  have htrace : WordTrace (prefixWord ++ tailWord_6654568) baseStart_6654568 baseEnd_6654568 := by
    simpa [prefixWord, tailWord_6654568, baseEnd_6654568] using wordTrace_append hprefix tailTrace_6654568
  have hstable : (prefixWord ++ tailWord_6654568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654568).length < 2 ^ (prefixWord ++ tailWord_6654568).sum := by decide
  have hdescent : baseEnd_6654568 < baseStart_6654568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654588 : List Nat := [2, 2, 2, 1, 1, 2, 4, 3, 1, 3, 2]
def baseStart_6654588 : Nat := 118140960795 + 6654588 * 2 ^ 59
def prefixEnd_6654588 : Nat := 4983230072969 + 3 ^ 40 * 6654588 * 2
def baseEnd_6654588 : Nat := 3417002201641915127546113

theorem tailTrace_6654588 : CollatzResearch.WordTrace tailWord_6654588 prefixEnd_6654588 3417002201641915127546113 := by
  unfold tailWord_6654588
  simp only [CollatzResearch.WordTrace]
  refine ⟨121356382007785831996538209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161808509343714442662050945 121356382007785831996538209)
  ·
    refine ⟨91017286505839373997403657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121356382007785831996538209 91017286505839373997403657)
    ·
      refine ⟨68262964879379530498052743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91017286505839373997403657 68262964879379530498052743)
      ·
        refine ⟨102394447319069295747079115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68262964879379530498052743 102394447319069295747079115)
        ·
          refine ⟨153591670978603943620618673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102394447319069295747079115 153591670978603943620618673)
          ·
            refine ⟨115193753233952957715464005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153591670978603943620618673 115193753233952957715464005)
            ·
              refine ⟨21598828731366179571649501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115193753233952957715464005 21598828731366179571649501)
              ·
                refine ⟨8099560774262317339368563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21598828731366179571649501 8099560774262317339368563)
                ·
                  refine ⟨12149341161393476009052845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8099560774262317339368563 12149341161393476009052845)
                  ·
                    refine ⟨4556002935522553503394817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12149341161393476009052845 4556002935522553503394817)
                    ·
                      refine ⟨3417002201641915127546113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4556002935522553503394817 3417002201641915127546113)
                      ·
                        rfl

theorem cell23_6654588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 3, 1, 3, 2].length) (baseStart_6654588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654588 prefixEnd_6654588 := by exact prefixLift 6654588
  have htrace : WordTrace (prefixWord ++ tailWord_6654588) baseStart_6654588 baseEnd_6654588 := by
    simpa [prefixWord, tailWord_6654588, baseEnd_6654588] using wordTrace_append hprefix tailTrace_6654588
  have hstable : (prefixWord ++ tailWord_6654588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654588).length < 2 ^ (prefixWord ++ tailWord_6654588).sum := by decide
  have hdescent : baseEnd_6654588 < baseStart_6654588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654612 : List Nat := [2, 4, 2, 2, 1, 1, 4, 1, 2, 1, 3]
def baseStart_6654612 : Nat := 118140960795 + 6654612 * 2 ^ 59
def prefixEnd_6654612 : Nat := 4983230072969 + 3 ^ 40 * 6654612 * 2
def baseEnd_6654612 : Nat := 3417014525177623033646003

theorem tailTrace_6654612 : CollatzResearch.WordTrace tailWord_6654612 prefixEnd_6654612 3417014525177623033646003 := by
  unfold tailWord_6654612
  simp only [CollatzResearch.WordTrace]
  refine ⟨121356819683742358045975045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161809092911656477394633393 121356819683742358045975045)
  ·
    refine ⟨22754403690701692133620321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121356819683742358045975045 22754403690701692133620321)
    ·
      refine ⟨17065802768026269100215241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22754403690701692133620321 17065802768026269100215241)
      ·
        refine ⟨12799352076019701825161431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17065802768026269100215241 12799352076019701825161431)
        ·
          refine ⟨19199028114029552737742147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12799352076019701825161431 19199028114029552737742147)
          ·
            refine ⟨28798542171044329106613221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19199028114029552737742147 28798542171044329106613221)
            ·
              refine ⟨5399726657070811707489979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28798542171044329106613221 5399726657070811707489979)
              ·
                refine ⟨8099589985606217561234969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5399726657070811707489979 8099589985606217561234969)
                ·
                  refine ⟨6074692489204663170926227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8099589985606217561234969 6074692489204663170926227)
                  ·
                    refine ⟨9112038733806994756389341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6074692489204663170926227 9112038733806994756389341)
                    ·
                      refine ⟨3417014525177623033646003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9112038733806994756389341 3417014525177623033646003)
                      ·
                        rfl

theorem cell23_6654612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_6654612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654612 prefixEnd_6654612 := by exact prefixLift 6654612
  have htrace : WordTrace (prefixWord ++ tailWord_6654612) baseStart_6654612 baseEnd_6654612 := by
    simpa [prefixWord, tailWord_6654612, baseEnd_6654612] using wordTrace_append hprefix tailTrace_6654612
  have hstable : (prefixWord ++ tailWord_6654612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654612).length < 2 ^ (prefixWord ++ tailWord_6654612).sum := by decide
  have hdescent : baseEnd_6654612 < baseStart_6654612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654638 : List Nat := [4, 1, 4, 1, 1, 1, 2, 1, 2, 1, 5]
def baseStart_6654638 : Nat := 118140960795 + 6654638 * 2 ^ 59
def prefixEnd_6654638 : Nat := 4983230072969 + 3 ^ 40 * 6654638 * 2
def baseEnd_6654638 : Nat := 3417027875674639931920883

theorem tailTrace_6654638 : CollatzResearch.WordTrace tailWord_6654638 prefixEnd_6654638 3417027875674639931920883 := by
  unfold tailWord_6654638
  simp only [CollatzResearch.WordTrace]
  refine ⟨30339323458173815316549571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161809725110260348354931045 30339323458173815316549571)
  ·
    refine ⟨45508985187260722974824357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30339323458173815316549571 45508985187260722974824357)
    ·
      refine ⟨8532934722611385557779567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45508985187260722974824357 8532934722611385557779567)
      ·
        refine ⟨12799402083917078336669351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8532934722611385557779567 12799402083917078336669351)
        ·
          refine ⟨19199103125875617505004027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12799402083917078336669351 19199103125875617505004027)
          ·
            refine ⟨28798654688813426257506041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19199103125875617505004027 28798654688813426257506041)
            ·
              refine ⟨21598991016610069693129531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28798654688813426257506041 21598991016610069693129531)
              ·
                refine ⟨32398486524915104539694297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21598991016610069693129531 32398486524915104539694297)
                ·
                  refine ⟨24298864893686328404770723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32398486524915104539694297 24298864893686328404770723)
                  ·
                    refine ⟨36448297340529492607156085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24298864893686328404770723 36448297340529492607156085)
                    ·
                      refine ⟨3417027875674639931920883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36448297340529492607156085 3417027875674639931920883)
                      ·
                        rfl

theorem cell23_6654638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_6654638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654638 prefixEnd_6654638 := by exact prefixLift 6654638
  have htrace : WordTrace (prefixWord ++ tailWord_6654638) baseStart_6654638 baseEnd_6654638 := by
    simpa [prefixWord, tailWord_6654638, baseEnd_6654638] using wordTrace_append hprefix tailTrace_6654638
  have hstable : (prefixWord ++ tailWord_6654638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654638).length < 2 ^ (prefixWord ++ tailWord_6654638).sum := by decide
  have hdescent : baseEnd_6654638 < baseStart_6654638 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654668 : List Nat := [2, 2, 1, 5, 1, 2, 1, 1, 2, 3, 3]
def baseStart_6654668 : Nat := 118140960795 + 6654668 * 2 ^ 59
def prefixEnd_6654668 : Nat := 4983230072969 + 3 ^ 40 * 6654668 * 2
def baseEnd_6654668 : Nat := 3417043280094274814545745

theorem tailTrace_6654668 : CollatzResearch.WordTrace tailWord_6654668 prefixEnd_6654668 3417043280094274814545745 := by
  unfold tailWord_6654668
  simp only [CollatzResearch.WordTrace]
  refine ⟨121357840927640918827994329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161810454570187891770659105 121357840927640918827994329)
  ·
    refine ⟨91018380695730689120995747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121357840927640918827994329 91018380695730689120995747)
    ·
      refine ⟨136527571043596033681493621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91018380695730689120995747 136527571043596033681493621)
      ·
        refine ⟨12799459785337128157640027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 136527571043596033681493621 12799459785337128157640027)
        ·
          refine ⟨19199189678005692236460041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12799459785337128157640027 19199189678005692236460041)
          ·
            refine ⟨14399392258504269177345031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19199189678005692236460041 14399392258504269177345031)
            ·
              refine ⟨21599088387756403766017547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14399392258504269177345031 21599088387756403766017547)
              ·
                refine ⟨32398632581634605649026321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21599088387756403766017547 32398632581634605649026321)
                ·
                  refine ⟨24298974436225954236769741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32398632581634605649026321 24298974436225954236769741)
                  ·
                    refine ⟨9112115413584732838788653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24298974436225954236769741 9112115413584732838788653)
                    ·
                      refine ⟨3417043280094274814545745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9112115413584732838788653 3417043280094274814545745)
                      ·
                        rfl

theorem cell23_6654668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_6654668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654668 prefixEnd_6654668 := by exact prefixLift 6654668
  have htrace : WordTrace (prefixWord ++ tailWord_6654668) baseStart_6654668 baseEnd_6654668 := by
    simpa [prefixWord, tailWord_6654668, baseEnd_6654668] using wordTrace_append hprefix tailTrace_6654668
  have hstable : (prefixWord ++ tailWord_6654668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654668).length < 2 ^ (prefixWord ++ tailWord_6654668).sum := by decide
  have hdescent : baseEnd_6654668 < baseStart_6654668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654704 : List Nat := [2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 6]
def baseStart_6654704 : Nat := 118140960795 + 6654704 * 2 ^ 59
def prefixEnd_6654704 : Nat := 4983230072969 + 3 ^ 40 * 6654704 * 2
def baseEnd_6654704 : Nat := 3417061765397836673695579

theorem tailTrace_6654704 : CollatzResearch.WordTrace tailWord_6654704 prefixEnd_6654704 3417061765397836673695579 := by
  unfold tailWord_6654704
  simp only [CollatzResearch.WordTrace]
  refine ⟨121358497441575707902149583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161811329922100943869532777 121358497441575707902149583)
  ·
    refine ⟨182037746162363561853224375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121358497441575707902149583 182037746162363561853224375)
    ·
      refine ⟨273056619243545342779836563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182037746162363561853224375 273056619243545342779836563)
      ·
        refine ⟨409584928865318014169754845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273056619243545342779836563 409584928865318014169754845)
        ·
          refine ⟨153594348324494255313658067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 409584928865318014169754845 153594348324494255313658067)
          ·
            refine ⟨230391522486741382970487101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153594348324494255313658067 230391522486741382970487101)
            ·
              refine ⟨86396820932528018613932663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 230391522486741382970487101 86396820932528018613932663)
              ·
                refine ⟨129595231398792027920898995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86396820932528018613932663 129595231398792027920898995)
                ·
                  refine ⟨194392847098188041881348493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129595231398792027920898995 194392847098188041881348493)
                  ·
                    refine ⟨72897317661820515705505685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 194392847098188041881348493 72897317661820515705505685)
                    ·
                      refine ⟨3417061765397836673695579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72897317661820515705505685 3417061765397836673695579)
                      ·
                        rfl

theorem cell23_6654704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 6].length) (baseStart_6654704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654704 prefixEnd_6654704 := by exact prefixLift 6654704
  have htrace : WordTrace (prefixWord ++ tailWord_6654704) baseStart_6654704 baseEnd_6654704 := by
    simpa [prefixWord, tailWord_6654704, baseEnd_6654704] using wordTrace_append hprefix tailTrace_6654704
  have hstable : (prefixWord ++ tailWord_6654704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654704).length < 2 ^ (prefixWord ++ tailWord_6654704).sum := by decide
  have hdescent : baseEnd_6654704 < baseStart_6654704 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654711 : List Nat := [1, 1, 3, 1, 1, 1, 3, 3, 4, 2, 3]
def baseStart_6654711 : Nat := 118140960795 + 6654711 * 2 ^ 59
def prefixEnd_6654711 : Nat := 4983230072969 + 3 ^ 40 * 6654711 * 2
def baseEnd_6654711 : Nat := 3417065359762418146308047

theorem tailTrace_6654711 : CollatzResearch.WordTrace tailWord_6654711 prefixEnd_6654711 3417065359762418146308047 := by
  unfold tailWord_6654711
  simp only [CollatzResearch.WordTrace]
  refine ⟨242717250194126055999803987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161811500129417370666535991 242717250194126055999803987)
  ·
    refine ⟨364075875291189083999705981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242717250194126055999803987 364075875291189083999705981)
    ·
      refine ⟨136528453234195906499889743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 364075875291189083999705981 136528453234195906499889743)
      ·
        refine ⟨204792679851293859749834615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136528453234195906499889743 204792679851293859749834615)
        ·
          refine ⟨307189019776940789624751923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204792679851293859749834615 307189019776940789624751923)
          ·
            refine ⟨460783529665411184437127885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307189019776940789624751923 460783529665411184437127885)
            ·
              refine ⟨172793823624529194163922957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 460783529665411184437127885 172793823624529194163922957)
              ·
                refine ⟨64797683859198447811471109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 172793823624529194163922957 64797683859198447811471109)
                ·
                  refine ⟨12149565723599708964650833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64797683859198447811471109 12149565723599708964650833)
                  ·
                    refine ⟨9112174292699781723488125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12149565723599708964650833 9112174292699781723488125)
                    ·
                      refine ⟨3417065359762418146308047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9112174292699781723488125 3417065359762418146308047)
                      ·
                        rfl

theorem cell23_6654711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 4, 2, 3].length) (baseStart_6654711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654711 prefixEnd_6654711 := by exact prefixLift 6654711
  have htrace : WordTrace (prefixWord ++ tailWord_6654711) baseStart_6654711 baseEnd_6654711 := by
    simpa [prefixWord, tailWord_6654711, baseEnd_6654711] using wordTrace_append hprefix tailTrace_6654711
  have hstable : (prefixWord ++ tailWord_6654711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654711).length < 2 ^ (prefixWord ++ tailWord_6654711).sum := by decide
  have hdescent : baseEnd_6654711 < baseStart_6654711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654741 : List Nat := [1, 3, 2, 1, 2, 2, 1, 1, 2, 5, 3]
def baseStart_6654741 : Nat := 118140960795 + 6654741 * 2 ^ 59
def prefixEnd_6654741 : Nat := 4983230072969 + 3 ^ 40 * 6654741 * 2
def baseEnd_6654741 : Nat := 3417080764182053028932909

theorem tailTrace_6654741 : CollatzResearch.WordTrace tailWord_6654741 prefixEnd_6654741 3417080764182053028932909 := by
  unfold tailWord_6654741
  simp only [CollatzResearch.WordTrace]
  refine ⟨242718344384017371123396077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161812229589344914082264051 242718344384017371123396077)
  ·
    refine ⟨91019379144006514171273529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242718344384017371123396077 91019379144006514171273529)
    ·
      refine ⟨68264534358004885628455147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91019379144006514171273529 68264534358004885628455147)
      ·
        refine ⟨102396801537007328442682721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68264534358004885628455147 102396801537007328442682721)
        ·
          refine ⟨76797601152755496332012041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102396801537007328442682721 76797601152755496332012041)
          ·
            refine ⟨57598200864566622249009031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76797601152755496332012041 57598200864566622249009031)
            ·
              refine ⟨86397301296849933373513547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57598200864566622249009031 86397301296849933373513547)
              ·
                refine ⟨129595951945274900060270321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86397301296849933373513547 129595951945274900060270321)
                ·
                  refine ⟨97196963958956175045202741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129595951945274900060270321 97196963958956175045202741)
                  ·
                    refine ⟨9112215371152141410487757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 97196963958956175045202741 9112215371152141410487757)
                    ·
                      refine ⟨3417080764182053028932909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9112215371152141410487757 3417080764182053028932909)
                      ·
                        rfl

theorem cell23_6654741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 5, 3].length) (baseStart_6654741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654741 prefixEnd_6654741 := by exact prefixLift 6654741
  have htrace : WordTrace (prefixWord ++ tailWord_6654741) baseStart_6654741 baseEnd_6654741 := by
    simpa [prefixWord, tailWord_6654741, baseEnd_6654741] using wordTrace_append hprefix tailTrace_6654741
  have hstable : (prefixWord ++ tailWord_6654741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654741).length < 2 ^ (prefixWord ++ tailWord_6654741).sum := by decide
  have hdescent : baseEnd_6654741 < baseStart_6654741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654752 : List Nat := [2, 1, 1, 5, 1, 4, 1, 3, 1, 4]
def baseStart_6654752 : Nat := 118140960795 + 6654752 * 2 ^ 59
def prefixEnd_6654752 : Nat := 4983230072969 + 3 ^ 40 * 6654752 * 2
def baseEnd_6654752 : Nat := 1139028804156417495298453

theorem tailTrace_6654752 : CollatzResearch.WordTrace tailWord_6654752 prefixEnd_6654752 1139028804156417495298453 := by
  unfold tailWord_6654752
  simp only [CollatzResearch.WordTrace]
  refine ⟨121359372793488760001023255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161812497057985013334697673 121359372793488760001023255)
  ·
    refine ⟨182039059190233140001534883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121359372793488760001023255 182039059190233140001534883)
    ·
      refine ⟨273058588785349710002302325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182039059190233140001534883 273058588785349710002302325)
      ·
        refine ⟨25599242698626535312715843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 273058588785349710002302325 25599242698626535312715843)
        ·
          refine ⟨38398864047939802969073765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25599242698626535312715843 38398864047939802969073765)
          ·
            refine ⟨7199787008988713056701331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38398864047939802969073765 7199787008988713056701331)
            ·
              refine ⟨10799680513483069585051997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7199787008988713056701331 10799680513483069585051997)
              ·
                refine ⟨4049880192556151094394499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10799680513483069585051997 4049880192556151094394499)
                ·
                  refine ⟨6074820288834226641591749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4049880192556151094394499 6074820288834226641591749)
                  ·
                    refine ⟨1139028804156417495298453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6074820288834226641591749 1139028804156417495298453)
                    ·
                      rfl

theorem cell23_6654752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 3, 1, 4].length) (baseStart_6654752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654752 prefixEnd_6654752 := by exact prefixLift 6654752
  have htrace : WordTrace (prefixWord ++ tailWord_6654752) baseStart_6654752 baseEnd_6654752 := by
    simpa [prefixWord, tailWord_6654752, baseEnd_6654752] using wordTrace_append hprefix tailTrace_6654752
  have hstable : (prefixWord ++ tailWord_6654752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654752).length < 2 ^ (prefixWord ++ tailWord_6654752).sum := by decide
  have hdescent : baseEnd_6654752 < baseStart_6654752 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654762 : List Nat := [3, 1, 4, 3, 1, 1, 1, 2, 2, 2, 3]
def baseStart_6654762 : Nat := 118140960795 + 6654762 * 2 ^ 59
def prefixEnd_6654762 : Nat := 4983230072969 + 3 ^ 40 * 6654762 * 2
def baseEnd_6654762 : Nat := 3417091547275797446770313

theorem tailTrace_6654762 : CollatzResearch.WordTrace tailWord_6654762 prefixEnd_6654762 3417091547275797446770313 := by
  unfold tailWord_6654762
  simp only [CollatzResearch.WordTrace]
  refine ⟨60679777579235322927477635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161812740211294194473273693 60679777579235322927477635)
  ·
    refine ⟨91019666368852984391216453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60679777579235322927477635 91019666368852984391216453)
    ·
      refine ⟨17066187444159934573353085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91019666368852984391216453 17066187444159934573353085)
      ·
        refine ⟨6399820291559975465007407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17066187444159934573353085 6399820291559975465007407)
        ·
          refine ⟨9599730437339963197511111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6399820291559975465007407 9599730437339963197511111)
          ·
            refine ⟨14399595656009944796266667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9599730437339963197511111 14399595656009944796266667)
            ·
              refine ⟨21599393484014917194400001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14399595656009944796266667 21599393484014917194400001)
              ·
                refine ⟨16199545113011187895800001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21599393484014917194400001 16199545113011187895800001)
                ·
                  refine ⟨12149658834758390921850001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16199545113011187895800001 12149658834758390921850001)
                  ·
                    refine ⟨9112244126068793191387501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12149658834758390921850001 9112244126068793191387501)
                    ·
                      refine ⟨3417091547275797446770313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9112244126068793191387501 3417091547275797446770313)
                      ·
                        rfl

theorem cell23_6654762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_6654762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654762 prefixEnd_6654762 := by exact prefixLift 6654762
  have htrace : WordTrace (prefixWord ++ tailWord_6654762) baseStart_6654762 baseEnd_6654762 := by
    simpa [prefixWord, tailWord_6654762, baseEnd_6654762] using wordTrace_append hprefix tailTrace_6654762
  have hstable : (prefixWord ++ tailWord_6654762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654762).length < 2 ^ (prefixWord ++ tailWord_6654762).sum := by decide
  have hdescent : baseEnd_6654762 < baseStart_6654762 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654782 : List Nat := [4, 2, 1, 2, 3, 2, 2, 1, 6]
def baseStart_6654782 : Nat := 118140960795 + 6654782 * 2 ^ 59
def prefixEnd_6654782 : Nat := 4983230072969 + 3 ^ 40 * 6654782 * 2
def baseEnd_6654782 : Nat := 379677979654320818724469

theorem tailTrace_6654782 : CollatzResearch.WordTrace tailWord_6654782 prefixEnd_6654782 379677979654320818724469 := by
  unfold tailWord_6654782
  simp only [CollatzResearch.WordTrace]
  refine ⟨30339979972108604390704825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161813226517912556750425733 30339979972108604390704825)
  ·
    refine ⟨22754984979081453293028619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30339979972108604390704825 22754984979081453293028619)
    ·
      refine ⟨34132477468622179939542929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22754984979081453293028619 34132477468622179939542929)
      ·
        refine ⟨25599358101466634954657197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34132477468622179939542929 25599358101466634954657197)
        ·
          refine ⟨9599759288049988107996449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25599358101466634954657197 9599759288049988107996449)
          ·
            refine ⟨7199819466037491080997337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9599759288049988107996449 7199819466037491080997337)
            ·
              refine ⟨5399864599528118310748003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7199819466037491080997337 5399864599528118310748003)
              ·
                refine ⟨8099796899292177466122005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5399864599528118310748003 8099796899292177466122005)
                ·
                  refine ⟨379677979654320818724469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8099796899292177466122005 379677979654320818724469)
                  ·
                    rfl

theorem cell23_6654782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 1, 6].length) (baseStart_6654782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654782 prefixEnd_6654782 := by exact prefixLift 6654782
  have htrace : WordTrace (prefixWord ++ tailWord_6654782) baseStart_6654782 baseEnd_6654782 := by
    simpa [prefixWord, tailWord_6654782, baseEnd_6654782] using wordTrace_append hprefix tailTrace_6654782
  have hstable : (prefixWord ++ tailWord_6654782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654782).length < 2 ^ (prefixWord ++ tailWord_6654782).sum := by decide
  have hdescent : baseEnd_6654782 < baseStart_6654782 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654791 : List Nat := [1, 1, 4, 1, 2, 1, 1, 5, 1, 6]
def baseStart_6654791 : Nat := 118140960795 + 6654791 * 2 ^ 59
def prefixEnd_6654791 : Nat := 4983230072969 + 3 ^ 40 * 6654791 * 2
def baseEnd_6654791 : Nat := 1139035479404925944435893

theorem tailTrace_6654791 : CollatzResearch.WordTrace tailWord_6654791 prefixEnd_6654791 1139035479404925944435893 := by
  unfold tailWord_6654791
  simp only [CollatzResearch.WordTrace]
  refine ⟨242720168033836229662716227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161813445355890819775144151 242720168033836229662716227)
  ·
    refine ⟨364080252050754344494074341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242720168033836229662716227 364080252050754344494074341)
    ·
      refine ⟨68265047259516439592638939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 364080252050754344494074341 68265047259516439592638939)
      ·
        refine ⟨102397570889274659388958409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68265047259516439592638939 102397570889274659388958409)
        ·
          refine ⟨76798178166955994541718807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102397570889274659388958409 76798178166955994541718807)
          ·
            refine ⟨115197267250433991812578211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76798178166955994541718807 115197267250433991812578211)
            ·
              refine ⟨172795900875650987718867317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115197267250433991812578211 172795900875650987718867317)
              ·
                refine ⟨16199615707092280098643811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 172795900875650987718867317 16199615707092280098643811)
                ·
                  refine ⟨24299423560638420147965717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16199615707092280098643811 24299423560638420147965717)
                  ·
                    refine ⟨1139035479404925944435893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24299423560638420147965717 1139035479404925944435893)
                    ·
                      rfl

theorem cell23_6654791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 6].length) (baseStart_6654791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654791 prefixEnd_6654791 := by exact prefixLift 6654791
  have htrace : WordTrace (prefixWord ++ tailWord_6654791) baseStart_6654791 baseEnd_6654791 := by
    simpa [prefixWord, tailWord_6654791, baseEnd_6654791] using wordTrace_append hprefix tailTrace_6654791
  have hstable : (prefixWord ++ tailWord_6654791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654791).length < 2 ^ (prefixWord ++ tailWord_6654791).sum := by decide
  have hdescent : baseEnd_6654791 < baseStart_6654791 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654798 : List Nat := [4, 1, 1, 1, 1, 1, 1, 3, 2, 6, 2]
def baseStart_6654798 : Nat := 118140960795 + 6654798 * 2 ^ 59
def prefixEnd_6654798 : Nat := 4983230072969 + 3 ^ 40 * 6654798 * 2
def baseEnd_6654798 : Nat := 3417110032579359305920147

theorem tailTrace_6654798 : CollatzResearch.WordTrace tailWord_6654798 prefixEnd_6654798 3417110032579359305920147 := by
  unfold tailWord_6654798
  simp only [CollatzResearch.WordTrace]
  refine ⟨30340052918101358732277631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161813615563207246572147365 30340052918101358732277631)
  ·
    refine ⟨45510079377152038098416447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30340052918101358732277631 45510079377152038098416447)
    ·
      refine ⟨68265119065728057147624671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45510079377152038098416447 68265119065728057147624671)
      ·
        refine ⟨102397678598592085721437007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68265119065728057147624671 102397678598592085721437007)
        ·
          refine ⟨153596517897888128582155511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102397678598592085721437007 153596517897888128582155511)
          ·
            refine ⟨230394776846832192873233267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153596517897888128582155511 230394776846832192873233267)
            ·
              refine ⟨345592165270248289309849901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230394776846832192873233267 345592165270248289309849901)
              ·
                refine ⟨129597061976343108491193713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 345592165270248289309849901 129597061976343108491193713)
                ·
                  refine ⟨97197796482257331368395285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129597061976343108491193713 97197796482257331368395285)
                  ·
                    refine ⟨4556146710105812407893529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 97197796482257331368395285 4556146710105812407893529)
                    ·
                      refine ⟨3417110032579359305920147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4556146710105812407893529 3417110032579359305920147)
                      ·
                        rfl

theorem cell23_6654798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 2, 6, 2].length) (baseStart_6654798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654798 prefixEnd_6654798 := by exact prefixLift 6654798
  have htrace : WordTrace (prefixWord ++ tailWord_6654798) baseStart_6654798 baseEnd_6654798 := by
    simpa [prefixWord, tailWord_6654798, baseEnd_6654798] using wordTrace_append hprefix tailTrace_6654798
  have hstable : (prefixWord ++ tailWord_6654798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654798).length < 2 ^ (prefixWord ++ tailWord_6654798).sum := by decide
  have hdescent : baseEnd_6654798 < baseStart_6654798 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654812 : List Nat := [2, 2, 4, 2, 1, 2, 3, 1, 1, 5]
def baseStart_6654812 : Nat := 118140960795 + 6654812 * 2 ^ 59
def prefixEnd_6654812 : Nat := 4983230072969 + 3 ^ 40 * 6654812 * 2
def baseEnd_6654812 : Nat := 1139039073769507417048361

theorem tailTrace_6654812 : CollatzResearch.WordTrace tailWord_6654812 prefixEnd_6654812 1139039073769507417048361 := by
  unfold tailWord_6654812
  simp only [CollatzResearch.WordTrace]
  refine ⟨121360466983380075124615345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161813955977840100166153793 121360466983380075124615345)
  ·
    refine ⟨91020350237535056343461509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121360466983380075124615345 91020350237535056343461509)
    ·
      refine ⟨17066315669537823064399033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91020350237535056343461509 17066315669537823064399033)
      ·
        refine ⟨12799736752153367298299275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17066315669537823064399033 12799736752153367298299275)
        ·
          refine ⟨19199605128230050947448913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12799736752153367298299275 19199605128230050947448913)
          ·
            refine ⟨14399703846172538210586685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19199605128230050947448913 14399703846172538210586685)
            ·
              refine ⟨5399888942314701828970007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14399703846172538210586685 5399888942314701828970007)
              ·
                refine ⟨8099833413472052743455011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5399888942314701828970007 8099833413472052743455011)
                ·
                  refine ⟨12149750120208079115182517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8099833413472052743455011 12149750120208079115182517)
                  ·
                    refine ⟨1139039073769507417048361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12149750120208079115182517 1139039073769507417048361)
                    ·
                      rfl

theorem cell23_6654812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_6654812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654812 prefixEnd_6654812 := by exact prefixLift 6654812
  have htrace : WordTrace (prefixWord ++ tailWord_6654812) baseStart_6654812 baseEnd_6654812 := by
    simpa [prefixWord, tailWord_6654812, baseEnd_6654812] using wordTrace_append hprefix tailTrace_6654812
  have hstable : (prefixWord ++ tailWord_6654812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654812).length < 2 ^ (prefixWord ++ tailWord_6654812).sum := by decide
  have hdescent : baseEnd_6654812 < baseStart_6654812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654815 : List Nat := [1, 1, 2, 3, 1, 3, 5, 1, 1, 1, 4]
def baseStart_6654815 : Nat := 118140960795 + 6654815 * 2 ^ 59
def prefixEnd_6654815 : Nat := 4983230072969 + 3 ^ 40 * 6654815 * 2
def baseEnd_6654815 : Nat := 3417118761750485739407569

theorem tailTrace_6654815 : CollatzResearch.WordTrace tailWord_6654815 prefixEnd_6654815 3417118761750485739407569 := by
  unfold tailWord_6654815
  simp only [CollatzResearch.WordTrace]
  refine ⟨242721043385749281761589899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161814028923832854507726599 242721043385749281761589899)
  ·
    refine ⟨364081565078623922642384849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242721043385749281761589899 364081565078623922642384849)
    ·
      refine ⟨273061173808967941981788637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364081565078623922642384849 273061173808967941981788637)
      ·
        refine ⟨102397940178362978243170739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273061173808967941981788637 102397940178362978243170739)
        ·
          refine ⟨153596910267544467364756109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102397940178362978243170739 153596910267544467364756109)
          ·
            refine ⟨57598841350329175261783541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153596910267544467364756109 57598841350329175261783541)
            ·
              refine ⟨5399891376593360180792207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57598841350329175261783541 5399891376593360180792207)
              ·
                refine ⟨8099837064890040271188311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5399891376593360180792207 8099837064890040271188311)
                ·
                  refine ⟨12149755597335060406782467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8099837064890040271188311 12149755597335060406782467)
                  ·
                    refine ⟨18224633396002590610173701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12149755597335060406782467 18224633396002590610173701)
                    ·
                      refine ⟨3417118761750485739407569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18224633396002590610173701 3417118761750485739407569)
                      ·
                        rfl

theorem cell23_6654815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 1, 1, 1, 4].length) (baseStart_6654815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654815 prefixEnd_6654815 := by exact prefixLift 6654815
  have htrace : WordTrace (prefixWord ++ tailWord_6654815) baseStart_6654815 baseEnd_6654815 := by
    simpa [prefixWord, tailWord_6654815, baseEnd_6654815] using wordTrace_append hprefix tailTrace_6654815
  have hstable : (prefixWord ++ tailWord_6654815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654815).length < 2 ^ (prefixWord ++ tailWord_6654815).sum := by decide
  have hdescent : baseEnd_6654815 < baseStart_6654815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654851 : List Nat := [1, 1, 1, 3, 4, 1, 1, 2, 2, 7]
def baseStart_6654851 : Nat := 118140960795 + 6654851 * 2 ^ 59
def prefixEnd_6654851 : Nat := 4983230072969 + 3 ^ 40 * 6654851 * 2
def baseEnd_6654851 : Nat := 1139045749018015866185801

theorem tailTrace_6654851 : CollatzResearch.WordTrace tailWord_6654851 prefixEnd_6654851 1139045749018015866185801 := by
  unfold tailWord_6654851
  simp only [CollatzResearch.WordTrace]
  refine ⟨242722356413618859909900407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161814904275745906606600271 242722356413618859909900407)
  ·
    refine ⟨364083534620428289864850611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242722356413618859909900407 364083534620428289864850611)
    ·
      refine ⟨546125301930642434797275917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364083534620428289864850611 546125301930642434797275917)
      ·
        refine ⟨204796988223990913048978469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 546125301930642434797275917 204796988223990913048978469)
        ·
          refine ⟨38399435291998296196683463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 204796988223990913048978469 38399435291998296196683463)
          ·
            refine ⟨57599152937997444295025195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38399435291998296196683463 57599152937997444295025195)
            ·
              refine ⟨86398729406996166442537793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57599152937997444295025195 86398729406996166442537793)
              ·
                refine ⟨64799047055247124831903345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86398729406996166442537793 64799047055247124831903345)
                ·
                  refine ⟨48599285291435343623927509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64799047055247124831903345 48599285291435343623927509)
                  ·
                    refine ⟨1139045749018015866185801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48599285291435343623927509 1139045749018015866185801)
                    ·
                      rfl

theorem cell23_6654851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 7].length) (baseStart_6654851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654851 prefixEnd_6654851 := by exact prefixLift 6654851
  have htrace : WordTrace (prefixWord ++ tailWord_6654851) baseStart_6654851 baseEnd_6654851 := by
    simpa [prefixWord, tailWord_6654851, baseEnd_6654851] using wordTrace_append hprefix tailTrace_6654851
  have hstable : (prefixWord ++ tailWord_6654851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654851).length < 2 ^ (prefixWord ++ tailWord_6654851).sum := by decide
  have hdescent : baseEnd_6654851 < baseStart_6654851 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654866 : List Nat := [3, 2, 3, 2, 3, 1, 2, 1, 1, 1, 4]
def baseStart_6654866 : Nat := 118140960795 + 6654866 * 2 ^ 59
def prefixEnd_6654866 : Nat := 4983230072969 + 3 ^ 40 * 6654866 * 2
def baseEnd_6654866 : Nat := 3417144949263865039869835

theorem tailTrace_6654866 : CollatzResearch.WordTrace tailWord_6654866 prefixEnd_6654866 3417144949263865039869835 := by
  unfold tailWord_6654866
  simp only [CollatzResearch.WordTrace]
  refine ⟨60680725877141129367924113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161815269005709678314464301 60680725877141129367924113)
  ·
    refine ⟨45510544407855847025943085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60680725877141129367924113 45510544407855847025943085)
    ·
      refine ⟨17066454152945942634728657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45510544407855847025943085 17066454152945942634728657)
      ·
        refine ⟨12799840614709456976046493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17066454152945942634728657 12799840614709456976046493)
        ·
          refine ⟨4799940230516046366017435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12799840614709456976046493 4799940230516046366017435)
          ·
            refine ⟨7199910345774069549026153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4799940230516046366017435 7199910345774069549026153)
            ·
              refine ⟨5399932759330552161769615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7199910345774069549026153 5399932759330552161769615)
              ·
                refine ⟨8099899138995828242654423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5399932759330552161769615 8099899138995828242654423)
                ·
                  refine ⟨12149848708493742363981635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8099899138995828242654423 12149848708493742363981635)
                  ·
                    refine ⟨18224773062740613545972453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12149848708493742363981635 18224773062740613545972453)
                    ·
                      refine ⟨3417144949263865039869835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18224773062740613545972453 3417144949263865039869835)
                      ·
                        rfl

theorem cell23_6654866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_6654866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654866 prefixEnd_6654866 := by exact prefixLift 6654866
  have htrace : WordTrace (prefixWord ++ tailWord_6654866) baseStart_6654866 baseEnd_6654866 := by
    simpa [prefixWord, tailWord_6654866, baseEnd_6654866] using wordTrace_append hprefix tailTrace_6654866
  have hstable : (prefixWord ++ tailWord_6654866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654866).length < 2 ^ (prefixWord ++ tailWord_6654866).sum := by decide
  have hdescent : baseEnd_6654866 < baseStart_6654866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654882 : List Nat := [3, 3, 1, 2, 2, 2, 1, 1, 4, 1, 3]
def baseStart_6654882 : Nat := 118140960795 + 6654882 * 2 ^ 59
def prefixEnd_6654882 : Nat := 4983230072969 + 3 ^ 40 * 6654882 * 2
def baseEnd_6654882 : Nat := 3417153164954336977269761

theorem tailTrace_6654882 : CollatzResearch.WordTrace tailWord_6654882 prefixEnd_6654882 3417153164954336977269761 := by
  unfold tailWord_6654882
  simp only [CollatzResearch.WordTrace]
  refine ⟨60680871769126638051069725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161815658051004368136185933 60680871769126638051069725)
  ·
    refine ⟨22755326913422489269151147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60680871769126638051069725 22755326913422489269151147)
    ·
      refine ⟨34132990370133733903726721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22755326913422489269151147 34132990370133733903726721)
      ·
        refine ⟨25599742777600300427795041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34132990370133733903726721 25599742777600300427795041)
        ·
          refine ⟨19199807083200225320846281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25599742777600300427795041 19199807083200225320846281)
          ·
            refine ⟨14399855312400168990634711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19199807083200225320846281 14399855312400168990634711)
            ·
              refine ⟨21599782968600253485952067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14399855312400168990634711 21599782968600253485952067)
              ·
                refine ⟨32399674452900380228928101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21599782968600253485952067 32399674452900380228928101)
                ·
                  refine ⟨6074938959918821292924019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32399674452900380228928101 6074938959918821292924019)
                  ·
                    refine ⟨9112408439878231939386029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6074938959918821292924019 9112408439878231939386029)
                    ·
                      refine ⟨3417153164954336977269761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9112408439878231939386029 3417153164954336977269761)
                      ·
                        rfl

theorem cell23_6654882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_6654882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654882 prefixEnd_6654882 := by exact prefixLift 6654882
  have htrace : WordTrace (prefixWord ++ tailWord_6654882) baseStart_6654882 baseEnd_6654882 := by
    simpa [prefixWord, tailWord_6654882, baseEnd_6654882] using wordTrace_append hprefix tailTrace_6654882
  have hstable : (prefixWord ++ tailWord_6654882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654882).length < 2 ^ (prefixWord ++ tailWord_6654882).sum := by decide
  have hdescent : baseEnd_6654882 < baseStart_6654882 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654891 : List Nat := [1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 5]
def baseStart_6654891 : Nat := 118140960795 + 6654891 * 2 ^ 59
def prefixEnd_6654891 : Nat := 4983230072969 + 3 ^ 40 * 6654891 * 2
def baseEnd_6654891 : Nat := 3417157786280227442057219

theorem tailTrace_6654891 : CollatzResearch.WordTrace tailWord_6654891 prefixEnd_6654891 3417157786280227442057219 := by
  unfold tailWord_6654891
  simp only [CollatzResearch.WordTrace]
  refine ⟨242723815333473946741356527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161815876888982631160904351 242723815333473946741356527)
  ·
    refine ⟨364085723000210920112034791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242723815333473946741356527 364085723000210920112034791)
    ·
      refine ⟨546128584500316380168052187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364085723000210920112034791 546128584500316380168052187)
      ·
        refine ⟨819192876750474570252078281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 546128584500316380168052187 819192876750474570252078281)
        ·
          refine ⟨614394657562855927689058711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 819192876750474570252078281 614394657562855927689058711)
          ·
            refine ⟨921591986344283891533588067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 614394657562855927689058711 921591986344283891533588067)
            ·
              refine ⟨1382387979516425837300382101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 921591986344283891533588067 1382387979516425837300382101)
              ·
                refine ⟨64799436539832461123455411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1382387979516425837300382101 64799436539832461123455411)
                ·
                  refine ⟨97199154809748691685183117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64799436539832461123455411 97199154809748691685183117)
                  ·
                    refine ⟨36449683053655759381943669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 97199154809748691685183117 36449683053655759381943669)
                    ·
                      refine ⟨3417157786280227442057219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36449683053655759381943669 3417157786280227442057219)
                      ·
                        rfl

theorem cell23_6654891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 5].length) (baseStart_6654891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654891 prefixEnd_6654891 := by exact prefixLift 6654891
  have htrace : WordTrace (prefixWord ++ tailWord_6654891) baseStart_6654891 baseEnd_6654891 := by
    simpa [prefixWord, tailWord_6654891, baseEnd_6654891] using wordTrace_append hprefix tailTrace_6654891
  have hstable : (prefixWord ++ tailWord_6654891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654891).length < 2 ^ (prefixWord ++ tailWord_6654891).sum := by decide
  have hdescent : baseEnd_6654891 < baseStart_6654891 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654909 : List Nat := [1, 4, 1, 2, 4, 1, 2, 2, 1, 3, 2]
def baseStart_6654909 : Nat := 118140960795 + 6654909 * 2 ^ 59
def prefixEnd_6654909 : Nat := 4983230072969 + 3 ^ 40 * 6654909 * 2
def baseEnd_6654909 : Nat := 3417167028932008371632137

theorem tailTrace_6654909 : CollatzResearch.WordTrace tailWord_6654909 prefixEnd_6654909 3417167028932008371632137 := by
  unfold tailWord_6654909
  simp only [CollatzResearch.WordTrace]
  refine ⟨242724471847408735815511781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161816314564939157210341187 242724471847408735815511781)
  ·
    refine ⟨45510838471389137965408459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 242724471847408735815511781 45510838471389137965408459)
    ·
      refine ⟨68266257707083706948112689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45510838471389137965408459 68266257707083706948112689)
      ·
        refine ⟨51199693280312780211084517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68266257707083706948112689 51199693280312780211084517)
        ·
          refine ⟨9599942490058646289578347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51199693280312780211084517 9599942490058646289578347)
          ·
            refine ⟨14399913735087969434367521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9599942490058646289578347 14399913735087969434367521)
            ·
              refine ⟨10799935301315977075775641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14399913735087969434367521 10799935301315977075775641)
              ·
                refine ⟨8099951475986982806831731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10799935301315977075775641 8099951475986982806831731)
                ·
                  refine ⟨12149927213980474210247597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8099951475986982806831731 12149927213980474210247597)
                  ·
                    refine ⟨4556222705242677828842849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12149927213980474210247597 4556222705242677828842849)
                    ·
                      refine ⟨3417167028932008371632137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4556222705242677828842849 3417167028932008371632137)
                      ·
                        rfl

theorem cell23_6654909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 2, 1, 3, 2].length) (baseStart_6654909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654909 prefixEnd_6654909 := by exact prefixLift 6654909
  have htrace : WordTrace (prefixWord ++ tailWord_6654909) baseStart_6654909 baseEnd_6654909 := by
    simpa [prefixWord, tailWord_6654909, baseEnd_6654909] using wordTrace_append hprefix tailTrace_6654909
  have hstable : (prefixWord ++ tailWord_6654909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654909).length < 2 ^ (prefixWord ++ tailWord_6654909).sum := by decide
  have hdescent : baseEnd_6654909 < baseStart_6654909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654911 : List Nat := [1, 1, 2, 2, 2, 1, 2, 3, 9]
def baseStart_6654911 : Nat := 118140960795 + 6654911 * 2 ^ 59
def prefixEnd_6654911 : Nat := 4983230072969 + 3 ^ 40 * 6654911 * 2
def baseEnd_6654911 : Nat := 379685339543701929311903

theorem tailTrace_6654911 : CollatzResearch.WordTrace tailWord_6654911 prefixEnd_6654911 379685339543701929311903 := by
  unfold tailWord_6654911
  simp only [CollatzResearch.WordTrace]
  refine ⟨242724544793401490157084587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161816363195600993438056391 242724544793401490157084587)
  ·
    refine ⟨364086817190102235235626881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242724544793401490157084587 364086817190102235235626881)
    ·
      refine ⟨273065112892576676426720161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364086817190102235235626881 273065112892576676426720161)
      ·
        refine ⟨204798834669432507320040121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273065112892576676426720161 204798834669432507320040121)
        ·
          refine ⟨153599126002074380490030091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204798834669432507320040121 153599126002074380490030091)
          ·
            refine ⟨230398689003111570735045137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153599126002074380490030091 230398689003111570735045137)
            ·
              refine ⟨172799016752333678051283853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230398689003111570735045137 172799016752333678051283853)
              ·
                refine ⟨64799631282125129269231445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 172799016752333678051283853 64799631282125129269231445)
                ·
                  refine ⟨379685339543701929311903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 64799631282125129269231445 379685339543701929311903)
                  ·
                    rfl

theorem cell23_6654911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 9].length) (baseStart_6654911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654911 prefixEnd_6654911 := by exact prefixLift 6654911
  have htrace : WordTrace (prefixWord ++ tailWord_6654911) baseStart_6654911 baseEnd_6654911 := by
    simpa [prefixWord, tailWord_6654911, baseEnd_6654911] using wordTrace_append hprefix tailTrace_6654911
  have hstable : (prefixWord ++ tailWord_6654911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654911).length < 2 ^ (prefixWord ++ tailWord_6654911).sum := by decide
  have hdescent : baseEnd_6654911 < baseStart_6654911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654921 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 3, 2, 7]
def baseStart_6654921 : Nat := 118140960795 + 6654921 * 2 ^ 59
def prefixEnd_6654921 : Nat := 4983230072969 + 3 ^ 40 * 6654921 * 2
def baseEnd_6654921 : Nat := 3417173190699862324682081

theorem tailTrace_6654921 : CollatzResearch.WordTrace tailWord_6654921 prefixEnd_6654921 3417173190699862324682081 := by
  unfold tailWord_6654921
  simp only [CollatzResearch.WordTrace]
  refine ⟨242724909523365261864948617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161816606348910174576632411 242724909523365261864948617)
  ·
    refine ⟨182043682142523946398711463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242724909523365261864948617 182043682142523946398711463)
    ·
      refine ⟨273065523213785919598067195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182043682142523946398711463 273065523213785919598067195)
      ·
        refine ⟨409598284820678879397100793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273065523213785919598067195 409598284820678879397100793)
        ·
          refine ⟨307198713615509159547825595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 409598284820678879397100793 307198713615509159547825595)
          ·
            refine ⟨460798070423263739321738393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307198713615509159547825595 460798070423263739321738393)
            ·
              refine ⟨345598552817447804491303795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 460798070423263739321738393 345598552817447804491303795)
              ·
                refine ⟨518397829226171706736955693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 345598552817447804491303795 518397829226171706736955693)
                ·
                  refine ⟨194399185959814390026358385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 518397829226171706736955693 194399185959814390026358385)
                  ·
                    refine ⟨145799389469860792519768789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 194399185959814390026358385 145799389469860792519768789)
                    ·
                      refine ⟨3417173190699862324682081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 145799389469860792519768789 3417173190699862324682081)
                      ·
                        rfl

theorem cell23_6654921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 2, 7].length) (baseStart_6654921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654921 prefixEnd_6654921 := by exact prefixLift 6654921
  have htrace : WordTrace (prefixWord ++ tailWord_6654921) baseStart_6654921 baseEnd_6654921 := by
    simpa [prefixWord, tailWord_6654921, baseEnd_6654921] using wordTrace_append hprefix tailTrace_6654921
  have hstable : (prefixWord ++ tailWord_6654921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654921).length < 2 ^ (prefixWord ++ tailWord_6654921).sum := by decide
  have hdescent : baseEnd_6654921 < baseStart_6654921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6654995 : List Nat := [1, 1, 1, 2, 1, 4, 1, 4, 2, 4, 2]
def baseStart_6654995 : Nat := 118140960795 + 6654995 * 2 ^ 59
def prefixEnd_6654995 : Nat := 4983230072969 + 3 ^ 40 * 6654995 * 2
def baseEnd_6654995 : Nat := 3417211188268295035156741

theorem tailTrace_6654995 : CollatzResearch.WordTrace tailWord_6654995 prefixEnd_6654995 3417211188268295035156741 := by
  unfold tailWord_6654995
  simp only [CollatzResearch.WordTrace]
  refine ⟨242727608525097172503142439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161818405683398115002094959 242727608525097172503142439)
  ·
    refine ⟨364091412787645758754713659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242727608525097172503142439 364091412787645758754713659)
    ·
      refine ⟨546137119181468638132070489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364091412787645758754713659 546137119181468638132070489)
      ·
        refine ⟨409602839386101478599052867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 546137119181468638132070489 409602839386101478599052867)
        ·
          refine ⟨614404259079152217898579301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409602839386101478599052867 614404259079152217898579301)
          ·
            refine ⟨115200798577341040855983619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 614404259079152217898579301 115200798577341040855983619)
            ·
              refine ⟨172801197866011561283975429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115200798577341040855983619 172801197866011561283975429)
              ·
                refine ⟨32400224599877167740745393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 172801197866011561283975429 32400224599877167740745393)
                ·
                  refine ⟨24300168449907875805559045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32400224599877167740745393 24300168449907875805559045)
                  ·
                    refine ⟨4556281584357726713542321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24300168449907875805559045 4556281584357726713542321)
                    ·
                      refine ⟨3417211188268295035156741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4556281584357726713542321 3417211188268295035156741)
                      ·
                        rfl

theorem cell23_6654995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 2, 4, 2].length) (baseStart_6654995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6654995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6654995 prefixEnd_6654995 := by exact prefixLift 6654995
  have htrace : WordTrace (prefixWord ++ tailWord_6654995) baseStart_6654995 baseEnd_6654995 := by
    simpa [prefixWord, tailWord_6654995, baseEnd_6654995] using wordTrace_append hprefix tailTrace_6654995
  have hstable : (prefixWord ++ tailWord_6654995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6654995).length < 2 ^ (prefixWord ++ tailWord_6654995).sum := by decide
  have hdescent : baseEnd_6654995 < baseStart_6654995 := by decide
  rcases family_descends (prefixWord ++ tailWord_6654995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6655012 : List Nat := [2, 3, 1, 4, 1, 1, 1, 1, 1, 6, 2]
def baseStart_6655012 : Nat := 118140960795 + 6655012 * 2 ^ 59
def prefixEnd_6655012 : Nat := 4983230072969 + 3 ^ 40 * 6655012 * 2
def baseEnd_6655012 : Nat := 3417219917439421468644163

theorem tailTrace_6655012 : CollatzResearch.WordTrace tailWord_6655012 prefixEnd_6655012 3417219917439421468644163 := by
  unfold tailWord_6655012
  simp only [CollatzResearch.WordTrace]
  refine ⟨121364114283017792203255645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161818819044023722937674193 121364114283017792203255645)
  ·
    refine ⟨45511542856131672076220867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121364114283017792203255645 45511542856131672076220867)
    ·
      refine ⟨68267314284197508114331301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45511542856131672076220867 68267314284197508114331301)
      ·
        refine ⟨12800121428287032771437119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68267314284197508114331301 12800121428287032771437119)
        ·
          refine ⟨19200182142430549157155679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12800121428287032771437119 19200182142430549157155679)
          ·
            refine ⟨28800273213645823735733519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19200182142430549157155679 28800273213645823735733519)
            ·
              refine ⟨43200409820468735603600279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28800273213645823735733519 43200409820468735603600279)
              ·
                refine ⟨64800614730703103405400419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43200409820468735603600279 64800614730703103405400419)
                ·
                  refine ⟨97200922096054655108100629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64800614730703103405400419 97200922096054655108100629)
                  ·
                    refine ⟨4556293223252561958192217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 97200922096054655108100629 4556293223252561958192217)
                    ·
                      refine ⟨3417219917439421468644163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4556293223252561958192217 3417219917439421468644163)
                      ·
                        rfl

theorem cell23_6655012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_6655012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6655012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6655012 prefixEnd_6655012 := by exact prefixLift 6655012
  have htrace : WordTrace (prefixWord ++ tailWord_6655012) baseStart_6655012 baseEnd_6655012 := by
    simpa [prefixWord, tailWord_6655012, baseEnd_6655012] using wordTrace_append hprefix tailTrace_6655012
  have hstable : (prefixWord ++ tailWord_6655012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6655012).length < 2 ^ (prefixWord ++ tailWord_6655012).sum := by decide
  have hdescent : baseEnd_6655012 < baseStart_6655012 := by decide
  rcases family_descends (prefixWord ++ tailWord_6655012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6655022 : List Nat := [4, 1, 3, 1, 1, 1, 3, 2, 3, 4]
def baseStart_6655022 : Nat := 118140960795 + 6655022 * 2 ^ 59
def prefixEnd_6655022 : Nat := 4983230072969 + 3 ^ 40 * 6655022 * 2
def baseEnd_6655022 : Nat := 1139075017415322143173039

theorem tailTrace_6655022 : CollatzResearch.WordTrace tailWord_6655022 prefixEnd_6655022 1139075017415322143173039 := by
  unfold tailWord_6655022
  simp only [CollatzResearch.WordTrace]
  refine ⟨30341074161999919514296915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161819062197332904076250213 30341074161999919514296915)
  ·
    refine ⟨45511611242999879271445373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30341074161999919514296915 45511611242999879271445373)
    ·
      refine ⟨17066854216124954726792015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45511611242999879271445373 17066854216124954726792015)
      ·
        refine ⟨25600281324187432090188023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17066854216124954726792015 25600281324187432090188023)
        ·
          refine ⟨38400421986281148135282035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25600281324187432090188023 38400421986281148135282035)
          ·
            refine ⟨57600632979421722202923053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38400421986281148135282035 57600632979421722202923053)
            ·
              refine ⟨21600237367283145826096145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57600632979421722202923053 21600237367283145826096145)
              ·
                refine ⟨16200178025462359369572109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21600237367283145826096145 16200178025462359369572109)
                ·
                  refine ⟨6075066759548384763589541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16200178025462359369572109 6075066759548384763589541)
                  ·
                    refine ⟨1139075017415322143173039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6075066759548384763589541 1139075017415322143173039)
                    ·
                      rfl

theorem cell23_6655022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_6655022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6655022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6655022 prefixEnd_6655022 := by exact prefixLift 6655022
  have htrace : WordTrace (prefixWord ++ tailWord_6655022) baseStart_6655022 baseEnd_6655022 := by
    simpa [prefixWord, tailWord_6655022, baseEnd_6655022] using wordTrace_append hprefix tailTrace_6655022
  have hstable : (prefixWord ++ tailWord_6655022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6655022).length < 2 ^ (prefixWord ++ tailWord_6655022).sum := by decide
  have hdescent : baseEnd_6655022 < baseStart_6655022 := by decide
  rcases family_descends (prefixWord ++ tailWord_6655022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6655032 : List Nat := [2, 1, 2, 1, 5, 1, 3, 1, 2, 2, 3]
def baseStart_6655032 : Nat := 118140960795 + 6655032 * 2 ^ 59
def prefixEnd_6655032 : Nat := 4983230072969 + 3 ^ 40 * 6655032 * 2
def baseEnd_6655032 : Nat := 3417230187052511390394071

theorem tailTrace_6655032 : CollatzResearch.WordTrace tailWord_6655032 prefixEnd_6655032 3417230187052511390394071 := by
  unfold tailWord_6655032
  simp only [CollatzResearch.WordTrace]
  refine ⟨121364479012981563911119675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161819305350642085214826233 121364479012981563911119675)
  ·
    refine ⟨182046718519472345866679513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121364479012981563911119675 182046718519472345866679513)
    ·
      refine ⟨136535038889604259400009635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182046718519472345866679513 136535038889604259400009635)
      ·
        refine ⟨204802558334406389100014453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136535038889604259400009635 204802558334406389100014453)
        ·
          refine ⟨19200239843850598978126355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 204802558334406389100014453 19200239843850598978126355)
          ·
            refine ⟨28800359765775898467189533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19200239843850598978126355 28800359765775898467189533)
            ·
              refine ⟨10800134912165961925196075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28800359765775898467189533 10800134912165961925196075)
              ·
                refine ⟨16200202368248942887794113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10800134912165961925196075 16200202368248942887794113)
                ·
                  refine ⟨12150151776186707165845585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16200202368248942887794113 12150151776186707165845585)
                  ·
                    refine ⟨9112613832140030374384189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12150151776186707165845585 9112613832140030374384189)
                    ·
                      refine ⟨3417230187052511390394071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9112613832140030374384189 3417230187052511390394071)
                      ·
                        rfl

theorem cell23_6655032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 2, 2, 3].length) (baseStart_6655032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6655032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6655032 prefixEnd_6655032 := by exact prefixLift 6655032
  have htrace : WordTrace (prefixWord ++ tailWord_6655032) baseStart_6655032 baseEnd_6655032 := by
    simpa [prefixWord, tailWord_6655032, baseEnd_6655032] using wordTrace_append hprefix tailTrace_6655032
  have hstable : (prefixWord ++ tailWord_6655032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6655032).length < 2 ^ (prefixWord ++ tailWord_6655032).sum := by decide
  have hdescent : baseEnd_6655032 < baseStart_6655032 := by decide
  rcases family_descends (prefixWord ++ tailWord_6655032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6655055 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 5, 5, 2]
def baseStart_6655055 : Nat := 118140960795 + 6655055 * 2 ^ 59
def prefixEnd_6655055 : Nat := 4983230072969 + 3 ^ 40 * 6655055 * 2
def baseEnd_6655055 : Nat := 3417241997107564800406465

theorem tailTrace_6655055 : CollatzResearch.WordTrace tailWord_6655055 prefixEnd_6655055 3417241997107564800406465 := by
  unfold tailWord_6655055
  simp only [CollatzResearch.WordTrace]
  refine ⟨242729796904879802750326619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161819864603253201833551079 242729796904879802750326619)
  ·
    refine ⟨364094695357319704125489929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242729796904879802750326619 364094695357319704125489929)
    ·
      refine ⟨273071021517989778094117447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364094695357319704125489929 273071021517989778094117447)
      ·
        refine ⟨409606532276984667141176171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273071021517989778094117447 409606532276984667141176171)
        ·
          refine ⟨614409798415477000711764257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409606532276984667141176171 614409798415477000711764257)
          ·
            refine ⟨460807348811607750533823193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 614409798415477000711764257 460807348811607750533823193)
            ·
              refine ⟨345605511608705812900367395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 460807348811607750533823193 345605511608705812900367395)
              ·
                refine ⟨518408267413058719350551093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 345605511608705812900367395 518408267413058719350551093)
                ·
                  refine ⟨48600775069974254939114165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 518408267413058719350551093 48600775069974254939114165)
                  ·
                    refine ⟨4556322662810086400541953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48600775069974254939114165 4556322662810086400541953)
                    ·
                      refine ⟨3417241997107564800406465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4556322662810086400541953 3417241997107564800406465)
                      ·
                        rfl

theorem cell23_6655055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 5, 2].length) (baseStart_6655055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6655055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6655055 prefixEnd_6655055 := by exact prefixLift 6655055
  have htrace : WordTrace (prefixWord ++ tailWord_6655055) baseStart_6655055 baseEnd_6655055 := by
    simpa [prefixWord, tailWord_6655055, baseEnd_6655055] using wordTrace_append hprefix tailTrace_6655055
  have hstable : (prefixWord ++ tailWord_6655055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6655055).length < 2 ^ (prefixWord ++ tailWord_6655055).sum := by decide
  have hdescent : baseEnd_6655055 < baseStart_6655055 := by decide
  rcases family_descends (prefixWord ++ tailWord_6655055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6655082 : List Nat := [3, 1, 3, 2, 2, 1, 1, 4, 1, 5]
def baseStart_6655082 : Nat := 118140960795 + 6655082 * 2 ^ 59
def prefixEnd_6655082 : Nat := 4983230072969 + 3 ^ 40 * 6655082 * 2
def baseEnd_6655082 : Nat := 1139085287028412064922947

theorem tailTrace_6655082 : CollatzResearch.WordTrace tailWord_6655082 prefixEnd_6655082 1139085287028412064922947 := by
  unfold tailWord_6655082
  simp only [CollatzResearch.WordTrace]
  refine ⟨60682695418945496590389875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161820521117187990907706333 60682695418945496590389875)
  ·
    refine ⟨91024043128418244885584813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60682695418945496590389875 91024043128418244885584813)
    ·
      refine ⟨34134016173156841832094305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91024043128418244885584813 34134016173156841832094305)
      ·
        refine ⟨25600512129867631374070729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34134016173156841832094305 25600512129867631374070729)
        ·
          refine ⟨19200384097400723530553047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25600512129867631374070729 19200384097400723530553047)
          ·
            refine ⟨28800576146101085295829571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19200384097400723530553047 28800576146101085295829571)
            ·
              refine ⟨43200864219151627943744357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28800576146101085295829571 43200864219151627943744357)
              ·
                refine ⟨8100162041090930239452067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43200864219151627943744357 8100162041090930239452067)
                ·
                  refine ⟨12150243061636395359178101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8100162041090930239452067 12150243061636395359178101)
                  ·
                    refine ⟨1139085287028412064922947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12150243061636395359178101 1139085287028412064922947)
                    ·
                      rfl

theorem cell23_6655082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_6655082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6655082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6655082 prefixEnd_6655082 := by exact prefixLift 6655082
  have htrace : WordTrace (prefixWord ++ tailWord_6655082) baseStart_6655082 baseEnd_6655082 := by
    simpa [prefixWord, tailWord_6655082, baseEnd_6655082] using wordTrace_append hprefix tailTrace_6655082
  have hstable : (prefixWord ++ tailWord_6655082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6655082).length < 2 ^ (prefixWord ++ tailWord_6655082).sum := by decide
  have hdescent : baseEnd_6655082 < baseStart_6655082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6655082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6655095 : List Nat := [1, 1, 3, 1, 1, 4, 1, 1, 6, 4]
def baseStart_6655095 : Nat := 118140960795 + 6655095 * 2 ^ 59
def prefixEnd_6655095 : Nat := 4983230072969 + 3 ^ 40 * 6655095 * 2
def baseEnd_6655095 : Nat := 1139087512111248214635427

theorem tailTrace_6655095 : CollatzResearch.WordTrace tailWord_6655095 prefixEnd_6655095 1139087512111248214635427 := by
  unfold tailWord_6655095
  simp only [CollatzResearch.WordTrace]
  refine ⟨242731255824734889581782739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161820837216489926387855159 242731255824734889581782739)
  ·
    refine ⟨364096883737102334372674109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242731255824734889581782739 364096883737102334372674109)
    ·
      refine ⟨136536331401413375389752791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 364096883737102334372674109 136536331401413375389752791)
      ·
        refine ⟨204804497102120063084629187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136536331401413375389752791 204804497102120063084629187)
        ·
          refine ⟨307206745653180094626943781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204804497102120063084629187 307206745653180094626943781)
          ·
            refine ⟨57601264809971267742551959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 307206745653180094626943781 57601264809971267742551959)
            ·
              refine ⟨86401897214956901613827939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57601264809971267742551959 86401897214956901613827939)
              ·
                refine ⟨129602845822435352420741909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86401897214956901613827939 129602845822435352420741909)
                ·
                  refine ⟨6075133397926657144722277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 129602845822435352420741909 6075133397926657144722277)
                  ·
                    refine ⟨1139087512111248214635427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6075133397926657144722277 1139087512111248214635427)
                    ·
                      rfl

theorem cell23_6655095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 6, 4].length) (baseStart_6655095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6655095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6655095 prefixEnd_6655095 := by exact prefixLift 6655095
  have htrace : WordTrace (prefixWord ++ tailWord_6655095) baseStart_6655095 baseEnd_6655095 := by
    simpa [prefixWord, tailWord_6655095, baseEnd_6655095] using wordTrace_append hprefix tailTrace_6655095
  have hstable : (prefixWord ++ tailWord_6655095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6655095).length < 2 ^ (prefixWord ++ tailWord_6655095).sum := by decide
  have hdescent : baseEnd_6655095 < baseStart_6655095 := by decide
  rcases family_descends (prefixWord ++ tailWord_6655095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6655122 : List Nat := [3, 2, 3, 1, 1, 2, 2, 2, 1, 1, 5]
def baseStart_6655122 : Nat := 118140960795 + 6655122 * 2 ^ 59
def prefixEnd_6655122 : Nat := 4983230072969 + 3 ^ 40 * 6655122 * 2
def baseEnd_6655122 : Nat := 3417276400311416038268657

theorem tailTrace_6655122 : CollatzResearch.WordTrace tailWord_6655122 prefixEnd_6655122 3417276400311416038268657 := by
  unfold tailWord_6655122
  simp only [CollatzResearch.WordTrace]
  refine ⟨60683060148909268298253905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161821493730424715462010413 60683060148909268298253905)
  ·
    refine ⟨45512295111681951223690429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60683060148909268298253905 45512295111681951223690429)
    ·
      refine ⟨17067110666880731708883911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45512295111681951223690429 17067110666880731708883911)
      ·
        refine ⟨25600666000321097563325867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17067110666880731708883911 25600666000321097563325867)
        ·
          refine ⟨38400999000481646344988801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25600666000321097563325867 38400999000481646344988801)
          ·
            refine ⟨28800749250361234758741601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38400999000481646344988801 28800749250361234758741601)
            ·
              refine ⟨21600561937770926069056201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28800749250361234758741601 21600561937770926069056201)
              ·
                refine ⟨16200421453328194551792151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21600561937770926069056201 16200421453328194551792151)
                ·
                  refine ⟨24300632179992291827688227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16200421453328194551792151 24300632179992291827688227)
                  ·
                    refine ⟨36450948269988437741532341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24300632179992291827688227 36450948269988437741532341)
                    ·
                      refine ⟨3417276400311416038268657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36450948269988437741532341 3417276400311416038268657)
                      ·
                        rfl

theorem cell23_6655122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_6655122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6655122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6655122 prefixEnd_6655122 := by exact prefixLift 6655122
  have htrace : WordTrace (prefixWord ++ tailWord_6655122) baseStart_6655122 baseEnd_6655122 := by
    simpa [prefixWord, tailWord_6655122, baseEnd_6655122] using wordTrace_append hprefix tailTrace_6655122
  have hstable : (prefixWord ++ tailWord_6655122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6655122).length < 2 ^ (prefixWord ++ tailWord_6655122).sum := by decide
  have hdescent : baseEnd_6655122 < baseStart_6655122 := by decide
  rcases family_descends (prefixWord ++ tailWord_6655122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6655149 : List Nat := [1, 5, 2, 1, 3, 1, 1, 2, 1, 2, 4]
def baseStart_6655149 : Nat := 118140960795 + 6655149 * 2 ^ 59
def prefixEnd_6655149 : Nat := 4983230072969 + 3 ^ 40 * 6655149 * 2
def baseEnd_6655149 : Nat := 3417290264289087432631033

theorem tailTrace_6655149 : CollatzResearch.WordTrace tailWord_6655149 prefixEnd_6655149 3417290264289087432631033 := by
  unfold tailWord_6655149
  simp only [CollatzResearch.WordTrace]
  refine ⟨242733225366539256804248501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161822150244359504536165667 242733225366539256804248501)
  ·
    refine ⟨22756239878113055325398297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 242733225366539256804248501 22756239878113055325398297)
    ·
      refine ⟨17067179908584791494048723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22756239878113055325398297 17067179908584791494048723)
      ·
        refine ⟨25600769862877187241073085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17067179908584791494048723 25600769862877187241073085)
        ·
          refine ⟨9600288698578945215402407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25600769862877187241073085 9600288698578945215402407)
          ·
            refine ⟨14400433047868417823103611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9600288698578945215402407 14400433047868417823103611)
            ·
              refine ⟨21600649571802626734655417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14400433047868417823103611 21600649571802626734655417)
              ·
                refine ⟨16200487178851970050991563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21600649571802626734655417 16200487178851970050991563)
                ·
                  refine ⟨24300730768277955076487345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16200487178851970050991563 24300730768277955076487345)
                  ·
                    refine ⟨18225548076208466307365509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24300730768277955076487345 18225548076208466307365509)
                    ·
                      refine ⟨3417290264289087432631033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18225548076208466307365509 3417290264289087432631033)
                      ·
                        rfl

theorem cell23_6655149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_6655149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6655149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6655149 prefixEnd_6655149 := by exact prefixLift 6655149
  have htrace : WordTrace (prefixWord ++ tailWord_6655149) baseStart_6655149 baseEnd_6655149 := by
    simpa [prefixWord, tailWord_6655149, baseEnd_6655149] using wordTrace_append hprefix tailTrace_6655149
  have hstable : (prefixWord ++ tailWord_6655149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6655149).length < 2 ^ (prefixWord ++ tailWord_6655149).sum := by decide
  have hdescent : baseEnd_6655149 < baseStart_6655149 := by decide
  rcases family_descends (prefixWord ++ tailWord_6655149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6655165 : List Nat := [1, 4, 1, 2, 1, 1, 2, 2, 2, 2, 5]
def baseStart_6655165 : Nat := 118140960795 + 6655165 * 2 ^ 59
def prefixEnd_6655165 : Nat := 4983230072969 + 3 ^ 40 * 6655165 * 2
def baseEnd_6655165 : Nat := 3417298479979559370030959

theorem tailTrace_6655165 : CollatzResearch.WordTrace tailWord_6655165 prefixEnd_6655165 3417298479979559370030959 := by
  unfold tailWord_6655165
  simp only [CollatzResearch.WordTrace]
  refine ⟨242733808934481291536830949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161822539289654194357887299 242733808934481291536830949)
  ·
    refine ⟨45512589175215242163155803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 242733808934481291536830949 45512589175215242163155803)
    ·
      refine ⟨68268883762822863244733705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45512589175215242163155803 68268883762822863244733705)
      ·
        refine ⟨51201662822117147433550279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68268883762822863244733705 51201662822117147433550279)
        ·
          refine ⟨76802494233175721150325419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51201662822117147433550279 76802494233175721150325419)
          ·
            refine ⟨115203741349763581725488129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76802494233175721150325419 115203741349763581725488129)
            ·
              refine ⟨86402806012322686294116097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115203741349763581725488129 86402806012322686294116097)
              ·
                refine ⟨64802104509242014720587073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86402806012322686294116097 64802104509242014720587073)
                ·
                  refine ⟨48601578381931511040440305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64802104509242014720587073 48601578381931511040440305)
                  ·
                    refine ⟨36451183786448633280330229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48601578381931511040440305 36451183786448633280330229)
                    ·
                      refine ⟨3417298479979559370030959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36451183786448633280330229 3417298479979559370030959)
                      ·
                        rfl

theorem cell23_6655165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_6655165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6655165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6655165 prefixEnd_6655165 := by exact prefixLift 6655165
  have htrace : WordTrace (prefixWord ++ tailWord_6655165) baseStart_6655165 baseEnd_6655165 := by
    simpa [prefixWord, tailWord_6655165, baseEnd_6655165] using wordTrace_append hprefix tailTrace_6655165
  have hstable : (prefixWord ++ tailWord_6655165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6655165).length < 2 ^ (prefixWord ++ tailWord_6655165).sum := by decide
  have hdescent : baseEnd_6655165 < baseStart_6655165 := by decide
  rcases family_descends (prefixWord ++ tailWord_6655165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6655195 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 3]
def baseStart_6655195 : Nat := 118140960795 + 6655195 * 2 ^ 59
def prefixEnd_6655195 : Nat := 4983230072969 + 3 ^ 40 * 6655195 * 2
def baseEnd_6655195 : Nat := 3417313884399194252655821

theorem tailTrace_6655195 : CollatzResearch.WordTrace tailWord_6655195 prefixEnd_6655195 3417313884399194252655821 := by
  unfold tailWord_6655195
  simp only [CollatzResearch.WordTrace]
  refine ⟨242734903124372606660423039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161823268749581737773615359 242734903124372606660423039)
  ·
    refine ⟨364102354686558909990634559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242734903124372606660423039 364102354686558909990634559)
    ·
      refine ⟨546153532029838364985951839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364102354686558909990634559 546153532029838364985951839)
      ·
        refine ⟨819230298044757547478927759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 546153532029838364985951839 819230298044757547478927759)
        ·
          refine ⟨1228845447067136321218391639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 819230298044757547478927759 1228845447067136321218391639)
          ·
            refine ⟨1843268170600704481827587459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1228845447067136321218391639 1843268170600704481827587459)
            ·
              refine ⟨2764902255901056722741381189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1843268170600704481827587459 2764902255901056722741381189)
              ·
                refine ⟨518419172981448135514008973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2764902255901056722741381189 518419172981448135514008973)
                ·
                  refine ⟨194407189868043050817753365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 518419172981448135514008973 194407189868043050817753365)
                  ·
                    refine ⟨9112837025064518007082189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 194407189868043050817753365 9112837025064518007082189)
                    ·
                      refine ⟨3417313884399194252655821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9112837025064518007082189 3417313884399194252655821)
                      ·
                        rfl

theorem cell23_6655195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 3].length) (baseStart_6655195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6655195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6655195 prefixEnd_6655195 := by exact prefixLift 6655195
  have htrace : WordTrace (prefixWord ++ tailWord_6655195) baseStart_6655195 baseEnd_6655195 := by
    simpa [prefixWord, tailWord_6655195, baseEnd_6655195] using wordTrace_append hprefix tailTrace_6655195
  have hstable : (prefixWord ++ tailWord_6655195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6655195).length < 2 ^ (prefixWord ++ tailWord_6655195).sum := by decide
  have hdescent : baseEnd_6655195 < baseStart_6655195 := by decide
  rcases family_descends (prefixWord ++ tailWord_6655195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6655213 : List Nat := [1, 5, 1, 2, 2, 1, 4, 1, 1, 3, 2]
def baseStart_6655213 : Nat := 118140960795 + 6655213 * 2 ^ 59
def prefixEnd_6655213 : Nat := 4983230072969 + 3 ^ 40 * 6655213 * 2
def baseEnd_6655213 : Nat := 3417323127050975182230739

theorem tailTrace_6655213 : CollatzResearch.WordTrace tailWord_6655213 prefixEnd_6655213 3417323127050975182230739 := by
  unfold tailWord_6655213
  simp only [CollatzResearch.WordTrace]
  refine ⟨242735559638307395734578293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161823706425538263823052195 242735559638307395734578293)
  ·
    refine ⟨22756458716091318350116715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 242735559638307395734578293 22756458716091318350116715)
    ·
      refine ⟨34134688074136977525175073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22756458716091318350116715 34134688074136977525175073)
      ·
        refine ⟨25601016055602733143881305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34134688074136977525175073 25601016055602733143881305)
        ·
          refine ⟨19200762041702049857910979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25601016055602733143881305 19200762041702049857910979)
          ·
            refine ⟨28801143062553074786866469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19200762041702049857910979 28801143062553074786866469)
            ·
              refine ⟨5400214324228701522537463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28801143062553074786866469 5400214324228701522537463)
              ·
                refine ⟨8100321486343052283806195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5400214324228701522537463 8100321486343052283806195)
                ·
                  refine ⟨12150482229514578425709293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8100321486343052283806195 12150482229514578425709293)
                  ·
                    refine ⟨4556430836067966909640985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12150482229514578425709293 4556430836067966909640985)
                    ·
                      refine ⟨3417323127050975182230739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4556430836067966909640985 3417323127050975182230739)
                      ·
                        rfl

theorem cell23_6655213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_6655213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6655213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6655213 prefixEnd_6655213 := by exact prefixLift 6655213
  have htrace : WordTrace (prefixWord ++ tailWord_6655213) baseStart_6655213 baseEnd_6655213 := by
    simpa [prefixWord, tailWord_6655213, baseEnd_6655213] using wordTrace_append hprefix tailTrace_6655213
  have hstable : (prefixWord ++ tailWord_6655213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6655213).length < 2 ^ (prefixWord ++ tailWord_6655213).sum := by decide
  have hdescent : baseEnd_6655213 < baseStart_6655213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6655213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6655220 : List Nat := [2, 6, 1, 2, 1, 1, 1, 1, 4, 1, 3]
def baseStart_6655220 : Nat := 118140960795 + 6655220 * 2 ^ 59
def prefixEnd_6655220 : Nat := 4983230072969 + 3 ^ 40 * 6655220 * 2
def baseEnd_6655220 : Nat := 3417326721415556654843207

theorem tailTrace_6655220 : CollatzResearch.WordTrace tailWord_6655220 prefixEnd_6655220 3417326721415556654843207 := by
  unfold tailWord_6655220
  simp only [CollatzResearch.WordTrace]
  refine ⟨121367907474641017965041557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161823876632854690620055409 121367907474641017965041557)
  ·
    refine ⟨5689120662873797717111323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 121367907474641017965041557 5689120662873797717111323)
    ·
      refine ⟨8533680994310696575666985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5689120662873797717111323 8533680994310696575666985)
      ·
        refine ⟨6400260745733022431750239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8533680994310696575666985 6400260745733022431750239)
        ·
          refine ⟨9600391118599533647625359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6400260745733022431750239 9600391118599533647625359)
          ·
            refine ⟨14400586677899300471438039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9600391118599533647625359 14400586677899300471438039)
            ·
              refine ⟨21600880016848950707157059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14400586677899300471438039 21600880016848950707157059)
              ·
                refine ⟨32401320025273426060735589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21600880016848950707157059 32401320025273426060735589)
                ·
                  refine ⟨6075247504738767386387923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32401320025273426060735589 6075247504738767386387923)
                  ·
                    refine ⟨9112871257108151079581885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6075247504738767386387923 9112871257108151079581885)
                    ·
                      refine ⟨3417326721415556654843207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9112871257108151079581885 3417326721415556654843207)
                      ·
                        rfl

theorem cell23_6655220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_6655220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6655220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6655220 prefixEnd_6655220 := by exact prefixLift 6655220
  have htrace : WordTrace (prefixWord ++ tailWord_6655220) baseStart_6655220 baseEnd_6655220 := by
    simpa [prefixWord, tailWord_6655220, baseEnd_6655220] using wordTrace_append hprefix tailTrace_6655220
  have hstable : (prefixWord ++ tailWord_6655220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6655220).length < 2 ^ (prefixWord ++ tailWord_6655220).sum := by decide
  have hdescent : baseEnd_6655220 < baseStart_6655220 := by decide
  rcases family_descends (prefixWord ++ tailWord_6655220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6655243 : List Nat := [1, 1, 1, 1, 5, 4, 3, 1, 2, 2, 2]
def baseStart_6655243 : Nat := 118140960795 + 6655243 * 2 ^ 59
def prefixEnd_6655243 : Nat := 4983230072969 + 3 ^ 40 * 6655243 * 2
def baseEnd_6655243 : Nat := 3417338531470610064855601

theorem tailTrace_6655243 : CollatzResearch.WordTrace tailWord_6655243 prefixEnd_6655243 3417338531470610064855601 := by
  unfold tailWord_6655243
  simp only [CollatzResearch.WordTrace]
  refine ⟨242736653828198710858170383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161824435885465807238780255 242736653828198710858170383)
  ·
    refine ⟨364104980742298066287255575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242736653828198710858170383 364104980742298066287255575)
    ·
      refine ⟨546157471113447099430883363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364104980742298066287255575 546157471113447099430883363)
      ·
        refine ⟨819236206670170649146325045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 546157471113447099430883363 819236206670170649146325045)
        ·
          refine ⟨76803394375328498357467973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 819236206670170649146325045 76803394375328498357467973)
          ·
            refine ⟨14400636445374093442025245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76803394375328498357467973 14400636445374093442025245)
            ·
              refine ⟨5400238667015285040759467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14400636445374093442025245 5400238667015285040759467)
              ·
                refine ⟨8100358000522927561139201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5400238667015285040759467 8100358000522927561139201)
                ·
                  refine ⟨6075268500392195670854401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8100358000522927561139201 6075268500392195670854401)
                  ·
                    refine ⟨4556451375294146753140801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6075268500392195670854401 4556451375294146753140801)
                    ·
                      refine ⟨3417338531470610064855601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4556451375294146753140801 3417338531470610064855601)
                      ·
                        rfl

theorem cell23_6655243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 1, 2, 2, 2].length) (baseStart_6655243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6655243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6655243 prefixEnd_6655243 := by exact prefixLift 6655243
  have htrace : WordTrace (prefixWord ++ tailWord_6655243) baseStart_6655243 baseEnd_6655243 := by
    simpa [prefixWord, tailWord_6655243, baseEnd_6655243] using wordTrace_append hprefix tailTrace_6655243
  have hstable : (prefixWord ++ tailWord_6655243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6655243).length < 2 ^ (prefixWord ++ tailWord_6655243).sum := by decide
  have hdescent : baseEnd_6655243 < baseStart_6655243 := by decide
  rcases family_descends (prefixWord ++ tailWord_6655243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6655289 : List Nat := [1, 2, 1, 6, 2, 1, 1, 1, 1, 2, 5]
def baseStart_6655289 : Nat := 118140960795 + 6655289 * 2 ^ 59
def prefixEnd_6655289 : Nat := 4983230072969 + 3 ^ 40 * 6655289 * 2
def baseEnd_6655289 : Nat := 3417362151580716884880389

theorem tailTrace_6655289 : CollatzResearch.WordTrace tailWord_6655289 prefixEnd_6655289 3417362151580716884880389 := by
  unfold tailWord_6655289
  simp only [CollatzResearch.WordTrace]
  refine ⟨242738331586032060714344921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161825554390688040476229947 242738331586032060714344921)
  ·
    refine ⟨182053748689524045535758691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242738331586032060714344921 182053748689524045535758691)
    ·
      refine ⟨273080623034286068303638037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182053748689524045535758691 273080623034286068303638037)
      ·
        refine ⟨12800654204732159451733033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 273080623034286068303638037 12800654204732159451733033)
        ·
          refine ⟨9600490653549119588799775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12800654204732159451733033 9600490653549119588799775)
          ·
            refine ⟨14400735980323679383199663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9600490653549119588799775 14400735980323679383199663)
            ·
              refine ⟨21601103970485519074799495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14400735980323679383199663 21601103970485519074799495)
              ·
                refine ⟨32401655955728278612199243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21601103970485519074799495 32401655955728278612199243)
                ·
                  refine ⟨48602483933592417918298865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32401655955728278612199243 48602483933592417918298865)
                  ·
                    refine ⟨36451862950194313438724149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48602483933592417918298865 36451862950194313438724149)
                    ·
                      refine ⟨3417362151580716884880389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36451862950194313438724149 3417362151580716884880389)
                      ·
                        rfl

theorem cell23_6655289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_6655289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6655289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6655289 prefixEnd_6655289 := by exact prefixLift 6655289
  have htrace : WordTrace (prefixWord ++ tailWord_6655289) baseStart_6655289 baseEnd_6655289 := by
    simpa [prefixWord, tailWord_6655289, baseEnd_6655289] using wordTrace_append hprefix tailTrace_6655289
  have hstable : (prefixWord ++ tailWord_6655289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6655289).length < 2 ^ (prefixWord ++ tailWord_6655289).sum := by decide
  have hdescent : baseEnd_6655289 < baseStart_6655289 := by decide
  rcases family_descends (prefixWord ++ tailWord_6655289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6655319 : List Nat := [1, 1, 3, 2, 3, 2, 1, 3, 2, 2, 3]
def baseStart_6655319 : Nat := 118140960795 + 6655319 * 2 ^ 59
def prefixEnd_6655319 : Nat := 4983230072969 + 3 ^ 40 * 6655319 * 2
def baseEnd_6655319 : Nat := 3417377556000351767505251

theorem tailTrace_6655319 : CollatzResearch.WordTrace tailWord_6655319 prefixEnd_6655319 3417377556000351767505251 := by
  unfold tailWord_6655319
  simp only [CollatzResearch.WordTrace]
  refine ⟨242739425775923375837937011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161826283850615583891958007 242739425775923375837937011)
  ·
    refine ⟨364109138663885063756905517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242739425775923375837937011 364109138663885063756905517)
    ·
      refine ⟨136540926998956898908839569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 364109138663885063756905517 136540926998956898908839569)
      ·
        refine ⟨102405695249217674181629677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136540926998956898908839569 102405695249217674181629677)
        ·
          refine ⟨38402135718456627818111129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102405695249217674181629677 38402135718456627818111129)
          ·
            refine ⟨28801601788842470863583347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38402135718456627818111129 28801601788842470863583347)
            ·
              refine ⟨43202402683263706295375021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28801601788842470863583347 43202402683263706295375021)
              ·
                refine ⟨16200901006223889860765633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43202402683263706295375021 16200901006223889860765633)
                ·
                  refine ⟨12150675754667917395574225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16200901006223889860765633 12150675754667917395574225)
                  ·
                    refine ⟨9113006816000938046680669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12150675754667917395574225 9113006816000938046680669)
                    ·
                      refine ⟨3417377556000351767505251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9113006816000938046680669 3417377556000351767505251)
                      ·
                        rfl

theorem cell23_6655319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 2, 2, 3].length) (baseStart_6655319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6655319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6655319 prefixEnd_6655319 := by exact prefixLift 6655319
  have htrace : WordTrace (prefixWord ++ tailWord_6655319) baseStart_6655319 baseEnd_6655319 := by
    simpa [prefixWord, tailWord_6655319, baseEnd_6655319] using wordTrace_append hprefix tailTrace_6655319
  have hstable : (prefixWord ++ tailWord_6655319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6655319).length < 2 ^ (prefixWord ++ tailWord_6655319).sum := by decide
  have hdescent : baseEnd_6655319 < baseStart_6655319 := by decide
  rcases family_descends (prefixWord ++ tailWord_6655319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6655390 : List Nat := [4, 3, 1, 2, 3, 1, 1, 2, 6]
def baseStart_6655390 : Nat := 118140960795 + 6655390 * 2 ^ 59
def prefixEnd_6655390 : Nat := 4983230072969 + 3 ^ 40 * 6655390 * 2
def baseEnd_6655390 : Nat := 379712668125202332190825

theorem tailTrace_6655390 : CollatzResearch.WordTrace tailWord_6655390 prefixEnd_6655390 379712668125202332190825 := by
  unfold tailWord_6655390
  simp only [CollatzResearch.WordTrace]
  refine ⟨30342751919833269370471453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161828010239110769975847749 30342751919833269370471453)
  ·
    refine ⟨11378531969937476013926795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30342751919833269370471453 11378531969937476013926795)
    ·
      refine ⟨17067797954906214020890193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11378531969937476013926795 17067797954906214020890193)
      ·
        refine ⟨12800848466179660515667645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17067797954906214020890193 12800848466179660515667645)
        ·
          refine ⟨4800318174817372693375367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12800848466179660515667645 4800318174817372693375367)
          ·
            refine ⟨7200477262226059040063051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4800318174817372693375367 7200477262226059040063051)
            ·
              refine ⟨10800715893339088560094577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7200477262226059040063051 10800715893339088560094577)
              ·
                refine ⟨8100536920004316420070933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10800715893339088560094577 8100536920004316420070933)
                ·
                  refine ⟨379712668125202332190825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8100536920004316420070933 379712668125202332190825)
                  ·
                    rfl

theorem cell23_6655390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_6655390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6655390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6655390 prefixEnd_6655390 := by exact prefixLift 6655390
  have htrace : WordTrace (prefixWord ++ tailWord_6655390) baseStart_6655390 baseEnd_6655390 := by
    simpa [prefixWord, tailWord_6655390, baseEnd_6655390] using wordTrace_append hprefix tailTrace_6655390
  have hstable : (prefixWord ++ tailWord_6655390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6655390).length < 2 ^ (prefixWord ++ tailWord_6655390).sum := by decide
  have hdescent : baseEnd_6655390 < baseStart_6655390 := by decide
  rcases family_descends (prefixWord ++ tailWord_6655390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6655400 : List Nat := [2, 1, 6, 1, 2, 1, 2, 1, 3, 1, 3]
def baseStart_6655400 : Nat := 118140960795 + 6655400 * 2 ^ 59
def prefixEnd_6655400 : Nat := 4983230072969 + 3 ^ 40 * 6655400 * 2
def baseEnd_6655400 : Nat := 3417419147933365950592379

theorem tailTrace_6655400 : CollatzResearch.WordTrace tailWord_6655400 prefixEnd_6655400 3417419147933365950592379 := by
  unfold tailWord_6655400
  simp only [CollatzResearch.WordTrace]
  refine ⟨121371190044314963335817827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161828253392419951114423769 121371190044314963335817827)
  ·
    refine ⟨182056785066472445003726741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121371190044314963335817827 182056785066472445003726741)
    ·
      refine ⟨8533911799990895859549691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 182056785066472445003726741 8533911799990895859549691)
      ·
        refine ⟨12800867699986343789324537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8533911799990895859549691 12800867699986343789324537)
        ·
          refine ⟨9600650774989757841993403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12800867699986343789324537 9600650774989757841993403)
          ·
            refine ⟨14400976162484636762990105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9600650774989757841993403 14400976162484636762990105)
            ·
              refine ⟨10800732121863477572242579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14400976162484636762990105 10800732121863477572242579)
              ·
                refine ⟨16201098182795216358363869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10800732121863477572242579 16201098182795216358363869)
                ·
                  refine ⟨6075411818548206134386451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16201098182795216358363869 6075411818548206134386451)
                  ·
                    refine ⟨9113117727822309201579677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6075411818548206134386451 9113117727822309201579677)
                    ·
                      refine ⟨3417419147933365950592379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9113117727822309201579677 3417419147933365950592379)
                      ·
                        rfl

theorem cell23_6655400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_6655400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6655400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6655400 prefixEnd_6655400 := by exact prefixLift 6655400
  have htrace : WordTrace (prefixWord ++ tailWord_6655400) baseStart_6655400 baseEnd_6655400 := by
    simpa [prefixWord, tailWord_6655400, baseEnd_6655400] using wordTrace_append hprefix tailTrace_6655400
  have hstable : (prefixWord ++ tailWord_6655400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6655400).length < 2 ^ (prefixWord ++ tailWord_6655400).sum := by decide
  have hdescent : baseEnd_6655400 < baseStart_6655400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6655400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6655409 : List Nat := [1, 2, 2, 4, 1, 1, 3, 2, 1, 1, 5]
def baseStart_6655409 : Nat := 118140960795 + 6655409 * 2 ^ 59
def prefixEnd_6655409 : Nat := 4983230072969 + 3 ^ 40 * 6655409 * 2
def baseEnd_6655409 : Nat := 3417423769259256415379837

theorem tailTrace_6655409 : CollatzResearch.WordTrace tailWord_6655409 prefixEnd_6655409 3417423769259256415379837 := by
  unfold tailWord_6655409
  simp only [CollatzResearch.WordTrace]
  refine ⟨242742708345597321208713281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161828472230398214139142187 242742708345597321208713281)
  ·
    refine ⟨182057031259197990906534961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242742708345597321208713281 182057031259197990906534961)
    ·
      refine ⟨136542773444398493179901221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182057031259197990906534961 136542773444398493179901221)
      ·
        refine ⟨25601770020824717471231479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136542773444398493179901221 25601770020824717471231479)
        ·
          refine ⟨38402655031237076206847219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25601770020824717471231479 38402655031237076206847219)
          ·
            refine ⟨57603982546855614310270829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38402655031237076206847219 57603982546855614310270829)
            ·
              refine ⟨21601493455070855366351561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57603982546855614310270829 21601493455070855366351561)
              ·
                refine ⟨16201120091303141524763671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21601493455070855366351561 16201120091303141524763671)
                ·
                  refine ⟨24301680136954712287145507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16201120091303141524763671 24301680136954712287145507)
                  ·
                    refine ⟨36452520205432068430718261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24301680136954712287145507 36452520205432068430718261)
                    ·
                      refine ⟨3417423769259256415379837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36452520205432068430718261 3417423769259256415379837)
                      ·
                        rfl

theorem cell23_6655409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_6655409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6655409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6655409 prefixEnd_6655409 := by exact prefixLift 6655409
  have htrace : WordTrace (prefixWord ++ tailWord_6655409) baseStart_6655409 baseEnd_6655409 := by
    simpa [prefixWord, tailWord_6655409, baseEnd_6655409] using wordTrace_append hprefix tailTrace_6655409
  have hstable : (prefixWord ++ tailWord_6655409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6655409).length < 2 ^ (prefixWord ++ tailWord_6655409).sum := by decide
  have hdescent : baseEnd_6655409 < baseStart_6655409 := by decide
  rcases family_descends (prefixWord ++ tailWord_6655409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6655439 : List Nat := [1, 1, 2, 1, 1, 4, 2, 4, 1, 3, 3]
def baseStart_6655439 : Nat := 118140960795 + 6655439 * 2 ^ 59
def prefixEnd_6655439 : Nat := 4983230072969 + 3 ^ 40 * 6655439 * 2
def baseEnd_6655439 : Nat := 3417439173678891298004699

theorem tailTrace_6655439 : CollatzResearch.WordTrace tailWord_6655439 prefixEnd_6655439 3417439173678891298004699 := by
  unfold tailWord_6655439
  simp only [CollatzResearch.WordTrace]
  refine ⟨242743802535488636332305371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161829201690325757554870247 242743802535488636332305371)
  ·
    refine ⟨364115703803232954498458057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242743802535488636332305371 364115703803232954498458057)
    ·
      refine ⟨273086777852424715873843543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364115703803232954498458057 273086777852424715873843543)
      ·
        refine ⟨409630166778637073810765315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273086777852424715873843543 409630166778637073810765315)
        ·
          refine ⟨614445250167955610716147973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409630166778637073810765315 614445250167955610716147973)
          ·
            refine ⟨115208484406491677009277745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 614445250167955610716147973 115208484406491677009277745)
            ·
              refine ⟨86406363304868757756958309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115208484406491677009277745 86406363304868757756958309)
              ·
                refine ⟨16201193119662892079429683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86406363304868757756958309 16201193119662892079429683)
                ·
                  refine ⟨24301789679494338119144525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16201193119662892079429683 24301789679494338119144525)
                  ·
                    refine ⟨9113171129810376794679197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24301789679494338119144525 9113171129810376794679197)
                    ·
                      refine ⟨3417439173678891298004699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9113171129810376794679197 3417439173678891298004699)
                      ·
                        rfl

theorem cell23_6655439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 3, 3].length) (baseStart_6655439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6655439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6655439 prefixEnd_6655439 := by exact prefixLift 6655439
  have htrace : WordTrace (prefixWord ++ tailWord_6655439) baseStart_6655439 baseEnd_6655439 := by
    simpa [prefixWord, tailWord_6655439, baseEnd_6655439] using wordTrace_append hprefix tailTrace_6655439
  have hstable : (prefixWord ++ tailWord_6655439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6655439).length < 2 ^ (prefixWord ++ tailWord_6655439).sum := by decide
  have hdescent : baseEnd_6655439 < baseStart_6655439 := by decide
  rcases family_descends (prefixWord ++ tailWord_6655439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6655446 : List Nat := [5, 2, 1, 1, 1, 4, 9]
def baseStart_6655446 : Nat := 118140960795 + 6655446 * 2 ^ 59
def prefixEnd_6655446 : Nat := 4983230072969 + 3 ^ 40 * 6655446 * 2
def baseEnd_6655446 : Nat := 42190651457326824328607

theorem tailTrace_6655446 : CollatzResearch.WordTrace tailWord_6655446 prefixEnd_6655446 42190651457326824328607 := by
  unfold tailWord_6655446
  simp only [CollatzResearch.WordTrace]
  refine ⟨15171503615403954782988137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161829371897642184351873461 15171503615403954782988137)
  ·
    refine ⟨11378627711552966087241103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15171503615403954782988137 11378627711552966087241103)
    ·
      refine ⟨17067941567329449130861655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11378627711552966087241103 17067941567329449130861655)
      ·
        refine ⟨25601912350994173696292483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17067941567329449130861655 25601912350994173696292483)
        ·
          refine ⟨38402868526491260544438725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25601912350994173696292483 38402868526491260544438725)
          ·
            refine ⟨7200537848717111352082261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38402868526491260544438725 7200537848717111352082261)
            ·
              refine ⟨42190651457326824328607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7200537848717111352082261 42190651457326824328607)
              ·
                rfl

theorem cell23_6655446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 9].length) (baseStart_6655446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6655446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6655446 prefixEnd_6655446 := by exact prefixLift 6655446
  have htrace : WordTrace (prefixWord ++ tailWord_6655446) baseStart_6655446 baseEnd_6655446 := by
    simpa [prefixWord, tailWord_6655446, baseEnd_6655446] using wordTrace_append hprefix tailTrace_6655446
  have hstable : (prefixWord ++ tailWord_6655446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6655446).length < 2 ^ (prefixWord ++ tailWord_6655446).sum := by decide
  have hdescent : baseEnd_6655446 < baseStart_6655446 := by decide
  rcases family_descends (prefixWord ++ tailWord_6655446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6655457 : List Nat := [1, 2, 3, 1, 2, 4, 3, 2, 1, 2, 2]
def baseStart_6655457 : Nat := 118140960795 + 6655457 * 2 ^ 59
def prefixEnd_6655457 : Nat := 4983230072969 + 3 ^ 40 * 6655457 * 2
def baseEnd_6655457 : Nat := 3417448416330672227579617

theorem tailTrace_6655457 : CollatzResearch.WordTrace tailWord_6655457 prefixEnd_6655457 3417448416330672227579617 := by
  unfold tailWord_6655457
  simp only [CollatzResearch.WordTrace]
  refine ⟨242744459049423425406460625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161829639366282283604307083 242744459049423425406460625)
  ·
    refine ⟨182058344287067569054845469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242744459049423425406460625 182058344287067569054845469)
    ·
      refine ⟨68271879107650338395567051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182058344287067569054845469 68271879107650338395567051)
      ·
        refine ⟨102407818661475507593350577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68271879107650338395567051 102407818661475507593350577)
        ·
          refine ⟨76805863996106630695012933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102407818661475507593350577 76805863996106630695012933)
          ·
            refine ⟨14401099499269993255314925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76805863996106630695012933 14401099499269993255314925)
            ·
              refine ⟨5400412312226247470743097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14401099499269993255314925 5400412312226247470743097)
              ·
                refine ⟨4050309234169685603057323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5400412312226247470743097 4050309234169685603057323)
                ·
                  refine ⟨6075463851254528404585985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4050309234169685603057323 6075463851254528404585985)
                  ·
                    refine ⟨4556597888440896303439489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6075463851254528404585985 4556597888440896303439489)
                    ·
                      refine ⟨3417448416330672227579617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4556597888440896303439489 3417448416330672227579617)
                      ·
                        rfl

theorem cell23_6655457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 2, 1, 2, 2].length) (baseStart_6655457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6655457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6655457 prefixEnd_6655457 := by exact prefixLift 6655457
  have htrace : WordTrace (prefixWord ++ tailWord_6655457) baseStart_6655457 baseEnd_6655457 := by
    simpa [prefixWord, tailWord_6655457, baseEnd_6655457] using wordTrace_append hprefix tailTrace_6655457
  have hstable : (prefixWord ++ tailWord_6655457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6655457).length < 2 ^ (prefixWord ++ tailWord_6655457).sum := by decide
  have hdescent : baseEnd_6655457 < baseStart_6655457 := by decide
  rcases family_descends (prefixWord ++ tailWord_6655457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6655473 : List Nat := [1, 2, 2, 2, 3, 3, 1, 3, 2, 1, 3]
def baseStart_6655473 : Nat := 118140960795 + 6655473 * 2 ^ 59
def prefixEnd_6655473 : Nat := 4983230072969 + 3 ^ 40 * 6655473 * 2
def baseEnd_6655473 : Nat := 3417456632021144164979543

theorem tailTrace_6655473 : CollatzResearch.WordTrace tailWord_6655473 prefixEnd_6655473 3417456632021144164979543 := by
  unfold tailWord_6655473
  simp only [CollatzResearch.WordTrace]
  refine ⟨242745042617365460139043073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161830028411576973426028715 242745042617365460139043073)
  ·
    refine ⟨182058781963024095104282305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242745042617365460139043073 182058781963024095104282305)
    ·
      refine ⟨136544086472268071328211729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182058781963024095104282305 136544086472268071328211729)
      ·
        refine ⟨102408064854201053496158797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136544086472268071328211729 102408064854201053496158797)
        ·
          refine ⟨38403024320325395061059549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102408064854201053496158797 38403024320325395061059549)
          ·
            refine ⟨14401134120122023147897331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38403024320325395061059549 14401134120122023147897331)
            ·
              refine ⟨21601701180183034721845997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14401134120122023147897331 21601701180183034721845997)
              ·
                refine ⟨8100637942568638020692249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21601701180183034721845997 8100637942568638020692249)
                ·
                  refine ⟨6075478456926478515519187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8100637942568638020692249 6075478456926478515519187)
                  ·
                    refine ⟨9113217685389717773278781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6075478456926478515519187 9113217685389717773278781)
                    ·
                      refine ⟨3417456632021144164979543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9113217685389717773278781 3417456632021144164979543)
                      ·
                        rfl

theorem cell23_6655473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 3, 2, 1, 3].length) (baseStart_6655473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6655473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6655473 prefixEnd_6655473 := by exact prefixLift 6655473
  have htrace : WordTrace (prefixWord ++ tailWord_6655473) baseStart_6655473 baseEnd_6655473 := by
    simpa [prefixWord, tailWord_6655473, baseEnd_6655473] using wordTrace_append hprefix tailTrace_6655473
  have hstable : (prefixWord ++ tailWord_6655473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6655473).length < 2 ^ (prefixWord ++ tailWord_6655473).sum := by decide
  have hdescent : baseEnd_6655473 < baseStart_6655473 := by decide
  rcases family_descends (prefixWord ++ tailWord_6655473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6655494 : List Nat := [6, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5]
def baseStart_6655494 : Nat := 118140960795 + 6655494 * 2 ^ 59
def prefixEnd_6655494 : Nat := 4983230072969 + 3 ^ 40 * 6655494 * 2
def baseEnd_6655494 : Nat := 3417467415114888582816947

theorem tailTrace_6655494 : CollatzResearch.WordTrace tailWord_6655494 prefixEnd_6655494 3417467415114888582816947 := by
  unfold tailWord_6655494
  simp only [CollatzResearch.WordTrace]
  refine ⟨7585806517196543147673673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 161830539033526253817038357 7585806517196543147673673)
  ·
    refine ⟨5689354887897407360755255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7585806517196543147673673 5689354887897407360755255)
    ·
      refine ⟨8534032331846111041132883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5689354887897407360755255 8534032331846111041132883)
      ·
        refine ⟨12801048497769166561699325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8534032331846111041132883 12801048497769166561699325)
        ·
          refine ⟨4800393186663437460637247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12801048497769166561699325 4800393186663437460637247)
          ·
            refine ⟨7200589779995156190955871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4800393186663437460637247 7200589779995156190955871)
            ·
              refine ⟨10800884669992734286433807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7200589779995156190955871 10800884669992734286433807)
              ·
                refine ⟨16201327004989101429650711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10800884669992734286433807 16201327004989101429650711)
                ·
                  refine ⟨24301990507483652144476067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16201327004989101429650711 24301990507483652144476067)
                  ·
                    refine ⟨36452985761225478216714101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24301990507483652144476067 36452985761225478216714101)
                    ·
                      refine ⟨3417467415114888582816947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36452985761225478216714101 3417467415114888582816947)
                      ·
                        rfl

theorem cell23_6655494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_6655494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6655494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6655494 prefixEnd_6655494 := by exact prefixLift 6655494
  have htrace : WordTrace (prefixWord ++ tailWord_6655494) baseStart_6655494 baseEnd_6655494 := by
    simpa [prefixWord, tailWord_6655494, baseEnd_6655494] using wordTrace_append hprefix tailTrace_6655494
  have hstable : (prefixWord ++ tailWord_6655494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6655494).length < 2 ^ (prefixWord ++ tailWord_6655494).sum := by decide
  have hdescent : baseEnd_6655494 < baseStart_6655494 := by decide
  rcases family_descends (prefixWord ++ tailWord_6655494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6655496 : List Nat := [2, 1, 3, 2, 1, 1, 3, 1, 3, 4, 2]
def baseStart_6655496 : Nat := 118140960795 + 6655496 * 2 ^ 59
def prefixEnd_6655496 : Nat := 4983230072969 + 3 ^ 40 * 6655496 * 2
def baseEnd_6655496 : Nat := 3417468442076197574991937

theorem tailTrace_6655496 : CollatzResearch.WordTrace tailWord_6655496 prefixEnd_6655496 3417468442076197574991937 := by
  unfold tailWord_6655496
  simp only [CollatzResearch.WordTrace]
  refine ⟨121372940748141067533565171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161830587664188090044753561 121372940748141067533565171)
  ·
    refine ⟨182059411122211601300347757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121372940748141067533565171 182059411122211601300347757)
    ·
      refine ⟨68272279170829350487630409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182059411122211601300347757 68272279170829350487630409)
      ·
        refine ⟨51204209378122012865722807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68272279170829350487630409 51204209378122012865722807)
        ·
          refine ⟨76806314067183019298584211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51204209378122012865722807 76806314067183019298584211)
          ·
            refine ⟨115209471100774528947876317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76806314067183019298584211 115209471100774528947876317)
            ·
              refine ⟨43203551662790448355453619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115209471100774528947876317 43203551662790448355453619)
              ·
                refine ⟨64805327494185672533180429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43203551662790448355453619 64805327494185672533180429)
                ·
                  refine ⟨24301997810319627199942661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64805327494185672533180429 24301997810319627199942661)
                  ·
                    refine ⟨4556624589434930099989249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24301997810319627199942661 4556624589434930099989249)
                    ·
                      refine ⟨3417468442076197574991937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4556624589434930099989249 3417468442076197574991937)
                      ·
                        rfl

theorem cell23_6655496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 3, 4, 2].length) (baseStart_6655496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6655496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6655496 prefixEnd_6655496 := by exact prefixLift 6655496
  have htrace : WordTrace (prefixWord ++ tailWord_6655496) baseStart_6655496 baseEnd_6655496 := by
    simpa [prefixWord, tailWord_6655496, baseEnd_6655496] using wordTrace_append hprefix tailTrace_6655496
  have hstable : (prefixWord ++ tailWord_6655496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6655496).length < 2 ^ (prefixWord ++ tailWord_6655496).sum := by decide
  have hdescent : baseEnd_6655496 < baseStart_6655496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6655496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6655508 : List Nat := [2, 4, 3, 1, 3, 1, 2, 2, 1, 2, 2]
def baseStart_6655508 : Nat := 118140960795 + 6655508 * 2 ^ 59
def prefixEnd_6655508 : Nat := 4983230072969 + 3 ^ 40 * 6655508 * 2
def baseEnd_6655508 : Nat := 3417474603844051528041883

theorem tailTrace_6655508 : CollatzResearch.WordTrace tailWord_6655508 prefixEnd_6655508 3417474603844051528041883 := by
  unfold tailWord_6655508
  simp only [CollatzResearch.WordTrace]
  refine ⟨121373159586119330558283589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161830879448159107411044785 121373159586119330558283589)
  ·
    refine ⟨22757467422397374479678173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121373159586119330558283589 22757467422397374479678173)
    ·
      refine ⟨8534050283399015429879315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22757467422397374479678173 8534050283399015429879315)
      ·
        refine ⟨12801075425098523144818973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8534050283399015429879315 12801075425098523144818973)
        ·
          refine ⟨4800403284411946179307115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12801075425098523144818973 4800403284411946179307115)
          ·
            refine ⟨7200604926617919268960673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4800403284411946179307115 7200604926617919268960673)
            ·
              refine ⟨5400453694963439451720505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7200604926617919268960673 5400453694963439451720505)
              ·
                refine ⟨4050340271222579588790379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5400453694963439451720505 4050340271222579588790379)
                ·
                  refine ⟨6075510406833869383185569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4050340271222579588790379 6075510406833869383185569)
                  ·
                    refine ⟨4556632805125402037389177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6075510406833869383185569 4556632805125402037389177)
                    ·
                      refine ⟨3417474603844051528041883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4556632805125402037389177 3417474603844051528041883)
                      ·
                        rfl

theorem cell23_6655508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_6655508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6655508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6655508 prefixEnd_6655508 := by exact prefixLift 6655508
  have htrace : WordTrace (prefixWord ++ tailWord_6655508) baseStart_6655508 baseEnd_6655508 := by
    simpa [prefixWord, tailWord_6655508, baseEnd_6655508] using wordTrace_append hprefix tailTrace_6655508
  have hstable : (prefixWord ++ tailWord_6655508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6655508).length < 2 ^ (prefixWord ++ tailWord_6655508).sum := by decide
  have hdescent : baseEnd_6655508 < baseStart_6655508 := by decide
  rcases family_descends (prefixWord ++ tailWord_6655508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6655530 : List Nat := [3, 1, 4, 1, 1, 1, 1, 5, 2, 2, 2]
def baseStart_6655530 : Nat := 118140960795 + 6655530 * 2 ^ 59
def prefixEnd_6655530 : Nat := 4983230072969 + 3 ^ 40 * 6655530 * 2
def baseEnd_6655530 : Nat := 3417485900418450441966781

theorem tailTrace_6655530 : CollatzResearch.WordTrace tailWord_6655530 prefixEnd_6655530 3417485900418450441966781 := by
  unfold tailWord_6655530
  simp only [CollatzResearch.WordTrace]
  refine ⟨60686780394539739718467011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161831414385439305915912029 60686780394539739718467011)
  ·
    refine ⟨91030170591809609577700517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60686780394539739718467011 91030170591809609577700517)
    ·
      refine ⟨17068156985964301795818847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91030170591809609577700517 17068156985964301795818847)
      ·
        refine ⟨25602235478946452693728271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17068156985964301795818847 25602235478946452693728271)
        ·
          refine ⟨38403353218419679040592407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25602235478946452693728271 38403353218419679040592407)
          ·
            refine ⟨57605029827629518560888611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38403353218419679040592407 57605029827629518560888611)
            ·
              refine ⟨86407544741444277841332917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57605029827629518560888611 86407544741444277841332917)
              ·
                refine ⟨8100707319510401047624961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86407544741444277841332917 8100707319510401047624961)
                ·
                  refine ⟨6075530489632800785718721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8100707319510401047624961 6075530489632800785718721)
                  ·
                    refine ⟨4556647867224600589289041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6075530489632800785718721 4556647867224600589289041)
                    ·
                      refine ⟨3417485900418450441966781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4556647867224600589289041 3417485900418450441966781)
                      ·
                        rfl

theorem cell23_6655530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_6655530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6655530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6655530 prefixEnd_6655530 := by exact prefixLift 6655530
  have htrace : WordTrace (prefixWord ++ tailWord_6655530) baseStart_6655530 baseEnd_6655530 := by
    simpa [prefixWord, tailWord_6655530, baseEnd_6655530] using wordTrace_append hprefix tailTrace_6655530
  have hstable : (prefixWord ++ tailWord_6655530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6655530).length < 2 ^ (prefixWord ++ tailWord_6655530).sum := by decide
  have hdescent : baseEnd_6655530 < baseStart_6655530 := by decide
  rcases family_descends (prefixWord ++ tailWord_6655530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6655553 : List Nat := [1, 2, 5, 1, 1, 1, 4, 3, 5]
def baseStart_6655553 : Nat := 118140960795 + 6655553 * 2 ^ 59
def prefixEnd_6655553 : Nat := 4983230072969 + 3 ^ 40 * 6655553 * 2
def baseEnd_6655553 : Nat := 379721967830389316886575

theorem tailTrace_6655553 : CollatzResearch.WordTrace tailWord_6655553 prefixEnd_6655553 379721967830389316886575 := by
  unfold tailWord_6655553
  simp only [CollatzResearch.WordTrace]
  refine ⟨242747960457075633801955313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161831973638050422534636875 242747960457075633801955313)
  ·
    refine ⟨182060970342806725351466485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242747960457075633801955313 182060970342806725351466485)
    ·
      refine ⟨17068215969638130501699983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 182060970342806725351466485 17068215969638130501699983)
      ·
        refine ⟨25602323954457195752549975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17068215969638130501699983 25602323954457195752549975)
        ·
          refine ⟨38403485931685793628824963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25602323954457195752549975 38403485931685793628824963)
          ·
            refine ⟨57605228897528690443237445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38403485931685793628824963 57605228897528690443237445)
            ·
              refine ⟨10800980418286629458107021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57605228897528690443237445 10800980418286629458107021)
              ·
                refine ⟨4050367656857486046790133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10800980418286629458107021 4050367656857486046790133)
                ·
                  refine ⟨379721967830389316886575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4050367656857486046790133 379721967830389316886575)
                  ·
                    rfl

theorem cell23_6655553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 3, 5].length) (baseStart_6655553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6655553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6655553 prefixEnd_6655553 := by exact prefixLift 6655553
  have htrace : WordTrace (prefixWord ++ tailWord_6655553) baseStart_6655553 baseEnd_6655553 := by
    simpa [prefixWord, tailWord_6655553, baseEnd_6655553] using wordTrace_append hprefix tailTrace_6655553
  have hstable : (prefixWord ++ tailWord_6655553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6655553).length < 2 ^ (prefixWord ++ tailWord_6655553).sum := by decide
  have hdescent : baseEnd_6655553 < baseStart_6655553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6655553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6655581 : List Nat := [1, 4, 4, 2, 1, 1, 3, 1, 2, 2, 2]
def baseStart_6655581 : Nat := 118140960795 + 6655581 * 2 ^ 59
def prefixEnd_6655581 : Nat := 4983230072969 + 3 ^ 40 * 6655581 * 2
def baseEnd_6655581 : Nat := 3417512087931829742429047

theorem tailTrace_6655581 : CollatzResearch.WordTrace tailWord_6655581 prefixEnd_6655581 3417512087931829742429047 := by
  unfold tailWord_6655581
  simp only [CollatzResearch.WordTrace]
  refine ⟨242748981700974194583974597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161832654467316129722649731 242748981700974194583974597)
  ·
    refine ⟨45515434068932661484495237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 242748981700974194583974597 45515434068932661484495237)
    ·
      refine ⟨8534143887924874028342857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45515434068932661484495237 8534143887924874028342857)
      ·
        refine ⟨6400607915943655521257143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8534143887924874028342857 6400607915943655521257143)
        ·
          refine ⟨9600911873915483281885715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6400607915943655521257143 9600911873915483281885715)
          ·
            refine ⟨14401367810873224922828573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9600911873915483281885715 14401367810873224922828573)
            ·
              refine ⟨5400512929077459346060715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14401367810873224922828573 5400512929077459346060715)
              ·
                refine ⟨8100769393616189019091073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5400512929077459346060715 8100769393616189019091073)
                ·
                  refine ⟨6075577045212141764318305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8100769393616189019091073 6075577045212141764318305)
                  ·
                    refine ⟨4556682783909106323238729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6075577045212141764318305 4556682783909106323238729)
                    ·
                      refine ⟨3417512087931829742429047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4556682783909106323238729 3417512087931829742429047)
                      ·
                        rfl

theorem cell23_6655581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_6655581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6655581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6655581 prefixEnd_6655581 := by exact prefixLift 6655581
  have htrace : WordTrace (prefixWord ++ tailWord_6655581) baseStart_6655581 baseEnd_6655581 := by
    simpa [prefixWord, tailWord_6655581, baseEnd_6655581] using wordTrace_append hprefix tailTrace_6655581
  have hstable : (prefixWord ++ tailWord_6655581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6655581).length < 2 ^ (prefixWord ++ tailWord_6655581).sum := by decide
  have hdescent : baseEnd_6655581 < baseStart_6655581 := by decide
  rcases family_descends (prefixWord ++ tailWord_6655581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6655599 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 1, 6, 4]
def baseStart_6655599 : Nat := 118140960795 + 6655599 * 2 ^ 59
def prefixEnd_6655599 : Nat := 4983230072969 + 3 ^ 40 * 6655599 * 2
def baseEnd_6655599 : Nat := 3417521330583610672003963

theorem tailTrace_6655599 : CollatzResearch.WordTrace tailWord_6655599 prefixEnd_6655599 3417521330583610672003963 := by
  unfold tailWord_6655599
  simp only [CollatzResearch.WordTrace]
  refine ⟨242749638214908983658129851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161833092143272655772086567 242749638214908983658129851)
  ·
    refine ⟨364124457322363475487194777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242749638214908983658129851 364124457322363475487194777)
    ·
      refine ⟨273093342991772606615396083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364124457322363475487194777 273093342991772606615396083)
      ·
        refine ⟨409640014487658909923094125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273093342991772606615396083 409640014487658909923094125)
        ·
          refine ⟨153615005432872091221160297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 409640014487658909923094125 153615005432872091221160297)
          ·
            refine ⟨115211254074654068415870223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153615005432872091221160297 115211254074654068415870223)
            ·
              refine ⟨172816881111981102623805335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115211254074654068415870223 172816881111981102623805335)
              ·
                refine ⟨259225321667971653935708003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172816881111981102623805335 259225321667971653935708003)
                ·
                  refine ⟨388837982501957480903562005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 259225321667971653935708003 388837982501957480903562005)
                  ·
                    refine ⟨18226780429779256917354469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 388837982501957480903562005 18226780429779256917354469)
                    ·
                      refine ⟨3417521330583610672003963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18226780429779256917354469 3417521330583610672003963)
                      ·
                        rfl

theorem cell23_6655599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 6, 4].length) (baseStart_6655599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6655599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6655599 prefixEnd_6655599 := by exact prefixLift 6655599
  have htrace : WordTrace (prefixWord ++ tailWord_6655599) baseStart_6655599 baseEnd_6655599 := by
    simpa [prefixWord, tailWord_6655599, baseEnd_6655599] using wordTrace_append hprefix tailTrace_6655599
  have hstable : (prefixWord ++ tailWord_6655599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6655599).length < 2 ^ (prefixWord ++ tailWord_6655599).sum := by decide
  have hdescent : baseEnd_6655599 < baseStart_6655599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6655599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6655609 : List Nat := [1, 2, 1, 3, 3, 1, 1, 1, 10]
def baseStart_6655609 : Nat := 118140960795 + 6655609 * 2 ^ 59
def prefixEnd_6655609 : Nat := 4983230072969 + 3 ^ 40 * 6655609 * 2
def baseEnd_6655609 : Nat := 379725162821128403653213

theorem tailTrace_6655609 : CollatzResearch.WordTrace tailWord_6655609 prefixEnd_6655609 379725162821128403653213 := by
  unfold tailWord_6655609
  simp only [CollatzResearch.WordTrace]
  refine ⟨242750002944872755365993881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161833335296581836910662587 242750002944872755365993881)
  ·
    refine ⟨182062502208654566524495411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242750002944872755365993881 182062502208654566524495411)
    ·
      refine ⟨273093753312981849786743117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182062502208654566524495411 273093753312981849786743117)
      ·
        refine ⟨102410157492368193670028669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273093753312981849786743117 102410157492368193670028669)
        ·
          refine ⟨38403809059638072626260751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102410157492368193670028669 38403809059638072626260751)
          ·
            refine ⟨57605713589457108939391127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38403809059638072626260751 57605713589457108939391127)
            ·
              refine ⟨86408570384185663409086691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57605713589457108939391127 86408570384185663409086691)
              ·
                refine ⟨129612855576278495113630037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86408570384185663409086691 129612855576278495113630037)
                ·
                  refine ⟨379725162821128403653213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 129612855576278495113630037 379725162821128403653213)
                  ·
                    rfl

theorem cell23_6655609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 10].length) (baseStart_6655609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6655609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6655609 prefixEnd_6655609 := by exact prefixLift 6655609
  have htrace : WordTrace (prefixWord ++ tailWord_6655609) baseStart_6655609 baseEnd_6655609 := by
    simpa [prefixWord, tailWord_6655609, baseEnd_6655609] using wordTrace_append hprefix tailTrace_6655609
  have hstable : (prefixWord ++ tailWord_6655609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6655609).length < 2 ^ (prefixWord ++ tailWord_6655609).sum := by decide
  have hdescent : baseEnd_6655609 < baseStart_6655609 := by decide
  rcases family_descends (prefixWord ++ tailWord_6655609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6655623 : List Nat := [1, 1, 4, 2, 1, 4, 1, 2, 2, 2, 3]
def baseStart_6655623 : Nat := 118140960795 + 6655623 * 2 ^ 59
def prefixEnd_6655623 : Nat := 4983230072969 + 3 ^ 40 * 6655623 * 2
def baseEnd_6655623 : Nat := 3417533654119318578103853

theorem tailTrace_6655623 : CollatzResearch.WordTrace tailWord_6655623 prefixEnd_6655623 3417533654119318578103853 := by
  unfold tailWord_6655623
  simp only [CollatzResearch.WordTrace]
  refine ⟨242750513566822035757003523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161833675711214690504669015 242750513566822035757003523)
  ·
    refine ⟨364125770350233053635505285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242750513566822035757003523 364125770350233053635505285)
    ·
      refine ⟨68273581940668697556657241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 364125770350233053635505285 68273581940668697556657241)
      ·
        refine ⟨51205186455501523167492931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68273581940668697556657241 51205186455501523167492931)
        ·
          refine ⟨76807779683252284751239397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51205186455501523167492931 76807779683252284751239397)
          ·
            refine ⟨14401458690609803390857387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76807779683252284751239397 14401458690609803390857387)
            ·
              refine ⟨21602188035914705086286081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14401458690609803390857387 21602188035914705086286081)
              ·
                refine ⟨16201641026936028814714561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21602188035914705086286081 16201641026936028814714561)
                ·
                  refine ⟨12151230770202021611035921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16201641026936028814714561 12151230770202021611035921)
                  ·
                    refine ⟨9113423077651516208276941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12151230770202021611035921 9113423077651516208276941)
                    ·
                      refine ⟨3417533654119318578103853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9113423077651516208276941 3417533654119318578103853)
                      ·
                        rfl

theorem cell23_6655623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_6655623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6655623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6655623 prefixEnd_6655623 := by exact prefixLift 6655623
  have htrace : WordTrace (prefixWord ++ tailWord_6655623) baseStart_6655623 baseEnd_6655623 := by
    simpa [prefixWord, tailWord_6655623, baseEnd_6655623] using wordTrace_append hprefix tailTrace_6655623
  have hstable : (prefixWord ++ tailWord_6655623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6655623).length < 2 ^ (prefixWord ++ tailWord_6655623).sum := by decide
  have hdescent : baseEnd_6655623 < baseStart_6655623 := by decide
  rcases family_descends (prefixWord ++ tailWord_6655623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6655626 : List Nat := [3, 1, 2, 3, 2, 1, 2, 1, 8]
def baseStart_6655626 : Nat := 118140960795 + 6655626 * 2 ^ 59
def prefixEnd_6655626 : Nat := 4983230072969 + 3 ^ 40 * 6655626 * 2
def baseEnd_6655626 : Nat := 379726132729031340707371

theorem tailTrace_6655626 : CollatzResearch.WordTrace tailWord_6655626 prefixEnd_6655626 379726132729031340707371 := by
  unfold tailWord_6655626
  simp only [CollatzResearch.WordTrace]
  refine ⟨60687655746452791817340683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161833748657207444846241821 60687655746452791817340683)
  ·
    refine ⟨91031483619679187726011025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60687655746452791817340683 91031483619679187726011025)
    ·
      refine ⟨68273612714759390794508269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91031483619679187726011025 68273612714759390794508269)
      ·
        refine ⟨25602604768034771547940601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68273612714759390794508269 25602604768034771547940601)
        ·
          refine ⟨19201953576026078660955451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25602604768034771547940601 19201953576026078660955451)
          ·
            refine ⟨28802930364039117991433177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19201953576026078660955451 28802930364039117991433177)
            ·
              refine ⟨21602197773029338493574883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28802930364039117991433177 21602197773029338493574883)
              ·
                refine ⟨32403296659544007740362325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21602197773029338493574883 32403296659544007740362325)
                ·
                  refine ⟨379726132729031340707371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32403296659544007740362325 379726132729031340707371)
                  ·
                    rfl

theorem cell23_6655626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 8].length) (baseStart_6655626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6655626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6655626 prefixEnd_6655626 := by exact prefixLift 6655626
  have htrace : WordTrace (prefixWord ++ tailWord_6655626) baseStart_6655626 baseEnd_6655626 := by
    simpa [prefixWord, tailWord_6655626, baseEnd_6655626] using wordTrace_append hprefix tailTrace_6655626
  have hstable : (prefixWord ++ tailWord_6655626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6655626).length < 2 ^ (prefixWord ++ tailWord_6655626).sum := by decide
  have hdescent : baseEnd_6655626 < baseStart_6655626 := by decide
  rcases family_descends (prefixWord ++ tailWord_6655626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6655630 : List Nat := [4, 1, 1, 3, 1, 4, 1, 1, 3, 4]
def baseStart_6655630 : Nat := 118140960795 + 6655630 * 2 ^ 59
def prefixEnd_6655630 : Nat := 4983230072969 + 3 ^ 40 * 6655630 * 2
def baseEnd_6655630 : Nat := 1139179082827966683572107

theorem tailTrace_6655630 : CollatzResearch.WordTrace tailWord_6655630 prefixEnd_6655630 1139179082827966683572107 := by
  unfold tailWord_6655630
  simp only [CollatzResearch.WordTrace]
  refine ⟨30343846109724584494063543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161833845918531117301672229 30343846109724584494063543)
  ·
    refine ⟨45515769164586876741095315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30343846109724584494063543 45515769164586876741095315)
    ·
      refine ⟨68273653746880315111642973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45515769164586876741095315 68273653746880315111642973)
      ·
        refine ⟨25602620155080118166866115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68273653746880315111642973 25602620155080118166866115)
        ·
          refine ⟨38403930232620177250299173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25602620155080118166866115 38403930232620177250299173)
          ·
            refine ⟨7200736918616283234431095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38403930232620177250299173 7200736918616283234431095)
            ·
              refine ⟨10801105377924424851646643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7200736918616283234431095 10801105377924424851646643)
              ·
                refine ⟨16201658066886637277469965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10801105377924424851646643 16201658066886637277469965)
                ·
                  refine ⟨6075621775082488979051237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16201658066886637277469965 6075621775082488979051237)
                  ·
                    refine ⟨1139179082827966683572107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6075621775082488979051237 1139179082827966683572107)
                    ·
                      rfl

theorem cell23_6655630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 3, 4].length) (baseStart_6655630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6655630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6655630 prefixEnd_6655630 := by exact prefixLift 6655630
  have htrace : WordTrace (prefixWord ++ tailWord_6655630) baseStart_6655630 baseEnd_6655630 := by
    simpa [prefixWord, tailWord_6655630, baseEnd_6655630] using wordTrace_append hprefix tailTrace_6655630
  have hstable : (prefixWord ++ tailWord_6655630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6655630).length < 2 ^ (prefixWord ++ tailWord_6655630).sum := by decide
  have hdescent : baseEnd_6655630 < baseStart_6655630 := by decide
  rcases family_descends (prefixWord ++ tailWord_6655630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6655653 : List Nat := [1, 3, 1, 2, 1, 2, 2, 4, 3, 1, 3]
def baseStart_6655653 : Nat := 118140960795 + 6655653 * 2 ^ 59
def prefixEnd_6655653 : Nat := 4983230072969 + 3 ^ 40 * 6655653 * 2
def baseEnd_6655653 : Nat := 3417549058538953460728715

theorem tailTrace_6655653 : CollatzResearch.WordTrace tailWord_6655653 prefixEnd_6655653 3417549058538953460728715 := by
  unfold tailWord_6655653
  simp only [CollatzResearch.WordTrace]
  refine ⟨242751607756713350880595613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161834405171142233920397075 242751607756713350880595613)
  ·
    refine ⟨91031852908767506580223355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242751607756713350880595613 91031852908767506580223355)
    ·
      refine ⟨136547779363151259870335033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91031852908767506580223355 136547779363151259870335033)
      ·
        refine ⟨102410834522363444902751275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136547779363151259870335033 102410834522363444902751275)
        ·
          refine ⟨153616251783545167354126913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102410834522363444902751275 153616251783545167354126913)
          ·
            refine ⟨115212188837658875515595185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153616251783545167354126913 115212188837658875515595185)
            ·
              refine ⟨86409141628244156636696389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115212188837658875515595185 86409141628244156636696389)
              ·
                refine ⟨16201714055295779369380573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86409141628244156636696389 16201714055295779369380573)
                ·
                  refine ⟨6075642770735917263517715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16201714055295779369380573 6075642770735917263517715)
                  ·
                    refine ⟨9113464156103875895276573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6075642770735917263517715 9113464156103875895276573)
                    ·
                      refine ⟨3417549058538953460728715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9113464156103875895276573 3417549058538953460728715)
                      ·
                        rfl

theorem cell23_6655653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 3, 1, 3].length) (baseStart_6655653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6655653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6655653 prefixEnd_6655653 := by exact prefixLift 6655653
  have htrace : WordTrace (prefixWord ++ tailWord_6655653) baseStart_6655653 baseEnd_6655653 := by
    simpa [prefixWord, tailWord_6655653, baseEnd_6655653] using wordTrace_append hprefix tailTrace_6655653
  have hstable : (prefixWord ++ tailWord_6655653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6655653).length < 2 ^ (prefixWord ++ tailWord_6655653).sum := by decide
  have hdescent : baseEnd_6655653 < baseStart_6655653 := by decide
  rcases family_descends (prefixWord ++ tailWord_6655653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6655703 : List Nat := [1, 1, 3, 2, 1, 3, 1, 5, 2, 4]
def baseStart_6655703 : Nat := 118140960795 + 6655703 * 2 ^ 59
def prefixEnd_6655703 : Nat := 4983230072969 + 3 ^ 40 * 6655703 * 2
def baseEnd_6655703 : Nat := 1139191577523892755034495

theorem tailTrace_6655703 : CollatzResearch.WordTrace tailWord_6655703 prefixEnd_6655703 1139191577523892755034495 := by
  unfold tailWord_6655703
  simp only [CollatzResearch.WordTrace]
  refine ⟨242753431406532209419915763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161835620937688139613277175 242753431406532209419915763)
  ·
    refine ⟨364130147109798314129873645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242753431406532209419915763 364130147109798314129873645)
    ·
      refine ⟨136548805166174367798702617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 364130147109798314129873645 136548805166174367798702617)
      ·
        refine ⟨102411603874630775849026963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136548805166174367798702617 102411603874630775849026963)
        ·
          refine ⟨153617405811946163773540445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102411603874630775849026963 153617405811946163773540445)
          ·
            refine ⟨57606527179479811415077667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153617405811946163773540445 57606527179479811415077667)
            ·
              refine ⟨86409790769219717122616501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57606527179479811415077667 86409790769219717122616501)
              ·
                refine ⟨8100917884614348480245297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86409790769219717122616501 8100917884614348480245297)
                ·
                  refine ⟨6075688413460761360183973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8100917884614348480245297 6075688413460761360183973)
                  ·
                    refine ⟨1139191577523892755034495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6075688413460761360183973 1139191577523892755034495)
                    ·
                      rfl

theorem cell23_6655703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 5, 2, 4].length) (baseStart_6655703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6655703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6655703 prefixEnd_6655703 := by exact prefixLift 6655703
  have htrace : WordTrace (prefixWord ++ tailWord_6655703) baseStart_6655703 baseEnd_6655703 := by
    simpa [prefixWord, tailWord_6655703, baseEnd_6655703] using wordTrace_append hprefix tailTrace_6655703
  have hstable : (prefixWord ++ tailWord_6655703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6655703).length < 2 ^ (prefixWord ++ tailWord_6655703).sum := by decide
  have hdescent : baseEnd_6655703 < baseStart_6655703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6655703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6655730 : List Nat := [3, 2, 1, 3, 1, 1, 3, 3, 1, 2, 3]
def baseStart_6655730 : Nat := 118140960795 + 6655730 * 2 ^ 59
def prefixEnd_6655730 : Nat := 4983230072969 + 3 ^ 40 * 6655730 * 2
def baseEnd_6655730 : Nat := 3417588596549349659465861

theorem tailTrace_6655730 : CollatzResearch.WordTrace tailWord_6655730 prefixEnd_6655730 3417588596549349659465861 := by
  unfold tailWord_6655730
  simp only [CollatzResearch.WordTrace]
  refine ⟨60688604044358598257787161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161836277451622928687432429 60688604044358598257787161)
  ·
    refine ⟨45516453033268948693340371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60688604044358598257787161 45516453033268948693340371)
    ·
      refine ⟨68274679549903423040010557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45516453033268948693340371 68274679549903423040010557)
      ·
        refine ⟨25603004831213783640003959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68274679549903423040010557 25603004831213783640003959)
        ·
          refine ⟨38404507246820675460005939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25603004831213783640003959 38404507246820675460005939)
          ·
            refine ⟨57606760870231013190008909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38404507246820675460005939 57606760870231013190008909)
            ·
              refine ⟨21602535326336629946253341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57606760870231013190008909 21602535326336629946253341)
              ·
                refine ⟨8100950747376236229845003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21602535326336629946253341 8100950747376236229845003)
                ·
                  refine ⟨12151426121064354344767505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8100950747376236229845003 12151426121064354344767505)
                  ·
                    refine ⟨9113569590798265758575629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12151426121064354344767505 9113569590798265758575629)
                    ·
                      refine ⟨3417588596549349659465861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9113569590798265758575629 3417588596549349659465861)
                      ·
                        rfl

theorem cell23_6655730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_6655730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6655730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6655730 prefixEnd_6655730 := by exact prefixLift 6655730
  have htrace : WordTrace (prefixWord ++ tailWord_6655730) baseStart_6655730 baseEnd_6655730 := by
    simpa [prefixWord, tailWord_6655730, baseEnd_6655730] using wordTrace_append hprefix tailTrace_6655730
  have hstable : (prefixWord ++ tailWord_6655730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6655730).length < 2 ^ (prefixWord ++ tailWord_6655730).sum := by decide
  have hdescent : baseEnd_6655730 < baseStart_6655730 := by decide
  rcases family_descends (prefixWord ++ tailWord_6655730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6655817 : List Nat := [1, 2, 1, 1, 2, 4, 3, 3, 2, 2, 2]
def baseStart_6655817 : Nat := 118140960795 + 6655817 * 2 ^ 59
def prefixEnd_6655817 : Nat := 4983230072969 + 3 ^ 40 * 6655817 * 2
def baseEnd_6655817 : Nat := 3417633269366290819077961

theorem tailTrace_6655817 : CollatzResearch.WordTrace tailWord_6655817 prefixEnd_6655817 3417633269366290819077961 := by
  unfold tailWord_6655817
  simp only [CollatzResearch.WordTrace]
  refine ⟨242757589328119206889565705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161838392885412804593043803 242757589328119206889565705)
  ·
    refine ⟨182068191996089405167174279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242757589328119206889565705 182068191996089405167174279)
    ·
      refine ⟨273102287994134107750761419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182068191996089405167174279 273102287994134107750761419)
      ·
        refine ⟨409653431991201161626142129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273102287994134107750761419 409653431991201161626142129)
        ·
          refine ⟨307240073993400871219606597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 409653431991201161626142129 307240073993400871219606597)
          ·
            refine ⟨57607513873762663353676237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 307240073993400871219606597 57607513873762663353676237)
            ·
              refine ⟨21602817702660998757628589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57607513873762663353676237 21602817702660998757628589)
              ·
                refine ⟨8101056638497874534110721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21602817702660998757628589 8101056638497874534110721)
                ·
                  refine ⟨6075792478873405900583041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8101056638497874534110721 6075792478873405900583041)
                  ·
                    refine ⟨4556844359155054425437281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6075792478873405900583041 4556844359155054425437281)
                    ·
                      refine ⟨3417633269366290819077961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4556844359155054425437281 3417633269366290819077961)
                      ·
                        rfl

theorem cell23_6655817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 3, 2, 2, 2].length) (baseStart_6655817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6655817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6655817 prefixEnd_6655817 := by exact prefixLift 6655817
  have htrace : WordTrace (prefixWord ++ tailWord_6655817) baseStart_6655817 baseEnd_6655817 := by
    simpa [prefixWord, tailWord_6655817, baseEnd_6655817] using wordTrace_append hprefix tailTrace_6655817
  have hstable : (prefixWord ++ tailWord_6655817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6655817).length < 2 ^ (prefixWord ++ tailWord_6655817).sum := by decide
  have hdescent : baseEnd_6655817 < baseStart_6655817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6655817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6655821 : List Nat := [1, 6, 1, 2, 1, 3, 1, 2, 1, 3, 2]
def baseStart_6655821 : Nat := 118140960795 + 6655821 * 2 ^ 59
def prefixEnd_6655821 : Nat := 4983230072969 + 3 ^ 40 * 6655821 * 2
def baseEnd_6655821 : Nat := 3417635323288908803427943

theorem tailTrace_6655821 : CollatzResearch.WordTrace tailWord_6655821 prefixEnd_6655821 3417635323288908803427943 := by
  unfold tailWord_6655821
  simp only [CollatzResearch.WordTrace]
  refine ⟨242757735220104715572711317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161838490146736477048474211 242757735220104715572711317)
  ·
    refine ⟨11379268838442408542470843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 242757735220104715572711317 11379268838442408542470843)
    ·
      refine ⟨17068903257663612813706265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11379268838442408542470843 17068903257663612813706265)
      ·
        refine ⟨12801677443247709610279699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17068903257663612813706265 12801677443247709610279699)
        ·
          refine ⟨19202516164871564415419549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12801677443247709610279699 19202516164871564415419549)
          ·
            refine ⟨7200943561826836655782331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19202516164871564415419549 7200943561826836655782331)
            ·
              refine ⟨10801415342740254983673497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7200943561826836655782331 10801415342740254983673497)
              ·
                refine ⟨8101061507055191237755123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10801415342740254983673497 8101061507055191237755123)
                ·
                  refine ⟨12151592260582786856632685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8101061507055191237755123 12151592260582786856632685)
                  ·
                    refine ⟨4556847097718545071237257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12151592260582786856632685 4556847097718545071237257)
                    ·
                      refine ⟨3417635323288908803427943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4556847097718545071237257 3417635323288908803427943)
                      ·
                        rfl

theorem cell23_6655821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_6655821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6655821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6655821 prefixEnd_6655821 := by exact prefixLift 6655821
  have htrace : WordTrace (prefixWord ++ tailWord_6655821) baseStart_6655821 baseEnd_6655821 := by
    simpa [prefixWord, tailWord_6655821, baseEnd_6655821] using wordTrace_append hprefix tailTrace_6655821
  have hstable : (prefixWord ++ tailWord_6655821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6655821).length < 2 ^ (prefixWord ++ tailWord_6655821).sum := by decide
  have hdescent : baseEnd_6655821 < baseStart_6655821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6655821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6655913 : List Nat := [1, 2, 1, 1, 1, 1, 4, 6, 6]
def baseStart_6655913 : Nat := 118140960795 + 6655913 * 2 ^ 59
def prefixEnd_6655913 : Nat := 4983230072969 + 3 ^ 40 * 6655913 * 2
def baseEnd_6655913 : Nat := 379742507056569160386391

theorem tailTrace_6655913 : CollatzResearch.WordTrace tailWord_6655913 prefixEnd_6655913 379742507056569160386391 := by
  unfold tailWord_6655913
  simp only [CollatzResearch.WordTrace]
  refine ⟨242761090735771415285060393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161840727157180943523373595 242761090735771415285060393)
  ·
    refine ⟨182070818051828561463795295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242761090735771415285060393 182070818051828561463795295)
    ·
      refine ⟨273106227077742842195692943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182070818051828561463795295 273106227077742842195692943)
      ·
        refine ⟨409659340616614263293539415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273106227077742842195692943 409659340616614263293539415)
        ·
          refine ⟨614489010924921394940309123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409659340616614263293539415 614489010924921394940309123)
          ·
            refine ⟨921733516387382092410463685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 614489010924921394940309123 921733516387382092410463685)
            ·
              refine ⟨172825034322634142326961941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 921733516387382092410463685 172825034322634142326961941)
              ·
                refine ⟨8101173483873475421576341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 172825034322634142326961941 8101173483873475421576341)
                ·
                  refine ⟨379742507056569160386391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8101173483873475421576341 379742507056569160386391)
                  ·
                    rfl

theorem cell23_6655913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 6, 6].length) (baseStart_6655913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6655913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6655913 prefixEnd_6655913 := by exact prefixLift 6655913
  have htrace : WordTrace (prefixWord ++ tailWord_6655913) baseStart_6655913 baseEnd_6655913 := by
    simpa [prefixWord, tailWord_6655913, baseEnd_6655913] using wordTrace_append hprefix tailTrace_6655913
  have hstable : (prefixWord ++ tailWord_6655913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6655913).length < 2 ^ (prefixWord ++ tailWord_6655913).sum := by decide
  have hdescent : baseEnd_6655913 < baseStart_6655913 := by decide
  rcases family_descends (prefixWord ++ tailWord_6655913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6655960 : List Nat := [2, 1, 2, 2, 2, 2, 1, 5, 1, 5]
def baseStart_6655960 : Nat := 118140960795 + 6655960 * 2 ^ 59
def prefixEnd_6655960 : Nat := 4983230072969 + 3 ^ 40 * 6655960 * 2
def baseEnd_6655960 : Nat := 1139235565699961253196601

theorem tailTrace_6655960 : CollatzResearch.WordTrace tailWord_6655960 prefixEnd_6655960 1139235565699961253196601 := by
  unfold tailWord_6655960
  simp only [CollatzResearch.WordTrace]
  refine ⟨121381402483300571156010667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161841869977734094874680889 121381402483300571156010667)
  ·
    refine ⟨182072103724950856734016001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121381402483300571156010667 182072103724950856734016001)
    ·
      refine ⟨136554077793713142550512001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182072103724950856734016001 136554077793713142550512001)
      ·
        refine ⟨102415558345284856912884001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136554077793713142550512001 102415558345284856912884001)
        ·
          refine ⟨76811668758963642684663001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102415558345284856912884001 76811668758963642684663001)
          ·
            refine ⟨57608751569222732013497251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76811668758963642684663001 57608751569222732013497251)
            ·
              refine ⟨86413127353834098020245877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57608751569222732013497251 86413127353834098020245877)
              ·
                refine ⟨8101230689421946689398051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86413127353834098020245877 8101230689421946689398051)
                ·
                  refine ⟨12151846034132920034097077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8101230689421946689398051 12151846034132920034097077)
                  ·
                    refine ⟨1139235565699961253196601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12151846034132920034097077 1139235565699961253196601)
                    ·
                      rfl

theorem cell23_6655960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 5, 1, 5].length) (baseStart_6655960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6655960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6655960 prefixEnd_6655960 := by exact prefixLift 6655960
  have htrace : WordTrace (prefixWord ++ tailWord_6655960) baseStart_6655960 baseEnd_6655960 := by
    simpa [prefixWord, tailWord_6655960, baseEnd_6655960] using wordTrace_append hprefix tailTrace_6655960
  have hstable : (prefixWord ++ tailWord_6655960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6655960).length < 2 ^ (prefixWord ++ tailWord_6655960).sum := by decide
  have hdescent : baseEnd_6655960 < baseStart_6655960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6655960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6655967 : List Nat := [1, 1, 2, 3, 4, 1, 1, 1, 4, 3, 2]
def baseStart_6655967 : Nat := 118140960795 + 6655967 * 2 ^ 59
def prefixEnd_6655967 : Nat := 4983230072969 + 3 ^ 40 * 6655967 * 2
def baseEnd_6655967 : Nat := 3417710291464465232202271

theorem tailTrace_6655967 : CollatzResearch.WordTrace tailWord_6655967 prefixEnd_6655967 3417710291464465232202271 := by
  unfold tailWord_6655967
  simp only [CollatzResearch.WordTrace]
  refine ⟨242763060277575782507526155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161842040185050521671684103 242763060277575782507526155)
  ·
    refine ⟨364144590416363673761289233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242763060277575782507526155 364144590416363673761289233)
    ·
      refine ⟨273108442812272755320966925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364144590416363673761289233 273108442812272755320966925)
      ·
        refine ⟨102415666054602283245362597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273108442812272755320966925 102415666054602283245362597)
        ·
          refine ⟨19202937385237928108505487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102415666054602283245362597 19202937385237928108505487)
          ·
            refine ⟨28804406077856892162758231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19202937385237928108505487 28804406077856892162758231)
            ·
              refine ⟨43206609116785338244137347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28804406077856892162758231 43206609116785338244137347)
              ·
                refine ⟨64809913675178007366206021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43206609116785338244137347 64809913675178007366206021)
                ·
                  refine ⟨12151858814095876381163629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64809913675178007366206021 12151858814095876381163629)
                  ·
                    refine ⟨4556947055285953642936361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12151858814095876381163629 4556947055285953642936361)
                    ·
                      refine ⟨3417710291464465232202271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4556947055285953642936361 3417710291464465232202271)
                      ·
                        rfl

theorem cell23_6655967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 4, 3, 2].length) (baseStart_6655967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6655967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6655967 prefixEnd_6655967 := by exact prefixLift 6655967
  have htrace : WordTrace (prefixWord ++ tailWord_6655967) baseStart_6655967 baseEnd_6655967 := by
    simpa [prefixWord, tailWord_6655967, baseEnd_6655967] using wordTrace_append hprefix tailTrace_6655967
  have hstable : (prefixWord ++ tailWord_6655967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6655967).length < 2 ^ (prefixWord ++ tailWord_6655967).sum := by decide
  have hdescent : baseEnd_6655967 < baseStart_6655967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6655967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6655981 : List Nat := [1, 5, 1, 4, 1, 2, 2, 1, 6]
def baseStart_6655981 : Nat := 118140960795 + 6655981 * 2 ^ 59
def prefixEnd_6655981 : Nat := 4983230072969 + 3 ^ 40 * 6655981 * 2
def baseEnd_6655981 : Nat := 379746386688180908603023

theorem tailTrace_6655981 : CollatzResearch.WordTrace tailWord_6655981 prefixEnd_6655981 379746386688180908603023 := by
  unfold tailWord_6655981
  simp only [CollatzResearch.WordTrace]
  refine ⟨242763570899525062898535797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161842380599683375265690531 242763570899525062898535797)
  ·
    refine ⟨22759084771830474646737731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 242763570899525062898535797 22759084771830474646737731)
    ·
      refine ⟨34138627157745711970106597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22759084771830474646737731 34138627157745711970106597)
      ·
        refine ⟨6400992592077320994394987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34138627157745711970106597 6400992592077320994394987)
        ·
          refine ⟨9601488888115981491592481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6400992592077320994394987 9601488888115981491592481)
          ·
            refine ⟨7201116666086986118694361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9601488888115981491592481 7201116666086986118694361)
            ·
              refine ⟨5400837499565239589020771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7201116666086986118694361 5400837499565239589020771)
              ·
                refine ⟨8101256249347859383531157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5400837499565239589020771 8101256249347859383531157)
                ·
                  refine ⟨379746386688180908603023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8101256249347859383531157 379746386688180908603023)
                  ·
                    rfl

theorem cell23_6655981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 1, 6].length) (baseStart_6655981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6655981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6655981 prefixEnd_6655981 := by exact prefixLift 6655981
  have htrace : WordTrace (prefixWord ++ tailWord_6655981) baseStart_6655981 baseEnd_6655981 := by
    simpa [prefixWord, tailWord_6655981, baseEnd_6655981] using wordTrace_append hprefix tailTrace_6655981
  have hstable : (prefixWord ++ tailWord_6655981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6655981).length < 2 ^ (prefixWord ++ tailWord_6655981).sum := by decide
  have hdescent : baseEnd_6655981 < baseStart_6655981 := by decide
  rcases family_descends (prefixWord ++ tailWord_6655981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6655997 : List Nat := [1, 4, 1, 1, 1, 2, 5, 2, 1, 1, 4]
def baseStart_6655997 : Nat := 118140960795 + 6655997 * 2 ^ 59
def prefixEnd_6655997 : Nat := 4983230072969 + 3 ^ 40 * 6655997 * 2
def baseEnd_6655997 : Nat := 3417725695884100114827133

theorem tailTrace_6655997 : CollatzResearch.WordTrace tailWord_6655997 prefixEnd_6655997 3417725695884100114827133 := by
  unfold tailWord_6655997
  simp only [CollatzResearch.WordTrace]
  refine ⟨242764154467467097631118245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161842769644978065087412163 242764154467467097631118245)
  ·
    refine ⟨45518278962650080805834671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 242764154467467097631118245 45518278962650080805834671)
    ·
      refine ⟨68277418443975121208752007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45518278962650080805834671 68277418443975121208752007)
      ·
        refine ⟨102416127665962681813128011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68277418443975121208752007 102416127665962681813128011)
        ·
          refine ⟨153624191498944022719692017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102416127665962681813128011 153624191498944022719692017)
          ·
            refine ⟨115218143624208017039769013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153624191498944022719692017 115218143624208017039769013)
            ·
              refine ⟨10801700964769501597478345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 115218143624208017039769013 10801700964769501597478345)
              ·
                refine ⟨8101275723577126198108759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10801700964769501597478345 8101275723577126198108759)
                ·
                  refine ⟨12151913585365689297163139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8101275723577126198108759 12151913585365689297163139)
                  ·
                    refine ⟨18227870378048533945744709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12151913585365689297163139 18227870378048533945744709)
                    ·
                      refine ⟨3417725695884100114827133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18227870378048533945744709 3417725695884100114827133)
                      ·
                        rfl

theorem cell23_6655997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 2, 1, 1, 4].length) (baseStart_6655997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6655997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6655997 prefixEnd_6655997 := by exact prefixLift 6655997
  have htrace : WordTrace (prefixWord ++ tailWord_6655997) baseStart_6655997 baseEnd_6655997 := by
    simpa [prefixWord, tailWord_6655997, baseEnd_6655997] using wordTrace_append hprefix tailTrace_6655997
  have hstable : (prefixWord ++ tailWord_6655997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6655997).length < 2 ^ (prefixWord ++ tailWord_6655997).sum := by decide
  have hdescent : baseEnd_6655997 < baseStart_6655997 := by decide
  rcases family_descends (prefixWord ++ tailWord_6655997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6656014 : List Nat := [4, 1, 1, 2, 2, 1, 5, 1, 1, 1, 4]
def baseStart_6656014 : Nat := 118140960795 + 6656014 * 2 ^ 59
def prefixEnd_6656014 : Nat := 4983230072969 + 3 ^ 40 * 6656014 * 2
def baseEnd_6656014 : Nat := 3417734425055226548314555

theorem tailTrace_6656014 : CollatzResearch.WordTrace tailWord_6656014 prefixEnd_6656014 3417734425055226548314555 := by
  unfold tailWord_6656014
  simp only [CollatzResearch.WordTrace]
  refine ⟨30345596813550688691810887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161843183005603673022991397 30345596813550688691810887)
  ·
    refine ⟨45518395220326033037716331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30345596813550688691810887 45518395220326033037716331)
    ·
      refine ⟨68277592830489049556574497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45518395220326033037716331 68277592830489049556574497)
      ·
        refine ⟨51208194622866787167430873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68277592830489049556574497 51208194622866787167430873)
        ·
          refine ⟨38406145967150090375573155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51208194622866787167430873 38406145967150090375573155)
          ·
            refine ⟨57609218950725135563359733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38406145967150090375573155 57609218950725135563359733)
            ·
              refine ⟨5400864276630481459064975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57609218950725135563359733 5400864276630481459064975)
              ·
                refine ⟨8101296414945722188597463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5400864276630481459064975 8101296414945722188597463)
                ·
                  refine ⟨12151944622418583282896195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8101296414945722188597463 12151944622418583282896195)
                  ·
                    refine ⟨18227916933627874924344293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12151944622418583282896195 18227916933627874924344293)
                    ·
                      refine ⟨3417734425055226548314555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18227916933627874924344293 3417734425055226548314555)
                      ·
                        rfl

theorem cell23_6656014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 1, 1, 1, 4].length) (baseStart_6656014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6656014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6656014 prefixEnd_6656014 := by exact prefixLift 6656014
  have htrace : WordTrace (prefixWord ++ tailWord_6656014) baseStart_6656014 baseEnd_6656014 := by
    simpa [prefixWord, tailWord_6656014, baseEnd_6656014] using wordTrace_append hprefix tailTrace_6656014
  have hstable : (prefixWord ++ tailWord_6656014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6656014).length < 2 ^ (prefixWord ++ tailWord_6656014).sum := by decide
  have hdescent : baseEnd_6656014 < baseStart_6656014 := by decide
  rcases family_descends (prefixWord ++ tailWord_6656014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6656031 : List Nat := [1, 1, 2, 4, 1, 2, 3, 4, 1, 2, 2]
def baseStart_6656031 : Nat := 118140960795 + 6656031 * 2 ^ 59
def prefixEnd_6656031 : Nat := 4983230072969 + 3 ^ 40 * 6656031 * 2
def baseEnd_6656031 : Nat := 3417743154226352981801977

theorem tailTrace_6656031 : CollatzResearch.WordTrace tailWord_6656031 prefixEnd_6656031 3417743154226352981801977 := by
  unfold tailWord_6656031
  simp only [CollatzResearch.WordTrace]
  refine ⟨242765394549343921437855947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161843596366229280958570631 242765394549343921437855947)
  ·
    refine ⟨364148091824015882156783921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242765394549343921437855947 364148091824015882156783921)
    ·
      refine ⟨273111068868011911617587941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364148091824015882156783921 273111068868011911617587941)
      ·
        refine ⟨51208325412752233428297739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 273111068868011911617587941 51208325412752233428297739)
        ·
          refine ⟨76812488119128350142446609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51208325412752233428297739 76812488119128350142446609)
          ·
            refine ⟨57609366089346262606834957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76812488119128350142446609 57609366089346262606834957)
            ·
              refine ⟨21603512283504848477563109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57609366089346262606834957 21603512283504848477563109)
              ·
                refine ⟨4050658553157159089543083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21603512283504848477563109 4050658553157159089543083)
                ·
                  refine ⟨6075987829735738634314625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4050658553157159089543083 6075987829735738634314625)
                  ·
                    refine ⟨4556990872301803975735969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6075987829735738634314625 4556990872301803975735969)
                    ·
                      refine ⟨3417743154226352981801977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4556990872301803975735969 3417743154226352981801977)
                      ·
                        rfl

theorem cell23_6656031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 4, 1, 2, 2].length) (baseStart_6656031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6656031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6656031 prefixEnd_6656031 := by exact prefixLift 6656031
  have htrace : WordTrace (prefixWord ++ tailWord_6656031) baseStart_6656031 baseEnd_6656031 := by
    simpa [prefixWord, tailWord_6656031, baseEnd_6656031] using wordTrace_append hprefix tailTrace_6656031
  have hstable : (prefixWord ++ tailWord_6656031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6656031).length < 2 ^ (prefixWord ++ tailWord_6656031).sum := by decide
  have hdescent : baseEnd_6656031 < baseStart_6656031 := by decide
  rcases family_descends (prefixWord ++ tailWord_6656031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6656060 : List Nat := [2, 2, 2, 2, 2, 1, 2, 1, 2, 2, 5]
def baseStart_6656060 : Nat := 118140960795 + 6656060 * 2 ^ 59
def prefixEnd_6656060 : Nat := 4983230072969 + 3 ^ 40 * 6656060 * 2
def baseEnd_6656060 : Nat := 3417758045165333368339343

theorem tailTrace_6656060 : CollatzResearch.WordTrace tailWord_6656060 prefixEnd_6656060 3417758045165333368339343 := by
  unfold tailWord_6656060
  simp only [CollatzResearch.WordTrace]
  refine ⟨121383226133119429695330817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161844301510825906260441089 121383226133119429695330817)
  ·
    refine ⟨91037419599839572271498113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121383226133119429695330817 91037419599839572271498113)
    ·
      refine ⟨68278064699879679203623585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91037419599839572271498113 68278064699879679203623585)
      ·
        refine ⟨51208548524909759402717689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68278064699879679203623585 51208548524909759402717689)
        ·
          refine ⟨38406411393682319552038267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51208548524909759402717689 38406411393682319552038267)
          ·
            refine ⟨57609617090523479328057401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38406411393682319552038267 57609617090523479328057401)
            ·
              refine ⟨43207212817892609496043051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57609617090523479328057401 43207212817892609496043051)
              ·
                refine ⟨64810819226838914244064577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43207212817892609496043051 64810819226838914244064577)
                ·
                  refine ⟨48608114420129185683048433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64810819226838914244064577 48608114420129185683048433)
                  ·
                    refine ⟨36456085815096889262286325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48608114420129185683048433 36456085815096889262286325)
                    ·
                      refine ⟨3417758045165333368339343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36456085815096889262286325 3417758045165333368339343)
                      ·
                        rfl

theorem cell23_6656060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_6656060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6656060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6656060 prefixEnd_6656060 := by exact prefixLift 6656060
  have htrace : WordTrace (prefixWord ++ tailWord_6656060) baseStart_6656060 baseEnd_6656060 := by
    simpa [prefixWord, tailWord_6656060, baseEnd_6656060] using wordTrace_append hprefix tailTrace_6656060
  have hstable : (prefixWord ++ tailWord_6656060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6656060).length < 2 ^ (prefixWord ++ tailWord_6656060).sum := by decide
  have hdescent : baseEnd_6656060 < baseStart_6656060 := by decide
  rcases family_descends (prefixWord ++ tailWord_6656060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6656087 : List Nat := [1, 1, 3, 2, 2, 1, 2, 2, 3, 4, 2]
def baseStart_6656087 : Nat := 118140960795 + 6656087 * 2 ^ 59
def prefixEnd_6656087 : Nat := 4983230072969 + 3 ^ 40 * 6656087 * 2
def baseEnd_6656087 : Nat := 3417771909143004762701719

theorem tailTrace_6656087 : CollatzResearch.WordTrace tailWord_6656087 prefixEnd_6656087 3417771909143004762701719 := by
  unfold tailWord_6656087
  simp only [CollatzResearch.WordTrace]
  refine ⟨242767437037141043001894515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161844958024760695334596343 242767437037141043001894515)
  ·
    refine ⟨364151155555711564502841773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242767437037141043001894515 364151155555711564502841773)
    ·
      refine ⟨136556683333391836688565665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 364151155555711564502841773 136556683333391836688565665)
      ·
        refine ⟨102417512500043877516424249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136556683333391836688565665 102417512500043877516424249)
        ·
          refine ⟨76813134375032908137318187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102417512500043877516424249 76813134375032908137318187)
          ·
            refine ⟨115219701562549362205977281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76813134375032908137318187 115219701562549362205977281)
            ·
              refine ⟨86414776171912021654482961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115219701562549362205977281 86414776171912021654482961)
              ·
                refine ⟨64811082128934016240862221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86414776171912021654482961 64811082128934016240862221)
                ·
                  refine ⟨24304155798350256090323333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64811082128934016240862221 24304155798350256090323333)
                  ·
                    refine ⟨4557029212190673016935625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24304155798350256090323333 4557029212190673016935625)
                    ·
                      refine ⟨3417771909143004762701719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4557029212190673016935625 3417771909143004762701719)
                      ·
                        rfl

theorem cell23_6656087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 4, 2].length) (baseStart_6656087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6656087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6656087 prefixEnd_6656087 := by exact prefixLift 6656087
  have htrace : WordTrace (prefixWord ++ tailWord_6656087) baseStart_6656087 baseEnd_6656087 := by
    simpa [prefixWord, tailWord_6656087, baseEnd_6656087] using wordTrace_append hprefix tailTrace_6656087
  have hstable : (prefixWord ++ tailWord_6656087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6656087).length < 2 ^ (prefixWord ++ tailWord_6656087).sum := by decide
  have hdescent : baseEnd_6656087 < baseStart_6656087 := by decide
  rcases family_descends (prefixWord ++ tailWord_6656087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6656098 : List Nat := [3, 3, 2, 2, 3, 1, 1, 1, 1, 3, 3]
def baseStart_6656098 : Nat := 118140960795 + 6656098 * 2 ^ 59
def prefixEnd_6656098 : Nat := 4983230072969 + 3 ^ 40 * 6656098 * 2
def baseEnd_6656098 : Nat := 3417777557430204219664169

theorem tailTrace_6656098 : CollatzResearch.WordTrace tailWord_6656098 prefixEnd_6656098 3417777557430204219664169 := by
  unfold tailWord_6656098
  simp only [CollatzResearch.WordTrace]
  refine ⟨60691959560025297970136237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161845225493400794587029965 60691959560025297970136237)
  ·
    refine ⟨22759484835009486738801089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60691959560025297970136237 22759484835009486738801089)
    ·
      refine ⟨17069613626257115054100817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22759484835009486738801089 17069613626257115054100817)
      ·
        refine ⟨12802210219692836290575613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17069613626257115054100817 12802210219692836290575613)
        ·
          refine ⟨4800828832384813608965855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12802210219692836290575613 4800828832384813608965855)
          ·
            refine ⟨7201243248577220413448783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4800828832384813608965855 7201243248577220413448783)
            ·
              refine ⟨10801864872865830620173175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7201243248577220413448783 10801864872865830620173175)
              ·
                refine ⟨16202797309298745930259763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10801864872865830620173175 16202797309298745930259763)
                ·
                  refine ⟨24304195963948118895389645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16202797309298745930259763 24304195963948118895389645)
                  ·
                    refine ⟨9114073486480544585771117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24304195963948118895389645 9114073486480544585771117)
                    ·
                      refine ⟨3417777557430204219664169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9114073486480544585771117 3417777557430204219664169)
                      ·
                        rfl

theorem cell23_6656098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_6656098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6656098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6656098 prefixEnd_6656098 := by exact prefixLift 6656098
  have htrace : WordTrace (prefixWord ++ tailWord_6656098) baseStart_6656098 baseEnd_6656098 := by
    simpa [prefixWord, tailWord_6656098, baseEnd_6656098] using wordTrace_append hprefix tailTrace_6656098
  have hstable : (prefixWord ++ tailWord_6656098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6656098).length < 2 ^ (prefixWord ++ tailWord_6656098).sum := by decide
  have hdescent : baseEnd_6656098 < baseStart_6656098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6656098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6656144 : List Nat := [2, 1, 1, 1, 1, 1, 9, 2, 5]
def baseStart_6656144 : Nat := 118140960795 + 6656144 * 2 ^ 59
def prefixEnd_6656144 : Nat := 4983230072969 + 3 ^ 40 * 6656144 * 2
def baseEnd_6656144 : Nat := 379755686393367893298773

theorem tailTrace_6656144 : CollatzResearch.WordTrace tailWord_6656144 prefixEnd_6656144 379755686393367893298773 := by
  unfold tailWord_6656144
  simp only [CollatzResearch.WordTrace]
  refine ⟨121384757998967270868359743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161846343998623027824479657 121384757998967270868359743)
  ·
    refine ⟨182077136998450906302539615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121384757998967270868359743 182077136998450906302539615)
    ·
      refine ⟨273115705497676359453809423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182077136998450906302539615 273115705497676359453809423)
      ·
        refine ⟨409673558246514539180714135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273115705497676359453809423 409673558246514539180714135)
        ·
          refine ⟨614510337369771808771071203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409673558246514539180714135 614510337369771808771071203)
          ·
            refine ⟨921765506054657713156606805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 614510337369771808771071203 921765506054657713156606805)
            ·
              refine ⟨5400969762039010038026993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 921765506054657713156606805 5400969762039010038026993)
              ·
                refine ⟨4050727321529257528520245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5400969762039010038026993 4050727321529257528520245)
                ·
                  refine ⟨379755686393367893298773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4050727321529257528520245 379755686393367893298773)
                  ·
                    rfl

theorem cell23_6656144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 2, 5].length) (baseStart_6656144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6656144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6656144 prefixEnd_6656144 := by exact prefixLift 6656144
  have htrace : WordTrace (prefixWord ++ tailWord_6656144) baseStart_6656144 baseEnd_6656144 := by
    simpa [prefixWord, tailWord_6656144, baseEnd_6656144] using wordTrace_append hprefix tailTrace_6656144
  have hstable : (prefixWord ++ tailWord_6656144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6656144).length < 2 ^ (prefixWord ++ tailWord_6656144).sum := by decide
  have hdescent : baseEnd_6656144 < baseStart_6656144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6656144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6656147 : List Nat := [1, 1, 1, 2, 1, 2, 3, 3, 2, 5, 2]
def baseStart_6656147 : Nat := 118140960795 + 6656147 * 2 ^ 59
def prefixEnd_6656147 : Nat := 4983230072969 + 3 ^ 40 * 6656147 * 2
def baseEnd_6656147 : Nat := 3417802717982274527951443

theorem tailTrace_6656147 : CollatzResearch.WordTrace tailWord_6656147 prefixEnd_6656147 3417802717982274527951443 := by
  unfold tailWord_6656147
  simp only [CollatzResearch.WordTrace]
  refine ⟨242769625416923673249078695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161846416944615782166052463 242769625416923673249078695)
  ·
    refine ⟨364154438125385509873618043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242769625416923673249078695 364154438125385509873618043)
    ·
      refine ⟨546231657188078264810427065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364154438125385509873618043 546231657188078264810427065)
      ·
        refine ⟨409673742891058698607820299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 546231657188078264810427065 409673742891058698607820299)
        ·
          refine ⟨614510614336588047911730449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409673742891058698607820299 614510614336588047911730449)
          ·
            refine ⟨460882960752441035933797837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 614510614336588047911730449 460882960752441035933797837)
            ·
              refine ⟨172831110282165388475174189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 460882960752441035933797837 172831110282165388475174189)
              ·
                refine ⟨64811666355812020678190321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 172831110282165388475174189 64811666355812020678190321)
                ·
                  refine ⟨48608749766859015508642741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64811666355812020678190321 48608749766859015508642741)
                  ·
                    refine ⟨4557070290643032703935257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48608749766859015508642741 4557070290643032703935257)
                    ·
                      refine ⟨3417802717982274527951443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4557070290643032703935257 3417802717982274527951443)
                      ·
                        rfl

theorem cell23_6656147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 5, 2].length) (baseStart_6656147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6656147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6656147 prefixEnd_6656147 := by exact prefixLift 6656147
  have htrace : WordTrace (prefixWord ++ tailWord_6656147) baseStart_6656147 baseEnd_6656147 := by
    simpa [prefixWord, tailWord_6656147, baseEnd_6656147] using wordTrace_append hprefix tailTrace_6656147
  have hstable : (prefixWord ++ tailWord_6656147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6656147).length < 2 ^ (prefixWord ++ tailWord_6656147).sum := by decide
  have hdescent : baseEnd_6656147 < baseStart_6656147 := by decide
  rcases family_descends (prefixWord ++ tailWord_6656147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6656217 : List Nat := [1, 2, 1, 2, 3, 1, 4, 3, 6]
def baseStart_6656217 : Nat := 118140960795 + 6656217 * 2 ^ 59
def prefixEnd_6656217 : Nat := 4983230072969 + 3 ^ 40 * 6656217 * 2
def baseEnd_6656217 : Nat := 379759851292009917119569

theorem tailTrace_6656217 : CollatzResearch.WordTrace tailWord_6656217 prefixEnd_6656217 379759851292009917119569 := by
  unfold tailWord_6656217
  simp only [CollatzResearch.WordTrace]
  refine ⟨242772178526670075204126905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161848119017780050136084603 242772178526670075204126905)
  ·
    refine ⟨182079133895002556403095179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242772178526670075204126905 182079133895002556403095179)
    ·
      refine ⟨273118700842503834604642769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182079133895002556403095179 273118700842503834604642769)
      ·
        refine ⟨204839025631877875953482077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273118700842503834604642769 204839025631877875953482077)
        ·
          refine ⟨76814634611954203482555779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204839025631877875953482077 76814634611954203482555779)
          ·
            refine ⟨115221951917931305223833669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76814634611954203482555779 115221951917931305223833669)
            ·
              refine ⟨21604115984612119729468813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115221951917931305223833669 21604115984612119729468813)
              ·
                refine ⟨8101543494229544898550805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21604115984612119729468813 8101543494229544898550805)
                ·
                  refine ⟨379759851292009917119569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8101543494229544898550805 379759851292009917119569)
                  ·
                    rfl

theorem cell23_6656217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 3, 6].length) (baseStart_6656217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6656217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6656217 prefixEnd_6656217 := by exact prefixLift 6656217
  have htrace : WordTrace (prefixWord ++ tailWord_6656217) baseStart_6656217 baseEnd_6656217 := by
    simpa [prefixWord, tailWord_6656217, baseEnd_6656217] using wordTrace_append hprefix tailTrace_6656217
  have hstable : (prefixWord ++ tailWord_6656217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6656217).length < 2 ^ (prefixWord ++ tailWord_6656217).sum := by decide
  have hdescent : baseEnd_6656217 < baseStart_6656217 := by decide
  rcases family_descends (prefixWord ++ tailWord_6656217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6656221 : List Nat := [1, 4, 3, 2, 1, 2, 1, 2, 3, 4]
def baseStart_6656221 : Nat := 118140960795 + 6656221 * 2 ^ 59
def prefixEnd_6656221 : Nat := 4983230072969 + 3 ^ 40 * 6656221 * 2
def baseEnd_6656221 : Nat := 1139280238516902412808701

theorem tailTrace_6656221 : CollatzResearch.WordTrace tailWord_6656221 prefixEnd_6656221 1139280238516902412808701 := by
  unfold tailWord_6656221
  simp only [CollatzResearch.WordTrace]
  refine ⟨242772324418655583887272517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161848216279103722591515011 242772324418655583887272517)
  ·
    refine ⟨45519810828497921978863597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 242772324418655583887272517 45519810828497921978863597)
    ·
      refine ⟨17069929060686720742073849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45519810828497921978863597 17069929060686720742073849)
      ·
        refine ⟨12802446795515040556555387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17069929060686720742073849 12802446795515040556555387)
        ·
          refine ⟨19203670193272560834833081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12802446795515040556555387 19203670193272560834833081)
          ·
            refine ⟨14402752644954420626124811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19203670193272560834833081 14402752644954420626124811)
            ·
              refine ⟨21604128967431630939187217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14402752644954420626124811 21604128967431630939187217)
              ·
                refine ⟨16203096725573723204390413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21604128967431630939187217 16203096725573723204390413)
                ·
                  refine ⟨6076161272090146201646405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16203096725573723204390413 6076161272090146201646405)
                  ·
                    refine ⟨1139280238516902412808701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6076161272090146201646405 1139280238516902412808701)
                    ·
                      rfl

theorem cell23_6656221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_6656221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6656221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6656221 prefixEnd_6656221 := by exact prefixLift 6656221
  have htrace : WordTrace (prefixWord ++ tailWord_6656221) baseStart_6656221 baseEnd_6656221 := by
    simpa [prefixWord, tailWord_6656221, baseEnd_6656221] using wordTrace_append hprefix tailTrace_6656221
  have hstable : (prefixWord ++ tailWord_6656221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6656221).length < 2 ^ (prefixWord ++ tailWord_6656221).sum := by decide
  have hdescent : baseEnd_6656221 < baseStart_6656221 := by decide
  rcases family_descends (prefixWord ++ tailWord_6656221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6656231 : List Nat := [1, 1, 5, 3, 1, 1, 3, 1, 2, 2, 3]
def baseStart_6656231 : Nat := 118140960795 + 6656231 * 2 ^ 59
def prefixEnd_6656231 : Nat := 4983230072969 + 3 ^ 40 * 6656231 * 2
def baseEnd_6656231 : Nat := 3417845850357252199301057

theorem tailTrace_6656231 : CollatzResearch.WordTrace tailWord_6656231 prefixEnd_6656231 3417845850357252199301057 := by
  unfold tailWord_6656231
  simp only [CollatzResearch.WordTrace]
  refine ⟨242772689148619355595136547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161848459432412903730091031 242772689148619355595136547)
  ·
    refine ⟨364159033722929033392704821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242772689148619355595136547 364159033722929033392704821)
    ·
      refine ⟨34139909411524596880566077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 364159033722929033392704821 34139909411524596880566077)
      ·
        refine ⟨12802466029321723830212279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34139909411524596880566077 12802466029321723830212279)
        ·
          refine ⟨19203699043982585745318419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12802466029321723830212279 19203699043982585745318419)
          ·
            refine ⟨28805548565973878617977629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19203699043982585745318419 28805548565973878617977629)
            ·
              refine ⟨10802080712240204481741611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28805548565973878617977629 10802080712240204481741611)
              ·
                refine ⟨16203121068360306722612417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10802080712240204481741611 16203121068360306722612417)
                ·
                  refine ⟨12152340801270230041959313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16203121068360306722612417 12152340801270230041959313)
                  ·
                    refine ⟨9114255600952672531469485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12152340801270230041959313 9114255600952672531469485)
                    ·
                      refine ⟨3417845850357252199301057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9114255600952672531469485 3417845850357252199301057)
                      ·
                        rfl

theorem cell23_6656231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_6656231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6656231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6656231 prefixEnd_6656231 := by exact prefixLift 6656231
  have htrace : WordTrace (prefixWord ++ tailWord_6656231) baseStart_6656231 baseEnd_6656231 := by
    simpa [prefixWord, tailWord_6656231, baseEnd_6656231] using wordTrace_append hprefix tailTrace_6656231
  have hstable : (prefixWord ++ tailWord_6656231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6656231).length < 2 ^ (prefixWord ++ tailWord_6656231).sum := by decide
  have hdescent : baseEnd_6656231 < baseStart_6656231 := by decide
  rcases family_descends (prefixWord ++ tailWord_6656231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6656284 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 1, 8, 2]
def baseStart_6656284 : Nat := 118140960795 + 6656284 * 2 ^ 59
def prefixEnd_6656284 : Nat := 4983230072969 + 3 ^ 40 * 6656284 * 2
def baseEnd_6656284 : Nat := 3417873064831940491938313

theorem tailTrace_6656284 : CollatzResearch.WordTrace tailWord_6656284 prefixEnd_6656284 3417873064831940491938313 := by
  unfold tailWord_6656284
  simp only [CollatzResearch.WordTrace]
  refine ⟨121387311108713672823407953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161849748144951563764543937 121387311108713672823407953)
  ·
    refine ⟨91040483331535254617555965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121387311108713672823407953 91040483331535254617555965)
    ·
      refine ⟨34140181249325720481583487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91040483331535254617555965 34140181249325720481583487)
      ·
        refine ⟨51210271873988580722375231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34140181249325720481583487 51210271873988580722375231)
        ·
          refine ⟨76815407810982871083562847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51210271873988580722375231 76815407810982871083562847)
          ·
            refine ⟨115223111716474306625344271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76815407810982871083562847 115223111716474306625344271)
            ·
              refine ⟨172834667574711459938016407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115223111716474306625344271 172834667574711459938016407)
              ·
                refine ⟨259252001362067189907024611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172834667574711459938016407 259252001362067189907024611)
                ·
                  refine ⟨388878002043100784860536917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 259252001362067189907024611 388878002043100784860536917)
                  ·
                    refine ⟨4557164086442587322584417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 388878002043100784860536917 4557164086442587322584417)
                    ·
                      refine ⟨3417873064831940491938313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4557164086442587322584417 3417873064831940491938313)
                      ·
                        rfl

theorem cell23_6656284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 1, 8, 2].length) (baseStart_6656284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6656284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6656284 prefixEnd_6656284 := by exact prefixLift 6656284
  have htrace : WordTrace (prefixWord ++ tailWord_6656284) baseStart_6656284 baseEnd_6656284 := by
    simpa [prefixWord, tailWord_6656284, baseEnd_6656284] using wordTrace_append hprefix tailTrace_6656284
  have hstable : (prefixWord ++ tailWord_6656284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6656284).length < 2 ^ (prefixWord ++ tailWord_6656284).sum := by decide
  have hdescent : baseEnd_6656284 < baseStart_6656284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6656284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6656327 : List Nat := [1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 6]
def baseStart_6656327 : Nat := 118140960795 + 6656327 * 2 ^ 59
def prefixEnd_6656327 : Nat := 4983230072969 + 3 ^ 40 * 6656327 * 2
def baseEnd_6656327 : Nat := 3417895144500083823700615

theorem tailTrace_6656327 : CollatzResearch.WordTrace tailWord_6656327 prefixEnd_6656327 3417895144500083823700615 := by
  unfold tailWord_6656327
  simp only [CollatzResearch.WordTrace]
  refine ⟨242776190556271563990631235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161850793704181042660420823 242776190556271563990631235)
  ·
    refine ⟨364164285834407345985946853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242776190556271563990631235 364164285834407345985946853)
    ·
      refine ⟨68280803593951377372365035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 364164285834407345985946853 68280803593951377372365035)
      ·
        refine ⟨102421205390927066058547553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68280803593951377372365035 102421205390927066058547553)
        ·
          refine ⟨76815904043195299543910665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102421205390927066058547553 76815904043195299543910665)
          ·
            refine ⟨57611928032396474657932999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76815904043195299543910665 57611928032396474657932999)
            ·
              refine ⟨86417892048594711986899499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57611928032396474657932999 86417892048594711986899499)
              ·
                refine ⟨129626838072892067980349249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86417892048594711986899499 129626838072892067980349249)
                ·
                  refine ⟨97220128554669050985261937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129626838072892067980349249 97220128554669050985261937)
                  ·
                    refine ⟨72915096416001788238946453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 97220128554669050985261937 72915096416001788238946453)
                    ·
                      refine ⟨3417895144500083823700615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72915096416001788238946453 3417895144500083823700615)
                      ·
                        rfl

theorem cell23_6656327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_6656327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6656327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6656327 prefixEnd_6656327 := by exact prefixLift 6656327
  have htrace : WordTrace (prefixWord ++ tailWord_6656327) baseStart_6656327 baseEnd_6656327 := by
    simpa [prefixWord, tailWord_6656327, baseEnd_6656327] using wordTrace_append hprefix tailTrace_6656327
  have hstable : (prefixWord ++ tailWord_6656327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6656327).length < 2 ^ (prefixWord ++ tailWord_6656327).sum := by decide
  have hdescent : baseEnd_6656327 < baseStart_6656327 := by decide
  rcases family_descends (prefixWord ++ tailWord_6656327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6656348 : List Nat := [2, 2, 4, 3, 1, 1, 1, 2, 1, 2, 4]
def baseStart_6656348 : Nat := 118140960795 + 6656348 * 2 ^ 59
def prefixEnd_6656348 : Nat := 4983230072969 + 3 ^ 40 * 6656348 * 2
def baseEnd_6656348 : Nat := 3417905927593828241538019

theorem tailTrace_6656348 : CollatzResearch.WordTrace tailWord_6656348 prefixEnd_6656348 3417905927593828241538019 := by
  unfold tailWord_6656348
  simp only [CollatzResearch.WordTrace]
  refine ⟨121388478244597742288572849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161851304326130323051430465 121388478244597742288572849)
  ·
    refine ⟨91041358683448306716429637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121388478244597742288572849 91041358683448306716429637)
    ·
      refine ⟨17070254753146557509330557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91041358683448306716429637 17070254753146557509330557)
      ·
        refine ⟨6401345532429959065998959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17070254753146557509330557 6401345532429959065998959)
        ·
          refine ⟨9602018298644938598998439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6401345532429959065998959 9602018298644938598998439)
          ·
            refine ⟨14403027447967407898497659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9602018298644938598998439 14403027447967407898497659)
            ·
              refine ⟨21604541171951111847746489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14403027447967407898497659 21604541171951111847746489)
              ·
                refine ⟨16203405878963333885809867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21604541171951111847746489 16203405878963333885809867)
                ·
                  refine ⟨24305108818445000828714801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16203405878963333885809867 24305108818445000828714801)
                  ·
                    refine ⟨18228831613833750621536101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24305108818445000828714801 18228831613833750621536101)
                    ·
                      refine ⟨3417905927593828241538019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18228831613833750621536101 3417905927593828241538019)
                      ·
                        rfl

theorem cell23_6656348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_6656348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6656348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6656348 prefixEnd_6656348 := by exact prefixLift 6656348
  have htrace : WordTrace (prefixWord ++ tailWord_6656348) baseStart_6656348 baseEnd_6656348 := by
    simpa [prefixWord, tailWord_6656348, baseEnd_6656348] using wordTrace_append hprefix tailTrace_6656348
  have hstable : (prefixWord ++ tailWord_6656348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6656348).length < 2 ^ (prefixWord ++ tailWord_6656348).sum := by decide
  have hdescent : baseEnd_6656348 < baseStart_6656348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6656348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6656368 : List Nat := [2, 1, 1, 1, 4, 4, 2, 2, 2, 1, 3]
def baseStart_6656368 : Nat := 118140960795 + 6656368 * 2 ^ 59
def prefixEnd_6656368 : Nat := 4983230072969 + 3 ^ 40 * 6656368 * 2
def baseEnd_6656368 : Nat := 3417916197206918163287927

theorem tailTrace_6656368 : CollatzResearch.WordTrace tailWord_6656368 prefixEnd_6656368 3417916197206918163287927 := by
  unfold tailWord_6656368
  simp only [CollatzResearch.WordTrace]
  refine ⟨121388842974561513996436879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161851790632748685328582505 121388842974561513996436879)
  ·
    refine ⟨182083264461842270994655319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121388842974561513996436879 182083264461842270994655319)
    ·
      refine ⟨273124896692763406491982979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182083264461842270994655319 273124896692763406491982979)
      ·
        refine ⟨409687345039145109737974469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273124896692763406491982979 409687345039145109737974469)
        ·
          refine ⟨76816377194839708075870213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 409687345039145109737974469 76816377194839708075870213)
          ·
            refine ⟨14403070724032445264225665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76816377194839708075870213 14403070724032445264225665)
            ·
              refine ⟨10802303043024333948169249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14403070724032445264225665 10802303043024333948169249)
              ·
                refine ⟨8101727282268250461126937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10802303043024333948169249 8101727282268250461126937)
                ·
                  refine ⟨6076295461701187845845203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8101727282268250461126937 6076295461701187845845203)
                  ·
                    refine ⟨9114443192551781768767805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6076295461701187845845203 9114443192551781768767805)
                    ·
                      refine ⟨3417916197206918163287927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9114443192551781768767805 3417916197206918163287927)
                      ·
                        rfl

theorem cell23_6656368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 2, 2, 1, 3].length) (baseStart_6656368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6656368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6656368 prefixEnd_6656368 := by exact prefixLift 6656368
  have htrace : WordTrace (prefixWord ++ tailWord_6656368) baseStart_6656368 baseEnd_6656368 := by
    simpa [prefixWord, tailWord_6656368, baseEnd_6656368] using wordTrace_append hprefix tailTrace_6656368
  have hstable : (prefixWord ++ tailWord_6656368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6656368).length < 2 ^ (prefixWord ++ tailWord_6656368).sum := by decide
  have hdescent : baseEnd_6656368 < baseStart_6656368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6656368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6656406 : List Nat := [5, 3, 1, 2, 1, 2, 2, 1, 1, 2, 3]
def baseStart_6656406 : Nat := 118140960795 + 6656406 * 2 ^ 59
def prefixEnd_6656406 : Nat := 4983230072969 + 3 ^ 40 * 6656406 * 2
def baseEnd_6656406 : Nat := 3417935709471789014612753

theorem tailTrace_6656406 : CollatzResearch.WordTrace tailWord_6656406 prefixEnd_6656406 3417935709471789014612753 := by
  unfold tailWord_6656406
  simp only [CollatzResearch.WordTrace]
  refine ⟨15173691995186585030172317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161852714615323573655171381 15173691995186585030172317)
  ·
    refine ⟨5690134498194969386314619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15173691995186585030172317 5690134498194969386314619)
    ·
      refine ⟨8535201747292454079471929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5690134498194969386314619 8535201747292454079471929)
      ·
        refine ⟨6401401310469340559603947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8535201747292454079471929 6401401310469340559603947)
        ·
          refine ⟨9602101965704010839405921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6401401310469340559603947 9602101965704010839405921)
          ·
            refine ⟨7201576474278008129554441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9602101965704010839405921 7201576474278008129554441)
            ·
              refine ⟨5401182355708506097165831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7201576474278008129554441 5401182355708506097165831)
              ·
                refine ⟨8101773533562759145748747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5401182355708506097165831 8101773533562759145748747)
                ·
                  refine ⟨12152660300344138718623121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8101773533562759145748747 12152660300344138718623121)
                  ·
                    refine ⟨9114495225258104038967341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12152660300344138718623121 9114495225258104038967341)
                    ·
                      refine ⟨3417935709471789014612753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9114495225258104038967341 3417935709471789014612753)
                      ·
                        rfl

theorem cell23_6656406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_6656406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6656406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6656406 prefixEnd_6656406 := by exact prefixLift 6656406
  have htrace : WordTrace (prefixWord ++ tailWord_6656406) baseStart_6656406 baseEnd_6656406 := by
    simpa [prefixWord, tailWord_6656406, baseEnd_6656406] using wordTrace_append hprefix tailTrace_6656406
  have hstable : (prefixWord ++ tailWord_6656406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6656406).length < 2 ^ (prefixWord ++ tailWord_6656406).sum := by decide
  have hdescent : baseEnd_6656406 < baseStart_6656406 := by decide
  rcases family_descends (prefixWord ++ tailWord_6656406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6656408 : List Nat := [2, 1, 2, 5, 1, 1, 2, 2, 1, 4, 2]
def baseStart_6656408 : Nat := 118140960795 + 6656408 * 2 ^ 59
def prefixEnd_6656408 : Nat := 4983230072969 + 3 ^ 40 * 6656408 * 2
def baseEnd_6656408 : Nat := 3417936736433098006787743

theorem tailTrace_6656408 : CollatzResearch.WordTrace tailWord_6656408 prefixEnd_6656408 3417936736433098006787743 := by
  unfold tailWord_6656408
  simp only [CollatzResearch.WordTrace]
  refine ⟨121389572434489057412164939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161852763245985409882886585 121389572434489057412164939)
  ·
    refine ⟨182084358651733586118247409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121389572434489057412164939 182084358651733586118247409)
    ·
      refine ⟨136563268988800189588685557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182084358651733586118247409 136563268988800189588685557)
      ·
        refine ⟨12802806467700017773939271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 136563268988800189588685557 12802806467700017773939271)
        ·
          refine ⟨19204209701550026660908907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12802806467700017773939271 19204209701550026660908907)
          ·
            refine ⟨28806314552325039991363361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19204209701550026660908907 28806314552325039991363361)
            ·
              refine ⟨21604735914243779993522521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28806314552325039991363361 21604735914243779993522521)
              ·
                refine ⟨16203551935682834995141891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21604735914243779993522521 16203551935682834995141891)
                ·
                  refine ⟨24305327903524252492712837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16203551935682834995141891 24305327903524252492712837)
                  ·
                    refine ⟨4557248981910797342383657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24305327903524252492712837 4557248981910797342383657)
                    ·
                      refine ⟨3417936736433098006787743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4557248981910797342383657 3417936736433098006787743)
                      ·
                        rfl

theorem cell23_6656408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_6656408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6656408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6656408 prefixEnd_6656408 := by exact prefixLift 6656408
  have htrace : WordTrace (prefixWord ++ tailWord_6656408) baseStart_6656408 baseEnd_6656408 := by
    simpa [prefixWord, tailWord_6656408, baseEnd_6656408] using wordTrace_append hprefix tailTrace_6656408
  have hstable : (prefixWord ++ tailWord_6656408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6656408).length < 2 ^ (prefixWord ++ tailWord_6656408).sum := by decide
  have hdescent : baseEnd_6656408 < baseStart_6656408 := by decide
  rcases family_descends (prefixWord ++ tailWord_6656408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6656441 : List Nat := [1, 2, 1, 4, 3, 1, 2, 1, 2, 3, 3]
def baseStart_6656441 : Nat := 118140960795 + 6656441 * 2 ^ 59
def prefixEnd_6656441 : Nat := 4983230072969 + 3 ^ 40 * 6656441 * 2
def baseEnd_6656441 : Nat := 3417953681294696377675091

theorem tailTrace_6656441 : CollatzResearch.WordTrace tailWord_6656441 prefixEnd_6656441 3417953681294696377675091 := by
  unfold tailWord_6656441
  simp only [CollatzResearch.WordTrace]
  refine ⟨242780348477858561460281177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161853565651905707640187451 242780348477858561460281177)
  ·
    refine ⟨182085261358393921095210883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242780348477858561460281177 182085261358393921095210883)
    ·
      refine ⟨273127892037590881642816325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182085261358393921095210883 273127892037590881642816325)
      ·
        refine ⟨51211479757048290308028061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 273127892037590881642816325 51211479757048290308028061)
        ·
          refine ⟨19204304908893108865510523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51211479757048290308028061 19204304908893108865510523)
          ·
            refine ⟨28806457363339663298265785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19204304908893108865510523 28806457363339663298265785)
            ·
              refine ⟨21604843022504747473699339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28806457363339663298265785 21604843022504747473699339)
              ·
                refine ⟨32407264533757121210549009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21604843022504747473699339 32407264533757121210549009)
                ·
                  refine ⟨24305448400317840907911757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32407264533757121210549009 24305448400317840907911757)
                  ·
                    refine ⟨9114543150119190340466909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24305448400317840907911757 9114543150119190340466909)
                    ·
                      refine ⟨3417953681294696377675091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9114543150119190340466909 3417953681294696377675091)
                      ·
                        rfl

theorem cell23_6656441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_6656441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6656441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6656441 prefixEnd_6656441 := by exact prefixLift 6656441
  have htrace : WordTrace (prefixWord ++ tailWord_6656441) baseStart_6656441 baseEnd_6656441 := by
    simpa [prefixWord, tailWord_6656441, baseEnd_6656441] using wordTrace_append hprefix tailTrace_6656441
  have hstable : (prefixWord ++ tailWord_6656441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6656441).length < 2 ^ (prefixWord ++ tailWord_6656441).sum := by decide
  have hdescent : baseEnd_6656441 < baseStart_6656441 := by decide
  rcases family_descends (prefixWord ++ tailWord_6656441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6656481 : List Nat := [1, 2, 3, 1, 2, 2, 3, 2, 2, 1, 4]
def baseStart_6656481 : Nat := 118140960795 + 6656481 * 2 ^ 59
def prefixEnd_6656481 : Nat := 4983230072969 + 3 ^ 40 * 6656481 * 2
def baseEnd_6656481 : Nat := 3417974220520876221174907

theorem tailTrace_6656481 : CollatzResearch.WordTrace tailWord_6656481 prefixEnd_6656481 3417974220520876221174907 := by
  unfold tailWord_6656481
  simp only [CollatzResearch.WordTrace]
  refine ⟨242781807397713648291737297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161854538265142432194491531 242781807397713648291737297)
  ·
    refine ⟨182086355548285236218802973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242781807397713648291737297 182086355548285236218802973)
    ·
      refine ⟨68282383330606963582051115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182086355548285236218802973 68282383330606963582051115)
      ·
        refine ⟨102423574995910445373076673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68282383330606963582051115 102423574995910445373076673)
        ·
          refine ⟨76817681246932834029807505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102423574995910445373076673 76817681246932834029807505)
          ·
            refine ⟨57613260935199625522355629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76817681246932834029807505 57613260935199625522355629)
            ·
              refine ⟨21604972850699859570883361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57613260935199625522355629 21604972850699859570883361)
              ·
                refine ⟨16203729638024894678162521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21604972850699859570883361 16203729638024894678162521)
                ·
                  refine ⟨12152797228518671008621891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16203729638024894678162521 12152797228518671008621891)
                  ·
                    refine ⟨18229195842778006512932837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12152797228518671008621891 18229195842778006512932837)
                    ·
                      refine ⟨3417974220520876221174907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18229195842778006512932837 3417974220520876221174907)
                      ·
                        rfl

theorem cell23_6656481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_6656481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6656481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6656481 prefixEnd_6656481 := by exact prefixLift 6656481
  have htrace : WordTrace (prefixWord ++ tailWord_6656481) baseStart_6656481 baseEnd_6656481 := by
    simpa [prefixWord, tailWord_6656481, baseEnd_6656481] using wordTrace_append hprefix tailTrace_6656481
  have hstable : (prefixWord ++ tailWord_6656481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6656481).length < 2 ^ (prefixWord ++ tailWord_6656481).sum := by decide
  have hdescent : baseEnd_6656481 < baseStart_6656481 := by decide
  rcases family_descends (prefixWord ++ tailWord_6656481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6656482 : List Nat := [3, 3, 3, 2, 2, 1, 1, 1, 7]
def baseStart_6656482 : Nat := 118140960795 + 6656482 * 2 ^ 59
def prefixEnd_6656482 : Nat := 4983230072969 + 3 ^ 40 * 6656482 * 2
def baseEnd_6656482 : Nat := 379774970444614524140267

theorem tailTrace_6656482 : CollatzResearch.WordTrace tailWord_6656482 prefixEnd_6656482 379774970444614524140267 := by
  unfold tailWord_6656482
  simp only [CollatzResearch.WordTrace]
  refine ⟨60695460967677506365630925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161854562580473350308349133 60695460967677506365630925)
  ·
    refine ⟨22760797862879064887111597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60695460967677506365630925 22760797862879064887111597)
    ·
      refine ⟨8535299198579649332666849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22760797862879064887111597 8535299198579649332666849)
      ·
        refine ⟨6401474398934736999500137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8535299198579649332666849 6401474398934736999500137)
        ·
          refine ⟨4801105799201052749625103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6401474398934736999500137 4801105799201052749625103)
          ·
            refine ⟨7201658698801579124437655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4801105799201052749625103 7201658698801579124437655)
            ·
              refine ⟨10802488048202368686656483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7201658698801579124437655 10802488048202368686656483)
              ·
                refine ⟨16203732072303553029984725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10802488048202368686656483 16203732072303553029984725)
                ·
                  refine ⟨379774970444614524140267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16203732072303553029984725 379774970444614524140267)
                  ·
                    rfl

theorem cell23_6656482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 7].length) (baseStart_6656482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6656482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6656482 prefixEnd_6656482 := by exact prefixLift 6656482
  have htrace : WordTrace (prefixWord ++ tailWord_6656482) baseStart_6656482 baseEnd_6656482 := by
    simpa [prefixWord, tailWord_6656482, baseEnd_6656482] using wordTrace_append hprefix tailTrace_6656482
  have hstable : (prefixWord ++ tailWord_6656482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6656482).length < 2 ^ (prefixWord ++ tailWord_6656482).sum := by decide
  have hdescent : baseEnd_6656482 < baseStart_6656482 := by decide
  rcases family_descends (prefixWord ++ tailWord_6656482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6656581 : List Nat := [1, 3, 1, 1, 1, 5, 2, 2, 1, 6]
def baseStart_6656581 : Nat := 118140960795 + 6656581 * 2 ^ 59
def prefixEnd_6656581 : Nat := 4983230072969 + 3 ^ 40 * 6656581 * 2
def baseEnd_6656581 : Nat := 1139341856195441943308149

theorem tailTrace_6656581 : CollatzResearch.WordTrace tailWord_6656581 prefixEnd_6656581 1139341856195441943308149 := by
  unfold tailWord_6656581
  simp only [CollatzResearch.WordTrace]
  refine ⟨242785454697351365370377597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161856969798234243580251731 242785454697351365370377597)
  ·
    refine ⟨91044545511506762013891599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242785454697351365370377597 91044545511506762013891599)
    ·
      refine ⟨136566818267260143020837399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91044545511506762013891599 136566818267260143020837399)
      ·
        refine ⟨204850227400890214531256099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136566818267260143020837399 204850227400890214531256099)
        ·
          refine ⟨307275341101335321796884149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204850227400890214531256099 307275341101335321796884149)
          ·
            refine ⟨28807063228250186418457889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 307275341101335321796884149 28807063228250186418457889)
            ·
              refine ⟨21605297421187639813843417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28807063228250186418457889 21605297421187639813843417)
              ·
                refine ⟨16203973065890729860382563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21605297421187639813843417 16203973065890729860382563)
                ·
                  refine ⟨24305959598836094790573845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16203973065890729860382563 24305959598836094790573845)
                  ·
                    refine ⟨1139341856195441943308149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24305959598836094790573845 1139341856195441943308149)
                    ·
                      rfl

theorem cell23_6656581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 6].length) (baseStart_6656581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6656581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6656581 prefixEnd_6656581 := by exact prefixLift 6656581
  have htrace : WordTrace (prefixWord ++ tailWord_6656581) baseStart_6656581 baseEnd_6656581 := by
    simpa [prefixWord, tailWord_6656581, baseEnd_6656581] using wordTrace_append hprefix tailTrace_6656581
  have hstable : (prefixWord ++ tailWord_6656581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6656581).length < 2 ^ (prefixWord ++ tailWord_6656581).sum := by decide
  have hdescent : baseEnd_6656581 < baseStart_6656581 := by decide
  rcases family_descends (prefixWord ++ tailWord_6656581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6656588 : List Nat := [2, 2, 1, 3, 1, 2, 3, 3, 1, 1, 4]
def baseStart_6656588 : Nat := 118140960795 + 6656588 * 2 ^ 59
def prefixEnd_6656588 : Nat := 4983230072969 + 3 ^ 40 * 6656588 * 2
def baseEnd_6656588 : Nat := 3418029162950907302536915

theorem tailTrace_6656588 : CollatzResearch.WordTrace tailWord_6656588 prefixEnd_6656588 3418029162950907302536915 := by
  unfold tailWord_6656588
  simp only [CollatzResearch.WordTrace]
  refine ⟨121392855004163002782941209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161857140005550670377254945 121392855004163002782941209)
  ·
    refine ⟨91044641253122252087205907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121392855004163002782941209 91044641253122252087205907)
    ·
      refine ⟨136566961879683378130808861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91044641253122252087205907 136566961879683378130808861)
      ·
        refine ⟨51212610704881266799053323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136566961879683378130808861 51212610704881266799053323)
        ·
          refine ⟨76818916057321900198579985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51212610704881266799053323 76818916057321900198579985)
          ·
            refine ⟨57614187042991425148934989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76818916057321900198579985 57614187042991425148934989)
            ·
              refine ⟨21605320141121784430850621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57614187042991425148934989 21605320141121784430850621)
              ·
                refine ⟨8101995052920669161568983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21605320141121784430850621 8101995052920669161568983)
                ·
                  refine ⟨12152992579381003742353475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8101995052920669161568983 12152992579381003742353475)
                  ·
                    refine ⟨18229488869071505613530213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12152992579381003742353475 18229488869071505613530213)
                    ·
                      refine ⟨3418029162950907302536915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18229488869071505613530213 3418029162950907302536915)
                      ·
                        rfl

theorem cell23_6656588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_6656588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6656588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6656588 prefixEnd_6656588 := by exact prefixLift 6656588
  have htrace : WordTrace (prefixWord ++ tailWord_6656588) baseStart_6656588 baseEnd_6656588 := by
    simpa [prefixWord, tailWord_6656588, baseEnd_6656588] using wordTrace_append hprefix tailTrace_6656588
  have hstable : (prefixWord ++ tailWord_6656588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6656588).length < 2 ^ (prefixWord ++ tailWord_6656588).sum := by decide
  have hdescent : baseEnd_6656588 < baseStart_6656588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6656588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6656622 : List Nat := [4, 1, 2, 2, 2, 1, 2, 2, 3, 2, 2]
def baseStart_6656622 : Nat := 118140960795 + 6656622 * 2 ^ 59
def prefixEnd_6656622 : Nat := 4983230072969 + 3 ^ 40 * 6656622 * 2
def baseEnd_6656622 : Nat := 3418046621293160169511759

theorem tailTrace_6656622 : CollatzResearch.WordTrace tailWord_6656622 prefixEnd_6656622 3418046621293160169511759 := by
  unfold tailWord_6656622
  simp only [CollatzResearch.WordTrace]
  refine ⟨30348368761275353671577515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161857966726801886248413413 30348368761275353671577515)
  ·
    refine ⟨45522553141913030507366273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30348368761275353671577515 45522553141913030507366273)
    ·
      refine ⟨34141914856434772880524705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45522553141913030507366273 34141914856434772880524705)
      ·
        refine ⟨25606436142326079660393529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34141914856434772880524705 25606436142326079660393529)
        ·
          refine ⟨19204827106744559745295147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25606436142326079660393529 19204827106744559745295147)
          ·
            refine ⟨28807240660116839617942721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19204827106744559745295147 28807240660116839617942721)
            ·
              refine ⟨21605430495087629713457041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28807240660116839617942721 21605430495087629713457041)
              ·
                refine ⟨16204072871315722285092781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21605430495087629713457041 16204072871315722285092781)
                ·
                  refine ⟨6076527326743395856909793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16204072871315722285092781 6076527326743395856909793)
                  ·
                    refine ⟨4557395495057546892682345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6076527326743395856909793 4557395495057546892682345)
                    ·
                      refine ⟨3418046621293160169511759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4557395495057546892682345 3418046621293160169511759)
                      ·
                        rfl

theorem cell23_6656622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_6656622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6656622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6656622 prefixEnd_6656622 := by exact prefixLift 6656622
  have htrace : WordTrace (prefixWord ++ tailWord_6656622) baseStart_6656622 baseEnd_6656622 := by
    simpa [prefixWord, tailWord_6656622, baseEnd_6656622] using wordTrace_append hprefix tailTrace_6656622
  have hstable : (prefixWord ++ tailWord_6656622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6656622).length < 2 ^ (prefixWord ++ tailWord_6656622).sum := by decide
  have hdescent : baseEnd_6656622 < baseStart_6656622 := by decide
  rcases family_descends (prefixWord ++ tailWord_6656622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6656666 : List Nat := [3, 1, 1, 6, 2, 1, 2, 1, 2, 4]
def baseStart_6656666 : Nat := 118140960795 + 6656666 * 2 ^ 59
def prefixEnd_6656666 : Nat := 4983230072969 + 3 ^ 40 * 6656666 * 2
def baseEnd_6656666 : Nat := 1139356404813985999120519

theorem tailTrace_6656666 : CollatzResearch.WordTrace tailWord_6656666 prefixEnd_6656666 1139356404813985999120519 := by
  unfold tailWord_6656666
  simp only [CollatzResearch.WordTrace]
  refine ⟨60697138725510856221805463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161859036601362283258147901 60697138725510856221805463)
  ·
    refine ⟨91045708088266284332708195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60697138725510856221805463 91045708088266284332708195)
    ·
      refine ⟨136568562132399426499062293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91045708088266284332708195 136568562132399426499062293)
      ·
        refine ⟨6401651349956223117143545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 136568562132399426499062293 6401651349956223117143545)
        ·
          refine ⟨4801238512467167337857659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6401651349956223117143545 4801238512467167337857659)
          ·
            refine ⟨7201857768700751006786489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4801238512467167337857659 7201857768700751006786489)
            ·
              refine ⟨5401393326525563255089867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7201857768700751006786489 5401393326525563255089867)
              ·
                refine ⟨8102089989788344882634801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5401393326525563255089867 8102089989788344882634801)
                ·
                  refine ⟨6076567492341258661976101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8102089989788344882634801 6076567492341258661976101)
                  ·
                    refine ⟨1139356404813985999120519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6076567492341258661976101 1139356404813985999120519)
                    ·
                      rfl

theorem cell23_6656666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 1, 2, 4].length) (baseStart_6656666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6656666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6656666 prefixEnd_6656666 := by exact prefixLift 6656666
  have htrace : WordTrace (prefixWord ++ tailWord_6656666) baseStart_6656666 baseEnd_6656666 := by
    simpa [prefixWord, tailWord_6656666, baseEnd_6656666] using wordTrace_append hprefix tailTrace_6656666
  have hstable : (prefixWord ++ tailWord_6656666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6656666).length < 2 ^ (prefixWord ++ tailWord_6656666).sum := by decide
  have hdescent : baseEnd_6656666 < baseStart_6656666 := by decide
  rcases family_descends (prefixWord ++ tailWord_6656666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6656672 : List Nat := [2, 1, 1, 4, 4, 1, 1, 3, 2, 1, 3]
def baseStart_6656672 : Nat := 118140960795 + 6656672 * 2 ^ 59
def prefixEnd_6656672 : Nat := 4983230072969 + 3 ^ 40 * 6656672 * 2
def baseEnd_6656672 : Nat := 3418072295325884973886529

theorem tailTrace_6656672 : CollatzResearch.WordTrace tailWord_6656672 prefixEnd_6656672 3418072295325884973886529 := by
  unfold tailWord_6656672
  simp only [CollatzResearch.WordTrace]
  refine ⟨121394386870010843955970135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161859182493347791941293513 121394386870010843955970135)
  ·
    refine ⟨182091580305016265933955203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121394386870010843955970135 182091580305016265933955203)
    ·
      refine ⟨273137370457524398900932805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182091580305016265933955203 273137370457524398900932805)
      ·
        refine ⟨51213256960785824793924901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 273137370457524398900932805 51213256960785824793924901)
        ·
          refine ⟨9602485680147342148860919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51213256960785824793924901 9602485680147342148860919)
          ·
            refine ⟨14403728520221013223291379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9602485680147342148860919 14403728520221013223291379)
            ·
              refine ⟨21605592780331519834937069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14403728520221013223291379 21605592780331519834937069)
              ·
                refine ⟨8102097292624319938101401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21605592780331519834937069 8102097292624319938101401)
                ·
                  refine ⟨6076572969468239953576051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8102097292624319938101401 6076572969468239953576051)
                  ·
                    refine ⟨9114859454202359930364077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6076572969468239953576051 9114859454202359930364077)
                    ·
                      refine ⟨3418072295325884973886529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9114859454202359930364077 3418072295325884973886529)
                      ·
                        rfl

theorem cell23_6656672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_6656672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6656672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6656672 prefixEnd_6656672 := by exact prefixLift 6656672
  have htrace : WordTrace (prefixWord ++ tailWord_6656672) baseStart_6656672 baseEnd_6656672 := by
    simpa [prefixWord, tailWord_6656672, baseEnd_6656672] using wordTrace_append hprefix tailTrace_6656672
  have hstable : (prefixWord ++ tailWord_6656672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6656672).length < 2 ^ (prefixWord ++ tailWord_6656672).sum := by decide
  have hdescent : baseEnd_6656672 < baseStart_6656672 := by decide
  rcases family_descends (prefixWord ++ tailWord_6656672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6656681 : List Nat := [1, 2, 1, 1, 1, 1, 2, 6, 2, 1, 5]
def baseStart_6656681 : Nat := 118140960795 + 6656681 * 2 ^ 59
def prefixEnd_6656681 : Nat := 4983230072969 + 3 ^ 40 * 6656681 * 2
def baseEnd_6656681 : Nat := 3418076916651775438673987

theorem tailTrace_6656681 : CollatzResearch.WordTrace tailWord_6656681 prefixEnd_6656681 3418076916651775438673987 := by
  unfold tailWord_6656681
  simp only [CollatzResearch.WordTrace]
  refine ⟨242789101996989082449017897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161859401331326054966011931 242789101996989082449017897)
  ·
    refine ⟨182091826497741811836763423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242789101996989082449017897 182091826497741811836763423)
    ·
      refine ⟨273137739746612717755145135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182091826497741811836763423 273137739746612717755145135)
      ·
        refine ⟨409706609619919076632717703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273137739746612717755145135 409706609619919076632717703)
        ·
          refine ⟨614559914429878614949076555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409706609619919076632717703 614559914429878614949076555)
          ·
            refine ⟨921839871644817922423614833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 614559914429878614949076555 921839871644817922423614833)
            ·
              refine ⟨691379903733613441817711125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 921839871644817922423614833 691379903733613441817711125)
              ·
                refine ⟨32408432987513130085205209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 691379903733613441817711125 32408432987513130085205209)
                ·
                  refine ⟨24306324740634847563903907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32408432987513130085205209 24306324740634847563903907)
                  ·
                    refine ⟨36459487110952271345855861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24306324740634847563903907 36459487110952271345855861)
                    ·
                      refine ⟨3418076916651775438673987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36459487110952271345855861 3418076916651775438673987)
                      ·
                        rfl

theorem cell23_6656681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 1, 5].length) (baseStart_6656681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6656681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6656681 prefixEnd_6656681 := by exact prefixLift 6656681
  have htrace : WordTrace (prefixWord ++ tailWord_6656681) baseStart_6656681 baseEnd_6656681 := by
    simpa [prefixWord, tailWord_6656681, baseEnd_6656681] using wordTrace_append hprefix tailTrace_6656681
  have hstable : (prefixWord ++ tailWord_6656681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6656681).length < 2 ^ (prefixWord ++ tailWord_6656681).sum := by decide
  have hdescent : baseEnd_6656681 < baseStart_6656681 := by decide
  rcases family_descends (prefixWord ++ tailWord_6656681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6656712 : List Nat := [2, 1, 3, 1, 2, 3, 1, 4, 2, 2, 2]
def baseStart_6656712 : Nat := 118140960795 + 6656712 * 2 ^ 59
def prefixEnd_6656712 : Nat := 4983230072969 + 3 ^ 40 * 6656712 * 2
def baseEnd_6656712 : Nat := 3418092834552064817386345

theorem tailTrace_6656712 : CollatzResearch.WordTrace tailWord_6656712 prefixEnd_6656712 3418092834552064817386345 := by
  unfold tailWord_6656712
  simp only [CollatzResearch.WordTrace]
  refine ⟨121395116329938387371698195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161860155106584516495597593 121395116329938387371698195)
  ·
    refine ⟨182092674494907581057547293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121395116329938387371698195 182092674494907581057547293)
    ·
      refine ⟨68284752935590342896580235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182092674494907581057547293 68284752935590342896580235)
      ·
        refine ⟨102427129403385514344870353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68284752935590342896580235 102427129403385514344870353)
        ·
          refine ⟨76820347052539135758652765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102427129403385514344870353 76820347052539135758652765)
          ·
            refine ⟨28807630144702175909494787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76820347052539135758652765 28807630144702175909494787)
            ·
              refine ⟨43211445217053263864242181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28807630144702175909494787 43211445217053263864242181)
              ·
                refine ⟨8102145978197486974545409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43211445217053263864242181 8102145978197486974545409)
                ·
                  refine ⟨6076609483648115230909057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8102145978197486974545409 6076609483648115230909057)
                  ·
                    refine ⟨4557457112736086423181793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6076609483648115230909057 4557457112736086423181793)
                    ·
                      refine ⟨3418092834552064817386345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4557457112736086423181793 3418092834552064817386345)
                      ·
                        rfl

theorem cell23_6656712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 4, 2, 2, 2].length) (baseStart_6656712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6656712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6656712 prefixEnd_6656712 := by exact prefixLift 6656712
  have htrace : WordTrace (prefixWord ++ tailWord_6656712) baseStart_6656712 baseEnd_6656712 := by
    simpa [prefixWord, tailWord_6656712, baseEnd_6656712] using wordTrace_append hprefix tailTrace_6656712
  have hstable : (prefixWord ++ tailWord_6656712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6656712).length < 2 ^ (prefixWord ++ tailWord_6656712).sum := by decide
  have hdescent : baseEnd_6656712 < baseStart_6656712 := by decide
  rcases family_descends (prefixWord ++ tailWord_6656712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6656728 : List Nat := [2, 1, 2, 2, 3, 2, 1, 1, 1, 5, 3]
def baseStart_6656728 : Nat := 118140960795 + 6656728 * 2 ^ 59
def prefixEnd_6656728 : Nat := 4983230072969 + 3 ^ 40 * 6656728 * 2
def baseEnd_6656728 : Nat := 3418101050242536754786271

theorem tailTrace_6656728 : CollatzResearch.WordTrace tailWord_6656728 prefixEnd_6656728 3418101050242536754786271 := by
  unfold tailWord_6656728
  simp only [CollatzResearch.WordTrace]
  refine ⟨121395408113909404737989419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161860544151879206317319225 121395408113909404737989419)
  ·
    refine ⟨182093112170864107106984129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121395408113909404737989419 182093112170864107106984129)
    ·
      refine ⟨136569834128148080330238097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182093112170864107106984129 136569834128148080330238097)
      ·
        refine ⟨102427375596111060247678573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136569834128148080330238097 102427375596111060247678573)
        ·
          refine ⟨38410265848541647592879465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102427375596111060247678573 38410265848541647592879465)
          ·
            refine ⟨28807699386406235694659599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38410265848541647592879465 28807699386406235694659599)
            ·
              refine ⟨43211549079609353541989399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28807699386406235694659599 43211549079609353541989399)
              ·
                refine ⟨64817323619414030312984099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43211549079609353541989399 64817323619414030312984099)
                ·
                  refine ⟨97225985429121045469476149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64817323619414030312984099 97225985429121045469476149)
                  ·
                    refine ⟨9114936133980098012763389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 97225985429121045469476149 9114936133980098012763389)
                    ·
                      refine ⟨3418101050242536754786271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9114936133980098012763389 3418101050242536754786271)
                      ·
                        rfl

theorem cell23_6656728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 1, 5, 3].length) (baseStart_6656728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6656728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6656728 prefixEnd_6656728 := by exact prefixLift 6656728
  have htrace : WordTrace (prefixWord ++ tailWord_6656728) baseStart_6656728 baseEnd_6656728 := by
    simpa [prefixWord, tailWord_6656728, baseEnd_6656728] using wordTrace_append hprefix tailTrace_6656728
  have hstable : (prefixWord ++ tailWord_6656728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6656728).length < 2 ^ (prefixWord ++ tailWord_6656728).sum := by decide
  have hdescent : baseEnd_6656728 < baseStart_6656728 := by decide
  rcases family_descends (prefixWord ++ tailWord_6656728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6656761 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 1, 10]
def baseStart_6656761 : Nat := 118140960795 + 6656761 * 2 ^ 59
def prefixEnd_6656761 : Nat := 4983230072969 + 3 ^ 40 * 6656761 * 2
def baseEnd_6656761 : Nat := 1139372665034711708557873

theorem tailTrace_6656761 : CollatzResearch.WordTrace tailWord_6656761 prefixEnd_6656761 1139372665034711708557873 := by
  unfold tailWord_6656761
  simp only [CollatzResearch.WordTrace]
  refine ⟨242792019836699256111930137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161861346557799504074620091 242792019836699256111930137)
  ·
    refine ⟨182094014877524442083947603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242792019836699256111930137 182094014877524442083947603)
    ·
      refine ⟨273141022316286663125921405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182094014877524442083947603 273141022316286663125921405)
      ·
        refine ⟨102427883368607498672220527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273141022316286663125921405 102427883368607498672220527)
        ·
          refine ⟨153641825052911248008330791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102427883368607498672220527 153641825052911248008330791)
          ·
            refine ⟨230462737579366872012496187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153641825052911248008330791 230462737579366872012496187)
            ·
              refine ⟨345694106369050308018744281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230462737579366872012496187 345694106369050308018744281)
              ·
                refine ⟨259270579776787731014058211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 345694106369050308018744281 259270579776787731014058211)
                ·
                  refine ⟨388905869665181596521087317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 259270579776787731014058211 388905869665181596521087317)
                  ·
                    refine ⟨1139372665034711708557873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 388905869665181596521087317 1139372665034711708557873)
                    ·
                      rfl

theorem cell23_6656761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 10].length) (baseStart_6656761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6656761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6656761 prefixEnd_6656761 := by exact prefixLift 6656761
  have htrace : WordTrace (prefixWord ++ tailWord_6656761) baseStart_6656761 baseEnd_6656761 := by
    simpa [prefixWord, tailWord_6656761, baseEnd_6656761] using wordTrace_append hprefix tailTrace_6656761
  have hstable : (prefixWord ++ tailWord_6656761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6656761).length < 2 ^ (prefixWord ++ tailWord_6656761).sum := by decide
  have hdescent : baseEnd_6656761 < baseStart_6656761 := by decide
  rcases family_descends (prefixWord ++ tailWord_6656761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6656785 : List Nat := [1, 2, 2, 1, 1, 3, 4, 1, 2, 4, 2]
def baseStart_6656785 : Nat := 118140960795 + 6656785 * 2 ^ 59
def prefixEnd_6656785 : Nat := 4983230072969 + 3 ^ 40 * 6656785 * 2
def baseEnd_6656785 : Nat := 3418130318639843031773509

theorem tailTrace_6656785 : CollatzResearch.WordTrace tailWord_6656785 prefixEnd_6656785 3418130318639843031773509 := by
  unfold tailWord_6656785
  simp only [CollatzResearch.WordTrace]
  refine ⟨242792895188612308210803809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161861930125741538807202539 242792895188612308210803809)
  ·
    refine ⟨182094671391459231158102857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242792895188612308210803809 182094671391459231158102857)
    ·
      refine ⟨136571003543594423368577143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182094671391459231158102857 136571003543594423368577143)
      ·
        refine ⟨204856505315391635052865715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136571003543594423368577143 204856505315391635052865715)
        ·
          refine ⟨307284757973087452579298573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204856505315391635052865715 307284757973087452579298573)
          ·
            refine ⟨115231784239907794717236965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 307284757973087452579298573 115231784239907794717236965)
            ·
              refine ⟨21605959544982711509481931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115231784239907794717236965 21605959544982711509481931)
              ·
                refine ⟨32408939317474067264222897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21605959544982711509481931 32408939317474067264222897)
                ·
                  refine ⟨24306704488105550448167173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32408939317474067264222897 24306704488105550448167173)
                  ·
                    refine ⟨4557507091519790709031345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24306704488105550448167173 4557507091519790709031345)
                    ·
                      refine ⟨3418130318639843031773509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4557507091519790709031345 3418130318639843031773509)
                      ·
                        rfl

theorem cell23_6656785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 4, 2].length) (baseStart_6656785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6656785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6656785 prefixEnd_6656785 := by exact prefixLift 6656785
  have htrace : WordTrace (prefixWord ++ tailWord_6656785) baseStart_6656785 baseEnd_6656785 := by
    simpa [prefixWord, tailWord_6656785, baseEnd_6656785] using wordTrace_append hprefix tailTrace_6656785
  have hstable : (prefixWord ++ tailWord_6656785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6656785).length < 2 ^ (prefixWord ++ tailWord_6656785).sum := by decide
  have hdescent : baseEnd_6656785 < baseStart_6656785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6656785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6656805 : List Nat := [1, 3, 1, 2, 3, 1, 2, 3, 2, 2, 3]
def baseStart_6656805 : Nat := 118140960795 + 6656805 * 2 ^ 59
def prefixEnd_6656805 : Nat := 4983230072969 + 3 ^ 40 * 6656805 * 2
def baseEnd_6656805 : Nat := 3418140588252932953523417

theorem tailTrace_6656805 : CollatzResearch.WordTrace tailWord_6656805 prefixEnd_6656805 3418140588252932953523417 := by
  unfold tailWord_6656805
  simp only [CollatzResearch.WordTrace]
  refine ⟨242793624648539851626531869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161862416432359901084354579 242793624648539851626531869)
  ·
    refine ⟨91047609243202444359949451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242793624648539851626531869 91047609243202444359949451)
    ·
      refine ⟨136571413864803666539924177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91047609243202444359949451 136571413864803666539924177)
      ·
        refine ⟨102428560398602749904943133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136571413864803666539924177 102428560398602749904943133)
        ·
          refine ⟨38410710149476031214353675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102428560398602749904943133 38410710149476031214353675)
          ·
            refine ⟨57616065224214046821530513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38410710149476031214353675 57616065224214046821530513)
            ·
              refine ⟨43212048918160535116147885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57616065224214046821530513 43212048918160535116147885)
              ·
                refine ⟨16204518344310200668555457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43212048918160535116147885 16204518344310200668555457)
                ·
                  refine ⟨12153388758232650501416593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16204518344310200668555457 12153388758232650501416593)
                  ·
                    refine ⟨9115041568674487876062445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12153388758232650501416593 9115041568674487876062445)
                    ·
                      refine ⟨3418140588252932953523417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9115041568674487876062445 3418140588252932953523417)
                      ·
                        rfl

theorem cell23_6656805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 2, 2, 3].length) (baseStart_6656805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6656805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6656805 prefixEnd_6656805 := by exact prefixLift 6656805
  have htrace : WordTrace (prefixWord ++ tailWord_6656805) baseStart_6656805 baseEnd_6656805 := by
    simpa [prefixWord, tailWord_6656805, baseEnd_6656805] using wordTrace_append hprefix tailTrace_6656805
  have hstable : (prefixWord ++ tailWord_6656805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6656805).length < 2 ^ (prefixWord ++ tailWord_6656805).sum := by decide
  have hdescent : baseEnd_6656805 < baseStart_6656805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6656805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6656808 : List Nat := [2, 1, 5, 1, 1, 1, 1, 1, 10]
def baseStart_6656808 : Nat := 118140960795 + 6656808 * 2 ^ 59
def prefixEnd_6656808 : Nat := 4983230072969 + 3 ^ 40 * 6656808 * 2
def baseEnd_6656808 : Nat := 379793569854988493531767

theorem tailTrace_6656808 : CollatzResearch.WordTrace tailWord_6656808 prefixEnd_6656808 379793569854988493531767 := by
  unfold tailWord_6656808
  simp only [CollatzResearch.WordTrace]
  refine ⟨121396867033764491569445539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161862489378352655425927385 121396867033764491569445539)
  ·
    refine ⟨182095300550646737354168309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121396867033764491569445539 182095300550646737354168309)
    ·
      refine ⟨17071434426623131626953279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 182095300550646737354168309 17071434426623131626953279)
      ·
        refine ⟨25607151639934697440429919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17071434426623131626953279 25607151639934697440429919)
        ·
          refine ⟨38410727459902046160644879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25607151639934697440429919 38410727459902046160644879)
          ·
            refine ⟨57616091189853069240967319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38410727459902046160644879 57616091189853069240967319)
            ·
              refine ⟨86424136784779603861450979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57616091189853069240967319 86424136784779603861450979)
              ·
                refine ⟨129636205177169405792176469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86424136784779603861450979 129636205177169405792176469)
                ·
                  refine ⟨379793569854988493531767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 129636205177169405792176469 379793569854988493531767)
                  ·
                    rfl

theorem cell23_6656808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 10].length) (baseStart_6656808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6656808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6656808 prefixEnd_6656808 := by exact prefixLift 6656808
  have htrace : WordTrace (prefixWord ++ tailWord_6656808) baseStart_6656808 baseEnd_6656808 := by
    simpa [prefixWord, tailWord_6656808, baseEnd_6656808] using wordTrace_append hprefix tailTrace_6656808
  have hstable : (prefixWord ++ tailWord_6656808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6656808).length < 2 ^ (prefixWord ++ tailWord_6656808).sum := by decide
  have hdescent : baseEnd_6656808 < baseStart_6656808 := by decide
  rcases family_descends (prefixWord ++ tailWord_6656808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6656829 : List Nat := [1, 4, 1, 4, 2, 2, 1, 1, 3, 4]
def baseStart_6656829 : Nat := 118140960795 + 6656829 * 2 ^ 59
def prefixEnd_6656829 : Nat := 4983230072969 + 3 ^ 40 * 6656829 * 2
def baseEnd_6656829 : Nat := 1139384303929546953207769

theorem tailTrace_6656829 : CollatzResearch.WordTrace tailWord_6656829 prefixEnd_6656829 1139384303929546953207769 := by
  unfold tailWord_6656829
  simp only [CollatzResearch.WordTrace]
  refine ⟨242794500000452903725405541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161863000000301935816937027 242794500000452903725405541)
  ·
    refine ⟨45523968750084919448513539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 242794500000452903725405541 45523968750084919448513539)
    ·
      refine ⟨68285953125127379172770309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45523968750084919448513539 68285953125127379172770309)
      ·
        refine ⟨12803616210961383594894433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68285953125127379172770309 12803616210961383594894433)
        ·
          refine ⟨9602712158221037696170825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12803616210961383594894433 9602712158221037696170825)
          ·
            refine ⟨7202034118665778272128119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9602712158221037696170825 7202034118665778272128119)
            ·
              refine ⟨10803051177998667408192179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7202034118665778272128119 10803051177998667408192179)
              ·
                refine ⟨16204576766998001112288269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10803051177998667408192179 16204576766998001112288269)
                ·
                  refine ⟨6076716287624250417108101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16204576766998001112288269 6076716287624250417108101)
                  ·
                    refine ⟨1139384303929546953207769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6076716287624250417108101 1139384303929546953207769)
                    ·
                      rfl

theorem cell23_6656829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 3, 4].length) (baseStart_6656829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6656829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6656829 prefixEnd_6656829 := by exact prefixLift 6656829
  have htrace : WordTrace (prefixWord ++ tailWord_6656829) baseStart_6656829 baseEnd_6656829 := by
    simpa [prefixWord, tailWord_6656829, baseEnd_6656829] using wordTrace_append hprefix tailTrace_6656829
  have hstable : (prefixWord ++ tailWord_6656829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6656829).length < 2 ^ (prefixWord ++ tailWord_6656829).sum := by decide
  have hdescent : baseEnd_6656829 < baseStart_6656829 := by decide
  rcases family_descends (prefixWord ++ tailWord_6656829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6656855 : List Nat := [1, 1, 3, 2, 4, 2, 1, 1, 3, 5]
def baseStart_6656855 : Nat := 118140960795 + 6656855 * 2 ^ 59
def prefixEnd_6656855 : Nat := 4983230072969 + 3 ^ 40 * 6656855 * 2
def baseEnd_6656855 : Nat := 1139388754095219252632729

theorem tailTrace_6656855 : CollatzResearch.WordTrace tailWord_6656855 prefixEnd_6656855 1139388754095219252632729 := by
  unfold tailWord_6656855
  simp only [CollatzResearch.WordTrace]
  refine ⟨242795448298358710165852019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161863632198905806777234679 242795448298358710165852019)
  ·
    refine ⟨364193172447538065248778029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242795448298358710165852019 364193172447538065248778029)
    ·
      refine ⟨136572439667826774468291761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 364193172447538065248778029 136572439667826774468291761)
      ·
        refine ⟨102429329750870080851218821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136572439667826774468291761 102429329750870080851218821)
        ·
          refine ⟨19205499328288140159603529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102429329750870080851218821 19205499328288140159603529)
          ·
            refine ⟨14404124496216105119702647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19205499328288140159603529 14404124496216105119702647)
            ·
              refine ⟨21606186744324157679553971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14404124496216105119702647 21606186744324157679553971)
              ·
                refine ⟨32409280116486236519330957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21606186744324157679553971 32409280116486236519330957)
                ·
                  refine ⟨12153480043682338694749109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32409280116486236519330957 12153480043682338694749109)
                  ·
                    refine ⟨1139388754095219252632729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12153480043682338694749109 1139388754095219252632729)
                    ·
                      rfl

theorem cell23_6656855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 3, 5].length) (baseStart_6656855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6656855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6656855 prefixEnd_6656855 := by exact prefixLift 6656855
  have htrace : WordTrace (prefixWord ++ tailWord_6656855) baseStart_6656855 baseEnd_6656855 := by
    simpa [prefixWord, tailWord_6656855, baseEnd_6656855] using wordTrace_append hprefix tailTrace_6656855
  have hstable : (prefixWord ++ tailWord_6656855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6656855).length < 2 ^ (prefixWord ++ tailWord_6656855).sum := by decide
  have hdescent : baseEnd_6656855 < baseStart_6656855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6656855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6656875 : List Nat := [1, 1, 1, 1, 2, 2, 4, 5, 1, 1, 4]
def baseStart_6656875 : Nat := 118140960795 + 6656875 * 2 ^ 59
def prefixEnd_6656875 : Nat := 4983230072969 + 3 ^ 40 * 6656875 * 2
def baseEnd_6656875 : Nat := 3418176531898747679648095

theorem tailTrace_6656875 : CollatzResearch.WordTrace tailWord_6656875 prefixEnd_6656875 3418176531898747679648095 := by
  unfold tailWord_6656875
  simp only [CollatzResearch.WordTrace]
  refine ⟨242796177758286253581580079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161864118505524169054386719 242796177758286253581580079)
  ·
    refine ⟨364194266637429380372370119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242796177758286253581580079 364194266637429380372370119)
    ·
      refine ⟨546291399956144070558555179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364194266637429380372370119 546291399956144070558555179)
      ·
        refine ⟨819437099934216105837832769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 546291399956144070558555179 819437099934216105837832769)
        ·
          refine ⟨614577824950662079378374577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 819437099934216105837832769 614577824950662079378374577)
          ·
            refine ⟨460933368712996559533780933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 614577824950662079378374577 460933368712996559533780933)
            ·
              refine ⟨86425006633686854912583925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 460933368712996559533780933 86425006633686854912583925)
              ·
                refine ⟨8102344371908142648054743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86425006633686854912583925 8102344371908142648054743)
                ·
                  refine ⟨12153516557862213972082115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8102344371908142648054743 12153516557862213972082115)
                  ·
                    refine ⟨18230274836793320958123173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12153516557862213972082115 18230274836793320958123173)
                    ·
                      refine ⟨3418176531898747679648095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18230274836793320958123173 3418176531898747679648095)
                      ·
                        rfl

theorem cell23_6656875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 5, 1, 1, 4].length) (baseStart_6656875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6656875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6656875 prefixEnd_6656875 := by exact prefixLift 6656875
  have htrace : WordTrace (prefixWord ++ tailWord_6656875) baseStart_6656875 baseEnd_6656875 := by
    simpa [prefixWord, tailWord_6656875, baseEnd_6656875] using wordTrace_append hprefix tailTrace_6656875
  have hstable : (prefixWord ++ tailWord_6656875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6656875).length < 2 ^ (prefixWord ++ tailWord_6656875).sum := by decide
  have hdescent : baseEnd_6656875 < baseStart_6656875 := by decide
  rcases family_descends (prefixWord ++ tailWord_6656875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6656888 : List Nat := [2, 1, 2, 1, 1, 1, 1, 6, 1, 1, 6]
def baseStart_6656888 : Nat := 118140960795 + 6656888 * 2 ^ 59
def prefixEnd_6656888 : Nat := 4983230072969 + 3 ^ 40 * 6656888 * 2
def baseEnd_6656888 : Nat := 3418183207147256128785535

theorem tailTrace_6656888 : CollatzResearch.WordTrace tailWord_6656888 prefixEnd_6656888 3418183207147256128785535 := by
  unfold tailWord_6656888
  simp only [CollatzResearch.WordTrace]
  refine ⟨121398325953619578400901659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161864434604826104534535545 121398325953619578400901659)
  ·
    refine ⟨182097488930429367601352489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121398325953619578400901659 182097488930429367601352489)
    ·
      refine ⟨136573116697822025701014367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182097488930429367601352489 136573116697822025701014367)
      ·
        refine ⟨204859675046733038551521551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136573116697822025701014367 204859675046733038551521551)
        ·
          refine ⟨307289512570099557827282327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204859675046733038551521551 307289512570099557827282327)
          ·
            refine ⟨460934268855149336740923491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307289512570099557827282327 460934268855149336740923491)
            ·
              refine ⟨691401403282724005111385237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 460934268855149336740923491 691401403282724005111385237)
              ·
                refine ⟨32409440778877687739596183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 691401403282724005111385237 32409440778877687739596183)
                ·
                  refine ⟨48614161168316531609394275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32409440778877687739596183 48614161168316531609394275)
                  ·
                    refine ⟨72921241752474797414091413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48614161168316531609394275 72921241752474797414091413)
                    ·
                      refine ⟨3418183207147256128785535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72921241752474797414091413 3418183207147256128785535)
                      ·
                        rfl

theorem cell23_6656888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 1, 1, 6].length) (baseStart_6656888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6656888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6656888 prefixEnd_6656888 := by exact prefixLift 6656888
  have htrace : WordTrace (prefixWord ++ tailWord_6656888) baseStart_6656888 baseEnd_6656888 := by
    simpa [prefixWord, tailWord_6656888, baseEnd_6656888] using wordTrace_append hprefix tailTrace_6656888
  have hstable : (prefixWord ++ tailWord_6656888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6656888).length < 2 ^ (prefixWord ++ tailWord_6656888).sum := by decide
  have hdescent : baseEnd_6656888 < baseStart_6656888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6656888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6656892 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 7, 2, 2]
def baseStart_6656892 : Nat := 118140960795 + 6656892 * 2 ^ 59
def prefixEnd_6656892 : Nat := 4983230072969 + 3 ^ 40 * 6656892 * 2
def baseEnd_6656892 : Nat := 3418185261069874113135517

theorem tailTrace_6656892 : CollatzResearch.WordTrace tailWord_6656892 prefixEnd_6656892 3418185261069874113135517 := by
  unfold tailWord_6656892
  simp only [CollatzResearch.WordTrace]
  refine ⟨121398398899612332742474465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161864531866149776989965953 121398398899612332742474465)
  ·
    refine ⟨91048799174709249556855849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121398398899612332742474465 91048799174709249556855849)
    ·
      refine ⟨68286599381031937167641887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91048799174709249556855849 68286599381031937167641887)
      ·
        refine ⟨102429899071547905751462831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68286599381031937167641887 102429899071547905751462831)
        ·
          refine ⟨153644848607321858627194247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102429899071547905751462831 153644848607321858627194247)
          ·
            refine ⟨230467272910982787940791371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153644848607321858627194247 230467272910982787940791371)
            ·
              refine ⟨345700909366474181911187057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230467272910982787940791371 345700909366474181911187057)
              ·
                refine ⟨259275682024855636433390293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 345700909366474181911187057 259275682024855636433390293)
                ·
                  refine ⟨6076773797457553978907585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 259275682024855636433390293 6076773797457553978907585)
                  ·
                    refine ⟨4557580348093165484180689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6076773797457553978907585 4557580348093165484180689)
                    ·
                      refine ⟨3418185261069874113135517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4557580348093165484180689 3418185261069874113135517)
                      ·
                        rfl

theorem cell23_6656892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 7, 2, 2].length) (baseStart_6656892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6656892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6656892 prefixEnd_6656892 := by exact prefixLift 6656892
  have htrace : WordTrace (prefixWord ++ tailWord_6656892) baseStart_6656892 baseEnd_6656892 := by
    simpa [prefixWord, tailWord_6656892, baseEnd_6656892] using wordTrace_append hprefix tailTrace_6656892
  have hstable : (prefixWord ++ tailWord_6656892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6656892).length < 2 ^ (prefixWord ++ tailWord_6656892).sum := by decide
  have hdescent : baseEnd_6656892 < baseStart_6656892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6656892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6656895 : List Nat := [1, 1, 2, 2, 1, 1, 5, 2, 3, 2, 3]
def baseStart_6656895 : Nat := 118140960795 + 6656895 * 2 ^ 59
def prefixEnd_6656895 : Nat := 4983230072969 + 3 ^ 40 * 6656895 * 2
def baseEnd_6656895 : Nat := 3418186801511837601398003

theorem tailTrace_6656895 : CollatzResearch.WordTrace tailWord_6656895 prefixEnd_6656895 3418186801511837601398003 := by
  unfold tailWord_6656895
  simp only [CollatzResearch.WordTrace]
  refine ⟨242796907218213796997308139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161864604812142531331538759 242796907218213796997308139)
  ·
    refine ⟨364195360827320695495962209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242796907218213796997308139 364195360827320695495962209)
    ·
      refine ⟨273146520620490521621971657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364195360827320695495962209 273146520620490521621971657)
      ·
        refine ⟨204859890465367891216478743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273146520620490521621971657 204859890465367891216478743)
        ·
          refine ⟨307289835698051836824718115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204859890465367891216478743 307289835698051836824718115)
          ·
            refine ⟨460934753547077755237077173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307289835698051836824718115 460934753547077755237077173)
            ·
              refine ⟨43212633145038539553475985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 460934753547077755237077173 43212633145038539553475985)
              ·
                refine ⟨32409474858778904665106989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43212633145038539553475985 32409474858778904665106989)
                ·
                  refine ⟨12153553072042089249415121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32409474858778904665106989 12153553072042089249415121)
                  ·
                    refine ⟨9115164804031566937061341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12153553072042089249415121 9115164804031566937061341)
                    ·
                      refine ⟨3418186801511837601398003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9115164804031566937061341 3418186801511837601398003)
                      ·
                        rfl

theorem cell23_6656895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 3, 2, 3].length) (baseStart_6656895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6656895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6656895 prefixEnd_6656895 := by exact prefixLift 6656895
  have htrace : WordTrace (prefixWord ++ tailWord_6656895) baseStart_6656895 baseEnd_6656895 := by
    simpa [prefixWord, tailWord_6656895, baseEnd_6656895] using wordTrace_append hprefix tailTrace_6656895
  have hstable : (prefixWord ++ tailWord_6656895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6656895).length < 2 ^ (prefixWord ++ tailWord_6656895).sum := by decide
  have hdescent : baseEnd_6656895 < baseStart_6656895 := by decide
  rcases family_descends (prefixWord ++ tailWord_6656895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6656905 : List Nat := [1, 2, 1, 1, 5, 2, 1, 3, 1, 2, 4]
def baseStart_6656905 : Nat := 118140960795 + 6656905 * 2 ^ 59
def prefixEnd_6656905 : Nat := 4983230072969 + 3 ^ 40 * 6656905 * 2
def baseEnd_6656905 : Nat := 3418191936318382562272957

theorem tailTrace_6656905 : CollatzResearch.WordTrace tailWord_6656905 prefixEnd_6656905 3418191936318382562272957 := by
  unfold tailWord_6656905
  simp only [CollatzResearch.WordTrace]
  refine ⟨242797271948177568705172169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161864847965451712470114779 242797271948177568705172169)
  ·
    refine ⟨182097953961133176528879127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242797271948177568705172169 182097953961133176528879127)
    ·
      refine ⟨273146930941699764793318691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182097953961133176528879127 273146930941699764793318691)
      ·
        refine ⟨409720396412549647189978037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273146930941699764793318691 409720396412549647189978037)
        ·
          refine ⟨38411287163676529424060441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 409720396412549647189978037 38411287163676529424060441)
          ·
            refine ⟨28808465372757397068045331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38411287163676529424060441 28808465372757397068045331)
            ·
              refine ⟨43212698059136095602067997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28808465372757397068045331 43212698059136095602067997)
              ·
                refine ⟨16204761772176035850775499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43212698059136095602067997 16204761772176035850775499)
                ·
                  refine ⟨24307142658264053776163249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16204761772176035850775499 24307142658264053776163249)
                  ·
                    refine ⟨18230356993698040332122437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24307142658264053776163249 18230356993698040332122437)
                    ·
                      refine ⟨3418191936318382562272957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18230356993698040332122437 3418191936318382562272957)
                      ·
                        rfl

theorem cell23_6656905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 2, 4].length) (baseStart_6656905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6656905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6656905 prefixEnd_6656905 := by exact prefixLift 6656905
  have htrace : WordTrace (prefixWord ++ tailWord_6656905) baseStart_6656905 baseEnd_6656905 := by
    simpa [prefixWord, tailWord_6656905, baseEnd_6656905] using wordTrace_append hprefix tailTrace_6656905
  have hstable : (prefixWord ++ tailWord_6656905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6656905).length < 2 ^ (prefixWord ++ tailWord_6656905).sum := by decide
  have hdescent : baseEnd_6656905 < baseStart_6656905 := by decide
  rcases family_descends (prefixWord ++ tailWord_6656905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6656929 : List Nat := [1, 2, 3, 4, 1, 2, 1, 3, 1, 2, 3]
def baseStart_6656929 : Nat := 118140960795 + 6656929 * 2 ^ 59
def prefixEnd_6656929 : Nat := 4983230072969 + 3 ^ 40 * 6656929 * 2
def baseEnd_6656929 : Nat := 3418204259854090468372847

theorem tailTrace_6656929 : CollatzResearch.WordTrace tailWord_6656929 prefixEnd_6656929 3418204259854090468372847 := by
  unfold tailWord_6656929
  simp only [CollatzResearch.WordTrace]
  refine ⟨242798147300090620804045841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161865431533393747202697227 242798147300090620804045841)
  ·
    refine ⟨182098610475067965603034381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242798147300090620804045841 182098610475067965603034381)
    ·
      refine ⟨68286978928150487101137893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182098610475067965603034381 68286978928150487101137893)
      ·
        refine ⟨12803808549028216331463355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68286978928150487101137893 12803808549028216331463355)
        ·
          refine ⟨19205712823542324497195033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12803808549028216331463355 19205712823542324497195033)
          ·
            refine ⟨14404284617656743372896275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19205712823542324497195033 14404284617656743372896275)
            ·
              refine ⟨21606426926485115059344413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14404284617656743372896275 21606426926485115059344413)
              ·
                refine ⟨8102410097431918147254155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21606426926485115059344413 8102410097431918147254155)
                ·
                  refine ⟨12153615146147877220881233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8102410097431918147254155 12153615146147877220881233)
                  ·
                    refine ⟨9115211359610907915660925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12153615146147877220881233 9115211359610907915660925)
                    ·
                      refine ⟨3418204259854090468372847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9115211359610907915660925 3418204259854090468372847)
                      ·
                        rfl

theorem cell23_6656929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_6656929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6656929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6656929 prefixEnd_6656929 := by exact prefixLift 6656929
  have htrace : WordTrace (prefixWord ++ tailWord_6656929) baseStart_6656929 baseEnd_6656929 := by
    simpa [prefixWord, tailWord_6656929, baseEnd_6656929] using wordTrace_append hprefix tailTrace_6656929
  have hstable : (prefixWord ++ tailWord_6656929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6656929).length < 2 ^ (prefixWord ++ tailWord_6656929).sum := by decide
  have hdescent : baseEnd_6656929 < baseStart_6656929 := by decide
  rcases family_descends (prefixWord ++ tailWord_6656929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6656985 : List Nat := [1, 2, 1, 2, 5, 1, 1, 1, 1, 3, 5]
def baseStart_6656985 : Nat := 118140960795 + 6656985 * 2 ^ 59
def prefixEnd_6656985 : Nat := 4983230072969 + 3 ^ 40 * 6656985 * 2
def baseEnd_6656985 : Nat := 3418233014770742249272589

theorem tailTrace_6656985 : CollatzResearch.WordTrace tailWord_6656985 prefixEnd_6656985 3418233014770742249272589 := by
  unfold tailWord_6656985
  simp only [CollatzResearch.WordTrace]
  refine ⟨242800189787887742368084409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161866793191925161578722939 242800189787887742368084409)
  ·
    refine ⟨182100142340915806776063307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242800189787887742368084409 182100142340915806776063307)
    ·
      refine ⟨273150213511373710164094961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182100142340915806776063307 273150213511373710164094961)
      ·
        refine ⟨204862660133530282623071221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273150213511373710164094961 204862660133530282623071221)
        ·
          refine ⟨19205874387518463995912927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 204862660133530282623071221 19205874387518463995912927)
          ·
            refine ⟨28808811581277695993869391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19205874387518463995912927 28808811581277695993869391)
            ·
              refine ⟨43213217371916543990804087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28808811581277695993869391 43213217371916543990804087)
              ·
                refine ⟨64819826057874815986206131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43213217371916543990804087 64819826057874815986206131)
                ·
                  refine ⟨97229739086812223979309197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64819826057874815986206131 97229739086812223979309197)
                  ·
                    refine ⟨36461152157554583992240949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 97229739086812223979309197 36461152157554583992240949)
                    ·
                      refine ⟨3418233014770742249272589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36461152157554583992240949 3418233014770742249272589)
                      ·
                        rfl

theorem cell23_6656985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 3, 5].length) (baseStart_6656985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6656985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6656985 prefixEnd_6656985 := by exact prefixLift 6656985
  have htrace : WordTrace (prefixWord ++ tailWord_6656985) baseStart_6656985 baseEnd_6656985 := by
    simpa [prefixWord, tailWord_6656985, baseEnd_6656985] using wordTrace_append hprefix tailTrace_6656985
  have hstable : (prefixWord ++ tailWord_6656985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6656985).length < 2 ^ (prefixWord ++ tailWord_6656985).sum := by decide
  have hdescent : baseEnd_6656985 < baseStart_6656985 := by decide
  rcases family_descends (prefixWord ++ tailWord_6656985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6657010 : List Nat := [3, 2, 1, 5, 1, 2, 2, 1, 2, 1, 3]
def baseStart_6657010 : Nat := 118140960795 + 6657010 * 2 ^ 59
def prefixEnd_6657010 : Nat := 4983230072969 + 3 ^ 40 * 6657010 * 2
def baseEnd_6657010 : Nat := 3418245851787104651459975

theorem tailTrace_6657010 : CollatzResearch.WordTrace tailWord_6657010 prefixEnd_6657010 3418245851787104651459975 := by
  unfold tailWord_6657010
  simp only [CollatzResearch.WordTrace]
  refine ⟨60700275403199292909436121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161867401075198114425162989 60700275403199292909436121)
  ·
    refine ⟨45525206552399469682077091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60700275403199292909436121 45525206552399469682077091)
    ·
      refine ⟨68287809828599204523115637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45525206552399469682077091 68287809828599204523115637)
      ·
        refine ⟨6401982171431175424042091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68287809828599204523115637 6401982171431175424042091)
        ·
          refine ⟨9602973257146763136063137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6401982171431175424042091 9602973257146763136063137)
          ·
            refine ⟨7202229942860072352047353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9602973257146763136063137 7202229942860072352047353)
            ·
              refine ⟨5401672457145054264035515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7202229942860072352047353 5401672457145054264035515)
              ·
                refine ⟨8102508685717581396053273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5401672457145054264035515 8102508685717581396053273)
                ·
                  refine ⟨6076881514288186047039955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8102508685717581396053273 6076881514288186047039955)
                  ·
                    refine ⟨9115322271432279070559933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6076881514288186047039955 9115322271432279070559933)
                    ·
                      refine ⟨3418245851787104651459975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9115322271432279070559933 3418245851787104651459975)
                      ·
                        rfl

theorem cell23_6657010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_6657010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6657010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6657010 prefixEnd_6657010 := by exact prefixLift 6657010
  have htrace : WordTrace (prefixWord ++ tailWord_6657010) baseStart_6657010 baseEnd_6657010 := by
    simpa [prefixWord, tailWord_6657010, baseEnd_6657010] using wordTrace_append hprefix tailTrace_6657010
  have hstable : (prefixWord ++ tailWord_6657010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6657010).length < 2 ^ (prefixWord ++ tailWord_6657010).sum := by decide
  have hdescent : baseEnd_6657010 < baseStart_6657010 := by decide
  rcases family_descends (prefixWord ++ tailWord_6657010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6657056 : List Nat := [2, 1, 1, 7, 1, 1, 1, 4, 5]
def baseStart_6657056 : Nat := 118140960795 + 6657056 * 2 ^ 59
def prefixEnd_6657056 : Nat := 4983230072969 + 3 ^ 40 * 6657056 * 2
def baseEnd_6657056 : Nat := 379807719099690163498307

theorem tailTrace_6657056 : CollatzResearch.WordTrace tailWord_6657056 prefixEnd_6657056 379807719099690163498307 := by
  unfold tailWord_6657056
  simp only [CollatzResearch.WordTrace]
  refine ⟨121401389685315260746959511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161868519580420347662612681 121401389685315260746959511)
  ·
    refine ⟨182102084527972891120439267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121401389685315260746959511 182102084527972891120439267)
    ·
      refine ⟨273153126791959336680658901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182102084527972891120439267 273153126791959336680658901)
      ·
        refine ⟨6402026409186546953452943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 273153126791959336680658901 6402026409186546953452943)
        ·
          refine ⟨9603039613779820430179415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6402026409186546953452943 9603039613779820430179415)
          ·
            refine ⟨14404559420669730645269123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9603039613779820430179415 14404559420669730645269123)
            ·
              refine ⟨21606839131004595967903685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14404559420669730645269123 21606839131004595967903685)
              ·
                refine ⟨4051282337063361743981941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21606839131004595967903685 4051282337063361743981941)
                ·
                  refine ⟨379807719099690163498307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4051282337063361743981941 379807719099690163498307)
                  ·
                    rfl

theorem cell23_6657056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 4, 5].length) (baseStart_6657056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6657056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6657056 prefixEnd_6657056 := by exact prefixLift 6657056
  have htrace : WordTrace (prefixWord ++ tailWord_6657056) baseStart_6657056 baseEnd_6657056 := by
    simpa [prefixWord, tailWord_6657056, baseEnd_6657056] using wordTrace_append hprefix tailTrace_6657056
  have hstable : (prefixWord ++ tailWord_6657056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6657056).length < 2 ^ (prefixWord ++ tailWord_6657056).sum := by decide
  have hdescent : baseEnd_6657056 < baseStart_6657056 := by decide
  rcases family_descends (prefixWord ++ tailWord_6657056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6657082 : List Nat := [3, 1, 1, 1, 3, 1, 3, 1, 5, 4]
def baseStart_6657082 : Nat := 118140960795 + 6657082 * 2 ^ 59
def prefixEnd_6657082 : Nat := 4983230072969 + 3 ^ 40 * 6657082 * 2
def baseEnd_6657082 : Nat := 1139427607464742789919881

theorem tailTrace_6657082 : CollatzResearch.WordTrace tailWord_6657082 prefixEnd_6657082 1139427607464742789919881 := by
  unfold tailWord_6657082
  simp only [CollatzResearch.WordTrace]
  refine ⟨60700931917134081983591375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161869151779024218622910333 60700931917134081983591375)
  ·
    refine ⟨91051397875701122975387063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60700931917134081983591375 91051397875701122975387063)
    ·
      refine ⟨136577096813551684463080595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91051397875701122975387063 136577096813551684463080595)
      ·
        refine ⟨204865645220327526694620893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136577096813551684463080595 204865645220327526694620893)
        ·
          refine ⟨76824616957622822510482835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204865645220327526694620893 76824616957622822510482835)
          ·
            refine ⟨115236925436434233765724253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76824616957622822510482835 115236925436434233765724253)
            ·
              refine ⟨43213847038662837662146595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115236925436434233765724253 43213847038662837662146595)
              ·
                refine ⟨64820770557994256493219893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43213847038662837662146595 64820770557994256493219893)
                ·
                  refine ⟨6076947239811961546239365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64820770557994256493219893 6076947239811961546239365)
                  ·
                    refine ⟨1139427607464742789919881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6076947239811961546239365 1139427607464742789919881)
                    ·
                      rfl

theorem cell23_6657082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 5, 4].length) (baseStart_6657082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6657082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6657082 prefixEnd_6657082 := by exact prefixLift 6657082
  have htrace : WordTrace (prefixWord ++ tailWord_6657082) baseStart_6657082 baseEnd_6657082 := by
    simpa [prefixWord, tailWord_6657082, baseEnd_6657082] using wordTrace_append hprefix tailTrace_6657082
  have hstable : (prefixWord ++ tailWord_6657082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6657082).length < 2 ^ (prefixWord ++ tailWord_6657082).sum := by decide
  have hdescent : baseEnd_6657082 < baseStart_6657082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6657082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6657086 : List Nat := [4, 2, 1, 3, 1, 3, 1, 1, 2, 5]
def baseStart_6657086 : Nat := 118140960795 + 6657086 * 2 ^ 59
def prefixEnd_6657086 : Nat := 4983230072969 + 3 ^ 40 * 6657086 * 2
def baseEnd_6657086 : Nat := 1139428292105615451369875

theorem tailTrace_6657086 : CollatzResearch.WordTrace tailWord_6657086 prefixEnd_6657086 1139428292105615451369875 := by
  unfold tailWord_6657086
  simp only [CollatzResearch.WordTrace]
  refine ⟨30350484195065229577188889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161869249040347891078340741 30350484195065229577188889)
  ·
    refine ⟨22762863146298922182891667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30350484195065229577188889 22762863146298922182891667)
    ·
      refine ⟨34144294719448383274337501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22762863146298922182891667 34144294719448383274337501)
      ·
        refine ⟨12804110519793143727876563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34144294719448383274337501 12804110519793143727876563)
        ·
          refine ⟨19206165779689715591814845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12804110519793143727876563 19206165779689715591814845)
          ·
            refine ⟨7202312167383643346930567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19206165779689715591814845 7202312167383643346930567)
            ·
              refine ⟨10803468251075465020395851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7202312167383643346930567 10803468251075465020395851)
              ·
                refine ⟨16205202376613197530593777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10803468251075465020395851 16205202376613197530593777)
                ·
                  refine ⟨12153901782459898147945333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16205202376613197530593777 12153901782459898147945333)
                  ·
                    refine ⟨1139428292105615451369875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12153901782459898147945333 1139428292105615451369875)
                    ·
                      rfl

theorem cell23_6657086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_6657086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6657086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6657086 prefixEnd_6657086 := by exact prefixLift 6657086
  have htrace : WordTrace (prefixWord ++ tailWord_6657086) baseStart_6657086 baseEnd_6657086 := by
    simpa [prefixWord, tailWord_6657086, baseEnd_6657086] using wordTrace_append hprefix tailTrace_6657086
  have hstable : (prefixWord ++ tailWord_6657086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6657086).length < 2 ^ (prefixWord ++ tailWord_6657086).sum := by decide
  have hdescent : baseEnd_6657086 < baseStart_6657086 := by decide
  rcases family_descends (prefixWord ++ tailWord_6657086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6657089 : List Nat := [1, 2, 5, 1, 3, 1, 1, 1, 1, 3, 4]
def baseStart_6657089 : Nat := 118140960795 + 6657089 * 2 ^ 59
def prefixEnd_6657089 : Nat := 4983230072969 + 3 ^ 40 * 6657089 * 2
def baseEnd_6657089 : Nat := 3418286416758809842372111

theorem tailTrace_6657089 : CollatzResearch.WordTrace tailWord_6657089 prefixEnd_6657089 3418286416758809842372111 := by
  unfold tailWord_6657089
  simp only [CollatzResearch.WordTrace]
  refine ⟨242803982979510968129870321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161869321986340645419913547 242803982979510968129870321)
  ·
    refine ⟨182102987234633226097402741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242803982979510968129870321 182102987234633226097402741)
    ·
      refine ⟨17072155053246864946631507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 182102987234633226097402741 17072155053246864946631507)
      ·
        refine ⟨25608232579870297419947261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17072155053246864946631507 25608232579870297419947261)
        ·
          refine ⟨9603087217451361532480223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25608232579870297419947261 9603087217451361532480223)
          ·
            refine ⟨14404630826177042298720335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9603087217451361532480223 14404630826177042298720335)
            ·
              refine ⟨21606946239265563448080503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14404630826177042298720335 21606946239265563448080503)
              ·
                refine ⟨32410419358898345172120755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21606946239265563448080503 32410419358898345172120755)
                ·
                  refine ⟨48615629038347517758181133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32410419358898345172120755 48615629038347517758181133)
                  ·
                    refine ⟨18230860889380319159317925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48615629038347517758181133 18230860889380319159317925)
                    ·
                      refine ⟨3418286416758809842372111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18230860889380319159317925 3418286416758809842372111)
                      ·
                        rfl

theorem cell23_6657089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_6657089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6657089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6657089 prefixEnd_6657089 := by exact prefixLift 6657089
  have htrace : WordTrace (prefixWord ++ tailWord_6657089) baseStart_6657089 baseEnd_6657089 := by
    simpa [prefixWord, tailWord_6657089, baseEnd_6657089] using wordTrace_append hprefix tailTrace_6657089
  have hstable : (prefixWord ++ tailWord_6657089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6657089).length < 2 ^ (prefixWord ++ tailWord_6657089).sum := by decide
  have hdescent : baseEnd_6657089 < baseStart_6657089 := by decide
  rcases family_descends (prefixWord ++ tailWord_6657089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6657116 : List Nat := [2, 2, 4, 1, 1, 1, 1, 6, 1, 4]
def baseStart_6657116 : Nat := 118140960795 + 6657116 * 2 ^ 59
def prefixEnd_6657116 : Nat := 4983230072969 + 3 ^ 40 * 6657116 * 2
def baseEnd_6657116 : Nat := 1139433426912160412244829

theorem tailTrace_6657116 : CollatzResearch.WordTrace tailWord_6657116 prefixEnd_6657116 1139433426912160412244829 := by
  unfold tailWord_6657116
  simp only [CollatzResearch.WordTrace]
  refine ⟨121402483875206575870551601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161869978500275434494068801 121402483875206575870551601)
  ·
    refine ⟨91051862906404931902913701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121402483875206575870551601 91051862906404931902913701)
    ·
      refine ⟨17072224294950924731796319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91051862906404931902913701 17072224294950924731796319)
      ·
        refine ⟨25608336442426387097694479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17072224294950924731796319 25608336442426387097694479)
        ·
          refine ⟨38412504663639580646541719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25608336442426387097694479 38412504663639580646541719)
          ·
            refine ⟨57618756995459370969812579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38412504663639580646541719 57618756995459370969812579)
            ·
              refine ⟨86428135493189056454718869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57618756995459370969812579 86428135493189056454718869)
              ·
                refine ⟨4051318851243237021314947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 86428135493189056454718869 4051318851243237021314947)
                ·
                  refine ⟨6076978276864855531972421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4051318851243237021314947 6076978276864855531972421)
                  ·
                    refine ⟨1139433426912160412244829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6076978276864855531972421 1139433426912160412244829)
                    ·
                      rfl

theorem cell23_6657116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_6657116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6657116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6657116 prefixEnd_6657116 := by exact prefixLift 6657116
  have htrace : WordTrace (prefixWord ++ tailWord_6657116) baseStart_6657116 baseEnd_6657116 := by
    simpa [prefixWord, tailWord_6657116, baseEnd_6657116] using wordTrace_append hprefix tailTrace_6657116
  have hstable : (prefixWord ++ tailWord_6657116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6657116).length < 2 ^ (prefixWord ++ tailWord_6657116).sum := by decide
  have hdescent : baseEnd_6657116 < baseStart_6657116 := by decide
  rcases family_descends (prefixWord ++ tailWord_6657116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6657129 : List Nat := [1, 2, 1, 1, 1, 7, 3, 1, 6]
def baseStart_6657129 : Nat := 118140960795 + 6657129 * 2 ^ 59
def prefixEnd_6657129 : Nat := 4983230072969 + 3 ^ 40 * 6657129 * 2
def baseEnd_6657129 : Nat := 379811883998332187319103

theorem tailTrace_6657129 : CollatzResearch.WordTrace tailWord_6657129 prefixEnd_6657129 379811883998332187319103 := by
  unfold tailWord_6657129
  simp only [CollatzResearch.WordTrace]
  refine ⟨242805441899366054961326441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161870294599577369974217627 242805441899366054961326441)
  ·
    refine ⟨182104081424524541220994831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242805441899366054961326441 182104081424524541220994831)
    ·
      refine ⟨273156122136786811831492247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182104081424524541220994831 273156122136786811831492247)
      ·
        refine ⟨409734183205180217747238371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273156122136786811831492247 409734183205180217747238371)
        ·
          refine ⟨614601274807770326620857557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409734183205180217747238371 614601274807770326620857557)
          ·
            refine ⟨14404717378307117030176349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 614601274807770326620857557 14404717378307117030176349)
            ·
              refine ⟨5401769016865168886316131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14404717378307117030176349 5401769016865168886316131)
              ·
                refine ⟨8102653525297753329474197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5401769016865168886316131 8102653525297753329474197)
                ·
                  refine ⟨379811883998332187319103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8102653525297753329474197 379811883998332187319103)
                  ·
                    rfl

theorem cell23_6657129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 1, 6].length) (baseStart_6657129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6657129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6657129 prefixEnd_6657129 := by exact prefixLift 6657129
  have htrace : WordTrace (prefixWord ++ tailWord_6657129) baseStart_6657129 baseEnd_6657129 := by
    simpa [prefixWord, tailWord_6657129, baseEnd_6657129] using wordTrace_append hprefix tailTrace_6657129
  have hstable : (prefixWord ++ tailWord_6657129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6657129).length < 2 ^ (prefixWord ++ tailWord_6657129).sum := by decide
  have hdescent : baseEnd_6657129 < baseStart_6657129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6657129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6657149 : List Nat := [1, 4, 1, 1, 3, 1, 1, 3, 1, 5, 2]
def baseStart_6657149 : Nat := 118140960795 + 6657149 * 2 ^ 59
def prefixEnd_6657149 : Nat := 4983230072969 + 3 ^ 40 * 6657149 * 2
def baseEnd_6657149 : Nat := 3418317225598079607621835

theorem tailTrace_6657149 : CollatzResearch.WordTrace tailWord_6657149 prefixEnd_6657149 3418317225598079607621835 := by
  unfold tailWord_6657149
  simp only [CollatzResearch.WordTrace]
  refine ⟨242806171359293598377054501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161870780906195732251369667 242806171359293598377054501)
  ·
    refine ⟨45526157129867549695697719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 242806171359293598377054501 45526157129867549695697719)
    ·
      refine ⟨68289235694801324543546579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45526157129867549695697719 68289235694801324543546579)
      ·
        refine ⟨102433853542201986815319869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68289235694801324543546579 102433853542201986815319869)
        ·
          refine ⟨38412695078325745055744951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102433853542201986815319869 38412695078325745055744951)
          ·
            refine ⟨57619042617488617583617427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38412695078325745055744951 57619042617488617583617427)
            ·
              refine ⟨86428563926232926375426141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57619042617488617583617427 86428563926232926375426141)
              ·
                refine ⟨32410711472337347390784803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86428563926232926375426141 32410711472337347390784803)
                ·
                  refine ⟨48616067208506021086177205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32410711472337347390784803 48616067208506021086177205)
                  ·
                    refine ⟨4557756300797439476829113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48616067208506021086177205 4557756300797439476829113)
                    ·
                      refine ⟨3418317225598079607621835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4557756300797439476829113 3418317225598079607621835)
                      ·
                        rfl

theorem cell23_6657149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 5, 2].length) (baseStart_6657149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6657149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6657149 prefixEnd_6657149 := by exact prefixLift 6657149
  have htrace : WordTrace (prefixWord ++ tailWord_6657149) baseStart_6657149 baseEnd_6657149 := by
    simpa [prefixWord, tailWord_6657149, baseEnd_6657149] using wordTrace_append hprefix tailTrace_6657149
  have hstable : (prefixWord ++ tailWord_6657149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6657149).length < 2 ^ (prefixWord ++ tailWord_6657149).sum := by decide
  have hdescent : baseEnd_6657149 < baseStart_6657149 := by decide
  rcases family_descends (prefixWord ++ tailWord_6657149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6657166 : List Nat := [4, 1, 1, 3, 2, 1, 1, 1, 4, 3, 2]
def baseStart_6657166 : Nat := 118140960795 + 6657166 * 2 ^ 59
def prefixEnd_6657166 : Nat := 4983230072969 + 3 ^ 40 * 6657166 * 2
def baseEnd_6657166 : Nat := 3418325954769206041109257

theorem tailTrace_6657166 : CollatzResearch.WordTrace tailWord_6657166 prefixEnd_6657166 3418325954769206041109257 := by
  unfold tailWord_6657166
  simp only [CollatzResearch.WordTrace]
  refine ⟨30350848925029001285052919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161871194266821340186948901 30350848925029001285052919)
  ·
    refine ⟨45526273387543501927579379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30350848925029001285052919 45526273387543501927579379)
    ·
      refine ⟨68289410081315252891369069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45526273387543501927579379 68289410081315252891369069)
      ·
        refine ⟨25608528780493219834263401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68289410081315252891369069 25608528780493219834263401)
        ·
          refine ⟨19206396585369914875697551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25608528780493219834263401 19206396585369914875697551)
          ·
            refine ⟨28809594878054872313546327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19206396585369914875697551 28809594878054872313546327)
            ·
              refine ⟨43214392317082308470319491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28809594878054872313546327 43214392317082308470319491)
              ·
                refine ⟨64821588475623462705479237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43214392317082308470319491 64821588475623462705479237)
                ·
                  refine ⟨12154047839179399257277357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64821588475623462705479237 12154047839179399257277357)
                  ·
                    refine ⟨4557767939692274721479009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12154047839179399257277357 4557767939692274721479009)
                    ·
                      refine ⟨3418325954769206041109257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4557767939692274721479009 3418325954769206041109257)
                      ·
                        rfl

theorem cell23_6657166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_6657166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6657166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6657166 prefixEnd_6657166 := by exact prefixLift 6657166
  have htrace : WordTrace (prefixWord ++ tailWord_6657166) baseStart_6657166 baseEnd_6657166 := by
    simpa [prefixWord, tailWord_6657166, baseEnd_6657166] using wordTrace_append hprefix tailTrace_6657166
  have hstable : (prefixWord ++ tailWord_6657166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6657166).length < 2 ^ (prefixWord ++ tailWord_6657166).sum := by decide
  have hdescent : baseEnd_6657166 < baseStart_6657166 := by decide
  rcases family_descends (prefixWord ++ tailWord_6657166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6657202 : List Nat := [3, 2, 1, 1, 1, 4, 2, 9]
def baseStart_6657202 : Nat := 118140960795 + 6657202 * 2 ^ 59
def prefixEnd_6657202 : Nat := 4983230072969 + 3 ^ 40 * 6657202 * 2
def baseEnd_6657202 : Nat := 126605349632324737046633

theorem tailTrace_6657202 : CollatzResearch.WordTrace tailWord_6657202 prefixEnd_6657202 126605349632324737046633 := by
  unfold tailWord_6657202
  simp only [CollatzResearch.WordTrace]
  refine ⟨60702026107025397107183465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161872069618734392285822573 60702026107025397107183465)
  ·
    refine ⟨45526519580269047830387599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60702026107025397107183465 45526519580269047830387599)
    ·
      refine ⟨68289779370403571745581399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45526519580269047830387599 68289779370403571745581399)
      ·
        refine ⟨102434669055605357618372099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68289779370403571745581399 102434669055605357618372099)
        ·
          refine ⟨153652003583408036427558149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102434669055605357618372099 153652003583408036427558149)
          ·
            refine ⟨28809750671889006830167153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153652003583408036427558149 28809750671889006830167153)
            ·
              refine ⟨21607313003916755122625365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28809750671889006830167153 21607313003916755122625365)
              ·
                refine ⟨126605349632324737046633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21607313003916755122625365 126605349632324737046633)
                ·
                  rfl

theorem cell23_6657202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 9].length) (baseStart_6657202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6657202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6657202 prefixEnd_6657202 := by exact prefixLift 6657202
  have htrace : WordTrace (prefixWord ++ tailWord_6657202) baseStart_6657202 baseEnd_6657202 := by
    simpa [prefixWord, tailWord_6657202, baseEnd_6657202] using wordTrace_append hprefix tailTrace_6657202
  have hstable : (prefixWord ++ tailWord_6657202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6657202).length < 2 ^ (prefixWord ++ tailWord_6657202).sum := by decide
  have hdescent : baseEnd_6657202 < baseStart_6657202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6657202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6657209 : List Nat := [1, 2, 1, 4, 1, 4, 1, 2, 1, 2, 4]
def baseStart_6657209 : Nat := 118140960795 + 6657209 * 2 ^ 59
def prefixEnd_6657209 : Nat := 4983230072969 + 3 ^ 40 * 6657209 * 2
def baseEnd_6657209 : Nat := 3418348034437349372871559

theorem tailTrace_6657209 : CollatzResearch.WordTrace tailWord_6657209 prefixEnd_6657209 3418348034437349372871559 := by
  unfold tailWord_6657209
  simp only [CollatzResearch.WordTrace]
  refine ⟨242808359739076228624238681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161872239826050819082825787 242808359739076228624238681)
  ·
    refine ⟨182106269804307171468179011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242808359739076228624238681 182106269804307171468179011)
    ·
      refine ⟨273159404706460757202268517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182106269804307171468179011 273159404706460757202268517)
      ·
        refine ⟨51217388382461391975425347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 273159404706460757202268517 51217388382461391975425347)
        ·
          refine ⟨76826082573692087963138021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51217388382461391975425347 76826082573692087963138021)
          ·
            refine ⟨14404890482567266493088379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76826082573692087963138021 14404890482567266493088379)
            ·
              refine ⟨21607335723850899739632569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14404890482567266493088379 21607335723850899739632569)
              ·
                refine ⟨16205501792888174804724427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21607335723850899739632569 16205501792888174804724427)
                ·
                  refine ⟨24308252689332262207086641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16205501792888174804724427 24308252689332262207086641)
                  ·
                    refine ⟨18231189516999196655314981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24308252689332262207086641 18231189516999196655314981)
                    ·
                      refine ⟨3418348034437349372871559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18231189516999196655314981 3418348034437349372871559)
                      ·
                        rfl

theorem cell23_6657209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_6657209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6657209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6657209 prefixEnd_6657209 := by exact prefixLift 6657209
  have htrace : WordTrace (prefixWord ++ tailWord_6657209) baseStart_6657209 baseEnd_6657209 := by
    simpa [prefixWord, tailWord_6657209, baseEnd_6657209] using wordTrace_append hprefix tailTrace_6657209
  have hstable : (prefixWord ++ tailWord_6657209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6657209).length < 2 ^ (prefixWord ++ tailWord_6657209).sum := by decide
  have hdescent : baseEnd_6657209 < baseStart_6657209 := by decide
  rcases family_descends (prefixWord ++ tailWord_6657209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6657216 : List Nat := [2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 5]
def baseStart_6657216 : Nat := 118140960795 + 6657216 * 2 ^ 59
def prefixEnd_6657216 : Nat := 4983230072969 + 3 ^ 40 * 6657216 * 2
def baseEnd_6657216 : Nat := 3418351628801930845484027

theorem tailTrace_6657216 : CollatzResearch.WordTrace tailWord_6657216 prefixEnd_6657216 3418351628801930845484027 := by
  unfold tailWord_6657216
  simp only [CollatzResearch.WordTrace]
  refine ⟨121404307525025434409871751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161872410033367245879829001 121404307525025434409871751)
  ·
    refine ⟨182106461287538151614807627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121404307525025434409871751 182106461287538151614807627)
    ·
      refine ⟨273159691931307227422211441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182106461287538151614807627 273159691931307227422211441)
      ·
        refine ⟨204869768948480420566658581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273159691931307227422211441 204869768948480420566658581)
        ·
          refine ⟨9603270419460019714062121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 204869768948480420566658581 9603270419460019714062121)
          ·
            refine ⟨7202452814595014785546591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9603270419460019714062121 7202452814595014785546591)
            ·
              refine ⟨10803679221892522178319887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7202452814595014785546591 10803679221892522178319887)
              ·
                refine ⟨16205518832838783267479831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10803679221892522178319887 16205518832838783267479831)
                ·
                  refine ⟨24308278249258174901219747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16205518832838783267479831 24308278249258174901219747)
                  ·
                    refine ⟨36462417373887262351829621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24308278249258174901219747 36462417373887262351829621)
                    ·
                      refine ⟨3418351628801930845484027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36462417373887262351829621 3418351628801930845484027)
                      ·
                        rfl

theorem cell23_6657216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 5].length) (baseStart_6657216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6657216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6657216 prefixEnd_6657216 := by exact prefixLift 6657216
  have htrace : WordTrace (prefixWord ++ tailWord_6657216) baseStart_6657216 baseEnd_6657216 := by
    simpa [prefixWord, tailWord_6657216, baseEnd_6657216] using wordTrace_append hprefix tailTrace_6657216
  have hstable : (prefixWord ++ tailWord_6657216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6657216).length < 2 ^ (prefixWord ++ tailWord_6657216).sum := by decide
  have hdescent : baseEnd_6657216 < baseStart_6657216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6657216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6657242 : List Nat := [3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 5]
def baseStart_6657242 : Nat := 118140960795 + 6657242 * 2 ^ 59
def prefixEnd_6657242 : Nat := 4983230072969 + 3 ^ 40 * 6657242 * 2
def baseEnd_6657242 : Nat := 3418364979298947743758907

theorem tailTrace_6657242 : CollatzResearch.WordTrace tailWord_6657242 prefixEnd_6657242 3418364979298947743758907 := by
  unfold tailWord_6657242
  simp only [CollatzResearch.WordTrace]
  refine ⟨60702390836989168815047495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161873042231971116840126653 60702390836989168815047495)
  ·
    refine ⟨91053586255483753222571243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60702390836989168815047495 91053586255483753222571243)
    ·
      refine ⟨136580379383225629833856865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91053586255483753222571243 136580379383225629833856865)
      ·
        refine ⟨102435284537419222375392649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136580379383225629833856865 102435284537419222375392649)
        ·
          refine ⟨76826463403064416781544487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102435284537419222375392649 76826463403064416781544487)
          ·
            refine ⟨115239695104596625172316731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76826463403064416781544487 115239695104596625172316731)
            ·
              refine ⟨172859542656894937758475097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115239695104596625172316731 172859542656894937758475097)
              ·
                refine ⟨129644656992671203318856323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172859542656894937758475097 129644656992671203318856323)
                ·
                  refine ⟨194466985489006804978284485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129644656992671203318856323 194466985489006804978284485)
                  ·
                    refine ⟨36462559779188775933428341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 194466985489006804978284485 36462559779188775933428341)
                    ·
                      refine ⟨3418364979298947743758907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36462559779188775933428341 3418364979298947743758907)
                      ·
                        rfl

theorem cell23_6657242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_6657242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6657242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6657242 prefixEnd_6657242 := by exact prefixLift 6657242
  have htrace : WordTrace (prefixWord ++ tailWord_6657242) baseStart_6657242 baseEnd_6657242 := by
    simpa [prefixWord, tailWord_6657242, baseEnd_6657242] using wordTrace_append hprefix tailTrace_6657242
  have hstable : (prefixWord ++ tailWord_6657242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6657242).length < 2 ^ (prefixWord ++ tailWord_6657242).sum := by decide
  have hdescent : baseEnd_6657242 < baseStart_6657242 := by decide
  rcases family_descends (prefixWord ++ tailWord_6657242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6657256 : List Nat := [2, 1, 4, 1, 2, 1, 1, 3, 3, 3, 2]
def baseStart_6657256 : Nat := 118140960795 + 6657256 * 2 ^ 59
def prefixEnd_6657256 : Nat := 4983230072969 + 3 ^ 40 * 6657256 * 2
def baseEnd_6657256 : Nat := 3418372168028110688983843

theorem tailTrace_6657256 : CollatzResearch.WordTrace tailWord_6657256 prefixEnd_6657256 3418372168028110688983843 := by
  unfold tailWord_6657256
  simp only [CollatzResearch.WordTrace]
  refine ⟨121405036984952977825599811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161873382646603970434133081 121405036984952977825599811)
  ·
    refine ⟨182107555477429466738399717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121405036984952977825599811 182107555477429466738399717)
    ·
      refine ⟨34145166652018025013449947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182107555477429466738399717 34145166652018025013449947)
      ·
        refine ⟨51217749978027037520174921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34145166652018025013449947 51217749978027037520174921)
        ·
          refine ⟨38413312483520278140131191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51217749978027037520174921 38413312483520278140131191)
          ·
            refine ⟨57619968725280417210196787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38413312483520278140131191 57619968725280417210196787)
            ·
              refine ⟨86429953087920625815295181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57619968725280417210196787 86429953087920625815295181)
              ·
                refine ⟨32411232407970234680735693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86429953087920625815295181 32411232407970234680735693)
                ·
                  refine ⟨12154212152988838005275885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32411232407970234680735693 12154212152988838005275885)
                  ·
                    refine ⟨4557829557370814251978457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12154212152988838005275885 4557829557370814251978457)
                    ·
                      refine ⟨3418372168028110688983843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4557829557370814251978457 3418372168028110688983843)
                      ·
                        rfl

theorem cell23_6657256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 3, 3, 2].length) (baseStart_6657256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6657256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6657256 prefixEnd_6657256 := by exact prefixLift 6657256
  have htrace : WordTrace (prefixWord ++ tailWord_6657256) baseStart_6657256 baseEnd_6657256 := by
    simpa [prefixWord, tailWord_6657256, baseEnd_6657256] using wordTrace_append hprefix tailTrace_6657256
  have hstable : (prefixWord ++ tailWord_6657256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6657256).length < 2 ^ (prefixWord ++ tailWord_6657256).sum := by decide
  have hdescent : baseEnd_6657256 < baseStart_6657256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6657256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6657343 : List Nat := [1, 1, 2, 2, 4, 3, 3, 2, 5]
def baseStart_6657343 : Nat := 118140960795 + 6657343 * 2 ^ 59
def prefixEnd_6657343 : Nat := 4983230072969 + 3 ^ 40 * 6657343 * 2
def baseEnd_6657343 : Nat := 379824093427227983177327

theorem tailTrace_6657343 : CollatzResearch.WordTrace tailWord_6657343 prefixEnd_6657343 379824093427227983177327 := by
  unfold tailWord_6657343
  simp only [CollatzResearch.WordTrace]
  refine ⟨242813247120590769509616683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161875498080393846339744455 242813247120590769509616683)
  ·
    refine ⟨364219870680886154264425025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242813247120590769509616683 364219870680886154264425025)
    ·
      refine ⟨273164903010664615698318769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364219870680886154264425025 273164903010664615698318769)
      ·
        refine ⟨204873677257998461773739077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273164903010664615698318769 204873677257998461773739077)
        ·
          refine ⟨38413814485874711582576077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 204873677257998461773739077 38413814485874711582576077)
          ·
            refine ⟨14405180432203016843466029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38413814485874711582576077 14405180432203016843466029)
            ·
              refine ⟨5401942662076131316299761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14405180432203016843466029 5401942662076131316299761)
              ·
                refine ⟨4051456996557098487224821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5401942662076131316299761 4051456996557098487224821)
                ·
                  refine ⟨379824093427227983177327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4051456996557098487224821 379824093427227983177327)
                  ·
                    rfl

theorem cell23_6657343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 2, 5].length) (baseStart_6657343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6657343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6657343 prefixEnd_6657343 := by exact prefixLift 6657343
  have htrace : WordTrace (prefixWord ++ tailWord_6657343) baseStart_6657343 baseEnd_6657343 := by
    simpa [prefixWord, tailWord_6657343, baseEnd_6657343] using wordTrace_append hprefix tailTrace_6657343
  have hstable : (prefixWord ++ tailWord_6657343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6657343).length < 2 ^ (prefixWord ++ tailWord_6657343).sum := by decide
  have hdescent : baseEnd_6657343 < baseStart_6657343 := by decide
  rcases family_descends (prefixWord ++ tailWord_6657343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6657376 : List Nat := [2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 4]
def baseStart_6657376 : Nat := 118140960795 + 6657376 * 2 ^ 59
def prefixEnd_6657376 : Nat := 4983230072969 + 3 ^ 40 * 6657376 * 2
def baseEnd_6657376 : Nat := 3418433785706650219483291

theorem tailTrace_6657376 : CollatzResearch.WordTrace tailWord_6657376 prefixEnd_6657376 3418433785706650219483291 := by
  unfold tailWord_6657376
  simp only [CollatzResearch.WordTrace]
  refine ⟨121407225364735608072783991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161876300486314144097045321 121407225364735608072783991)
  ·
    refine ⟨182110838047103412109175987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121407225364735608072783991 182110838047103412109175987)
    ·
      refine ⟨273166257070655118163763981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182110838047103412109175987 273166257070655118163763981)
      ·
        refine ⟨102437346401495669311411493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273166257070655118163763981 102437346401495669311411493)
        ·
          refine ⟨19207002450280437995889655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102437346401495669311411493 19207002450280437995889655)
          ·
            refine ⟨28810503675420656993834483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19207002450280437995889655 28810503675420656993834483)
            ·
              refine ⟨43215755513130985490751725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28810503675420656993834483 43215755513130985490751725)
              ·
                refine ⟨16205908317424119559031897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43215755513130985490751725 16205908317424119559031897)
                ·
                  refine ⟨12154431238068089669273923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16205908317424119559031897 12154431238068089669273923)
                  ·
                    refine ⟨18231646857102134503910885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12154431238068089669273923 18231646857102134503910885)
                    ·
                      refine ⟨3418433785706650219483291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18231646857102134503910885 3418433785706650219483291)
                      ·
                        rfl

theorem cell23_6657376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_6657376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6657376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6657376 prefixEnd_6657376 := by exact prefixLift 6657376
  have htrace : WordTrace (prefixWord ++ tailWord_6657376) baseStart_6657376 baseEnd_6657376 := by
    simpa [prefixWord, tailWord_6657376, baseEnd_6657376] using wordTrace_append hprefix tailTrace_6657376
  have hstable : (prefixWord ++ tailWord_6657376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6657376).length < 2 ^ (prefixWord ++ tailWord_6657376).sum := by decide
  have hdescent : baseEnd_6657376 < baseStart_6657376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6657376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6657403 : List Nat := [1, 1, 1, 1, 1, 6, 3, 4, 1, 4]
def baseStart_6657403 : Nat := 118140960795 + 6657403 * 2 ^ 59
def prefixEnd_6657403 : Nat := 4983230072969 + 3 ^ 40 * 6657403 * 2
def baseEnd_6657403 : Nat := 1139482549894773871281889

theorem tailTrace_6657403 : CollatzResearch.WordTrace tailWord_6657403 prefixEnd_6657403 1139482549894773871281889 := by
  unfold tailWord_6657403
  simp only [CollatzResearch.WordTrace]
  refine ⟨242815435500373399756800863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161876957000248933171200575 242815435500373399756800863)
  ·
    refine ⟨364223153250560099635201295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242815435500373399756800863 364223153250560099635201295)
    ·
      refine ⟨546334729875840149452801943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364223153250560099635201295 546334729875840149452801943)
      ·
        refine ⟨819502094813760224179202915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 546334729875840149452801943 819502094813760224179202915)
        ·
          refine ⟨1229253142220640336268804373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 819502094813760224179202915 1229253142220640336268804373)
          ·
            refine ⟨57621241041592515762600205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1229253142220640336268804373 57621241041592515762600205)
            ·
              refine ⟨21607965390597193410975077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57621241041592515762600205 21607965390597193410975077)
              ·
                refine ⟨4051493510736973764557827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21607965390597193410975077 4051493510736973764557827)
                ·
                  refine ⟨6077240266105460646836741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4051493510736973764557827 6077240266105460646836741)
                  ·
                    refine ⟨1139482549894773871281889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6077240266105460646836741 1139482549894773871281889)
                    ·
                      rfl

theorem cell23_6657403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 4, 1, 4].length) (baseStart_6657403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6657403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6657403 prefixEnd_6657403 := by exact prefixLift 6657403
  have htrace : WordTrace (prefixWord ++ tailWord_6657403) baseStart_6657403 baseEnd_6657403 := by
    simpa [prefixWord, tailWord_6657403, baseEnd_6657403] using wordTrace_append hprefix tailTrace_6657403
  have hstable : (prefixWord ++ tailWord_6657403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6657403).length < 2 ^ (prefixWord ++ tailWord_6657403).sum := by decide
  have hdescent : baseEnd_6657403 < baseStart_6657403 := by decide
  rcases family_descends (prefixWord ++ tailWord_6657403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6657410 : List Nat := [3, 4, 2, 1, 1, 1, 1, 1, 1, 6, 2]
def baseStart_6657410 : Nat := 118140960795 + 6657410 * 2 ^ 59
def prefixEnd_6657410 : Nat := 4983230072969 + 3 ^ 40 * 6657410 * 2
def baseEnd_6657410 : Nat := 3418451244048903086458135

theorem tailTrace_6657410 : CollatzResearch.WordTrace tailWord_6657410 prefixEnd_6657410 3418451244048903086458135 := by
  unfold tailWord_6657410
  simp only [CollatzResearch.WordTrace]
  refine ⟨60703922702837009988076421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161877127207565359968203789 60703922702837009988076421)
  ·
    refine ⟨11381985506781939372764329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60703922702837009988076421 11381985506781939372764329)
    ·
      refine ⟨8536489130086454529573247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11381985506781939372764329 8536489130086454529573247)
      ·
        refine ⟨12804733695129681794359871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8536489130086454529573247 12804733695129681794359871)
        ·
          refine ⟨19207100542694522691539807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12804733695129681794359871 19207100542694522691539807)
          ·
            refine ⟨28810650814041784037309711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19207100542694522691539807 28810650814041784037309711)
            ·
              refine ⟨43215976221062676055964567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28810650814041784037309711 43215976221062676055964567)
              ·
                refine ⟨64823964331594014083946851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43215976221062676055964567 64823964331594014083946851)
                ·
                  refine ⟨97235946497391021125920277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64823964331594014083946851 97235946497391021125920277)
                  ·
                    refine ⟨4557934992065204115277513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 97235946497391021125920277 4557934992065204115277513)
                    ·
                      refine ⟨3418451244048903086458135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4557934992065204115277513 3418451244048903086458135)
                      ·
                        rfl

theorem cell23_6657410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_6657410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6657410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6657410 prefixEnd_6657410 := by exact prefixLift 6657410
  have htrace : WordTrace (prefixWord ++ tailWord_6657410) baseStart_6657410 baseEnd_6657410 := by
    simpa [prefixWord, tailWord_6657410, baseEnd_6657410] using wordTrace_append hprefix tailTrace_6657410
  have hstable : (prefixWord ++ tailWord_6657410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6657410).length < 2 ^ (prefixWord ++ tailWord_6657410).sum := by decide
  have hdescent : baseEnd_6657410 < baseStart_6657410 := by decide
  rcases family_descends (prefixWord ++ tailWord_6657410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6657416 : List Nat := [2, 1, 3, 3, 1, 2, 2, 3, 6]
def baseStart_6657416 : Nat := 118140960795 + 6657416 * 2 ^ 59
def prefixEnd_6657416 : Nat := 4983230072969 + 3 ^ 40 * 6657416 * 2
def baseEnd_6657416 : Nat := 379828258325870006998123

theorem tailTrace_6657416 : CollatzResearch.WordTrace tailWord_6657416 prefixEnd_6657416 379828258325870006998123 := by
  unfold tailWord_6657416
  simp only [CollatzResearch.WordTrace]
  refine ⟨121407954824663151488512051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161877273099550868651349401 121407954824663151488512051)
  ·
    refine ⟨182111932236994727232768077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121407954824663151488512051 182111932236994727232768077)
    ·
      refine ⟨68291974588873022712288029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182111932236994727232768077 68291974588873022712288029)
      ·
        refine ⟨25609490470827383517108011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68291974588873022712288029 25609490470827383517108011)
        ·
          refine ⟨38414235706241075275662017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25609490470827383517108011 38414235706241075275662017)
          ·
            refine ⟨28810676779680806456746513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38414235706241075275662017 28810676779680806456746513)
            ·
              refine ⟨21608007584760604842559885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28810676779680806456746513 21608007584760604842559885)
              ·
                refine ⟨8103002844285226815959957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21608007584760604842559885 8103002844285226815959957)
                ·
                  refine ⟨379828258325870006998123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8103002844285226815959957 379828258325870006998123)
                  ·
                    rfl

theorem cell23_6657416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 3, 6].length) (baseStart_6657416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6657416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6657416 prefixEnd_6657416 := by exact prefixLift 6657416
  have htrace : WordTrace (prefixWord ++ tailWord_6657416) baseStart_6657416 baseEnd_6657416 := by
    simpa [prefixWord, tailWord_6657416, baseEnd_6657416] using wordTrace_append hprefix tailTrace_6657416
  have hstable : (prefixWord ++ tailWord_6657416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6657416).length < 2 ^ (prefixWord ++ tailWord_6657416).sum := by decide
  have hdescent : baseEnd_6657416 < baseStart_6657416 := by decide
  rcases family_descends (prefixWord ++ tailWord_6657416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6657459 : List Nat := [1, 1, 1, 2, 3, 1, 1, 4, 3, 6]
def baseStart_6657459 : Nat := 118140960795 + 6657459 * 2 ^ 59
def prefixEnd_6657459 : Nat := 4983230072969 + 3 ^ 40 * 6657459 * 2
def baseEnd_6657459 : Nat := 1139492134866991131581803

theorem tailTrace_6657459 : CollatzResearch.WordTrace tailWord_6657459 prefixEnd_6657459 1139492134866991131581803 := by
  unfold tailWord_6657459
  simp only [CollatzResearch.WordTrace]
  refine ⟨242817477988170521320839431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161878318658780347547226287 242817477988170521320839431)
  ·
    refine ⟨364226216982255781981259147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242817477988170521320839431 364226216982255781981259147)
    ·
      refine ⟨546339325473383672971888721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364226216982255781981259147 546339325473383672971888721)
      ·
        refine ⟨409754494105037754728916541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 546339325473383672971888721 409754494105037754728916541)
        ·
          refine ⟨153657935289389158023343703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 409754494105037754728916541 153657935289389158023343703)
          ·
            refine ⟨230486902934083737035015555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153657935289389158023343703 230486902934083737035015555)
            ·
              refine ⟨345730354401125605552523333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230486902934083737035015555 345730354401125605552523333)
              ·
                refine ⟨64824441450211051041098125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 345730354401125605552523333 64824441450211051041098125)
                ·
                  refine ⟨24309165543829144140411797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64824441450211051041098125 24309165543829144140411797)
                  ·
                    refine ⟨1139492134866991131581803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24309165543829144140411797 1139492134866991131581803)
                    ·
                      rfl

theorem cell23_6657459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 6].length) (baseStart_6657459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6657459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6657459 prefixEnd_6657459 := by exact prefixLift 6657459
  have htrace : WordTrace (prefixWord ++ tailWord_6657459) baseStart_6657459 baseEnd_6657459 := by
    simpa [prefixWord, tailWord_6657459, baseEnd_6657459] using wordTrace_append hprefix tailTrace_6657459
  have hstable : (prefixWord ++ tailWord_6657459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6657459).length < 2 ^ (prefixWord ++ tailWord_6657459).sum := by decide
  have hdescent : baseEnd_6657459 < baseStart_6657459 := by decide
  rcases family_descends (prefixWord ++ tailWord_6657459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6657494 : List Nat := [5, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3]
def baseStart_6657494 : Nat := 118140960795 + 6657494 * 2 ^ 59
def prefixEnd_6657494 : Nat := 4983230072969 + 3 ^ 40 * 6657494 * 2
def baseEnd_6657494 : Nat := 3418494376423880757807749

theorem tailTrace_6657494 : CollatzResearch.WordTrace tailWord_6657494 prefixEnd_6657494 3418494376423880757807749 := by
  unfold tailWord_6657494
  simp only [CollatzResearch.WordTrace]
  refine ⟨15176172158940232643647721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161879169695362481532242357 15176172158940232643647721)
  ·
    refine ⟨11382129119205174482735791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15176172158940232643647721 11382129119205174482735791)
    ·
      refine ⟨17073193678807761724103687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11382129119205174482735791 17073193678807761724103687)
      ·
        refine ⟨25609790518211642586155531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17073193678807761724103687 25609790518211642586155531)
        ·
          refine ⟨38414685777317463879233297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25609790518211642586155531 38414685777317463879233297)
          ·
            refine ⟨28811014332988097909424973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38414685777317463879233297 28811014332988097909424973)
            ·
              refine ⟨10804130374870536716034365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28811014332988097909424973 10804130374870536716034365)
              ·
                refine ⟨4051548890576451268512887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10804130374870536716034365 4051548890576451268512887)
                ·
                  refine ⟨6077323335864676902769331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4051548890576451268512887 6077323335864676902769331)
                  ·
                    refine ⟨9115985003797015354153997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6077323335864676902769331 9115985003797015354153997)
                    ·
                      refine ⟨3418494376423880757807749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9115985003797015354153997 3418494376423880757807749)
                      ·
                        rfl

theorem cell23_6657494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_6657494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6657494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6657494 prefixEnd_6657494 := by exact prefixLift 6657494
  have htrace : WordTrace (prefixWord ++ tailWord_6657494) baseStart_6657494 baseEnd_6657494 := by
    simpa [prefixWord, tailWord_6657494, baseEnd_6657494] using wordTrace_append hprefix tailTrace_6657494
  have hstable : (prefixWord ++ tailWord_6657494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6657494).length < 2 ^ (prefixWord ++ tailWord_6657494).sum := by decide
  have hdescent : baseEnd_6657494 < baseStart_6657494 := by decide
  rcases family_descends (prefixWord ++ tailWord_6657494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6657496 : List Nat := [2, 1, 2, 2, 2, 1, 2, 4, 1, 2, 4]
def baseStart_6657496 : Nat := 118140960795 + 6657496 * 2 ^ 59
def prefixEnd_6657496 : Nat := 4983230072969 + 3 ^ 40 * 6657496 * 2
def baseEnd_6657496 : Nat := 3418495403385189749982739

theorem tailTrace_6657496 : CollatzResearch.WordTrace tailWord_6657496 prefixEnd_6657496 3418495403385189749982739 := by
  unfold tailWord_6657496
  simp only [CollatzResearch.WordTrace]
  refine ⟨121409413744518238319968171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161879218326024317759957561 121409413744518238319968171)
  ·
    refine ⟨182114120616777357479952257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121409413744518238319968171 182114120616777357479952257)
    ·
      refine ⟨136585590462583018109964193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182114120616777357479952257 136585590462583018109964193)
      ·
        refine ⟨102439192846937263582473145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136585590462583018109964193 102439192846937263582473145)
        ·
          refine ⟨76829394635202947686854859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102439192846937263582473145 76829394635202947686854859)
          ·
            refine ⟨115244091952804421530282289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76829394635202947686854859 115244091952804421530282289)
            ·
              refine ⟨86433068964603316147711717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115244091952804421530282289 86433068964603316147711717)
              ·
                refine ⟨16206200430863121777695947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86433068964603316147711717 16206200430863121777695947)
                ·
                  refine ⟨24309300646294682666543921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16206200430863121777695947 24309300646294682666543921)
                  ·
                    refine ⟨18231975484721011999907941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24309300646294682666543921 18231975484721011999907941)
                    ·
                      refine ⟨3418495403385189749982739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18231975484721011999907941 3418495403385189749982739)
                      ·
                        rfl

theorem cell23_6657496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_6657496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6657496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6657496 prefixEnd_6657496 := by exact prefixLift 6657496
  have htrace : WordTrace (prefixWord ++ tailWord_6657496) baseStart_6657496 baseEnd_6657496 := by
    simpa [prefixWord, tailWord_6657496, baseEnd_6657496] using wordTrace_append hprefix tailTrace_6657496
  have hstable : (prefixWord ++ tailWord_6657496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6657496).length < 2 ^ (prefixWord ++ tailWord_6657496).sum := by decide
  have hdescent : baseEnd_6657496 < baseStart_6657496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6657496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6657503 : List Nat := [1, 1, 2, 3, 3, 1, 1, 5, 1, 2, 3]
def baseStart_6657503 : Nat := 118140960795 + 6657503 * 2 ^ 59
def prefixEnd_6657503 : Nat := 4983230072969 + 3 ^ 40 * 6657503 * 2
def baseEnd_6657503 : Nat := 3418498997749771222595207

theorem tailTrace_6657503 : CollatzResearch.WordTrace tailWord_6657503 prefixEnd_6657503 3418498997749771222595207 := by
  unfold tailWord_6657503
  simp only [CollatzResearch.WordTrace]
  refine ⟨242819082800011116835441163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161879388533340744556960775 242819082800011116835441163)
  ·
    refine ⟨364228624200016675253161745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242819082800011116835441163 364228624200016675253161745)
    ·
      refine ⟨273171468150012506439871309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364228624200016675253161745 273171468150012506439871309)
      ·
        refine ⟨102439300556254689914951741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273171468150012506439871309 102439300556254689914951741)
        ·
          refine ⟨38414737708595508718106903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102439300556254689914951741 38414737708595508718106903)
          ·
            refine ⟨57622106562893263077160355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38414737708595508718106903 57622106562893263077160355)
            ·
              refine ⟨86433159844339894615740533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57622106562893263077160355 86433159844339894615740533)
              ·
                refine ⟨8103108735406865120225675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86433159844339894615740533 8103108735406865120225675)
                ·
                  refine ⟨12154663103110297680338513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8103108735406865120225675 12154663103110297680338513)
                  ·
                    refine ⟨9115997327332723260253885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12154663103110297680338513 9115997327332723260253885)
                    ·
                      refine ⟨3418498997749771222595207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9115997327332723260253885 3418498997749771222595207)
                      ·
                        rfl

theorem cell23_6657503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 5, 1, 2, 3].length) (baseStart_6657503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6657503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6657503 prefixEnd_6657503 := by exact prefixLift 6657503
  have htrace : WordTrace (prefixWord ++ tailWord_6657503) baseStart_6657503 baseEnd_6657503 := by
    simpa [prefixWord, tailWord_6657503, baseEnd_6657503] using wordTrace_append hprefix tailTrace_6657503
  have hstable : (prefixWord ++ tailWord_6657503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6657503).length < 2 ^ (prefixWord ++ tailWord_6657503).sum := by decide
  have hdescent : baseEnd_6657503 < baseStart_6657503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6657503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6657516 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 3]
def baseStart_6657516 : Nat := 118140960795 + 6657516 * 2 ^ 59
def prefixEnd_6657516 : Nat := 4983230072969 + 3 ^ 40 * 6657516 * 2
def baseEnd_6657516 : Nat := 3418505672998279671732647

theorem tailTrace_6657516 : CollatzResearch.WordTrace tailWord_6657516 prefixEnd_6657516 3418505672998279671732647 := by
  unfold tailWord_6657516
  simp only [CollatzResearch.WordTrace]
  refine ⟨121409778474482010027832201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161879704632642680037109601 121409778474482010027832201)
  ·
    refine ⟨91057333855861507520874151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121409778474482010027832201 91057333855861507520874151)
    ·
      refine ⟨136586000783792261281311227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91057333855861507520874151 136586000783792261281311227)
      ·
        refine ⟨204879001175688391921966841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136586000783792261281311227 204879001175688391921966841)
        ·
          refine ⟨153659250881766293941475131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204879001175688391921966841 153659250881766293941475131)
          ·
            refine ⟨230488876322649440912212697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153659250881766293941475131 230488876322649440912212697)
            ·
              refine ⟨172866657241987080684159523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230488876322649440912212697 172866657241987080684159523)
              ·
                refine ⟨259299985862980621026239285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172866657241987080684159523 259299985862980621026239285)
                ·
                  refine ⟨24309373674654433221209933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 259299985862980621026239285 24309373674654433221209933)
                  ·
                    refine ⟨9116015127995412457953725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24309373674654433221209933 9116015127995412457953725)
                    ·
                      refine ⟨3418505672998279671732647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9116015127995412457953725 3418505672998279671732647)
                      ·
                        rfl

theorem cell23_6657516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 3].length) (baseStart_6657516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6657516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6657516 prefixEnd_6657516 := by exact prefixLift 6657516
  have htrace : WordTrace (prefixWord ++ tailWord_6657516) baseStart_6657516 baseEnd_6657516 := by
    simpa [prefixWord, tailWord_6657516, baseEnd_6657516] using wordTrace_append hprefix tailTrace_6657516
  have hstable : (prefixWord ++ tailWord_6657516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6657516).length < 2 ^ (prefixWord ++ tailWord_6657516).sum := by decide
  have hdescent : baseEnd_6657516 < baseStart_6657516 := by decide
  rcases family_descends (prefixWord ++ tailWord_6657516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6657534 : List Nat := [4, 2, 2, 3, 1, 2, 1, 2, 1, 1, 4]
def baseStart_6657534 : Nat := 118140960795 + 6657534 * 2 ^ 59
def prefixEnd_6657534 : Nat := 4983230072969 + 3 ^ 40 * 6657534 * 2
def baseEnd_6657534 : Nat := 3418514915650060601307565

theorem tailTrace_6657534 : CollatzResearch.WordTrace tailWord_6657534 prefixEnd_6657534 3418514915650060601307565 := by
  unfold tailWord_6657534
  simp only [CollatzResearch.WordTrace]
  refine ⟨30352526682862351141227457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161880142308599206086546437 30352526682862351141227457)
  ·
    refine ⟨22764395012146763355920593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30352526682862351141227457 22764395012146763355920593)
    ·
      refine ⟨17073296259110072516940445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22764395012146763355920593 17073296259110072516940445)
      ·
        refine ⟨6402486097166277193852667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17073296259110072516940445 6402486097166277193852667)
        ·
          refine ⟨9603729145749415790779001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6402486097166277193852667 9603729145749415790779001)
          ·
            refine ⟨7202796859312061843084251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9603729145749415790779001 7202796859312061843084251)
            ·
              refine ⟨10804195288968092764626377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7202796859312061843084251 10804195288968092764626377)
              ·
                refine ⟨8103146466726069573469783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10804195288968092764626377 8103146466726069573469783)
                ·
                  refine ⟨12154719700089104360204675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8103146466726069573469783 12154719700089104360204675)
                  ·
                    refine ⟨18232079550133656540307013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12154719700089104360204675 18232079550133656540307013)
                    ·
                      refine ⟨3418514915650060601307565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18232079550133656540307013 3418514915650060601307565)
                      ·
                        rfl

theorem cell23_6657534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_6657534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6657534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6657534 prefixEnd_6657534 := by exact prefixLift 6657534
  have htrace : WordTrace (prefixWord ++ tailWord_6657534) baseStart_6657534 baseEnd_6657534 := by
    simpa [prefixWord, tailWord_6657534, baseEnd_6657534] using wordTrace_append hprefix tailTrace_6657534
  have hstable : (prefixWord ++ tailWord_6657534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6657534).length < 2 ^ (prefixWord ++ tailWord_6657534).sum := by decide
  have hdescent : baseEnd_6657534 < baseStart_6657534 := by decide
  rcases family_descends (prefixWord ++ tailWord_6657534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6657537 : List Nat := [1, 2, 4, 1, 4, 2, 1, 2, 1, 2, 3]
def baseStart_6657537 : Nat := 118140960795 + 6657537 * 2 ^ 59
def prefixEnd_6657537 : Nat := 4983230072969 + 3 ^ 40 * 6657537 * 2
def baseEnd_6657537 : Nat := 3418516456092024089570051

theorem tailTrace_6657537 : CollatzResearch.WordTrace tailWord_6657537 prefixEnd_6657537 3418516456092024089570051 := by
  unfold tailWord_6657537
  simp only [CollatzResearch.WordTrace]
  refine ⟨242820322881887940642178865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161880215254591960428119243 242820322881887940642178865)
  ·
    refine ⟨182115242161415955481634149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242820322881887940642178865 182115242161415955481634149)
    ·
      refine ⟨34146607905265491652806403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182115242161415955481634149 34146607905265491652806403)
      ·
        refine ⟨51219911857898237479209605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34146607905265491652806403 51219911857898237479209605)
        ·
          refine ⟨9603733473355919527351801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51219911857898237479209605 9603733473355919527351801)
          ·
            refine ⟨7202800105016939645513851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9603733473355919527351801 7202800105016939645513851)
            ·
              refine ⟨10804200157525409468270777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7202800105016939645513851 10804200157525409468270777)
              ·
                refine ⟨8103150118144057101203083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10804200157525409468270777 8103150118144057101203083)
                ·
                  refine ⟨12154725177216085651804625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8103150118144057101203083 12154725177216085651804625)
                  ·
                    refine ⟨9116043882912064238853469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12154725177216085651804625 9116043882912064238853469)
                    ·
                      refine ⟨3418516456092024089570051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9116043882912064238853469 3418516456092024089570051)
                      ·
                        rfl

theorem cell23_6657537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_6657537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6657537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6657537 prefixEnd_6657537 := by exact prefixLift 6657537
  have htrace : WordTrace (prefixWord ++ tailWord_6657537) baseStart_6657537 baseEnd_6657537 := by
    simpa [prefixWord, tailWord_6657537, baseEnd_6657537] using wordTrace_append hprefix tailTrace_6657537
  have hstable : (prefixWord ++ tailWord_6657537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6657537).length < 2 ^ (prefixWord ++ tailWord_6657537).sum := by decide
  have hdescent : baseEnd_6657537 < baseStart_6657537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6657537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6657550 : List Nat := [4, 1, 1, 2, 4, 1, 1, 2, 1, 3, 3]
def baseStart_6657550 : Nat := 118140960795 + 6657550 * 2 ^ 59
def prefixEnd_6657550 : Nat := 4983230072969 + 3 ^ 40 * 6657550 * 2
def baseEnd_6657550 : Nat := 3418523131340532538707491

theorem tailTrace_6657550 : CollatzResearch.WordTrace tailWord_6657550 prefixEnd_6657550 3418523131340532538707491 := by
  unfold tailWord_6657550
  simp only [CollatzResearch.WordTrace]
  refine ⟨30352599628855105482800263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161880531353893895908268069 30352599628855105482800263)
  ·
    refine ⟨45528899443282658224200395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30352599628855105482800263 45528899443282658224200395)
    ·
      refine ⟨68293349164923987336300593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45528899443282658224200395 68293349164923987336300593)
      ·
        refine ⟨51220011873692990502225445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68293349164923987336300593 51220011873692990502225445)
        ·
          refine ⟨9603752226317435719167271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51220011873692990502225445 9603752226317435719167271)
          ·
            refine ⟨14405628339476153578750907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9603752226317435719167271 14405628339476153578750907)
            ·
              refine ⟨21608442509214230368126361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14405628339476153578750907 21608442509214230368126361)
              ·
                refine ⟨16206331881910672776094771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21608442509214230368126361 16206331881910672776094771)
                ·
                  refine ⟨24309497822866009164142157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16206331881910672776094771 24309497822866009164142157)
                  ·
                    refine ⟨9116061683574753436553309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24309497822866009164142157 9116061683574753436553309)
                    ·
                      refine ⟨3418523131340532538707491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9116061683574753436553309 3418523131340532538707491)
                      ·
                        rfl

theorem cell23_6657550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_6657550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6657550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6657550 prefixEnd_6657550 := by exact prefixLift 6657550
  have htrace : WordTrace (prefixWord ++ tailWord_6657550) baseStart_6657550 baseEnd_6657550 := by
    simpa [prefixWord, tailWord_6657550, baseEnd_6657550] using wordTrace_append hprefix tailTrace_6657550
  have hstable : (prefixWord ++ tailWord_6657550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6657550).length < 2 ^ (prefixWord ++ tailWord_6657550).sum := by decide
  have hdescent : baseEnd_6657550 < baseStart_6657550 := by decide
  rcases family_descends (prefixWord ++ tailWord_6657550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6657573 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 5, 4, 2]
def baseStart_6657573 : Nat := 118140960795 + 6657573 * 2 ^ 59
def prefixEnd_6657573 : Nat := 4983230072969 + 3 ^ 40 * 6657573 * 2
def baseEnd_6657573 : Nat := 3418534941395585948719885

theorem tailTrace_6657573 : CollatzResearch.WordTrace tailWord_6657573 prefixEnd_6657573 3418534941395585948719885 := by
  unfold tailWord_6657573
  simp only [CollatzResearch.WordTrace]
  refine ⟨242821635909757518790489373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161881090606505012526992915 242821635909757518790489373)
  ·
    refine ⟨91058113466159069546433515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242821635909757518790489373 91058113466159069546433515)
    ·
      refine ⟨136587170199238604319650273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91058113466159069546433515 136587170199238604319650273)
      ·
        refine ⟨102440377649428953239737705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136587170199238604319650273 102440377649428953239737705)
        ·
          refine ⟨76830283237071714929803279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102440377649428953239737705 76830283237071714929803279)
          ·
            refine ⟨115245424855607572394704919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76830283237071714929803279 115245424855607572394704919)
            ·
              refine ⟨172868137283411358592057379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115245424855607572394704919 172868137283411358592057379)
              ·
                refine ⟨259302205925117037888086069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172868137283411358592057379 259302205925117037888086069)
                ·
                  refine ⟨24309581805479722302008069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 259302205925117037888086069 24309581805479722302008069)
                  ·
                    refine ⟨4558046588527447931626513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24309581805479722302008069 4558046588527447931626513)
                    ·
                      refine ⟨3418534941395585948719885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4558046588527447931626513 3418534941395585948719885)
                      ·
                        rfl

theorem cell23_6657573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 4, 2].length) (baseStart_6657573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6657573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6657573 prefixEnd_6657573 := by exact prefixLift 6657573
  have htrace : WordTrace (prefixWord ++ tailWord_6657573) baseStart_6657573 baseEnd_6657573 := by
    simpa [prefixWord, tailWord_6657573, baseEnd_6657573] using wordTrace_append hprefix tailTrace_6657573
  have hstable : (prefixWord ++ tailWord_6657573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6657573).length < 2 ^ (prefixWord ++ tailWord_6657573).sum := by decide
  have hdescent : baseEnd_6657573 < baseStart_6657573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6657573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
