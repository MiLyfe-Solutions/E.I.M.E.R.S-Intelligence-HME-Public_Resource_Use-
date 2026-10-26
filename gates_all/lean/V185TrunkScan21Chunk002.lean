import V185TrunkScan21Chunk001

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_25562 : List Nat := [3, 1, 1, 2, 4, 2, 3, 2, 3]
def baseStart_25562 : Nat := 118140960795 + 25562 * 2 ^ 59
def prefixEnd_25562 : Nat := 4983230072969 + 3 ^ 40 * 25562 * 2
def baseEnd_25562 : Nat := 5833596662370765447755

theorem tailTrace_25562 : CollatzResearch.WordTrace tailWord_25562 prefixEnd_25562 5833596662370765447755 := by
  unfold tailWord_25562
  simp only [CollatzResearch.WordTrace]
  refine ⟨233080683350178621785735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 621548488933809658095293 233080683350178621785735)
  ·
    refine ⟨349621025025267932678603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 233080683350178621785735 349621025025267932678603)
    ·
      refine ⟨524431537537901899017905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349621025025267932678603 524431537537901899017905)
      ·
        refine ⟨393323653153426424263429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 524431537537901899017905 393323653153426424263429)
        ·
          refine ⟨73748184966267454549393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 393323653153426424263429 73748184966267454549393)
          ·
            refine ⟨55311138724700590912045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73748184966267454549393 55311138724700590912045)
            ·
              refine ⟨20741677021762721592017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55311138724700590912045 20741677021762721592017)
              ·
                refine ⟨15556257766322041194013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20741677021762721592017 15556257766322041194013)
                ·
                  refine ⟨5833596662370765447755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15556257766322041194013 5833596662370765447755)
                  ·
                    rfl

theorem cell21_25562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 2, 3].length) (baseStart_25562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_25562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_25562 prefixEnd_25562 := by exact prefixLift 25562
  have htrace : WordTrace (prefixWord ++ tailWord_25562) baseStart_25562 baseEnd_25562 := by
    simpa [prefixWord, tailWord_25562, baseEnd_25562] using wordTrace_append hprefix tailTrace_25562
  have hstable : (prefixWord ++ tailWord_25562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25562).length < 2 ^ (prefixWord ++ tailWord_25562).sum := by decide
  have hdescent : baseEnd_25562 < baseStart_25562 := by decide
  rcases family_descends (prefixWord ++ tailWord_25562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25621 : List Nat := [1, 3, 2, 1, 4, 2, 1, 4, 3]
def baseStart_25621 : Nat := 118140960795 + 25621 * 2 ^ 59
def prefixEnd_25621 : Nat := 4983230072969 + 3 ^ 40 * 25621 * 2
def baseEnd_25621 : Nat := 5847061266199773964301

theorem tailTrace_25621 : CollatzResearch.WordTrace tailWord_25621 prefixEnd_25621 5847061266199773964301 := by
  unfold tailWord_25621
  simp only [CollatzResearch.WordTrace]
  refine ⟨934474640186967563540717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 622983093457978375693811 934474640186967563540717)
  ·
    refine ⟨350427990070112836327769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 934474640186967563540717 350427990070112836327769)
    ·
      refine ⟨262820992552584627245827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 350427990070112836327769 262820992552584627245827)
      ·
        refine ⟨394231488828876940868741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262820992552584627245827 394231488828876940868741)
        ·
          refine ⟨73918404155414426412889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 394231488828876940868741 73918404155414426412889)
          ·
            refine ⟨55438803116560819809667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73918404155414426412889 55438803116560819809667)
            ·
              refine ⟨83158204674841229714501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55438803116560819809667 83158204674841229714501)
              ·
                refine ⟨15592163376532730571469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83158204674841229714501 15592163376532730571469)
                ·
                  refine ⟨5847061266199773964301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15592163376532730571469 5847061266199773964301)
                  ·
                    rfl

theorem cell21_25621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 4, 3].length) (baseStart_25621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_25621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_25621 prefixEnd_25621 := by exact prefixLift 25621
  have htrace : WordTrace (prefixWord ++ tailWord_25621) baseStart_25621 baseEnd_25621 := by
    simpa [prefixWord, tailWord_25621, baseEnd_25621] using wordTrace_append hprefix tailTrace_25621
  have hstable : (prefixWord ++ tailWord_25621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25621).length < 2 ^ (prefixWord ++ tailWord_25621).sum := by decide
  have hdescent : baseEnd_25621 < baseStart_25621 := by decide
  rcases family_descends (prefixWord ++ tailWord_25621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25649 : List Nat := [1, 2, 2, 3, 1, 2, 5, 5]
def baseStart_25649 : Nat := 118140960795 + 25649 * 2 ^ 59
def prefixEnd_25649 : Nat := 4983230072969 + 3 ^ 40 * 25649 * 2
def baseEnd_25649 : Nat := 1951150415892649165859

theorem tailTrace_25649 : CollatzResearch.WordTrace tailWord_25649 prefixEnd_25649 1951150415892649165859 := by
  unfold tailWord_25649
  simp only [CollatzResearch.WordTrace]
  refine ⟨935495884085528345560001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 623663922723685563706667 935495884085528345560001)
  ·
    refine ⟨701621913064146259170001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 935495884085528345560001 701621913064146259170001)
    ·
      refine ⟨526216434798109694377501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 701621913064146259170001 526216434798109694377501)
      ·
        refine ⟨197331163049291135391563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 526216434798109694377501 197331163049291135391563)
        ·
          refine ⟨295996744573936703087345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197331163049291135391563 295996744573936703087345)
          ·
            refine ⟨221997558430452527315509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295996744573936703087345 221997558430452527315509)
            ·
              refine ⟨20812271102854924435829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 221997558430452527315509 20812271102854924435829)
              ·
                refine ⟨1951150415892649165859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20812271102854924435829 1951150415892649165859)
                ·
                  rfl

theorem cell21_25649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 5].length) (baseStart_25649 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_25649 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_25649 prefixEnd_25649 := by exact prefixLift 25649
  have htrace : WordTrace (prefixWord ++ tailWord_25649) baseStart_25649 baseEnd_25649 := by
    simpa [prefixWord, tailWord_25649, baseEnd_25649] using wordTrace_append hprefix tailTrace_25649
  have hstable : (prefixWord ++ tailWord_25649).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25649).length < 2 ^ (prefixWord ++ tailWord_25649).sum := by decide
  have hdescent : baseEnd_25649 < baseStart_25649 := by decide
  rcases family_descends (prefixWord ++ tailWord_25649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25686 : List Nat := [5, 2, 2, 1, 2, 1, 3, 1, 4]
def baseStart_25686 : Nat := 118140960795 + 25686 * 2 ^ 59
def prefixEnd_25686 : Nat := 4983230072969 + 3 ^ 40 * 25686 * 2
def baseEnd_25686 : Nat := 5861895151774105380835

theorem tailTrace_25686 : CollatzResearch.WordTrace tailWord_25686 prefixEnd_25686 5861895151774105380835 := by
  unfold tailWord_25686
  simp only [CollatzResearch.WordTrace]
  refine ⟨58552836559467729041057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 624563589967655776437941 58552836559467729041057)
  ·
    refine ⟨43914627419600796780793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58552836559467729041057 43914627419600796780793)
    ·
      refine ⟨32935970564700597585595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43914627419600796780793 32935970564700597585595)
      ·
        refine ⟨49403955847050896378393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32935970564700597585595 49403955847050896378393)
        ·
          refine ⟨37052966885288172283795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49403955847050896378393 37052966885288172283795)
          ·
            refine ⟨55579450327932258425693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37052966885288172283795 55579450327932258425693)
            ·
              refine ⟨20842293872974596909635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55579450327932258425693 20842293872974596909635)
              ·
                refine ⟨31263440809461895364453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20842293872974596909635 31263440809461895364453)
                ·
                  refine ⟨5861895151774105380835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31263440809461895364453 5861895151774105380835)
                  ·
                    rfl

theorem cell21_25686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_25686 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_25686 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_25686 prefixEnd_25686 := by exact prefixLift 25686
  have htrace : WordTrace (prefixWord ++ tailWord_25686) baseStart_25686 baseEnd_25686 := by
    simpa [prefixWord, tailWord_25686, baseEnd_25686] using wordTrace_append hprefix tailTrace_25686
  have hstable : (prefixWord ++ tailWord_25686).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25686).length < 2 ^ (prefixWord ++ tailWord_25686).sum := by decide
  have hdescent : baseEnd_25686 < baseStart_25686 := by decide
  rcases family_descends (prefixWord ++ tailWord_25686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25708 : List Nat := [2, 2, 1, 1, 3, 2, 3, 7]
def baseStart_25708 : Nat := 118140960795 + 25708 * 2 ^ 59
def prefixEnd_25708 : Nat := 4983230072969 + 3 ^ 40 * 25708 * 2
def baseEnd_25708 : Nat := 1955638617168985338041

theorem tailTrace_25708 : CollatzResearch.WordTrace tailWord_25708 prefixEnd_25708 1955638617168985338041 := by
  unfold tailWord_25708
  simp only [CollatzResearch.WordTrace]
  refine ⟨468823895435890710978889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 625098527247854281305185 468823895435890710978889)
  ·
    refine ⟨351617921576918033234167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 468823895435890710978889 351617921576918033234167)
    ·
      refine ⟨527426882365377049851251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351617921576918033234167 527426882365377049851251)
      ·
        refine ⟨791140323548065574776877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 527426882365377049851251 791140323548065574776877)
        ·
          refine ⟨296677621330524590541329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 791140323548065574776877 296677621330524590541329)
          ·
            refine ⟨222508215997893442905997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 296677621330524590541329 222508215997893442905997)
            ·
              refine ⟨83440580999210041089749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 222508215997893442905997 83440580999210041089749)
              ·
                refine ⟨1955638617168985338041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 83440580999210041089749 1955638617168985338041)
                ·
                  rfl

theorem cell21_25708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 7].length) (baseStart_25708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_25708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_25708 prefixEnd_25708 := by exact prefixLift 25708
  have htrace : WordTrace (prefixWord ++ tailWord_25708) baseStart_25708 baseEnd_25708 := by
    simpa [prefixWord, tailWord_25708, baseEnd_25708] using wordTrace_append hprefix tailTrace_25708
  have hstable : (prefixWord ++ tailWord_25708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25708).length < 2 ^ (prefixWord ++ tailWord_25708).sum := by decide
  have hdescent : baseEnd_25708 < baseStart_25708 := by decide
  rcases family_descends (prefixWord ++ tailWord_25708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25790 : List Nat := [4, 2, 1, 1, 3, 1, 4, 2, 3]
def baseStart_25790 : Nat := 118140960795 + 25790 * 2 ^ 59
def prefixEnd_25790 : Nat := 4983230072969 + 3 ^ 40 * 25790 * 2
def baseEnd_25790 : Nat := 5885629368693035647289

theorem tailTrace_25790 : CollatzResearch.WordTrace tailWord_25790 prefixEnd_25790 5885629368693035647289 := by
  unfold tailWord_25790
  simp only [CollatzResearch.WordTrace]
  refine ⟨117579822071838678305353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 627092384383139617628549 117579822071838678305353)
  ·
    refine ⟨88184866553879008729015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117579822071838678305353 88184866553879008729015)
    ·
      refine ⟨132277299830818513093523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88184866553879008729015 132277299830818513093523)
      ·
        refine ⟨198415949746227769640285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132277299830818513093523 198415949746227769640285)
        ·
          refine ⟨74405981154835413615107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198415949746227769640285 74405981154835413615107)
          ·
            refine ⟨111608971732253120422661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74405981154835413615107 111608971732253120422661)
            ·
              refine ⟨20926682199797460079249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111608971732253120422661 20926682199797460079249)
              ·
                refine ⟨15695011649848095059437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20926682199797460079249 15695011649848095059437)
                ·
                  refine ⟨5885629368693035647289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15695011649848095059437 5885629368693035647289)
                  ·
                    rfl

theorem cell21_25790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_25790 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_25790 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_25790 prefixEnd_25790 := by exact prefixLift 25790
  have htrace : WordTrace (prefixWord ++ tailWord_25790) baseStart_25790 baseEnd_25790 := by
    simpa [prefixWord, tailWord_25790, baseEnd_25790] using wordTrace_append hprefix tailTrace_25790
  have hstable : (prefixWord ++ tailWord_25790).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25790).length < 2 ^ (prefixWord ++ tailWord_25790).sum := by decide
  have hdescent : baseEnd_25790 < baseStart_25790 := by decide
  rcases family_descends (prefixWord ++ tailWord_25790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_25959 : List Nat := [1, 1, 5, 1, 5, 1, 2, 2, 3]
def baseStart_25959 : Nat := 118140960795 + 25959 * 2 ^ 59
def prefixEnd_25959 : Nat := 4983230072969 + 3 ^ 40 * 25959 * 2
def baseEnd_25959 : Nat := 5924197471186297330277

theorem tailTrace_25959 : CollatzResearch.WordTrace tailWord_25959 prefixEnd_25959 5924197471186297330277 := by
  unfold tailWord_25959
  simp only [CollatzResearch.WordTrace]
  refine ⟨946802512962451289344931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 631201675308300859563287 946802512962451289344931)
  ·
    refine ⟨1420203769443676934017397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 946802512962451289344931 1420203769443676934017397)
    ·
      refine ⟨133144103385344712564131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1420203769443676934017397 133144103385344712564131)
      ·
        refine ⟨199716155078017068846197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133144103385344712564131 199716155078017068846197)
        ·
          refine ⟨18723389538564100204331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 199716155078017068846197 18723389538564100204331)
          ·
            refine ⟨28085084307846150306497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18723389538564100204331 28085084307846150306497)
            ·
              refine ⟨21063813230884612729873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28085084307846150306497 21063813230884612729873)
              ·
                refine ⟨15797859923163459547405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21063813230884612729873 15797859923163459547405)
                ·
                  refine ⟨5924197471186297330277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15797859923163459547405 5924197471186297330277)
                  ·
                    rfl

theorem cell21_25959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 2, 3].length) (baseStart_25959 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_25959 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_25959 prefixEnd_25959 := by exact prefixLift 25959
  have htrace : WordTrace (prefixWord ++ tailWord_25959) baseStart_25959 baseEnd_25959 := by
    simpa [prefixWord, tailWord_25959, baseEnd_25959] using wordTrace_append hprefix tailTrace_25959
  have hstable : (prefixWord ++ tailWord_25959).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_25959).length < 2 ^ (prefixWord ++ tailWord_25959).sum := by decide
  have hdescent : baseEnd_25959 < baseStart_25959 := by decide
  rcases family_descends (prefixWord ++ tailWord_25959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26015 : List Nat := [1, 1, 2, 5, 1, 4, 1, 2, 4]
def baseStart_26015 : Nat := 118140960795 + 26015 * 2 ^ 59
def prefixEnd_26015 : Nat := 4983230072969 + 3 ^ 40 * 26015 * 2
def baseEnd_26015 : Nat := 5936977434142644396829

theorem tailTrace_26015 : CollatzResearch.WordTrace tailWord_26015 prefixEnd_26015 5936977434142644396829 := by
  unfold tailWord_26015
  simp only [CollatzResearch.WordTrace]
  refine ⟨948845000759572853383499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 632563333839715235588999 948845000759572853383499)
  ·
    refine ⟨1423267501139359280075249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 948845000759572853383499 1423267501139359280075249)
    ·
      refine ⟨1067450625854519460056437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1423267501139359280075249 1067450625854519460056437)
      ·
        refine ⟨100073496173861199380291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1067450625854519460056437 100073496173861199380291)
        ·
          refine ⟨150110244260791799070437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100073496173861199380291 150110244260791799070437)
          ·
            refine ⟨28145670798898462325707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150110244260791799070437 28145670798898462325707)
            ·
              refine ⟨42218506198347693488561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28145670798898462325707 42218506198347693488561)
              ·
                refine ⟨31663879648760770116421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42218506198347693488561 31663879648760770116421)
                ·
                  refine ⟨5936977434142644396829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31663879648760770116421 5936977434142644396829)
                  ·
                    rfl

theorem cell21_26015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 2, 4].length) (baseStart_26015 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_26015 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_26015 prefixEnd_26015 := by exact prefixLift 26015
  have htrace : WordTrace (prefixWord ++ tailWord_26015) baseStart_26015 baseEnd_26015 := by
    simpa [prefixWord, tailWord_26015, baseEnd_26015] using wordTrace_append hprefix tailTrace_26015
  have hstable : (prefixWord ++ tailWord_26015).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26015).length < 2 ^ (prefixWord ++ tailWord_26015).sum := by decide
  have hdescent : baseEnd_26015 < baseStart_26015 := by decide
  rcases family_descends (prefixWord ++ tailWord_26015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26088 : List Nat := [2, 1, 4, 1, 1, 2, 4, 6]
def baseStart_26088 : Nat := 118140960795 + 26088 * 2 ^ 59
def prefixEnd_26088 : Nat := 4983230072969 + 3 ^ 40 * 26088 * 2
def baseEnd_26088 : Nat := 1984545676236913226671

theorem tailTrace_26088 : CollatzResearch.WordTrace tailWord_26088 prefixEnd_26088 1984545676236913226671 := by
  unfold tailWord_26088
  simp only [CollatzResearch.WordTrace]
  refine ⟨475753764747553160395459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 634338352996737547193945 475753764747553160395459)
  ·
    refine ⟨713630647121329740593189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 475753764747553160395459 713630647121329740593189)
    ·
      refine ⟨133805746335249326361223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 713630647121329740593189 133805746335249326361223)
      ·
        refine ⟨200708619502873989541835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133805746335249326361223 200708619502873989541835)
        ·
          refine ⟨301062929254310984312753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200708619502873989541835 301062929254310984312753)
          ·
            refine ⟨225797196940733238234565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 301062929254310984312753 225797196940733238234565)
            ·
              refine ⟨42336974426387482168981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 225797196940733238234565 42336974426387482168981)
              ·
                refine ⟨1984545676236913226671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42336974426387482168981 1984545676236913226671)
                ·
                  rfl

theorem cell21_26088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 6].length) (baseStart_26088 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_26088 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_26088 prefixEnd_26088 := by exact prefixLift 26088
  have htrace : WordTrace (prefixWord ++ tailWord_26088) baseStart_26088 baseEnd_26088 := by
    simpa [prefixWord, tailWord_26088, baseEnd_26088] using wordTrace_append hprefix tailTrace_26088
  have hstable : (prefixWord ++ tailWord_26088).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26088).length < 2 ^ (prefixWord ++ tailWord_26088).sum := by decide
  have hdescent : baseEnd_26088 < baseStart_26088 := by decide
  rcases family_descends (prefixWord ++ tailWord_26088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26125 : List Nat := [1, 7, 1, 1, 2, 1, 2, 2, 4]
def baseStart_26125 : Nat := 118140960795 + 26125 * 2 ^ 59
def prefixEnd_26125 : Nat := 4983230072969 + 3 ^ 40 * 26125 * 2
def baseEnd_26125 : Nat := 5962080932806897563271

theorem tailTrace_26125 : CollatzResearch.WordTrace tailWord_26125 prefixEnd_26125 5962080932806897563271 := by
  unfold tailWord_26125
  simp only [CollatzResearch.WordTrace]
  refine ⟨952857030361061639887829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 635238020240707759925219 952857030361061639887829)
  ·
    refine ⟨22332586649087382184871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 952857030361061639887829 22332586649087382184871)
    ·
      refine ⟨33498879973631073277307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22332586649087382184871 33498879973631073277307)
      ·
        refine ⟨50248319960446609915961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33498879973631073277307 50248319960446609915961)
        ·
          refine ⟨37686239970334957436971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50248319960446609915961 37686239970334957436971)
          ·
            refine ⟨56529359955502436155457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37686239970334957436971 56529359955502436155457)
            ·
              refine ⟨42397019966626827116593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56529359955502436155457 42397019966626827116593)
              ·
                refine ⟨31797764974970120337445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42397019966626827116593 31797764974970120337445)
                ·
                  refine ⟨5962080932806897563271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31797764974970120337445 5962080932806897563271)
                  ·
                    rfl

theorem cell21_26125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_26125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_26125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_26125 prefixEnd_26125 := by exact prefixLift 26125
  have htrace : WordTrace (prefixWord ++ tailWord_26125) baseStart_26125 baseEnd_26125 := by
    simpa [prefixWord, tailWord_26125, baseEnd_26125] using wordTrace_append hprefix tailTrace_26125
  have hstable : (prefixWord ++ tailWord_26125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26125).length < 2 ^ (prefixWord ++ tailWord_26125).sum := by decide
  have hdescent : baseEnd_26125 < baseStart_26125 := by decide
  rcases family_descends (prefixWord ++ tailWord_26125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26229 : List Nat := [1, 3, 4, 2, 1, 1, 3, 3, 3]
def baseStart_26229 : Nat := 118140960795 + 26229 * 2 ^ 59
def prefixEnd_26229 : Nat := 4983230072969 + 3 ^ 40 * 26229 * 2
def baseEnd_26229 : Nat := 5985815149725827829725

theorem tailTrace_26229 : CollatzResearch.WordTrace tailWord_26229 prefixEnd_26229 5985815149725827829725 := by
  unfold tailWord_26229
  simp only [CollatzResearch.WordTrace]
  refine ⟨956650221984287401673741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 637766814656191601115827 956650221984287401673741)
  ·
    refine ⟨358743833244107775627653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 956650221984287401673741 358743833244107775627653)
    ·
      refine ⟨67264468733270207930185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 358743833244107775627653 67264468733270207930185)
      ·
        refine ⟨50448351549952655947639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67264468733270207930185 50448351549952655947639)
        ·
          refine ⟨75672527324928983921459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50448351549952655947639 75672527324928983921459)
          ·
            refine ⟨113508790987393475882189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75672527324928983921459 113508790987393475882189)
            ·
              refine ⟨42565796620272553455821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113508790987393475882189 42565796620272553455821)
              ·
                refine ⟨15962173732602207545933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42565796620272553455821 15962173732602207545933)
                ·
                  refine ⟨5985815149725827829725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15962173732602207545933 5985815149725827829725)
                  ·
                    rfl

theorem cell21_26229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 3, 3].length) (baseStart_26229 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_26229 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_26229 prefixEnd_26229 := by exact prefixLift 26229
  have htrace : WordTrace (prefixWord ++ tailWord_26229) baseStart_26229 baseEnd_26229 := by
    simpa [prefixWord, tailWord_26229, baseEnd_26229] using wordTrace_append hprefix tailTrace_26229
  have hstable : (prefixWord ++ tailWord_26229).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26229).length < 2 ^ (prefixWord ++ tailWord_26229).sum := by decide
  have hdescent : baseEnd_26229 < baseStart_26229 := by decide
  rcases family_descends (prefixWord ++ tailWord_26229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26302 : List Nat := [4, 2, 1, 1, 2, 2, 1, 4, 4]
def baseStart_26302 : Nat := 118140960795 + 26302 * 2 ^ 59
def prefixEnd_26302 : Nat := 4983230072969 + 3 ^ 40 * 26302 * 2
def baseEnd_26302 : Nat := 6002474744293923112909

theorem tailTrace_26302 : CollatzResearch.WordTrace tailWord_26302 prefixEnd_26302 6002474744293923112909 := by
  unfold tailWord_26302
  simp only [CollatzResearch.WordTrace]
  refine ⟨119914093839977608635145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 639541833813213912720773 119914093839977608635145)
  ·
    refine ⟨89935570379983206476359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119914093839977608635145 89935570379983206476359)
    ·
      refine ⟨134903355569974809714539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89935570379983206476359 134903355569974809714539)
      ·
        refine ⟨202355033354962214571809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134903355569974809714539 202355033354962214571809)
        ·
          refine ⟨151766275016221660928857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202355033354962214571809 151766275016221660928857)
          ·
            refine ⟨113824706262166245696643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151766275016221660928857 113824706262166245696643)
            ·
              refine ⟨170737059393249368544965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113824706262166245696643 170737059393249368544965)
              ·
                refine ⟨32013198636234256602181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 170737059393249368544965 32013198636234256602181)
                ·
                  refine ⟨6002474744293923112909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32013198636234256602181 6002474744293923112909)
                  ·
                    rfl

theorem cell21_26302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_26302 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_26302 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_26302 prefixEnd_26302 := by exact prefixLift 26302
  have htrace : WordTrace (prefixWord ++ tailWord_26302) baseStart_26302 baseEnd_26302 := by
    simpa [prefixWord, tailWord_26302, baseEnd_26302] using wordTrace_append hprefix tailTrace_26302
  have hstable : (prefixWord ++ tailWord_26302).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26302).length < 2 ^ (prefixWord ++ tailWord_26302).sum := by decide
  have hdescent : baseEnd_26302 < baseStart_26302 := by decide
  rcases family_descends (prefixWord ++ tailWord_26302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26330 : List Nat := [3, 1, 1, 2, 2, 3, 1, 1, 7]
def baseStart_26330 : Nat := 118140960795 + 26330 * 2 ^ 59
def prefixEnd_26330 : Nat := 4983230072969 + 3 ^ 40 * 26330 * 2
def baseEnd_26330 : Nat := 6008864725772096646185

theorem tailTrace_26330 : CollatzResearch.WordTrace tailWord_26330 prefixEnd_26330 6008864725772096646185 := by
  unfold tailWord_26330
  simp only [CollatzResearch.WordTrace]
  refine ⟨240083498654595412775111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 640222663078921100733629 240083498654595412775111)
  ·
    refine ⟨360125247981893119162667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240083498654595412775111 360125247981893119162667)
    ·
      refine ⟨540187871972839678744001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360125247981893119162667 540187871972839678744001)
      ·
        refine ⟨405140903979629759058001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 540187871972839678744001 405140903979629759058001)
        ·
          refine ⟨303855677984722319293501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 405140903979629759058001 303855677984722319293501)
          ·
            refine ⟨113945879244270869735063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 303855677984722319293501 113945879244270869735063)
            ·
              refine ⟨170918818866406304602595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113945879244270869735063 170918818866406304602595)
              ·
                refine ⟨256378228299609456903893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170918818866406304602595 256378228299609456903893)
                ·
                  refine ⟨6008864725772096646185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 256378228299609456903893 6008864725772096646185)
                  ·
                    rfl

theorem cell21_26330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 7].length) (baseStart_26330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_26330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_26330 prefixEnd_26330 := by exact prefixLift 26330
  have htrace : WordTrace (prefixWord ++ tailWord_26330) baseStart_26330 baseEnd_26330 := by
    simpa [prefixWord, tailWord_26330, baseEnd_26330] using wordTrace_append hprefix tailTrace_26330
  have hstable : (prefixWord ++ tailWord_26330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26330).length < 2 ^ (prefixWord ++ tailWord_26330).sum := by decide
  have hdescent : baseEnd_26330 < baseStart_26330 := by decide
  rcases family_descends (prefixWord ++ tailWord_26330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26347 : List Nat := [1, 1, 1, 1, 2, 4, 3, 5, 3]
def baseStart_26347 : Nat := 118140960795 + 26347 * 2 ^ 59
def prefixEnd_26347 : Nat := 4983230072969 + 3 ^ 40 * 26347 * 2
def baseEnd_26347 : Nat := 6012744357383844862817

theorem tailTrace_26347 : CollatzResearch.WordTrace tailWord_26347 prefixEnd_26347 6012744357383844862817 := by
  unfold tailWord_26347
  simp only [CollatzResearch.WordTrace]
  refine ⟨960954035556793554469295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 640636023704529036312863 960954035556793554469295)
  ·
    refine ⟨1441431053335190331703943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 960954035556793554469295 1441431053335190331703943)
    ·
      refine ⟨2162146580002785497555915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1441431053335190331703943 2162146580002785497555915)
      ·
        refine ⟨3243219870004178246333873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2162146580002785497555915 3243219870004178246333873)
        ·
          refine ⟨2432414902503133684750405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3243219870004178246333873 2432414902503133684750405)
          ·
            refine ⟨456077794219337565890701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2432414902503133684750405 456077794219337565890701)
            ·
              refine ⟨171029172832251587209013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 456077794219337565890701 171029172832251587209013)
              ·
                refine ⟨16033984953023586300845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 171029172832251587209013 16033984953023586300845)
                ·
                  refine ⟨6012744357383844862817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16033984953023586300845 6012744357383844862817)
                  ·
                    rfl

theorem cell21_26347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 5, 3].length) (baseStart_26347 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_26347 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_26347 prefixEnd_26347 := by exact prefixLift 26347
  have htrace : WordTrace (prefixWord ++ tailWord_26347) baseStart_26347 baseEnd_26347 := by
    simpa [prefixWord, tailWord_26347, baseEnd_26347] using wordTrace_append hprefix tailTrace_26347
  have hstable : (prefixWord ++ tailWord_26347).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26347).length < 2 ^ (prefixWord ++ tailWord_26347).sum := by decide
  have hdescent : baseEnd_26347 < baseStart_26347 := by decide
  rcases family_descends (prefixWord ++ tailWord_26347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26392 : List Nat := [2, 1, 2, 3, 1, 1, 6, 5]
def baseStart_26392 : Nat := 118140960795 + 26392 * 2 ^ 59
def prefixEnd_26392 : Nat := 4983230072969 + 3 ^ 40 * 26392 * 2
def baseEnd_26392 : Nat := 2007671323491255537575

theorem tailTrace_26392 : CollatzResearch.WordTrace tailWord_26392 prefixEnd_26392 2007671323491255537575 := by
  unfold tailWord_26392
  simp only [CollatzResearch.WordTrace]
  refine ⟨481297660196883119928715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 641730213595844159904953 481297660196883119928715)
  ·
    refine ⟨721946490295324679893073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 481297660196883119928715 721946490295324679893073)
    ·
      refine ⟨541459867721493509919805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 721946490295324679893073 541459867721493509919805)
      ·
        refine ⟨203047450395560066219927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 541459867721493509919805 203047450395560066219927)
        ·
          refine ⟨304571175593340099329891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203047450395560066219927 304571175593340099329891)
          ·
            refine ⟨456856763390010148994837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304571175593340099329891 456856763390010148994837)
            ·
              refine ⟨21415160783906725734133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 456856763390010148994837 21415160783906725734133)
              ·
                refine ⟨2007671323491255537575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21415160783906725734133 2007671323491255537575)
                ·
                  rfl

theorem cell21_26392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 5].length) (baseStart_26392 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_26392 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_26392 prefixEnd_26392 := by exact prefixLift 26392
  have htrace : WordTrace (prefixWord ++ tailWord_26392) baseStart_26392 baseEnd_26392 := by
    simpa [prefixWord, tailWord_26392, baseEnd_26392] using wordTrace_append hprefix tailTrace_26392
  have hstable : (prefixWord ++ tailWord_26392).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26392).length < 2 ^ (prefixWord ++ tailWord_26392).sum := by decide
  have hdescent : baseEnd_26392 < baseStart_26392 := by decide
  rcases family_descends (prefixWord ++ tailWord_26392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26437 : List Nat := [1, 3, 1, 1, 1, 2, 5, 3, 4]
def baseStart_26437 : Nat := 118140960795 + 26437 * 2 ^ 59
def prefixEnd_26437 : Nat := 4983230072969 + 3 ^ 40 * 26437 * 2
def baseEnd_26437 : Nat := 6033283583563688362633

theorem tailTrace_26437 : CollatzResearch.WordTrace tailWord_26437 prefixEnd_26437 6033283583563688362633 := by
  unfold tailWord_26437
  simp only [CollatzResearch.WordTrace]
  refine ⟨964236605230738925245565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 642824403487159283497043 964236605230738925245565)
  ·
    refine ⟨361588726961527096967087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 964236605230738925245565 361588726961527096967087)
    ·
      refine ⟨542383090442290645450631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361588726961527096967087 542383090442290645450631)
      ·
        refine ⟨813574635663435968175947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 542383090442290645450631 813574635663435968175947)
        ·
          refine ⟨1220361953495153952263921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 813574635663435968175947 1220361953495153952263921)
          ·
            refine ⟨915271465121365464197941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1220361953495153952263921 915271465121365464197941)
            ·
              refine ⟨85806699855128012268557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 915271465121365464197941 85806699855128012268557)
              ·
                refine ⟨32177512445673004600709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85806699855128012268557 32177512445673004600709)
                ·
                  refine ⟨6033283583563688362633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32177512445673004600709 6033283583563688362633)
                  ·
                    rfl

theorem cell21_26437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 3, 4].length) (baseStart_26437 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_26437 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_26437 prefixEnd_26437 := by exact prefixLift 26437
  have htrace : WordTrace (prefixWord ++ tailWord_26437) baseStart_26437 baseEnd_26437 := by
    simpa [prefixWord, tailWord_26437, baseEnd_26437] using wordTrace_append hprefix tailTrace_26437
  have hstable : (prefixWord ++ tailWord_26437).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26437).length < 2 ^ (prefixWord ++ tailWord_26437).sum := by decide
  have hdescent : baseEnd_26437 < baseStart_26437 := by decide
  rcases family_descends (prefixWord ++ tailWord_26437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26468 : List Nat := [2, 3, 1, 1, 6, 8]
def baseStart_26468 : Nat := 118140960795 + 26468 * 2 ^ 59
def prefixEnd_26468 : Nat := 4983230072969 + 3 ^ 40 * 26468 * 2
def baseEnd_26468 : Nat := 223716970589426790589

theorem tailTrace_26468 : CollatzResearch.WordTrace tailWord_26468 prefixEnd_26468 223716970589426790589 := by
  unfold tailWord_26468
  simp only [CollatzResearch.WordTrace]
  refine ⟨482683634059215609812029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 643578178745620813082705 482683634059215609812029)
  ·
    refine ⟨181006362772205853679511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 482683634059215609812029 181006362772205853679511)
    ·
      refine ⟨271509544158308780519267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181006362772205853679511 271509544158308780519267)
      ·
        refine ⟨407264316237463170778901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271509544158308780519267 407264316237463170778901)
        ·
          refine ⟨19090514823631086130261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 407264316237463170778901 19090514823631086130261)
          ·
            refine ⟨223716970589426790589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 19090514823631086130261 223716970589426790589)
            ·
              rfl

theorem cell21_26468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 8].length) (baseStart_26468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_26468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_26468 prefixEnd_26468 := by exact prefixLift 26468
  have htrace : WordTrace (prefixWord ++ tailWord_26468) baseStart_26468 baseEnd_26468 := by
    simpa [prefixWord, tailWord_26468, baseEnd_26468] using wordTrace_append hprefix tailTrace_26468
  have hstable : (prefixWord ++ tailWord_26468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26468).length < 2 ^ (prefixWord ++ tailWord_26468).sum := by decide
  have hdescent : baseEnd_26468 < baseStart_26468 := by decide
  rcases family_descends (prefixWord ++ tailWord_26468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26482 : List Nat := [3, 2, 1, 2, 1, 1, 1, 5, 5]
def baseStart_26482 : Nat := 118140960795 + 26482 * 2 ^ 59
def prefixEnd_26482 : Nat := 4983230072969 + 3 ^ 40 * 26482 * 2
def baseEnd_26482 : Nat := 6043553196653610112541

theorem tailTrace_26482 : CollatzResearch.WordTrace tailWord_26482 prefixEnd_26482 6043553196653610112541 := by
  unfold tailWord_26482
  simp only [CollatzResearch.WordTrace]
  refine ⟨241469472516927902658425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 643918593378474407089133 241469472516927902658425)
  ·
    refine ⟨181102104387695926993819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241469472516927902658425 181102104387695926993819)
    ·
      refine ⟨271653156581543890490729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181102104387695926993819 271653156581543890490729)
      ·
        refine ⟨203739867436157917868047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271653156581543890490729 203739867436157917868047)
        ·
          refine ⟨305609801154236876802071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203739867436157917868047 305609801154236876802071)
          ·
            refine ⟨458414701731355315203107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305609801154236876802071 458414701731355315203107)
            ·
              refine ⟨687622052597032972804661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 458414701731355315203107 687622052597032972804661)
              ·
                refine ⟨64464567430971841200437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 687622052597032972804661 64464567430971841200437)
                ·
                  refine ⟨6043553196653610112541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64464567430971841200437 6043553196653610112541)
                  ·
                    rfl

theorem cell21_26482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_26482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_26482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_26482 prefixEnd_26482 := by exact prefixLift 26482
  have htrace : WordTrace (prefixWord ++ tailWord_26482) baseStart_26482 baseEnd_26482 := by
    simpa [prefixWord, tailWord_26482, baseEnd_26482] using wordTrace_append hprefix tailTrace_26482
  have hstable : (prefixWord ++ tailWord_26482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26482).length < 2 ^ (prefixWord ++ tailWord_26482).sum := by decide
  have hdescent : baseEnd_26482 < baseStart_26482 := by decide
  rcases family_descends (prefixWord ++ tailWord_26482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26516 : List Nat := [2, 4, 2, 1, 1, 2, 1, 5, 3]
def baseStart_26516 : Nat := 118140960795 + 26516 * 2 ^ 59
def prefixEnd_26516 : Nat := 4983230072969 + 3 ^ 40 * 26516 * 2
def baseEnd_26516 : Nat := 6051312459877106545805

theorem tailTrace_26516 : CollatzResearch.WordTrace tailWord_26516 prefixEnd_26516 6051312459877106545805 := by
  unfold tailWord_26516
  simp only [CollatzResearch.WordTrace]
  refine ⟨483558985972267708685701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 644745314629690278247601 483558985972267708685701)
  ·
    refine ⟨90667309869800195378569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 483558985972267708685701 90667309869800195378569)
    ·
      refine ⟨68000482402350146533927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90667309869800195378569 68000482402350146533927)
      ·
        refine ⟨102000723603525219800891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68000482402350146533927 102000723603525219800891)
        ·
          refine ⟨153001085405287829701337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102000723603525219800891 153001085405287829701337)
          ·
            refine ⟨114750814053965872276003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153001085405287829701337 114750814053965872276003)
            ·
              refine ⟨172126221080948808414005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114750814053965872276003 172126221080948808414005)
              ·
                refine ⟨16136833226338950788813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 172126221080948808414005 16136833226338950788813)
                ·
                  refine ⟨6051312459877106545805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16136833226338950788813 6051312459877106545805)
                  ·
                    rfl

theorem cell21_26516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_26516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_26516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_26516 prefixEnd_26516 := by exact prefixLift 26516
  have htrace : WordTrace (prefixWord ++ tailWord_26516) baseStart_26516 baseEnd_26516 := by
    simpa [prefixWord, tailWord_26516, baseEnd_26516] using wordTrace_append hprefix tailTrace_26516
  have hstable : (prefixWord ++ tailWord_26516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26516).length < 2 ^ (prefixWord ++ tailWord_26516).sum := by decide
  have hdescent : baseEnd_26516 < baseStart_26516 := by decide
  rcases family_descends (prefixWord ++ tailWord_26516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26530 : List Nat := [3, 3, 1, 2, 3, 1, 1, 1, 6]
def baseStart_26530 : Nat := 118140960795 + 26530 * 2 ^ 59
def prefixEnd_26530 : Nat := 4983230072969 + 3 ^ 40 * 26530 * 2
def baseEnd_26530 : Nat := 6054507450616193312443

theorem tailTrace_26530 : CollatzResearch.WordTrace tailWord_26530 prefixEnd_26530 6054507450616193312443 := by
  unfold tailWord_26530
  simp only [CollatzResearch.WordTrace]
  refine ⟨241907148473453952095261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 645085729262543872254029 241907148473453952095261)
  ·
    refine ⟨90715180677545232035723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241907148473453952095261 90715180677545232035723)
    ·
      refine ⟨136072771016317848053585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90715180677545232035723 136072771016317848053585)
      ·
        refine ⟨102054578262238386040189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136072771016317848053585 102054578262238386040189)
        ·
          refine ⟨38270466848339394765071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102054578262238386040189 38270466848339394765071)
          ·
            refine ⟨57405700272509092147607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38270466848339394765071 57405700272509092147607)
            ·
              refine ⟨86108550408763638221411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57405700272509092147607 86108550408763638221411)
              ·
                refine ⟨129162825613145457332117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86108550408763638221411 129162825613145457332117)
                ·
                  refine ⟨6054507450616193312443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 129162825613145457332117 6054507450616193312443)
                  ·
                    rfl

theorem cell21_26530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_26530 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_26530 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_26530 prefixEnd_26530 := by exact prefixLift 26530
  have htrace : WordTrace (prefixWord ++ tailWord_26530) baseStart_26530 baseEnd_26530 := by
    simpa [prefixWord, tailWord_26530, baseEnd_26530] using wordTrace_append hprefix tailTrace_26530
  have hstable : (prefixWord ++ tailWord_26530).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26530).length < 2 ^ (prefixWord ++ tailWord_26530).sum := by decide
  have hdescent : baseEnd_26530 < baseStart_26530 := by decide
  rcases family_descends (prefixWord ++ tailWord_26530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26606 : List Nat := [4, 1, 2, 1, 3, 2, 1, 3, 4]
def baseStart_26606 : Nat := 118140960795 + 26606 * 2 ^ 59
def prefixEnd_26606 : Nat := 4983230072969 + 3 ^ 40 * 26606 * 2
def baseEnd_26606 : Nat := 6071851686056950045621

theorem tailTrace_26606 : CollatzResearch.WordTrace tailWord_26606 prefixEnd_26606 6071851686056950045621 := by
  unfold tailWord_26606
  simp only [CollatzResearch.WordTrace]
  refine ⟨121300067702310098518459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 646933694412320525431781 121300067702310098518459)
  ·
    refine ⟨181950101553465147777689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121300067702310098518459 181950101553465147777689)
    ·
      refine ⟨136462576165098860833267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181950101553465147777689 136462576165098860833267)
      ·
        refine ⟨204693864247648291249901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136462576165098860833267 204693864247648291249901)
        ·
          refine ⟨76760199092868109218713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204693864247648291249901 76760199092868109218713)
          ·
            refine ⟨57570149319651081914035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76760199092868109218713 57570149319651081914035)
            ·
              refine ⟨86355223979476622871053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57570149319651081914035 86355223979476622871053)
              ·
                refine ⟨32383208992303733576645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86355223979476622871053 32383208992303733576645)
                ·
                  refine ⟨6071851686056950045621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32383208992303733576645 6071851686056950045621)
                  ·
                    rfl

theorem cell21_26606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_26606 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_26606 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_26606 prefixEnd_26606 := by exact prefixLift 26606
  have htrace : WordTrace (prefixWord ++ tailWord_26606) baseStart_26606 baseEnd_26606 := by
    simpa [prefixWord, tailWord_26606, baseEnd_26606] using wordTrace_append hprefix tailTrace_26606
  have hstable : (prefixWord ++ tailWord_26606).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26606).length < 2 ^ (prefixWord ++ tailWord_26606).sum := by decide
  have hdescent : baseEnd_26606 < baseStart_26606 := by decide
  rcases family_descends (prefixWord ++ tailWord_26606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26637 : List Nat := [1, 7, 1, 2, 10]
def baseStart_26637 : Nat := 118140960795 + 26637 * 2 ^ 59
def prefixEnd_26637 : Nat := 4983230072969 + 3 ^ 40 * 26637 * 2
def baseEnd_26637 : Nat := 75048472943305988011

theorem tailTrace_26637 : CollatzResearch.WordTrace tailWord_26637 prefixEnd_26637 75048472943305988011 := by
  unfold tailWord_26637
  simp only [CollatzResearch.WordTrace]
  refine ⟨971531204506173082526165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 647687469670782055017443 971531204506173082526165)
  ·
    refine ⟨22770262605613431621707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 971531204506173082526165 22770262605613431621707)
    ·
      refine ⟨34155393908420147432561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22770262605613431621707 34155393908420147432561)
      ·
        refine ⟨25616545431315110574421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34155393908420147432561 25616545431315110574421)
        ·
          refine ⟨75048472943305988011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 25616545431315110574421 75048472943305988011)
          ·
            rfl

theorem cell21_26637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 10].length) (baseStart_26637 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_26637 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_26637 prefixEnd_26637 := by exact prefixLift 26637
  have htrace : WordTrace (prefixWord ++ tailWord_26637) baseStart_26637 baseEnd_26637 := by
    simpa [prefixWord, tailWord_26637, baseEnd_26637] using wordTrace_append hprefix tailTrace_26637
  have hstable : (prefixWord ++ tailWord_26637).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26637).length < 2 ^ (prefixWord ++ tailWord_26637).sum := by decide
  have hdescent : baseEnd_26637 < baseStart_26637 := by decide
  rcases family_descends (prefixWord ++ tailWord_26637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26693 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 9]
def baseStart_26693 : Nat := 118140960795 + 26693 * 2 ^ 59
def prefixEnd_26693 : Nat := 4983230072969 + 3 ^ 40 * 26693 * 2
def baseEnd_26693 : Nat := 6091706271364132095443

theorem tailTrace_26693 : CollatzResearch.WordTrace tailWord_26693 prefixEnd_26693 6091706271364132095443 := by
  unfold tailWord_26693
  simp only [CollatzResearch.WordTrace]
  refine ⟨973573692303294646564733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 649049128202196431043155 973573692303294646564733)
  ·
    refine ⟨365090134613735492461775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 973573692303294646564733 365090134613735492461775)
    ·
      refine ⟨547635201920603238692663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365090134613735492461775 547635201920603238692663)
      ·
        refine ⟨821452802880904858038995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547635201920603238692663 821452802880904858038995)
        ·
          refine ⟨1232179204321357287058493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 821452802880904858038995 1232179204321357287058493)
          ·
            refine ⟨462067201620508982646935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1232179204321357287058493 462067201620508982646935)
            ·
              refine ⟨693100802430763473970403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 462067201620508982646935 693100802430763473970403)
              ·
                refine ⟨1039651203646145210955605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 693100802430763473970403 1039651203646145210955605)
                ·
                  refine ⟨6091706271364132095443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1039651203646145210955605 6091706271364132095443)
                  ·
                    rfl

theorem cell21_26693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 9].length) (baseStart_26693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_26693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_26693 prefixEnd_26693 := by exact prefixLift 26693
  have htrace : WordTrace (prefixWord ++ tailWord_26693) baseStart_26693 baseEnd_26693 := by
    simpa [prefixWord, tailWord_26693, baseEnd_26693] using wordTrace_append hprefix tailTrace_26693
  have hstable : (prefixWord ++ tailWord_26693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26693).length < 2 ^ (prefixWord ++ tailWord_26693).sum := by decide
  have hdescent : baseEnd_26693 < baseStart_26693 := by decide
  rcases family_descends (prefixWord ++ tailWord_26693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26730 : List Nat := [3, 1, 3, 2, 4, 1, 2, 5]
def baseStart_26730 : Nat := 118140960795 + 26730 * 2 ^ 59
def prefixEnd_26730 : Nat := 4983230072969 + 3 ^ 40 * 26730 * 2
def baseEnd_26730 : Nat := 2033383391820096659567

theorem tailTrace_26730 : CollatzResearch.WordTrace tailWord_26730 prefixEnd_26730 2033383391820096659567 := by
  unfold tailWord_26730
  simp only [CollatzResearch.WordTrace]
  refine ⟨243730798292312491415411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 649948795446166643774429 243730798292312491415411)
  ·
    refine ⟨365596197438468737123117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243730798292312491415411 365596197438468737123117)
    ·
      refine ⟨137098574039425776421169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 365596197438468737123117 137098574039425776421169)
      ·
        refine ⟨102823930529569332315877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137098574039425776421169 102823930529569332315877)
        ·
          refine ⟨19279486974294249809227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102823930529569332315877 19279486974294249809227)
          ·
            refine ⟨28919230461441374713841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19279486974294249809227 28919230461441374713841)
            ·
              refine ⟨21689422846081031035381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28919230461441374713841 21689422846081031035381)
              ·
                refine ⟨2033383391820096659567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21689422846081031035381 2033383391820096659567)
                ·
                  rfl

theorem cell21_26730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 5].length) (baseStart_26730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_26730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_26730 prefixEnd_26730 := by exact prefixLift 26730
  have htrace : WordTrace (prefixWord ++ tailWord_26730) baseStart_26730 baseEnd_26730 := by
    simpa [prefixWord, tailWord_26730, baseEnd_26730] using wordTrace_append hprefix tailTrace_26730
  have hstable : (prefixWord ++ tailWord_26730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26730).length < 2 ^ (prefixWord ++ tailWord_26730).sum := by decide
  have hdescent : baseEnd_26730 < baseStart_26730 := by decide
  rcases family_descends (prefixWord ++ tailWord_26730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26755 : List Nat := [1, 1, 1, 3, 3, 5, 7]
def baseStart_26755 : Nat := 118140960795 + 26755 * 2 ^ 59
def prefixEnd_26755 : Nat := 4983230072969 + 3 ^ 40 * 26755 * 2
def baseEnd_26755 : Nat := 678428390673978006887

theorem tailTrace_26755 : CollatzResearch.WordTrace tailWord_26755 prefixEnd_26755 678428390673978006887 := by
  unfold tailWord_26755
  simp only [CollatzResearch.WordTrace]
  refine ⟨975835018078679235321719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 650556678719119490214479 975835018078679235321719)
  ·
    refine ⟨1463752527118018852982579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 975835018078679235321719 1463752527118018852982579)
    ·
      refine ⟨2195628790677028279473869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1463752527118018852982579 2195628790677028279473869)
      ·
        refine ⟨823360796503885604802701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2195628790677028279473869 823360796503885604802701)
        ·
          refine ⟨308760298688957101801013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 823360796503885604802701 308760298688957101801013)
          ·
            refine ⟨28946278002089728293845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 308760298688957101801013 28946278002089728293845)
            ·
              refine ⟨678428390673978006887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 28946278002089728293845 678428390673978006887)
              ·
                rfl

theorem cell21_26755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 7].length) (baseStart_26755 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_26755 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_26755 prefixEnd_26755 := by exact prefixLift 26755
  have htrace : WordTrace (prefixWord ++ tailWord_26755) baseStart_26755 baseEnd_26755 := by
    simpa [prefixWord, tailWord_26755, baseEnd_26755] using wordTrace_append hprefix tailTrace_26755
  have hstable : (prefixWord ++ tailWord_26755).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26755).length < 2 ^ (prefixWord ++ tailWord_26755).sum := by decide
  have hdescent : baseEnd_26755 < baseStart_26755 := by decide
  rcases family_descends (prefixWord ++ tailWord_26755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26775 : List Nat := [1, 1, 3, 3, 4, 2, 2, 1, 4]
def baseStart_26775 : Nat := 118140960795 + 26775 * 2 ^ 59
def prefixEnd_26775 : Nat := 4983230072969 + 3 ^ 40 * 26775 * 2
def baseEnd_26775 : Nat := 6110419788550211728609

theorem tailTrace_26775 : CollatzResearch.WordTrace tailWord_26775 prefixEnd_26775 6110419788550211728609 := by
  unfold tailWord_26775
  simp only [CollatzResearch.WordTrace]
  refine ⟨976564478006222651049779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 651042985337481767366519 976564478006222651049779)
  ·
    refine ⟨1464846717009333976574669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 976564478006222651049779 1464846717009333976574669)
    ·
      refine ⟨549317518878500241215501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1464846717009333976574669 549317518878500241215501)
      ·
        refine ⟨205994069579437590455813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 549317518878500241215501 205994069579437590455813)
        ·
          refine ⟨38623888046144548210465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 205994069579437590455813 38623888046144548210465)
          ·
            refine ⟨28967916034608411157849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38623888046144548210465 28967916034608411157849)
            ·
              refine ⟨21725937025956308368387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28967916034608411157849 21725937025956308368387)
              ·
                refine ⟨32588905538934462552581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21725937025956308368387 32588905538934462552581)
                ·
                  refine ⟨6110419788550211728609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32588905538934462552581 6110419788550211728609)
                  ·
                    rfl

theorem cell21_26775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 1, 4].length) (baseStart_26775 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_26775 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_26775 prefixEnd_26775 := by exact prefixLift 26775
  have htrace : WordTrace (prefixWord ++ tailWord_26775) baseStart_26775 baseEnd_26775 := by
    simpa [prefixWord, tailWord_26775, baseEnd_26775] using wordTrace_append hprefix tailTrace_26775
  have hstable : (prefixWord ++ tailWord_26775).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26775).length < 2 ^ (prefixWord ++ tailWord_26775).sum := by decide
  have hdescent : baseEnd_26775 < baseStart_26775 := by decide
  rcases family_descends (prefixWord ++ tailWord_26775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26820 : List Nat := [2, 3, 3, 1, 2, 2, 1, 4, 3]
def baseStart_26820 : Nat := 118140960795 + 26820 * 2 ^ 59
def prefixEnd_26820 : Nat := 4983230072969 + 3 ^ 40 * 26820 * 2
def baseEnd_26820 : Nat := 6120689401640133478517

theorem tailTrace_26820 : CollatzResearch.WordTrace tailWord_26820 prefixEnd_26820 6120689401640133478517 := by
  unfold tailWord_26820
  simp only [CollatzResearch.WordTrace]
  refine ⟨489102881421597668218957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 652137175228796890958609 489102881421597668218957)
  ·
    refine ⟨183413580533099125582109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 489102881421597668218957 183413580533099125582109)
    ·
      refine ⟨68780092699912172093291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183413580533099125582109 68780092699912172093291)
      ·
        refine ⟨103170139049868258139937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68780092699912172093291 103170139049868258139937)
        ·
          refine ⟨77377604287401193604953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103170139049868258139937 77377604287401193604953)
          ·
            refine ⟨58033203215550895203715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77377604287401193604953 58033203215550895203715)
            ·
              refine ⟨87049804823326342805573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58033203215550895203715 87049804823326342805573)
              ·
                refine ⟨16321838404373689276045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87049804823326342805573 16321838404373689276045)
                ·
                  refine ⟨6120689401640133478517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16321838404373689276045 6120689401640133478517)
                  ·
                    rfl

theorem cell21_26820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 4, 3].length) (baseStart_26820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_26820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_26820 prefixEnd_26820 := by exact prefixLift 26820
  have htrace : WordTrace (prefixWord ++ tailWord_26820) baseStart_26820 baseEnd_26820 := by
    simpa [prefixWord, tailWord_26820, baseEnd_26820] using wordTrace_append hprefix tailTrace_26820
  have hstable : (prefixWord ++ tailWord_26820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26820).length < 2 ^ (prefixWord ++ tailWord_26820).sum := by decide
  have hdescent : baseEnd_26820 < baseStart_26820 := by decide
  rcases family_descends (prefixWord ++ tailWord_26820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26907 : List Nat := [1, 1, 1, 1, 1, 1, 10, 5]
def baseStart_26907 : Nat := 118140960795 + 26907 * 2 ^ 59
def prefixEnd_26907 : Nat := 4983230072969 + 3 ^ 40 * 26907 * 2
def baseEnd_26907 : Nat := 2046847995649105176113

theorem tailTrace_26907 : CollatzResearch.WordTrace tailWord_26907 prefixEnd_26907 2046847995649105176113 := by
  unfold tailWord_26907
  simp only [CollatzResearch.WordTrace]
  refine ⟨981378913528009194854975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 654252609018672796569983 981378913528009194854975)
  ·
    refine ⟨1472068370292013792282463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 981378913528009194854975 1472068370292013792282463)
    ·
      refine ⟨2208102555438020688423695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1472068370292013792282463 2208102555438020688423695)
      ·
        refine ⟨3312153833157031032635543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2208102555438020688423695 3312153833157031032635543)
        ·
          refine ⟨4968230749735546548953315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3312153833157031032635543 4968230749735546548953315)
          ·
            refine ⟨7452346124603319823429973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4968230749735546548953315 7452346124603319823429973)
            ·
              refine ⟨21833045286923788545205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7452346124603319823429973 21833045286923788545205)
              ·
                refine ⟨2046847995649105176113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21833045286923788545205 2046847995649105176113)
                ·
                  rfl

theorem cell21_26907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 5].length) (baseStart_26907 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_26907 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_26907 prefixEnd_26907 := by exact prefixLift 26907
  have htrace : WordTrace (prefixWord ++ tailWord_26907) baseStart_26907 baseEnd_26907 := by
    simpa [prefixWord, tailWord_26907, baseEnd_26907] using wordTrace_append hprefix tailTrace_26907
  have hstable : (prefixWord ++ tailWord_26907).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26907).length < 2 ^ (prefixWord ++ tailWord_26907).sum := by decide
  have hdescent : baseEnd_26907 < baseStart_26907 := by decide
  rcases family_descends (prefixWord ++ tailWord_26907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26910 : List Nat := [4, 3, 2, 1, 1, 1, 1, 2, 6]
def baseStart_26910 : Nat := 118140960795 + 26910 * 2 ^ 59
def prefixEnd_26910 : Nat := 4983230072969 + 3 ^ 40 * 26910 * 2
def baseEnd_26910 : Nat := 6141228627819976978333

theorem tailTrace_26910 : CollatzResearch.WordTrace tailWord_26910 prefixEnd_26910 6141228627819976978333 := by
  unfold tailWord_26910
  simp only [CollatzResearch.WordTrace]
  refine ⟨122686041564642588401773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 654325555011427138142789 122686041564642588401773)
  ·
    refine ⟨46007265586740970650665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122686041564642588401773 46007265586740970650665)
    ·
      refine ⟨34505449190055727987999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46007265586740970650665 34505449190055727987999)
      ·
        refine ⟨51758173785083591981999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34505449190055727987999 51758173785083591981999)
        ·
          refine ⟨77637260677625387972999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51758173785083591981999 77637260677625387972999)
          ·
            refine ⟨116455891016438081959499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77637260677625387972999 116455891016438081959499)
            ·
              refine ⟨174683836524657122939249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116455891016438081959499 174683836524657122939249)
              ·
                refine ⟨131012877393492842204437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174683836524657122939249 131012877393492842204437)
                ·
                  refine ⟨6141228627819976978333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 131012877393492842204437 6141228627819976978333)
                  ·
                    rfl

theorem cell21_26910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_26910 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_26910 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_26910 prefixEnd_26910 := by exact prefixLift 26910
  have htrace : WordTrace (prefixWord ++ tailWord_26910) baseStart_26910 baseEnd_26910 := by
    simpa [prefixWord, tailWord_26910, baseEnd_26910] using wordTrace_append hprefix tailTrace_26910
  have hstable : (prefixWord ++ tailWord_26910).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26910).length < 2 ^ (prefixWord ++ tailWord_26910).sum := by decide
  have hdescent : baseEnd_26910 < baseStart_26910 := by decide
  rcases family_descends (prefixWord ++ tailWord_26910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26938 : List Nat := [3, 1, 1, 1, 4, 2, 3, 1, 5]
def baseStart_26938 : Nat := 118140960795 + 26938 * 2 ^ 59
def prefixEnd_26938 : Nat := 4983230072969 + 3 ^ 40 * 26938 * 2
def baseEnd_26938 : Nat := 6147618609298150511609

theorem tailTrace_26938 : CollatzResearch.WordTrace tailWord_26938 prefixEnd_26938 6147618609298150511609 := by
  unfold tailWord_26938
  simp only [CollatzResearch.WordTrace]
  refine ⟨245627394103925372308367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 655006384277134326155645 245627394103925372308367)
  ·
    refine ⟨368441091155888058462551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 245627394103925372308367 368441091155888058462551)
    ·
      refine ⟨552661636733832087693827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 368441091155888058462551 552661636733832087693827)
      ·
        refine ⟨828992455100748131540741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 552661636733832087693827 828992455100748131540741)
        ·
          refine ⟨155436085331390274663889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 828992455100748131540741 155436085331390274663889)
          ·
            refine ⟨116577063998542705997917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155436085331390274663889 116577063998542705997917)
            ·
              refine ⟨43716398999453514749219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116577063998542705997917 43716398999453514749219)
              ·
                refine ⟨65574598499180272123829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43716398999453514749219 65574598499180272123829)
                ·
                  refine ⟨6147618609298150511609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65574598499180272123829 6147618609298150511609)
                  ·
                    rfl

theorem cell21_26938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 5].length) (baseStart_26938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_26938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_26938 prefixEnd_26938 := by exact prefixLift 26938
  have htrace : WordTrace (prefixWord ++ tailWord_26938) baseStart_26938 baseEnd_26938 := by
    simpa [prefixWord, tailWord_26938, baseEnd_26938] using wordTrace_append hprefix tailTrace_26938
  have hstable : (prefixWord ++ tailWord_26938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26938).length < 2 ^ (prefixWord ++ tailWord_26938).sum := by decide
  have hdescent : baseEnd_26938 < baseStart_26938 := by decide
  rcases family_descends (prefixWord ++ tailWord_26938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_26986 : List Nat := [3, 1, 3, 3, 1, 2, 2, 2, 4]
def baseStart_26986 : Nat := 118140960795 + 26986 * 2 ^ 59
def prefixEnd_26986 : Nat := 4983230072969 + 3 ^ 40 * 26986 * 2
def baseEnd_26986 : Nat := 6158572863260733711511

theorem tailTrace_26986 : CollatzResearch.WordTrace tailWord_26986 prefixEnd_26986 6158572863260733711511 := by
  unfold tailWord_26986
  simp only [CollatzResearch.WordTrace]
  refine ⟨246065070060451421745203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 656173520161203791320541 246065070060451421745203)
  ·
    refine ⟨369097605090677132617805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246065070060451421745203 369097605090677132617805)
    ·
      refine ⟨138411601909003924731677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 369097605090677132617805 138411601909003924731677)
      ·
        refine ⟨51904350715876471774379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138411601909003924731677 51904350715876471774379)
        ·
          refine ⟨77856526073814707661569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51904350715876471774379 77856526073814707661569)
          ·
            refine ⟨58392394555361030746177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77856526073814707661569 58392394555361030746177)
            ·
              refine ⟨43794295916520773059633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58392394555361030746177 43794295916520773059633)
              ·
                refine ⟨32845721937390579794725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43794295916520773059633 32845721937390579794725)
                ·
                  refine ⟨6158572863260733711511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32845721937390579794725 6158572863260733711511)
                  ·
                    rfl

theorem cell21_26986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 2, 4].length) (baseStart_26986 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_26986 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_26986 prefixEnd_26986 := by exact prefixLift 26986
  have htrace : WordTrace (prefixWord ++ tailWord_26986) baseStart_26986 baseEnd_26986 := by
    simpa [prefixWord, tailWord_26986, baseEnd_26986] using wordTrace_append hprefix tailTrace_26986
  have hstable : (prefixWord ++ tailWord_26986).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_26986).length < 2 ^ (prefixWord ++ tailWord_26986).sum := by decide
  have hdescent : baseEnd_26986 < baseStart_26986 := by decide
  rcases family_descends (prefixWord ++ tailWord_26986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27048 : List Nat := [2, 1, 6, 1, 1, 1, 2, 4, 3]
def baseStart_27048 : Nat := 118140960795 + 27048 * 2 ^ 59
def prefixEnd_27048 : Nat := 4983230072969 + 3 ^ 40 * 27048 * 2
def baseEnd_27048 : Nat := 6172722107962403678051

theorem tailTrace_27048 : CollatzResearch.WordTrace tailWord_27048 prefixEnd_27048 6172722107962403678051 := by
  unfold tailWord_27048
  simp only [CollatzResearch.WordTrace]
  refine ⟨493260803008595137868899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 657681070678126850491865 493260803008595137868899)
  ·
    refine ⟨739891204512892706803349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 493260803008595137868899 739891204512892706803349)
    ·
      refine ⟨34682400211541845631407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 739891204512892706803349 34682400211541845631407)
      ·
        refine ⟨52023600317312768447111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34682400211541845631407 52023600317312768447111)
        ·
          refine ⟨78035400475969152670667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52023600317312768447111 78035400475969152670667)
          ·
            refine ⟨117053100713953729006001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78035400475969152670667 117053100713953729006001)
            ·
              refine ⟨87789825535465296754501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117053100713953729006001 87789825535465296754501)
              ·
                refine ⟨16460592287899743141469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87789825535465296754501 16460592287899743141469)
                ·
                  refine ⟨6172722107962403678051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16460592287899743141469 6172722107962403678051)
                  ·
                    rfl

theorem cell21_27048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 4, 3].length) (baseStart_27048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_27048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_27048 prefixEnd_27048 := by exact prefixLift 27048
  have htrace : WordTrace (prefixWord ++ tailWord_27048) baseStart_27048 baseEnd_27048 := by
    simpa [prefixWord, tailWord_27048, baseEnd_27048] using wordTrace_append hprefix tailTrace_27048
  have hstable : (prefixWord ++ tailWord_27048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27048).length < 2 ^ (prefixWord ++ tailWord_27048).sum := by decide
  have hdescent : baseEnd_27048 < baseStart_27048 := by decide
  rcases family_descends (prefixWord ++ tailWord_27048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27076 : List Nat := [2, 3, 3, 2, 2, 1, 1, 7]
def baseStart_27076 : Nat := 118140960795 + 27076 * 2 ^ 59
def prefixEnd_27076 : Nat := 4983230072969 + 3 ^ 40 * 27076 * 2
def baseEnd_27076 : Nat := 2059704029813525737109

theorem tailTrace_27076 : CollatzResearch.WordTrace tailWord_27076 prefixEnd_27076 2059704029813525737109 := by
  unfold tailWord_27076
  simp only [CollatzResearch.WordTrace]
  refine ⟨493771424957875528878541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 658361899943834038504721 493771424957875528878541)
  ·
    refine ⟨185164284359203323329453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 493771424957875528878541 185164284359203323329453)
    ·
      refine ⟨69436606634701246248545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185164284359203323329453 69436606634701246248545)
      ·
        refine ⟨52077454976025934686409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69436606634701246248545 52077454976025934686409)
        ·
          refine ⟨39058091232019451014807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52077454976025934686409 39058091232019451014807)
          ·
            refine ⟨58587136848029176522211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39058091232019451014807 58587136848029176522211)
            ·
              refine ⟨87880705272043764783317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58587136848029176522211 87880705272043764783317)
              ·
                refine ⟨2059704029813525737109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 87880705272043764783317 2059704029813525737109)
                ·
                  rfl

theorem cell21_27076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 7].length) (baseStart_27076 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_27076 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_27076 prefixEnd_27076 := by exact prefixLift 27076
  have htrace : WordTrace (prefixWord ++ tailWord_27076) baseStart_27076 baseEnd_27076 := by
    simpa [prefixWord, tailWord_27076, baseEnd_27076] using wordTrace_append hprefix tailTrace_27076
  have hstable : (prefixWord ++ tailWord_27076).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27076).length < 2 ^ (prefixWord ++ tailWord_27076).sum := by decide
  have hdescent : baseEnd_27076 < baseStart_27076 := by decide
  rcases family_descends (prefixWord ++ tailWord_27076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27104 : List Nat := [2, 1, 1, 3, 1, 1, 4, 4, 4]
def baseStart_27104 : Nat := 118140960795 + 27104 * 2 ^ 59
def prefixEnd_27104 : Nat := 4983230072969 + 3 ^ 40 * 27104 * 2
def baseEnd_27104 : Nat := 6185502070918750744603

theorem tailTrace_27104 : CollatzResearch.WordTrace tailWord_27104 prefixEnd_27104 6185502070918750744603 := by
  unfold tailWord_27104
  simp only [CollatzResearch.WordTrace]
  refine ⟨494282046907155919888183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 659042729209541226517577 494282046907155919888183)
  ·
    refine ⟨741423070360733879832275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 494282046907155919888183 741423070360733879832275)
    ·
      refine ⟨1112134605541100819748413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 741423070360733879832275 1112134605541100819748413)
      ·
        refine ⟨417050477077912807405655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1112134605541100819748413 417050477077912807405655)
        ·
          refine ⟨625575715616869211108483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417050477077912807405655 625575715616869211108483)
          ·
            refine ⟨938363573425303816662725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 625575715616869211108483 938363573425303816662725)
            ·
              refine ⟨175943170017244465624261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 938363573425303816662725 175943170017244465624261)
              ·
                refine ⟨32989344378233337304549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 175943170017244465624261 32989344378233337304549)
                ·
                  refine ⟨6185502070918750744603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32989344378233337304549 6185502070918750744603)
                  ·
                    rfl

theorem cell21_27104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 4, 4].length) (baseStart_27104 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_27104 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_27104 prefixEnd_27104 := by exact prefixLift 27104
  have htrace : WordTrace (prefixWord ++ tailWord_27104) baseStart_27104 baseEnd_27104 := by
    simpa [prefixWord, tailWord_27104, baseEnd_27104] using wordTrace_append hprefix tailTrace_27104
  have hstable : (prefixWord ++ tailWord_27104).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27104).length < 2 ^ (prefixWord ++ tailWord_27104).sum := by decide
  have hdescent : baseEnd_27104 < baseStart_27104 := by decide
  rcases family_descends (prefixWord ++ tailWord_27104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27107 : List Nat := [1, 1, 1, 6, 3, 2, 1, 1, 5]
def baseStart_27107 : Nat := 118140960795 + 27107 * 2 ^ 59
def prefixEnd_27107 : Nat := 4983230072969 + 3 ^ 40 * 27107 * 2
def baseEnd_27107 : Nat := 6186186711791412194597

theorem tailTrace_27107 : CollatzResearch.WordTrace tailWord_27107 prefixEnd_27107 6186186711791412194597 := by
  unfold tailWord_27107
  simp only [CollatzResearch.WordTrace]
  refine ⟨988673512803443352135575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 659115675202295568090383 988673512803443352135575)
  ·
    refine ⟨1483010269205165028203363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 988673512803443352135575 1483010269205165028203363)
    ·
      refine ⟨2224515403807747542305045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1483010269205165028203363 2224515403807747542305045)
      ·
        refine ⟨104274159553488166045549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2224515403807747542305045 104274159553488166045549)
        ·
          refine ⟨39102809832558062267081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104274159553488166045549 39102809832558062267081)
          ·
            refine ⟨29327107374418546700311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39102809832558062267081 29327107374418546700311)
            ·
              refine ⟨43990661061627820050467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29327107374418546700311 43990661061627820050467)
              ·
                refine ⟨65985991592441730075701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43990661061627820050467 65985991592441730075701)
                ·
                  refine ⟨6186186711791412194597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65985991592441730075701 6186186711791412194597)
                  ·
                    rfl

theorem cell21_27107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 5].length) (baseStart_27107 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_27107 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_27107 prefixEnd_27107 := by exact prefixLift 27107
  have htrace : WordTrace (prefixWord ++ tailWord_27107) baseStart_27107 baseEnd_27107 := by
    simpa [prefixWord, tailWord_27107, baseEnd_27107] using wordTrace_append hprefix tailTrace_27107
  have hstable : (prefixWord ++ tailWord_27107).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27107).length < 2 ^ (prefixWord ++ tailWord_27107).sum := by decide
  have hdescent : baseEnd_27107 < baseStart_27107 := by decide
  rcases family_descends (prefixWord ++ tailWord_27107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27290 : List Nat := [3, 1, 1, 6, 1, 1, 1, 3, 4]
def baseStart_27290 : Nat := 118140960795 + 27290 * 2 ^ 59
def prefixEnd_27290 : Nat := 4983230072969 + 3 ^ 40 * 27290 * 2
def baseEnd_27290 : Nat := 6227949805023760644223

theorem tailTrace_27290 : CollatzResearch.WordTrace tailWord_27290 prefixEnd_27290 6227949805023760644223 := by
  unfold tailWord_27290
  simp only [CollatzResearch.WordTrace]
  refine ⟨248837017785116401511831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 663565380760310404031549 248837017785116401511831)
  ·
    refine ⟨373255526677674602267747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248837017785116401511831 373255526677674602267747)
    ·
      refine ⟨559883290016511903401621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373255526677674602267747 559883290016511903401621)
      ·
        refine ⟨26244529219523995471951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 559883290016511903401621 26244529219523995471951)
        ·
          refine ⟨39366793829285993207927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26244529219523995471951 39366793829285993207927)
          ·
            refine ⟨59050190743928989811891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39366793829285993207927 59050190743928989811891)
            ·
              refine ⟨88575286115893484717837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59050190743928989811891 88575286115893484717837)
              ·
                refine ⟨33215732293460056769189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88575286115893484717837 33215732293460056769189)
                ·
                  refine ⟨6227949805023760644223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33215732293460056769189 6227949805023760644223)
                  ·
                    rfl

theorem cell21_27290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 3, 4].length) (baseStart_27290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_27290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_27290 prefixEnd_27290 := by exact prefixLift 27290
  have htrace : WordTrace (prefixWord ++ tailWord_27290) baseStart_27290 baseEnd_27290 := by
    simpa [prefixWord, tailWord_27290, baseEnd_27290] using wordTrace_append hprefix tailTrace_27290
  have hstable : (prefixWord ++ tailWord_27290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27290).length < 2 ^ (prefixWord ++ tailWord_27290).sum := by decide
  have hdescent : baseEnd_27290 < baseStart_27290 := by decide
  rcases family_descends (prefixWord ++ tailWord_27290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27394 : List Nat := [3, 4, 1, 1, 1, 2, 1, 3, 5]
def baseStart_27394 : Nat := 118140960795 + 27394 * 2 ^ 59
def prefixEnd_27394 : Nat := 4983230072969 + 3 ^ 40 * 27394 * 2
def baseEnd_27394 : Nat := 6251684021942690910677

theorem tailTrace_27394 : CollatzResearch.WordTrace tailWord_27394 prefixEnd_27394 6251684021942690910677 := by
  unfold tailWord_27394
  simp only [CollatzResearch.WordTrace]
  refine ⟨249785315690922841958309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 666094175175794245222157 249785315690922841958309)
  ·
    refine ⟨46834746692048032867183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249785315690922841958309 46834746692048032867183)
    ·
      refine ⟨70252120038072049300775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46834746692048032867183 70252120038072049300775)
      ·
        refine ⟨105378180057108073951163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70252120038072049300775 105378180057108073951163)
        ·
          refine ⟨158067270085662110926745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105378180057108073951163 158067270085662110926745)
          ·
            refine ⟨118550452564246583195059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158067270085662110926745 118550452564246583195059)
            ·
              refine ⟨177825678846369874792589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118550452564246583195059 177825678846369874792589)
              ·
                refine ⟨66684629567388703047221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 177825678846369874792589 66684629567388703047221)
                ·
                  refine ⟨6251684021942690910677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66684629567388703047221 6251684021942690910677)
                  ·
                    rfl

theorem cell21_27394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_27394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_27394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_27394 prefixEnd_27394 := by exact prefixLift 27394
  have htrace : WordTrace (prefixWord ++ tailWord_27394) baseStart_27394 baseEnd_27394 := by
    simpa [prefixWord, tailWord_27394, baseEnd_27394] using wordTrace_append hprefix tailTrace_27394
  have hstable : (prefixWord ++ tailWord_27394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27394).length < 2 ^ (prefixWord ++ tailWord_27394).sum := by decide
  have hdescent : baseEnd_27394 < baseStart_27394 := by decide
  rcases family_descends (prefixWord ++ tailWord_27394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27428 : List Nat := [2, 3, 1, 3, 3, 2, 1, 3, 3]
def baseStart_27428 : Nat := 118140960795 + 27428 * 2 ^ 59
def prefixEnd_27428 : Nat := 4983230072969 + 3 ^ 40 * 27428 * 2
def baseEnd_27428 : Nat := 6259443285166187343941

theorem tailTrace_27428 : CollatzResearch.WordTrace tailWord_27428 prefixEnd_27428 6259443285166187343941 := by
  unfold tailWord_27428
  simp only [CollatzResearch.WordTrace]
  refine ⟨500190672320257587285469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 666920896427010116380625 500190672320257587285469)
  ·
    refine ⟨187571502120096595232051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 500190672320257587285469 187571502120096595232051)
    ·
      refine ⟨281357253180144892848077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187571502120096595232051 281357253180144892848077)
      ·
        refine ⟨105508969942554334818029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 281357253180144892848077 105508969942554334818029)
        ·
          refine ⟨39565863728457875556761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105508969942554334818029 39565863728457875556761)
          ·
            refine ⟨29674397796343406667571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39565863728457875556761 29674397796343406667571)
            ·
              refine ⟨44511596694515110001357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29674397796343406667571 44511596694515110001357)
              ·
                refine ⟨16691848760443166250509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44511596694515110001357 16691848760443166250509)
                ·
                  refine ⟨6259443285166187343941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16691848760443166250509 6259443285166187343941)
                  ·
                    rfl

theorem cell21_27428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 3, 3].length) (baseStart_27428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_27428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_27428 prefixEnd_27428 := by exact prefixLift 27428
  have htrace : WordTrace (prefixWord ++ tailWord_27428) baseStart_27428 baseEnd_27428 := by
    simpa [prefixWord, tailWord_27428, baseEnd_27428] using wordTrace_append hprefix tailTrace_27428
  have hstable : (prefixWord ++ tailWord_27428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27428).length < 2 ^ (prefixWord ++ tailWord_27428).sum := by decide
  have hdescent : baseEnd_27428 < baseStart_27428 := by decide
  rcases family_descends (prefixWord ++ tailWord_27428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27529 : List Nat := [1, 2, 1, 1, 5, 3, 1, 2, 5]
def baseStart_27529 : Nat := 118140960795 + 27529 * 2 ^ 59
def prefixEnd_27529 : Nat := 4983230072969 + 3 ^ 40 * 27529 * 2
def baseEnd_27529 : Nat := 6282492861212456160401

theorem tailTrace_27529 : CollatzResearch.WordTrace tailWord_27529 prefixEnd_27529 6282492861212456160401 := by
  unfold tailWord_27529
  simp only [CollatzResearch.WordTrace]
  refine ⟨1004065117274609423997641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 669376744849739615998427 1004065117274609423997641)
  ·
    refine ⟨753048837955957067998231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1004065117274609423997641 753048837955957067998231)
    ·
      refine ⟨1129573256933935601997347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 753048837955957067998231 1129573256933935601997347)
      ·
        refine ⟨1694359885400903402996021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1129573256933935601997347 1694359885400903402996021)
        ·
          refine ⟨158846239256334694030877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1694359885400903402996021 158846239256334694030877)
          ·
            refine ⟨59567339721125510261579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158846239256334694030877 59567339721125510261579)
            ·
              refine ⟨89351009581688265392369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59567339721125510261579 89351009581688265392369)
              ·
                refine ⟨67013257186266199044277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89351009581688265392369 67013257186266199044277)
                ·
                  refine ⟨6282492861212456160401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67013257186266199044277 6282492861212456160401)
                  ·
                    rfl

theorem cell21_27529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 5].length) (baseStart_27529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_27529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_27529 prefixEnd_27529 := by exact prefixLift 27529
  have htrace : WordTrace (prefixWord ++ tailWord_27529) baseStart_27529 baseEnd_27529 := by
    simpa [prefixWord, tailWord_27529, baseEnd_27529] using wordTrace_append hprefix tailTrace_27529
  have hstable : (prefixWord ++ tailWord_27529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27529).length < 2 ^ (prefixWord ++ tailWord_27529).sum := by decide
  have hdescent : baseEnd_27529 < baseStart_27529 := by decide
  rcases family_descends (prefixWord ++ tailWord_27529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27543 : List Nat := [1, 1, 3, 3, 1, 2, 2, 2, 6]
def baseStart_27543 : Nat := 118140960795 + 27543 * 2 ^ 59
def prefixEnd_27543 : Nat := 4983230072969 + 3 ^ 40 * 27543 * 2
def baseEnd_27543 : Nat := 6285687851951542927039

theorem tailTrace_27543 : CollatzResearch.WordTrace tailWord_27543 prefixEnd_27543 6285687851951542927039 := by
  unfold tailWord_27543
  simp only [CollatzResearch.WordTrace]
  refine ⟨1004575739223889815007283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 669717159482593210004855 1004575739223889815007283)
  ·
    refine ⟨1506863608835834722510925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1004575739223889815007283 1506863608835834722510925)
    ·
      refine ⟨565073853313438020941597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1506863608835834722510925 565073853313438020941597)
      ·
        refine ⟨211902694992539257853099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 565073853313438020941597 211902694992539257853099)
        ·
          refine ⟨317854042488808886779649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211902694992539257853099 317854042488808886779649)
          ·
            refine ⟨238390531866606665084737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 317854042488808886779649 238390531866606665084737)
            ·
              refine ⟨178792898899954998813553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238390531866606665084737 178792898899954998813553)
              ·
                refine ⟨134094674174966249110165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178792898899954998813553 134094674174966249110165)
                ·
                  refine ⟨6285687851951542927039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 134094674174966249110165 6285687851951542927039)
                  ·
                    rfl

theorem cell21_27543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 6].length) (baseStart_27543 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_27543 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_27543 prefixEnd_27543 := by exact prefixLift 27543
  have htrace : WordTrace (prefixWord ++ tailWord_27543) baseStart_27543 baseEnd_27543 := by
    simpa [prefixWord, tailWord_27543, baseEnd_27543] using wordTrace_append hprefix tailTrace_27543
  have hstable : (prefixWord ++ tailWord_27543).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27543).length < 2 ^ (prefixWord ++ tailWord_27543).sum := by decide
  have hdescent : baseEnd_27543 < baseStart_27543 := by decide
  rcases family_descends (prefixWord ++ tailWord_27543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27577 : List Nat := [1, 2, 1, 4, 2, 3, 3, 1, 4]
def baseStart_27577 : Nat := 118140960795 + 27577 * 2 ^ 59
def prefixEnd_27577 : Nat := 4983230072969 + 3 ^ 40 * 27577 * 2
def baseEnd_27577 : Nat := 6293447115175039360303

theorem tailTrace_27577 : CollatzResearch.WordTrace tailWord_27577 prefixEnd_27577 6293447115175039360303 := by
  unfold tailWord_27577
  simp only [CollatzResearch.WordTrace]
  refine ⟨1005815821100713621744985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 670543880733809081163323 1005815821100713621744985)
  ·
    refine ⟨754361865825535216308739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1005815821100713621744985 754361865825535216308739)
    ·
      refine ⟨1131542798738302824463109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 754361865825535216308739 1131542798738302824463109)
      ·
        refine ⟨212164274763431779586833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1131542798738302824463109 212164274763431779586833)
        ·
          refine ⟨159123206072573834690125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212164274763431779586833 159123206072573834690125)
          ·
            refine ⟨59671202277215188008797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159123206072573834690125 59671202277215188008797)
            ·
              refine ⟨22376700853955695503299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59671202277215188008797 22376700853955695503299)
              ·
                refine ⟨33565051280933543254949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22376700853955695503299 33565051280933543254949)
                ·
                  refine ⟨6293447115175039360303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33565051280933543254949 6293447115175039360303)
                  ·
                    rfl

theorem cell21_27577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 1, 4].length) (baseStart_27577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_27577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_27577 prefixEnd_27577 := by exact prefixLift 27577
  have htrace : WordTrace (prefixWord ++ tailWord_27577) baseStart_27577 baseEnd_27577 := by
    simpa [prefixWord, tailWord_27577, baseEnd_27577] using wordTrace_append hprefix tailTrace_27577
  have hstable : (prefixWord ++ tailWord_27577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27577).length < 2 ^ (prefixWord ++ tailWord_27577).sum := by decide
  have hdescent : baseEnd_27577 < baseStart_27577 := by decide
  rcases family_descends (prefixWord ++ tailWord_27577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27619 : List Nat := [1, 1, 1, 6, 1, 1, 1, 3, 6]
def baseStart_27619 : Nat := 118140960795 + 27619 * 2 ^ 59
def prefixEnd_27619 : Nat := 4983230072969 + 3 ^ 40 * 27619 * 2
def baseEnd_27619 : Nat := 6303032087392299660217

theorem tailTrace_27619 : CollatzResearch.WordTrace tailWord_27619 prefixEnd_27619 6303032087392299660217 := by
  unfold tailWord_27619
  simp only [CollatzResearch.WordTrace]
  refine ⟨1007347686948554794773911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 671565124632369863182607 1007347686948554794773911)
  ·
    refine ⟨1511021530422832192160867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1007347686948554794773911 1511021530422832192160867)
    ·
      refine ⟨2266532295634248288241301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1511021530422832192160867 2266532295634248288241301)
      ·
        refine ⟨106243701357855388511311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2266532295634248288241301 106243701357855388511311)
        ·
          refine ⟨159365552036783082766967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106243701357855388511311 159365552036783082766967)
          ·
            refine ⟨239048328055174624150451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159365552036783082766967 239048328055174624150451)
            ·
              refine ⟨358572492082761936225677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239048328055174624150451 358572492082761936225677)
              ·
                refine ⟨134464684531035726084629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 358572492082761936225677 134464684531035726084629)
                ·
                  refine ⟨6303032087392299660217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 134464684531035726084629 6303032087392299660217)
                  ·
                    rfl

theorem cell21_27619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 6].length) (baseStart_27619 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_27619 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_27619 prefixEnd_27619 := by exact prefixLift 27619
  have htrace : WordTrace (prefixWord ++ tailWord_27619) baseStart_27619 baseEnd_27619 := by
    simpa [prefixWord, tailWord_27619, baseEnd_27619] using wordTrace_append hprefix tailTrace_27619
  have hstable : (prefixWord ++ tailWord_27619).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27619).length < 2 ^ (prefixWord ++ tailWord_27619).sum := by decide
  have hdescent : baseEnd_27619 < baseStart_27619 := by decide
  rcases family_descends (prefixWord ++ tailWord_27619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27746 : List Nat := [3, 3, 2, 2, 1, 2, 3, 1, 4]
def baseStart_27746 : Nat := 118140960795 + 27746 * 2 ^ 59
def prefixEnd_27746 : Nat := 4983230072969 + 3 ^ 40 * 27746 * 2
def baseEnd_27746 : Nat := 6332015217668301043291

theorem tailTrace_27746 : CollatzResearch.WordTrace tailWord_27746 prefixEnd_27746 6332015217668301043291 := by
  unfold tailWord_27746
  simp only [CollatzResearch.WordTrace]
  refine ⟨252994939372113871161773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 674653171658970323098061 252994939372113871161773)
  ·
    refine ⟨94873102264542701685665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252994939372113871161773 94873102264542701685665)
    ·
      refine ⟨71154826698407026264249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94873102264542701685665 71154826698407026264249)
      ·
        refine ⟨53366120023805269698187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71154826698407026264249 53366120023805269698187)
        ·
          refine ⟨80049180035707904547281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53366120023805269698187 80049180035707904547281)
          ·
            refine ⟨60036885026780928410461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80049180035707904547281 60036885026780928410461)
            ·
              refine ⟨22513831885042848153923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60036885026780928410461 22513831885042848153923)
              ·
                refine ⟨33770747827564272230885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22513831885042848153923 33770747827564272230885)
                ·
                  refine ⟨6332015217668301043291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33770747827564272230885 6332015217668301043291)
                  ·
                    rfl

theorem cell21_27746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_27746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_27746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_27746 prefixEnd_27746 := by exact prefixLift 27746
  have htrace : WordTrace (prefixWord ++ tailWord_27746) baseStart_27746 baseEnd_27746 := by
    simpa [prefixWord, tailWord_27746, baseEnd_27746] using wordTrace_append hprefix tailTrace_27746
  have hstable : (prefixWord ++ tailWord_27746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27746).length < 2 ^ (prefixWord ++ tailWord_27746).sum := by decide
  have hdescent : baseEnd_27746 < baseStart_27746 := by decide
  rcases family_descends (prefixWord ++ tailWord_27746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27757 : List Nat := [1, 5, 1, 1, 2, 2, 2, 2, 5]
def baseStart_27757 : Nat := 118140960795 + 27757 * 2 ^ 59
def prefixEnd_27757 : Nat := 4983230072969 + 3 ^ 40 * 27757 * 2
def baseEnd_27757 : Nat := 6334525567534726359935

theorem tailTrace_27757 : CollatzResearch.WordTrace tailWord_27757 prefixEnd_27757 6334525567534726359935 := by
  unfold tailWord_27757
  simp only [CollatzResearch.WordTrace]
  refine ⟨1012380960448604363297525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 674920640299069575531683 1012380960448604363297525)
  ·
    refine ⟨94910715042056659059143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1012380960448604363297525 94910715042056659059143)
    ·
      refine ⟨142366072563084988588715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94910715042056659059143 142366072563084988588715)
      ·
        refine ⟨213549108844627482883073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142366072563084988588715 213549108844627482883073)
        ·
          refine ⟨160161831633470612162305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213549108844627482883073 160161831633470612162305)
          ·
            refine ⟨120121373725102959121729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160161831633470612162305 120121373725102959121729)
            ·
              refine ⟨90091030293827219341297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120121373725102959121729 90091030293827219341297)
              ·
                refine ⟨67568272720370414505973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90091030293827219341297 67568272720370414505973)
                ·
                  refine ⟨6334525567534726359935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67568272720370414505973 6334525567534726359935)
                  ·
                    rfl

theorem cell21_27757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_27757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_27757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_27757 prefixEnd_27757 := by exact prefixLift 27757
  have htrace : WordTrace (prefixWord ++ tailWord_27757) baseStart_27757 baseEnd_27757 := by
    simpa [prefixWord, tailWord_27757, baseEnd_27757] using wordTrace_append hprefix tailTrace_27757
  have hstable : (prefixWord ++ tailWord_27757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27757).length < 2 ^ (prefixWord ++ tailWord_27757).sum := by decide
  have hdescent : baseEnd_27757 < baseStart_27757 := by decide
  rcases family_descends (prefixWord ++ tailWord_27757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27785 : List Nat := [1, 2, 1, 1, 4, 3, 9]
def baseStart_27785 : Nat := 118140960795 + 27785 * 2 ^ 59
def prefixEnd_27785 : Nat := 4983230072969 + 3 ^ 40 * 27785 * 2
def baseEnd_27785 : Nat := 704546172112544432579

theorem tailTrace_27785 : CollatzResearch.WordTrace tailWord_27785 prefixEnd_27785 704546172112544432579 := by
  unfold tailWord_27785
  simp only [CollatzResearch.WordTrace]
  refine ⟨1013402204347165145316809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 675601469564776763544539 1013402204347165145316809)
  ·
    refine ⟨760051653260373858987607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1013402204347165145316809 760051653260373858987607)
    ·
      refine ⟨1140077479890560788481411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 760051653260373858987607 1140077479890560788481411)
      ·
        refine ⟨1710116219835841182722117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1140077479890560788481411 1710116219835841182722117)
        ·
          refine ⟨320646791219220221760397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1710116219835841182722117 320646791219220221760397)
          ·
            refine ⟨120242546707207583160149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 320646791219220221760397 120242546707207583160149)
            ·
              refine ⟨704546172112544432579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 120242546707207583160149 704546172112544432579)
              ·
                rfl

theorem cell21_27785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 9].length) (baseStart_27785 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_27785 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_27785 prefixEnd_27785 := by exact prefixLift 27785
  have htrace : WordTrace (prefixWord ++ tailWord_27785) baseStart_27785 baseEnd_27785 := by
    simpa [prefixWord, tailWord_27785, baseEnd_27785] using wordTrace_append hprefix tailTrace_27785
  have hstable : (prefixWord ++ tailWord_27785).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27785).length < 2 ^ (prefixWord ++ tailWord_27785).sum := by decide
  have hdescent : baseEnd_27785 < baseStart_27785 := by decide
  rcases family_descends (prefixWord ++ tailWord_27785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27802 : List Nat := [3, 1, 1, 5, 1, 1, 1, 8]
def baseStart_27802 : Nat := 118140960795 + 27802 * 2 ^ 59
def prefixEnd_27802 : Nat := 4983230072969 + 3 ^ 40 * 27802 * 2
def baseEnd_27802 : Nat := 2114931726874882703281

theorem tailTrace_27802 : CollatzResearch.WordTrace tailWord_27802 prefixEnd_27802 2114931726874882703281 := by
  unfold tailWord_27802
  simp only [CollatzResearch.WordTrace]
  refine ⟨253505561321394262171415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 676014830190384699123773 253505561321394262171415)
  ·
    refine ⟨380258341982091393257123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253505561321394262171415 380258341982091393257123)
    ·
      refine ⟨570387512973137089885685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380258341982091393257123 570387512973137089885685)
      ·
        refine ⟨53473829341231602176783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 570387512973137089885685 53473829341231602176783)
        ·
          refine ⟨80210744011847403265175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53473829341231602176783 80210744011847403265175)
          ·
            refine ⟨120316116017771104897763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80210744011847403265175 120316116017771104897763)
            ·
              refine ⟨180474174026656657346645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120316116017771104897763 180474174026656657346645)
              ·
                refine ⟨2114931726874882703281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 180474174026656657346645 2114931726874882703281)
                ·
                  rfl

theorem cell21_27802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 8].length) (baseStart_27802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_27802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_27802 prefixEnd_27802 := by exact prefixLift 27802
  have htrace : WordTrace (prefixWord ++ tailWord_27802) baseStart_27802 baseEnd_27802 := by
    simpa [prefixWord, tailWord_27802, baseEnd_27802] using wordTrace_append hprefix tailTrace_27802
  have hstable : (prefixWord ++ tailWord_27802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27802).length < 2 ^ (prefixWord ++ tailWord_27802).sum := by decide
  have hdescent : baseEnd_27802 < baseStart_27802 := by decide
  rcases family_descends (prefixWord ++ tailWord_27802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27842 : List Nat := [3, 5, 1, 1, 2, 2, 2, 2, 3]
def baseStart_27842 : Nat := 118140960795 + 27842 * 2 ^ 59
def prefixEnd_27842 : Nat := 4983230072969 + 3 ^ 40 * 27842 * 2
def baseEnd_27842 : Nat := 6353923725593467443095

theorem tailTrace_27842 : CollatzResearch.WordTrace tailWord_27842 prefixEnd_27842 6353923725593467443095 := by
  unfold tailWord_27842
  simp only [CollatzResearch.WordTrace]
  refine ⟨253870291285165970035445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 676987443427109253427853 253870291285165970035445)
  ·
    refine ⟨23800339807984309690823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 253870291285165970035445 23800339807984309690823)
    ·
      refine ⟨35700509711976464536235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23800339807984309690823 35700509711976464536235)
      ·
        refine ⟨53550764567964696804353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35700509711976464536235 53550764567964696804353)
        ·
          refine ⟨40163073425973522603265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53550764567964696804353 40163073425973522603265)
          ·
            refine ⟨30122305069480141952449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40163073425973522603265 30122305069480141952449)
            ·
              refine ⟨22591728802110106464337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30122305069480141952449 22591728802110106464337)
              ·
                refine ⟨16943796601582579848253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22591728802110106464337 16943796601582579848253)
                ·
                  refine ⟨6353923725593467443095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16943796601582579848253 6353923725593467443095)
                  ·
                    rfl

theorem cell21_27842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_27842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_27842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_27842 prefixEnd_27842 := by exact prefixLift 27842
  have htrace : WordTrace (prefixWord ++ tailWord_27842) baseStart_27842 baseEnd_27842 := by
    simpa [prefixWord, tailWord_27842, baseEnd_27842] using wordTrace_append hprefix tailTrace_27842
  have hstable : (prefixWord ++ tailWord_27842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27842).length < 2 ^ (prefixWord ++ tailWord_27842).sum := by decide
  have hdescent : baseEnd_27842 < baseStart_27842 := by decide
  rcases family_descends (prefixWord ++ tailWord_27842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27850 : List Nat := [3, 1, 2, 1, 3, 3, 1, 4, 3]
def baseStart_27850 : Nat := 118140960795 + 27850 * 2 ^ 59
def prefixEnd_27850 : Nat := 4983230072969 + 3 ^ 40 * 27850 * 2
def baseEnd_27850 : Nat := 6355749434587231309745

theorem tailTrace_27850 : CollatzResearch.WordTrace tailWord_27850 prefixEnd_27850 6355749434587231309745 := by
  unfold tailWord_27850
  simp only [CollatzResearch.WordTrace]
  refine ⟨253943237277920311608251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 677181966074454164288669 253943237277920311608251)
  ·
    refine ⟨380914855916880467412377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253943237277920311608251 380914855916880467412377)
    ·
      refine ⟨285686141937660350559283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380914855916880467412377 285686141937660350559283)
      ·
        refine ⟨428529212906490525838925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285686141937660350559283 428529212906490525838925)
        ·
          refine ⟨160698454839933947189597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 428529212906490525838925 160698454839933947189597)
          ·
            refine ⟨60261920564975230196099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160698454839933947189597 60261920564975230196099)
            ·
              refine ⟨90392880847462845294149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60261920564975230196099 90392880847462845294149)
              ·
                refine ⟨16948665158899283492653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90392880847462845294149 16948665158899283492653)
                ·
                  refine ⟨6355749434587231309745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16948665158899283492653 6355749434587231309745)
                  ·
                    rfl

theorem cell21_27850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 4, 3].length) (baseStart_27850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_27850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_27850 prefixEnd_27850 := by exact prefixLift 27850
  have htrace : WordTrace (prefixWord ++ tailWord_27850) baseStart_27850 baseEnd_27850 := by
    simpa [prefixWord, tailWord_27850, baseEnd_27850] using wordTrace_append hprefix tailTrace_27850
  have hstable : (prefixWord ++ tailWord_27850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27850).length < 2 ^ (prefixWord ++ tailWord_27850).sum := by decide
  have hdescent : baseEnd_27850 < baseStart_27850 := by decide
  rcases family_descends (prefixWord ++ tailWord_27850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27853 : List Nat := [1, 6, 2, 2, 1, 2, 1, 6]
def baseStart_27853 : Nat := 118140960795 + 27853 * 2 ^ 59
def prefixEnd_27853 : Nat := 4983230072969 + 3 ^ 40 * 27853 * 2
def baseEnd_27853 : Nat := 2118811358486630919913

theorem tailTrace_27853 : CollatzResearch.WordTrace tailWord_27853 prefixEnd_27853 2118811358486630919913 := by
  unfold tailWord_27853
  simp only [CollatzResearch.WordTrace]
  refine ⟨1015882368100812758792213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 677254912067208505861475 1015882368100812758792213)
  ·
    refine ⟨47619486004725598068385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1015882368100812758792213 47619486004725598068385)
    ·
      refine ⟨35714614503544198551289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47619486004725598068385 35714614503544198551289)
      ·
        refine ⟨26785960877658148913467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35714614503544198551289 26785960877658148913467)
        ·
          refine ⟨40178941316487223370201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26785960877658148913467 40178941316487223370201)
          ·
            refine ⟨30134205987365417527651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40178941316487223370201 30134205987365417527651)
            ·
              refine ⟨45201308981048126291477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30134205987365417527651 45201308981048126291477)
              ·
                refine ⟨2118811358486630919913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45201308981048126291477 2118811358486630919913)
                ·
                  rfl

theorem cell21_27853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 6].length) (baseStart_27853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_27853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_27853 prefixEnd_27853 := by exact prefixLift 27853
  have htrace : WordTrace (prefixWord ++ tailWord_27853) baseStart_27853 baseEnd_27853 := by
    simpa [prefixWord, tailWord_27853, baseEnd_27853] using wordTrace_append hprefix tailTrace_27853
  have hstable : (prefixWord ++ tailWord_27853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27853).length < 2 ^ (prefixWord ++ tailWord_27853).sum := by decide
  have hdescent : baseEnd_27853 < baseStart_27853 := by decide
  rcases family_descends (prefixWord ++ tailWord_27853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27909 : List Nat := [1, 3, 1, 1, 2, 1, 3, 6, 3]
def baseStart_27909 : Nat := 118140960795 + 27909 * 2 ^ 59
def prefixEnd_27909 : Nat := 4983230072969 + 3 ^ 40 * 27909 * 2
def baseEnd_27909 : Nat := 6369214038416239826291

theorem tailTrace_27909 : CollatzResearch.WordTrace tailWord_27909 prefixEnd_27909 6369214038416239826291 := by
  unfold tailWord_27909
  simp only [CollatzResearch.WordTrace]
  refine ⟨1017924855897934322830781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 678616570598622881887187 1017924855897934322830781)
  ·
    refine ⟨381721820961725371061543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1017924855897934322830781 381721820961725371061543)
    ·
      refine ⟨572582731442588056592315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381721820961725371061543 572582731442588056592315)
      ·
        refine ⟨858874097163882084888473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 572582731442588056592315 858874097163882084888473)
        ·
          refine ⟨644155572872911563666355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 858874097163882084888473 644155572872911563666355)
          ·
            refine ⟨966233359309367345499533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 644155572872911563666355 966233359309367345499533)
            ·
              refine ⟨362337509741012754562325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 966233359309367345499533 362337509741012754562325)
              ·
                refine ⟨16984570769109972870109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 362337509741012754562325 16984570769109972870109)
                ·
                  refine ⟨6369214038416239826291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16984570769109972870109 6369214038416239826291)
                  ·
                    rfl

theorem cell21_27909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 6, 3].length) (baseStart_27909 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_27909 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_27909 prefixEnd_27909 := by exact prefixLift 27909
  have htrace : WordTrace (prefixWord ++ tailWord_27909) baseStart_27909 baseEnd_27909 := by
    simpa [prefixWord, tailWord_27909, baseEnd_27909] using wordTrace_append hprefix tailTrace_27909
  have hstable : (prefixWord ++ tailWord_27909).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27909).length < 2 ^ (prefixWord ++ tailWord_27909).sum := by decide
  have hdescent : baseEnd_27909 < baseStart_27909 := by decide
  rcases family_descends (prefixWord ++ tailWord_27909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_27954 : List Nat := [3, 2, 1, 1, 4, 3, 7]
def baseStart_27954 : Nat := 118140960795 + 27954 * 2 ^ 59
def prefixEnd_27954 : Nat := 4983230072969 + 3 ^ 40 * 27954 * 2
def baseEnd_27954 : Nat := 708831516834017952911

theorem tailTrace_27954 : CollatzResearch.WordTrace tailWord_27954 prefixEnd_27954 708831516834017952911 := by
  unfold tailWord_27954
  simp only [CollatzResearch.WordTrace]
  refine ⟨254891535183726752054729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 679710760489938005479277 254891535183726752054729)
  ·
    refine ⟨191168651387795064041047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254891535183726752054729 191168651387795064041047)
    ·
      refine ⟨286752977081692596061571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191168651387795064041047 286752977081692596061571)
      ·
        refine ⟨430129465622538894092357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286752977081692596061571 430129465622538894092357)
        ·
          refine ⟨80649274804226042642317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 430129465622538894092357 80649274804226042642317)
          ·
            refine ⟨30243478051584765990869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80649274804226042642317 30243478051584765990869)
            ·
              refine ⟨708831516834017952911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 30243478051584765990869 708831516834017952911)
              ·
                rfl

theorem cell21_27954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 7].length) (baseStart_27954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_27954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_27954 prefixEnd_27954 := by exact prefixLift 27954
  have htrace : WordTrace (prefixWord ++ tailWord_27954) baseStart_27954 baseEnd_27954 := by
    simpa [prefixWord, tailWord_27954, baseEnd_27954] using wordTrace_append hprefix tailTrace_27954
  have hstable : (prefixWord ++ tailWord_27954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_27954).length < 2 ^ (prefixWord ++ tailWord_27954).sum := by decide
  have hdescent : baseEnd_27954 < baseStart_27954 := by decide
  rcases family_descends (prefixWord ++ tailWord_27954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28002 : List Nat := [3, 3, 2, 1, 1, 1, 2, 5, 3]
def baseStart_28002 : Nat := 118140960795 + 28002 * 2 ^ 59
def prefixEnd_28002 : Nat := 4983230072969 + 3 ^ 40 * 28002 * 2
def baseEnd_28002 : Nat := 6390437905468744776101

theorem tailTrace_28002 : CollatzResearch.WordTrace tailWord_28002 prefixEnd_28002 6390437905468744776101 := by
  unfold tailWord_28002
  simp only [CollatzResearch.WordTrace]
  refine ⟨255329211140252801491565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 680877896374007470644173 255329211140252801491565)
  ·
    refine ⟨95748454177594800559337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255329211140252801491565 95748454177594800559337)
    ·
      refine ⟨71811340633196100419503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95748454177594800559337 71811340633196100419503)
      ·
        refine ⟨107717010949794150629255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71811340633196100419503 107717010949794150629255)
        ·
          refine ⟨161575516424691225943883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107717010949794150629255 161575516424691225943883)
          ·
            refine ⟨242363274637036838915825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161575516424691225943883 242363274637036838915825)
            ·
              refine ⟨181772455977777629186869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242363274637036838915825 181772455977777629186869)
              ·
                refine ⟨17041167747916652736269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 181772455977777629186869 17041167747916652736269)
                ·
                  refine ⟨6390437905468744776101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17041167747916652736269 6390437905468744776101)
                  ·
                    rfl

theorem cell21_28002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_28002 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_28002 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_28002 prefixEnd_28002 := by exact prefixLift 28002
  have htrace : WordTrace (prefixWord ++ tailWord_28002) baseStart_28002 baseEnd_28002 := by
    simpa [prefixWord, tailWord_28002, baseEnd_28002] using wordTrace_append hprefix tailTrace_28002
  have hstable : (prefixWord ++ tailWord_28002).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28002).length < 2 ^ (prefixWord ++ tailWord_28002).sum := by decide
  have hdescent : baseEnd_28002 < baseStart_28002 := by decide
  rcases family_descends (prefixWord ++ tailWord_28002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28013 : List Nat := [1, 5, 1, 1, 1, 12]
def baseStart_28013 : Nat := 118140960795 + 28013 * 2 ^ 59
def prefixEnd_28013 : Nat := 4983230072969 + 3 ^ 40 * 28013 * 2
def baseEnd_28013 : Nat := 236775861308710003435

theorem tailTrace_28013 : CollatzResearch.WordTrace tailWord_28013 prefixEnd_28013 236775861308710003435 := by
  unfold tailWord_28013
  simp only [CollatzResearch.WordTrace]
  refine ⟨1021718047521160084616693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 681145365014106723077795 1021718047521160084616693)
  ·
    refine ⟨95786066955108757932815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1021718047521160084616693 95786066955108757932815)
    ·
      refine ⟨143679100432663136899223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95786066955108757932815 143679100432663136899223)
      ·
        refine ⟨215518650648994705348835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143679100432663136899223 215518650648994705348835)
        ·
          refine ⟨323277975973492058023253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215518650648994705348835 323277975973492058023253)
          ·
            refine ⟨236775861308710003435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 323277975973492058023253 236775861308710003435)
            ·
              rfl

theorem cell21_28013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 12].length) (baseStart_28013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_28013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_28013 prefixEnd_28013 := by exact prefixLift 28013
  have htrace : WordTrace (prefixWord ++ tailWord_28013) baseStart_28013 baseEnd_28013 := by
    simpa [prefixWord, tailWord_28013, baseEnd_28013] using wordTrace_append hprefix tailTrace_28013
  have hstable : (prefixWord ++ tailWord_28013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28013).length < 2 ^ (prefixWord ++ tailWord_28013).sum := by decide
  have hdescent : baseEnd_28013 < baseStart_28013 := by decide
  rcases family_descends (prefixWord ++ tailWord_28013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28044 : List Nat := [2, 2, 1, 2, 1, 3, 3, 2, 5]
def baseStart_28044 : Nat := 118140960795 + 28044 * 2 ^ 59
def prefixEnd_28044 : Nat := 4983230072969 + 3 ^ 40 * 28044 * 2
def baseEnd_28044 : Nat := 6400022877686005076015

theorem tailTrace_28044 : CollatzResearch.WordTrace tailWord_28044 prefixEnd_28044 6400022877686005076015 := by
  unfold tailWord_28044
  simp only [CollatzResearch.WordTrace]
  refine ⟨511424355204426189497593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 681899140272568252663457 511424355204426189497593)
  ·
    refine ⟨383568266403319642123195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 511424355204426189497593 383568266403319642123195)
    ·
      refine ⟨575352399604979463184793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383568266403319642123195 575352399604979463184793)
      ·
        refine ⟨431514299703734597388595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 575352399604979463184793 431514299703734597388595)
        ·
          refine ⟨647271449555601896082893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431514299703734597388595 647271449555601896082893)
          ·
            refine ⟨242726793583350711031085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 647271449555601896082893 242726793583350711031085)
            ·
              refine ⟨91022547593756516636657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 242726793583350711031085 91022547593756516636657)
              ·
                refine ⟨68266910695317387477493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91022547593756516636657 68266910695317387477493)
                ·
                  refine ⟨6400022877686005076015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68266910695317387477493 6400022877686005076015)
                  ·
                    rfl

theorem cell21_28044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 5].length) (baseStart_28044 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_28044 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_28044 prefixEnd_28044 := by exact prefixLift 28044
  have htrace : WordTrace (prefixWord ++ tailWord_28044) baseStart_28044 baseEnd_28044 := by
    simpa [prefixWord, tailWord_28044, baseEnd_28044] using wordTrace_append hprefix tailTrace_28044
  have hstable : (prefixWord ++ tailWord_28044).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28044).length < 2 ^ (prefixWord ++ tailWord_28044).sum := by decide
  have hdescent : baseEnd_28044 < baseStart_28044 := by decide
  rcases family_descends (prefixWord ++ tailWord_28044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28106 : List Nat := [3, 1, 2, 1, 2, 3, 4, 5]
def baseStart_28106 : Nat := 118140960795 + 28106 * 2 ^ 59
def prefixEnd_28106 : Nat := 4983230072969 + 3 ^ 40 * 28106 * 2
def baseEnd_28106 : Nat := 2138057374129225014185

theorem tailTrace_28106 : CollatzResearch.WordTrace tailWord_28106 prefixEnd_28106 2138057374129225014185 := by
  unfold tailWord_28106
  simp only [CollatzResearch.WordTrace]
  refine ⟨256277509046059241938043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 683406690789491311834781 256277509046059241938043)
  ·
    refine ⟨384416263569088862907065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256277509046059241938043 384416263569088862907065)
    ·
      refine ⟨288312197676816647180299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384416263569088862907065 288312197676816647180299)
      ·
        refine ⟨432468296515224970770449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288312197676816647180299 432468296515224970770449)
        ·
          refine ⟨324351222386418728077837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 432468296515224970770449 324351222386418728077837)
          ·
            refine ⟨121631708394907023029189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 324351222386418728077837 121631708394907023029189)
            ·
              refine ⟨22805945324045066817973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121631708394907023029189 22805945324045066817973)
              ·
                refine ⟨2138057374129225014185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22805945324045066817973 2138057374129225014185)
                ·
                  rfl

theorem cell21_28106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 5].length) (baseStart_28106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_28106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_28106 prefixEnd_28106 := by exact prefixLift 28106
  have htrace : WordTrace (prefixWord ++ tailWord_28106) baseStart_28106 baseEnd_28106 := by
    simpa [prefixWord, tailWord_28106, baseEnd_28106] using wordTrace_append hprefix tailTrace_28106
  have hstable : (prefixWord ++ tailWord_28106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28106).length < 2 ^ (prefixWord ++ tailWord_28106).sum := by decide
  have hdescent : baseEnd_28106 < baseStart_28106 := by decide
  rcases family_descends (prefixWord ++ tailWord_28106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28210 : List Nat := [3, 2, 1, 1, 2, 1, 1, 2, 8]
def baseStart_28210 : Nat := 118140960795 + 28210 * 2 ^ 59
def prefixEnd_28210 : Nat := 4983230072969 + 3 ^ 40 * 28210 * 2
def baseEnd_28210 : Nat := 6437906339306605309009

theorem tailTrace_28210 : CollatzResearch.WordTrace tailWord_28210 prefixEnd_28210 6437906339306605309009 := by
  unfold tailWord_28210
  simp only [CollatzResearch.WordTrace]
  refine ⟨257225806951865682384521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 685935485204975153025389 257225806951865682384521)
  ·
    refine ⟨192919355213899261788391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 257225806951865682384521 192919355213899261788391)
    ·
      refine ⟨289379032820848892682587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192919355213899261788391 289379032820848892682587)
      ·
        refine ⟨434068549231273339023881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289379032820848892682587 434068549231273339023881)
        ·
          refine ⟨325551411923455004267911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 434068549231273339023881 325551411923455004267911)
          ·
            refine ⟨488327117885182506401867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325551411923455004267911 488327117885182506401867)
            ·
              refine ⟨732490676827773759602801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 488327117885182506401867 732490676827773759602801)
              ·
                refine ⟨549368007620830319702101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 732490676827773759602801 549368007620830319702101)
                ·
                  refine ⟨6437906339306605309009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 549368007620830319702101 6437906339306605309009)
                  ·
                    rfl

theorem cell21_28210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_28210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_28210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_28210 prefixEnd_28210 := by exact prefixLift 28210
  have htrace : WordTrace (prefixWord ++ tailWord_28210) baseStart_28210 baseEnd_28210 := by
    simpa [prefixWord, tailWord_28210, baseEnd_28210] using wordTrace_append hprefix tailTrace_28210
  have hstable : (prefixWord ++ tailWord_28210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28210).length < 2 ^ (prefixWord ++ tailWord_28210).sum := by decide
  have hdescent : baseEnd_28210 < baseStart_28210 := by decide
  rcases family_descends (prefixWord ++ tailWord_28210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28272 : List Nat := [2, 1, 1, 1, 6, 1, 2, 2, 5]
def baseStart_28272 : Nat := 118140960795 + 28272 * 2 ^ 59
def prefixEnd_28272 : Nat := 4983230072969 + 3 ^ 40 * 28272 * 2
def baseEnd_28272 : Nat := 6452055584008275275549

theorem tailTrace_28272 : CollatzResearch.WordTrace tailWord_28272 prefixEnd_28272 6452055584008275275549 := by
  unfold tailWord_28272
  simp only [CollatzResearch.WordTrace]
  refine ⟨515582276791423659147535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 687443035721898212196713 515582276791423659147535)
  ·
    refine ⟨773373415187135488721303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 515582276791423659147535 773373415187135488721303)
    ·
      refine ⟨1160060122780703233081955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 773373415187135488721303 1160060122780703233081955)
      ·
        refine ⟨1740090184171054849622933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1160060122780703233081955 1740090184171054849622933)
        ·
          refine ⟨81566727383018196076075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1740090184171054849622933 81566727383018196076075)
          ·
            refine ⟨122350091074527294114113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81566727383018196076075 122350091074527294114113)
            ·
              refine ⟨91762568305895470585585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122350091074527294114113 91762568305895470585585)
              ·
                refine ⟨68821926229421602939189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91762568305895470585585 68821926229421602939189)
                ·
                  refine ⟨6452055584008275275549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68821926229421602939189 6452055584008275275549)
                  ·
                    rfl

theorem cell21_28272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 5].length) (baseStart_28272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_28272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_28272 prefixEnd_28272 := by exact prefixLift 28272
  have htrace : WordTrace (prefixWord ++ tailWord_28272) baseStart_28272 baseEnd_28272 := by
    simpa [prefixWord, tailWord_28272, baseEnd_28272] using wordTrace_append hprefix tailTrace_28272
  have hstable : (prefixWord ++ tailWord_28272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28272).length < 2 ^ (prefixWord ++ tailWord_28272).sum := by decide
  have hdescent : baseEnd_28272 < baseStart_28272 := by decide
  rcases family_descends (prefixWord ++ tailWord_28272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28306 : List Nat := [3, 2, 3, 1, 3, 2, 1, 1, 5]
def baseStart_28306 : Nat := 118140960795 + 28306 * 2 ^ 59
def prefixEnd_28306 : Nat := 4983230072969 + 3 ^ 40 * 28306 * 2
def baseEnd_28306 : Nat := 6459814847231771708813

theorem tailTrace_28306 : CollatzResearch.WordTrace tailWord_28306 prefixEnd_28306 6459814847231771708813 := by
  unfold tailWord_28306
  simp only [CollatzResearch.WordTrace]
  refine ⟨258101158864917781258193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 688269756973114083355181 258101158864917781258193)
  ·
    refine ⟨193575869148688335943645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258101158864917781258193 193575869148688335943645)
    ·
      refine ⟨72590950930758125978867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193575869148688335943645 72590950930758125978867)
      ·
        refine ⟨108886426396137188968301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72590950930758125978867 108886426396137188968301)
        ·
          refine ⟨40832409898551445863113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108886426396137188968301 40832409898551445863113)
          ·
            refine ⟨30624307423913584397335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40832409898551445863113 30624307423913584397335)
            ·
              refine ⟨45936461135870376596003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30624307423913584397335 45936461135870376596003)
              ·
                refine ⟨68904691703805564894005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45936461135870376596003 68904691703805564894005)
                ·
                  refine ⟨6459814847231771708813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68904691703805564894005 6459814847231771708813)
                  ·
                    rfl

theorem cell21_28306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_28306 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_28306 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_28306 prefixEnd_28306 := by exact prefixLift 28306
  have htrace : WordTrace (prefixWord ++ tailWord_28306) baseStart_28306 baseEnd_28306 := by
    simpa [prefixWord, tailWord_28306, baseEnd_28306] using wordTrace_append hprefix tailTrace_28306
  have hstable : (prefixWord ++ tailWord_28306).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28306).length < 2 ^ (prefixWord ++ tailWord_28306).sum := by decide
  have hdescent : baseEnd_28306 < baseStart_28306 := by decide
  rcases family_descends (prefixWord ++ tailWord_28306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28320 : List Nat := [2, 1, 1, 4, 3, 1, 4, 1, 4]
def baseStart_28320 : Nat := 118140960795 + 28320 * 2 ^ 59
def prefixEnd_28320 : Nat := 4983230072969 + 3 ^ 40 * 28320 * 2
def baseEnd_28320 : Nat := 6463009837970858475451

theorem tailTrace_28320 : CollatzResearch.WordTrace tailWord_28320 prefixEnd_28320 6463009837970858475451 := by
  unfold tailWord_28320
  simp only [CollatzResearch.WordTrace]
  refine ⟨516457628704475758021207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 688610171605967677361609 516457628704475758021207)
  ·
    refine ⟨774686443056713637031811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 516457628704475758021207 774686443056713637031811)
    ·
      refine ⟨1162029664585070455547717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 774686443056713637031811 1162029664585070455547717)
      ·
        refine ⟨217880562109700710415197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1162029664585070455547717 217880562109700710415197)
        ·
          refine ⟨81705210791137766405699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217880562109700710415197 81705210791137766405699)
          ·
            refine ⟨122557816186706649608549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81705210791137766405699 122557816186706649608549)
            ·
              refine ⟨22979590535007496801603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122557816186706649608549 22979590535007496801603)
              ·
                refine ⟨34469385802511245202405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22979590535007496801603 34469385802511245202405)
                ·
                  refine ⟨6463009837970858475451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34469385802511245202405 6463009837970858475451)
                  ·
                    rfl

theorem cell21_28320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 1, 4].length) (baseStart_28320 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_28320 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_28320 prefixEnd_28320 := by exact prefixLift 28320
  have htrace : WordTrace (prefixWord ++ tailWord_28320) baseStart_28320 baseEnd_28320 := by
    simpa [prefixWord, tailWord_28320, baseEnd_28320] using wordTrace_append hprefix tailTrace_28320
  have hstable : (prefixWord ++ tailWord_28320).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28320).length < 2 ^ (prefixWord ++ tailWord_28320).sum := by decide
  have hdescent : baseEnd_28320 < baseStart_28320 := by decide
  rcases family_descends (prefixWord ++ tailWord_28320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28424 : List Nat := [2, 1, 3, 2, 2, 1, 4, 1, 5]
def baseStart_28424 : Nat := 118140960795 + 28424 * 2 ^ 59
def prefixEnd_28424 : Nat := 4983230072969 + 3 ^ 40 * 28424 * 2
def baseEnd_28424 : Nat := 6486744054889788741905

theorem tailTrace_28424 : CollatzResearch.WordTrace tailWord_28424 prefixEnd_28424 6486744054889788741905 := by
  unfold tailWord_28424
  simp only [CollatzResearch.WordTrace]
  refine ⟨518354224516088638914163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 691138966021451518552217 518354224516088638914163)
  ·
    refine ⟨777531336774132958371245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 518354224516088638914163 777531336774132958371245)
    ·
      refine ⟨291574251290299859389217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 777531336774132958371245 291574251290299859389217)
      ·
        refine ⟨218680688467724894541913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291574251290299859389217 218680688467724894541913)
        ·
          refine ⟨164010516350793670906435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218680688467724894541913 164010516350793670906435)
          ·
            refine ⟨246015774526190506359653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164010516350793670906435 246015774526190506359653)
            ·
              refine ⟨46127957723660719942435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 246015774526190506359653 46127957723660719942435)
              ·
                refine ⟨69191936585491079913653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46127957723660719942435 69191936585491079913653)
                ·
                  refine ⟨6486744054889788741905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69191936585491079913653 6486744054889788741905)
                  ·
                    rfl

theorem cell21_28424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 5].length) (baseStart_28424 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_28424 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_28424 prefixEnd_28424 := by exact prefixLift 28424
  have htrace : WordTrace (prefixWord ++ tailWord_28424) baseStart_28424 baseEnd_28424 := by
    simpa [prefixWord, tailWord_28424, baseEnd_28424] using wordTrace_append hprefix tailTrace_28424
  have hstable : (prefixWord ++ tailWord_28424).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28424).length < 2 ^ (prefixWord ++ tailWord_28424).sum := by decide
  have hdescent : baseEnd_28424 < baseStart_28424 := by decide
  rcases family_descends (prefixWord ++ tailWord_28424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28593 : List Nat := [1, 2, 2, 4, 2, 1, 2, 4, 3]
def baseStart_28593 : Nat := 118140960795 + 28593 * 2 ^ 59
def prefixEnd_28593 : Nat := 4983230072969 + 3 ^ 40 * 28593 * 2
def baseEnd_28593 : Nat := 6525312157383050424893

theorem tailTrace_28593 : CollatzResearch.WordTrace tailWord_28593 prefixEnd_28593 6525312157383050424893 := by
  unfold tailWord_28593
  simp only [CollatzResearch.WordTrace]
  refine ⟨1042872385419919140730433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 695248256946612760486955 1042872385419919140730433)
  ·
    refine ⟨782154289064939355547825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1042872385419919140730433 782154289064939355547825)
    ·
      refine ⟨586615716798704516660869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 782154289064939355547825 586615716798704516660869)
      ·
        refine ⟨109990446899757096873913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 586615716798704516660869 109990446899757096873913)
        ·
          refine ⟨82492835174817822655435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109990446899757096873913 82492835174817822655435)
          ·
            refine ⟨123739252762226733983153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82492835174817822655435 123739252762226733983153)
            ·
              refine ⟨92804439571670050487365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123739252762226733983153 92804439571670050487365)
              ·
                refine ⟨17400832419688134466381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92804439571670050487365 17400832419688134466381)
                ·
                  refine ⟨6525312157383050424893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17400832419688134466381 6525312157383050424893)
                  ·
                    rfl

theorem cell21_28593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 4, 3].length) (baseStart_28593 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_28593 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_28593 prefixEnd_28593 := by exact prefixLift 28593
  have htrace : WordTrace (prefixWord ++ tailWord_28593) baseStart_28593 baseEnd_28593 := by
    simpa [prefixWord, tailWord_28593, baseEnd_28593] using wordTrace_append hprefix tailTrace_28593
  have hstable : (prefixWord ++ tailWord_28593).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28593).length < 2 ^ (prefixWord ++ tailWord_28593).sum := by decide
  have hdescent : baseEnd_28593 < baseStart_28593 := by decide
  rcases family_descends (prefixWord ++ tailWord_28593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28607 : List Nat := [1, 1, 2, 2, 2, 1, 7, 1, 4]
def baseStart_28607 : Nat := 118140960795 + 28607 * 2 ^ 59
def prefixEnd_28607 : Nat := 4983230072969 + 3 ^ 40 * 28607 * 2
def baseEnd_28607 : Nat := 6528507148122137191531

theorem tailTrace_28607 : CollatzResearch.WordTrace tailWord_28607 prefixEnd_28607 6528507148122137191531 := by
  unfold tailWord_28607
  simp only [CollatzResearch.WordTrace]
  refine ⟨1043383007369199531740075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 695588671579466354493383 1043383007369199531740075)
  ·
    refine ⟨1565074511053799297610113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1043383007369199531740075 1565074511053799297610113)
    ·
      refine ⟨1173805883290349473207585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1565074511053799297610113 1173805883290349473207585)
      ·
        refine ⟨880354412467762104905689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1173805883290349473207585 880354412467762104905689)
        ·
          refine ⟨660265809350821578679267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 880354412467762104905689 660265809350821578679267)
          ·
            refine ⟨990398714026232368018901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 660265809350821578679267 990398714026232368018901)
            ·
              refine ⟨23212469859989821125443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 990398714026232368018901 23212469859989821125443)
              ·
                refine ⟨34818704789984731688165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23212469859989821125443 34818704789984731688165)
                ·
                  refine ⟨6528507148122137191531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34818704789984731688165 6528507148122137191531)
                  ·
                    rfl

theorem cell21_28607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 1, 4].length) (baseStart_28607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_28607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_28607 prefixEnd_28607 := by exact prefixLift 28607
  have htrace : WordTrace (prefixWord ++ tailWord_28607) baseStart_28607 baseEnd_28607 := by
    simpa [prefixWord, tailWord_28607, baseEnd_28607] using wordTrace_append hprefix tailTrace_28607
  have hstable : (prefixWord ++ tailWord_28607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28607).length < 2 ^ (prefixWord ++ tailWord_28607).sum := by decide
  have hdescent : baseEnd_28607 < baseStart_28607 := by decide
  rcases family_descends (prefixWord ++ tailWord_28607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28652 : List Nat := [2, 2, 1, 1, 2, 1, 1, 8, 3]
def baseStart_28652 : Nat := 118140960795 + 28652 * 2 ^ 59
def prefixEnd_28652 : Nat := 4983230072969 + 3 ^ 40 * 28652 * 2
def baseEnd_28652 : Nat := 6538776761212058941439

theorem tailTrace_28652 : CollatzResearch.WordTrace tailWord_28652 prefixEnd_28652 6538776761212058941439 := by
  unfold tailWord_28652
  simp only [CollatzResearch.WordTrace]
  refine ⟨522512146103086108564105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 696682861470781478085473 522512146103086108564105)
  ·
    refine ⟨391884109577314581423079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 522512146103086108564105 391884109577314581423079)
    ·
      refine ⟨587826164365971872134619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391884109577314581423079 587826164365971872134619)
      ·
        refine ⟨881739246548957808201929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 587826164365971872134619 881739246548957808201929)
        ·
          refine ⟨661304434911718356151447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 881739246548957808201929 661304434911718356151447)
          ·
            refine ⟨991956652367577534227171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 661304434911718356151447 991956652367577534227171)
            ·
              refine ⟨1487934978551366301340757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 991956652367577534227171 1487934978551366301340757)
              ·
                refine ⟨17436738029898823843837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1487934978551366301340757 17436738029898823843837)
                ·
                  refine ⟨6538776761212058941439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17436738029898823843837 6538776761212058941439)
                  ·
                    rfl

theorem cell21_28652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 8, 3].length) (baseStart_28652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_28652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_28652 prefixEnd_28652 := by exact prefixLift 28652
  have htrace : WordTrace (prefixWord ++ tailWord_28652) baseStart_28652 baseEnd_28652 := by
    simpa [prefixWord, tailWord_28652, baseEnd_28652] using wordTrace_append hprefix tailTrace_28652
  have hstable : (prefixWord ++ tailWord_28652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28652).length < 2 ^ (prefixWord ++ tailWord_28652).sum := by decide
  have hdescent : baseEnd_28652 < baseStart_28652 := by decide
  rcases family_descends (prefixWord ++ tailWord_28652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28680 : List Nat := [2, 1, 3, 2, 1, 2, 1, 9]
def baseStart_28680 : Nat := 118140960795 + 28680 * 2 ^ 59
def prefixEnd_28680 : Nat := 4983230072969 + 3 ^ 40 * 28680 * 2
def baseEnd_28680 : Nat := 2181722247563410824905

theorem tailTrace_28680 : CollatzResearch.WordTrace tailWord_28680 prefixEnd_28680 2181722247563410824905 := by
  unfold tailWord_28680
  simp only [CollatzResearch.WordTrace]
  refine ⟨523022768052366499573747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 697363690736488666098329 523022768052366499573747)
  ·
    refine ⟨784534152078549749360621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 523022768052366499573747 784534152078549749360621)
    ·
      refine ⟨294200307029456156010233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 784534152078549749360621 294200307029456156010233)
      ·
        refine ⟨220650230272092117007675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294200307029456156010233 220650230272092117007675)
        ·
          refine ⟨330975345408138175511513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220650230272092117007675 330975345408138175511513)
          ·
            refine ⟨248231509056103631633635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 330975345408138175511513 248231509056103631633635)
            ·
              refine ⟨372347263584155447450453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248231509056103631633635 372347263584155447450453)
              ·
                refine ⟨2181722247563410824905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 372347263584155447450453 2181722247563410824905)
                ·
                  rfl

theorem cell21_28680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 9].length) (baseStart_28680 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_28680 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_28680 prefixEnd_28680 := by exact prefixLift 28680
  have htrace : WordTrace (prefixWord ++ tailWord_28680) baseStart_28680 baseEnd_28680 := by
    simpa [prefixWord, tailWord_28680, baseEnd_28680] using wordTrace_append hprefix tailTrace_28680
  have hstable : (prefixWord ++ tailWord_28680).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28680).length < 2 ^ (prefixWord ++ tailWord_28680).sum := by decide
  have hdescent : baseEnd_28680 < baseStart_28680 := by decide
  rcases family_descends (prefixWord ++ tailWord_28680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28714 : List Nat := [3, 1, 4, 1, 2, 3, 1, 6]
def baseStart_28714 : Nat := 118140960795 + 28714 * 2 ^ 59
def prefixEnd_28714 : Nat := 4983230072969 + 3 ^ 40 * 28714 * 2
def baseEnd_28714 : Nat := 2184308668637909635993

theorem tailTrace_28714 : CollatzResearch.WordTrace tailWord_28714 prefixEnd_28714 2184308668637909635993 := by
  unfold tailWord_28714
  simp only [CollatzResearch.WordTrace]
  refine ⟨261821404495389201471299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 698190411987704537256797 261821404495389201471299)
  ·
    refine ⟨392732106743083802206949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261821404495389201471299 392732106743083802206949)
    ·
      refine ⟨73637270014328212913803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 392732106743083802206949 73637270014328212913803)
      ·
        refine ⟨110455905021492319370705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73637270014328212913803 110455905021492319370705)
        ·
          refine ⟨82841928766119239528029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110455905021492319370705 82841928766119239528029)
          ·
            refine ⟨31065723287294714823011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82841928766119239528029 31065723287294714823011)
            ·
              refine ⟨46598584930942072234517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31065723287294714823011 46598584930942072234517)
              ·
                refine ⟨2184308668637909635993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46598584930942072234517 2184308668637909635993)
                ·
                  rfl

theorem cell21_28714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 6].length) (baseStart_28714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_28714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_28714 prefixEnd_28714 := by exact prefixLift 28714
  have htrace : WordTrace (prefixWord ++ tailWord_28714) baseStart_28714 baseEnd_28714 := by
    simpa [prefixWord, tailWord_28714, baseEnd_28714] using wordTrace_append hprefix tailTrace_28714
  have hstable : (prefixWord ++ tailWord_28714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28714).length < 2 ^ (prefixWord ++ tailWord_28714).sum := by decide
  have hdescent : baseEnd_28714 < baseStart_28714 := by decide
  rcases family_descends (prefixWord ++ tailWord_28714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28728 : List Nat := [2, 1, 2, 1, 6, 1, 1, 2, 5]
def baseStart_28728 : Nat := 118140960795 + 28728 * 2 ^ 59
def prefixEnd_28728 : Nat := 4983230072969 + 3 ^ 40 * 28728 * 2
def baseEnd_28728 : Nat := 6556120996652815674617

theorem tailTrace_28728 : CollatzResearch.WordTrace tailWord_28728 prefixEnd_28728 6556120996652815674617 := by
  unfold tailWord_28728
  simp only [CollatzResearch.WordTrace]
  refine ⟨523898119965418598447419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 698530826620558131263225 523898119965418598447419)
  ·
    refine ⟨785847179948127897671129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 523898119965418598447419 785847179948127897671129)
    ·
      refine ⟨589385384961095923253347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 785847179948127897671129 589385384961095923253347)
      ·
        refine ⟨884078077441643884880021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 589385384961095923253347 884078077441643884880021)
        ·
          refine ⟨41441159880077057103751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 884078077441643884880021 41441159880077057103751)
          ·
            refine ⟨62161739820115585655627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41441159880077057103751 62161739820115585655627)
            ·
              refine ⟨93242609730173378483441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62161739820115585655627 93242609730173378483441)
              ·
                refine ⟨69931957297630033862581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93242609730173378483441 69931957297630033862581)
                ·
                  refine ⟨6556120996652815674617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69931957297630033862581 6556120996652815674617)
                  ·
                    rfl

theorem cell21_28728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 5].length) (baseStart_28728 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_28728 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_28728 prefixEnd_28728 := by exact prefixLift 28728
  have htrace : WordTrace (prefixWord ++ tailWord_28728) baseStart_28728 baseEnd_28728 := by
    simpa [prefixWord, tailWord_28728, baseEnd_28728] using wordTrace_append hprefix tailTrace_28728
  have hstable : (prefixWord ++ tailWord_28728).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28728).length < 2 ^ (prefixWord ++ tailWord_28728).sum := by decide
  have hdescent : baseEnd_28728 < baseStart_28728 := by decide
  rcases family_descends (prefixWord ++ tailWord_28728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28790 : List Nat := [5, 1, 1, 2, 1, 2, 4, 5]
def baseStart_28790 : Nat := 118140960795 + 28790 * 2 ^ 59
def prefixEnd_28790 : Nat := 4983230072969 + 3 ^ 40 * 28790 * 2
def baseEnd_28790 : Nat := 2190090080451495213719

theorem tailTrace_28790 : CollatzResearch.WordTrace tailWord_28790 prefixEnd_28790 2190090080451495213719 := by
  unfold tailWord_28790
  simp only [CollatzResearch.WordTrace]
  refine ⟨65628597856638861603239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 700038377137481190434549 65628597856638861603239)
  ·
    refine ⟨98442896784958292404859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65628597856638861603239 98442896784958292404859)
    ·
      refine ⟨147664345177437438607289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98442896784958292404859 147664345177437438607289)
      ·
        refine ⟨110748258883078078955467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147664345177437438607289 110748258883078078955467)
        ·
          refine ⟨166122388324617118433201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110748258883078078955467 166122388324617118433201)
          ·
            refine ⟨124591791243462838824901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166122388324617118433201 124591791243462838824901)
            ·
              refine ⟨23360960858149282279669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124591791243462838824901 23360960858149282279669)
              ·
                refine ⟨2190090080451495213719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23360960858149282279669 2190090080451495213719)
                ·
                  rfl

theorem cell21_28790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_28790 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_28790 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_28790 prefixEnd_28790 := by exact prefixLift 28790
  have htrace : WordTrace (prefixWord ++ tailWord_28790) baseStart_28790 baseEnd_28790 := by
    simpa [prefixWord, tailWord_28790, baseEnd_28790] using wordTrace_append hprefix tailTrace_28790
  have hstable : (prefixWord ++ tailWord_28790).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28790).length < 2 ^ (prefixWord ++ tailWord_28790).sum := by decide
  have hdescent : baseEnd_28790 < baseStart_28790 := by decide
  rcases family_descends (prefixWord ++ tailWord_28790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28818 : List Nat := [3, 2, 3, 1, 1, 1, 1, 3, 6]
def baseStart_28818 : Nat := 118140960795 + 28818 * 2 ^ 59
def prefixEnd_28818 : Nat := 4983230072969 + 3 ^ 40 * 28818 * 2
def baseEnd_28818 : Nat := 6576660222832659174433

theorem tailTrace_28818 : CollatzResearch.WordTrace tailWord_28818 prefixEnd_28818 6576660222832659174433 := by
  unfold tailWord_28818
  simp only [CollatzResearch.WordTrace]
  refine ⟨262769702401195641917777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 700719206403188378447405 262769702401195641917777)
  ·
    refine ⟨197077276800896731438333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262769702401195641917777 197077276800896731438333)
    ·
      refine ⟨73903978800336274289375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197077276800896731438333 73903978800336274289375)
      ·
        refine ⟨110855968200504411434063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73903978800336274289375 110855968200504411434063)
        ·
          refine ⟨166283952300756617151095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110855968200504411434063 166283952300756617151095)
          ·
            refine ⟨249425928451134925726643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166283952300756617151095 249425928451134925726643)
            ·
              refine ⟨374138892676702388589965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249425928451134925726643 374138892676702388589965)
              ·
                refine ⟨140302084753763395721237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 374138892676702388589965 140302084753763395721237)
                ·
                  refine ⟨6576660222832659174433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 140302084753763395721237 6576660222832659174433)
                  ·
                    rfl

theorem cell21_28818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_28818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_28818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_28818 prefixEnd_28818 := by exact prefixLift 28818
  have htrace : WordTrace (prefixWord ++ tailWord_28818) baseStart_28818 baseEnd_28818 := by
    simpa [prefixWord, tailWord_28818, baseEnd_28818] using wordTrace_append hprefix tailTrace_28818
  have hstable : (prefixWord ++ tailWord_28818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28818).length < 2 ^ (prefixWord ++ tailWord_28818).sum := by decide
  have hdescent : baseEnd_28818 < baseStart_28818 := by decide
  rcases family_descends (prefixWord ++ tailWord_28818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28821 : List Nat := [1, 3, 2, 1, 1, 1, 7, 2, 3]
def baseStart_28821 : Nat := 118140960795 + 28821 * 2 ^ 59
def prefixEnd_28821 : Nat := 4983230072969 + 3 ^ 40 * 28821 * 2
def baseEnd_28821 : Nat := 6577344863705320624427

theorem tailTrace_28821 : CollatzResearch.WordTrace tailWord_28821 prefixEnd_28821 6577344863705320624427 := by
  unfold tailWord_28821
  simp only [CollatzResearch.WordTrace]
  refine ⟨1051188228593914080030317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 700792152395942720020211 1051188228593914080030317)
  ·
    refine ⟨394195585722717780011369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1051188228593914080030317 394195585722717780011369)
    ·
      refine ⟨295646689292038335008527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394195585722717780011369 295646689292038335008527)
      ·
        refine ⟨443470033938057502512791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295646689292038335008527 443470033938057502512791)
        ·
          refine ⟨665205050907086253769187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443470033938057502512791 665205050907086253769187)
          ·
            refine ⟨997807576360629380653781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 665205050907086253769187 997807576360629380653781)
            ·
              refine ⟨23386115070952251109073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 997807576360629380653781 23386115070952251109073)
              ·
                refine ⟨17539586303214188331805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23386115070952251109073 17539586303214188331805)
                ·
                  refine ⟨6577344863705320624427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17539586303214188331805 6577344863705320624427)
                  ·
                    rfl

theorem cell21_28821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 2, 3].length) (baseStart_28821 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_28821 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_28821 prefixEnd_28821 := by exact prefixLift 28821
  have htrace : WordTrace (prefixWord ++ tailWord_28821) baseStart_28821 baseEnd_28821 := by
    simpa [prefixWord, tailWord_28821, baseEnd_28821] using wordTrace_append hprefix tailTrace_28821
  have hstable : (prefixWord ++ tailWord_28821).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28821).length < 2 ^ (prefixWord ++ tailWord_28821).sum := by decide
  have hdescent : baseEnd_28821 < baseStart_28821 := by decide
  rcases family_descends (prefixWord ++ tailWord_28821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28832 : List Nat := [2, 1, 1, 4, 2, 2, 1, 8]
def baseStart_28832 : Nat := 118140960795 + 28832 * 2 ^ 59
def prefixEnd_28832 : Nat := 4983230072969 + 3 ^ 40 * 28832 * 2
def baseEnd_28832 : Nat := 2193285071190581980357

theorem tailTrace_28832 : CollatzResearch.WordTrace tailWord_28832 prefixEnd_28832 2193285071190581980357 := by
  unfold tailWord_28832
  simp only [CollatzResearch.WordTrace]
  refine ⟨525794715777031479340375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 701059621036041972453833 525794715777031479340375)
  ·
    refine ⟨788692073665547219010563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 525794715777031479340375 788692073665547219010563)
    ·
      refine ⟨1183038110498320828515845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 788692073665547219010563 1183038110498320828515845)
      ·
        refine ⟨221819645718435155346721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1183038110498320828515845 221819645718435155346721)
        ·
          refine ⟨166364734288826366510041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221819645718435155346721 166364734288826366510041)
          ·
            refine ⟨124773550716619774882531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166364734288826366510041 124773550716619774882531)
            ·
              refine ⟨187160326074929662323797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124773550716619774882531 187160326074929662323797)
              ·
                refine ⟨2193285071190581980357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 187160326074929662323797 2193285071190581980357)
                ·
                  rfl

theorem cell21_28832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 8].length) (baseStart_28832 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_28832 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_28832 prefixEnd_28832 := by exact prefixLift 28832
  have htrace : WordTrace (prefixWord ++ tailWord_28832) baseStart_28832 baseEnd_28832 := by
    simpa [prefixWord, tailWord_28832, baseEnd_28832] using wordTrace_append hprefix tailTrace_28832
  have hstable : (prefixWord ++ tailWord_28832).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28832).length < 2 ^ (prefixWord ++ tailWord_28832).sum := by decide
  have hdescent : baseEnd_28832 < baseStart_28832 := by decide
  rcases family_descends (prefixWord ++ tailWord_28832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28866 : List Nat := [3, 5, 1, 1, 1, 10]
def baseStart_28866 : Nat := 118140960795 + 28866 * 2 ^ 59
def prefixEnd_28866 : Nat := 4983230072969 + 3 ^ 40 * 28866 * 2
def baseEnd_28866 : Nat := 243985721362786754605

theorem tailTrace_28866 : CollatzResearch.WordTrace tailWord_28866 prefixEnd_28866 243985721362786754605 := by
  unfold tailWord_28866
  simp only [CollatzResearch.WordTrace]
  refine ⟨263207378357721691354613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 701886342287257843612301 263207378357721691354613)
  ·
    refine ⟨24675691721036408564495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 263207378357721691354613 24675691721036408564495)
    ·
      refine ⟨37013537581554612846743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24675691721036408564495 37013537581554612846743)
      ·
        refine ⟨55520306372331919270115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37013537581554612846743 55520306372331919270115)
        ·
          refine ⟨83280459558497878905173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55520306372331919270115 83280459558497878905173)
          ·
            refine ⟨243985721362786754605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 83280459558497878905173 243985721362786754605)
            ·
              rfl

theorem cell21_28866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 10].length) (baseStart_28866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_28866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_28866 prefixEnd_28866 := by exact prefixLift 28866
  have htrace : WordTrace (prefixWord ++ tailWord_28866) baseStart_28866 baseEnd_28866 := by
    simpa [prefixWord, tailWord_28866, baseEnd_28866] using wordTrace_append hprefix tailTrace_28866
  have hstable : (prefixWord ++ tailWord_28866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28866).length < 2 ^ (prefixWord ++ tailWord_28866).sum := by decide
  have hdescent : baseEnd_28866 < baseStart_28866 := by decide
  rcases family_descends (prefixWord ++ tailWord_28866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28939 : List Nat := [1, 1, 1, 1, 5, 2, 4, 1, 5]
def baseStart_28939 : Nat := 118140960795 + 28939 * 2 ^ 59
def prefixEnd_28939 : Nat := 4983230072969 + 3 ^ 40 * 28939 * 2
def baseEnd_28939 : Nat := 6604274071363337657519

theorem tailTrace_28939 : CollatzResearch.WordTrace tailWord_28939 prefixEnd_28939 6604274071363337657519 := by
  unfold tailWord_28939
  simp only [CollatzResearch.WordTrace]
  refine ⟨1055492042166420232825871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 703661361444280155217247 1055492042166420232825871)
  ·
    refine ⟨1583238063249630349238807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1055492042166420232825871 1583238063249630349238807)
    ·
      refine ⟨2374857094874445523858211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1583238063249630349238807 2374857094874445523858211)
      ·
        refine ⟨3562285642311668285787317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2374857094874445523858211 3562285642311668285787317)
        ·
          refine ⟨333964278966718901792561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3562285642311668285787317 333964278966718901792561)
          ·
            refine ⟨250473209225039176344421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 333964278966718901792561 250473209225039176344421)
            ·
              refine ⟨46963726729694845564579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 250473209225039176344421 46963726729694845564579)
              ·
                refine ⟨70445590094542268346869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46963726729694845564579 70445590094542268346869)
                ·
                  refine ⟨6604274071363337657519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70445590094542268346869 6604274071363337657519)
                  ·
                    rfl

theorem cell21_28939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 5].length) (baseStart_28939 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_28939 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_28939 prefixEnd_28939 := by exact prefixLift 28939
  have htrace : WordTrace (prefixWord ++ tailWord_28939) baseStart_28939 baseEnd_28939 := by
    simpa [prefixWord, tailWord_28939, baseEnd_28939] using wordTrace_append hprefix tailTrace_28939
  have hstable : (prefixWord ++ tailWord_28939).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28939).length < 2 ^ (prefixWord ++ tailWord_28939).sum := by decide
  have hdescent : baseEnd_28939 < baseStart_28939 := by decide
  rcases family_descends (prefixWord ++ tailWord_28939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_28990 : List Nat := [4, 2, 1, 2, 1, 3, 3, 2, 3]
def baseStart_28990 : Nat := 118140960795 + 28990 * 2 ^ 59
def prefixEnd_28990 : Nat := 4983230072969 + 3 ^ 40 * 28990 * 2
def baseEnd_28990 : Nat := 6615912966198582307415

theorem tailTrace_28990 : CollatzResearch.WordTrace tailWord_28990 prefixEnd_28990 6615912966198582307415 := by
  unfold tailWord_28990
  simp only [CollatzResearch.WordTrace]
  refine ⟨132169020622706992866553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 704901443321103961954949 132169020622706992866553)
  ·
    refine ⟨99126765467030244649915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132169020622706992866553 99126765467030244649915)
    ·
      refine ⟨148690148200545366974873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99126765467030244649915 148690148200545366974873)
      ·
        refine ⟨111517611150409025231155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148690148200545366974873 111517611150409025231155)
        ·
          refine ⟨167276416725613537846733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111517611150409025231155 167276416725613537846733)
          ·
            refine ⟨62728656272105076692525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167276416725613537846733 62728656272105076692525)
            ·
              refine ⟨23523246102039403759697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62728656272105076692525 23523246102039403759697)
              ·
                refine ⟨17642434576529552819773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23523246102039403759697 17642434576529552819773)
                ·
                  refine ⟨6615912966198582307415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17642434576529552819773 6615912966198582307415)
                  ·
                    rfl

theorem cell21_28990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_28990 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_28990 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_28990 prefixEnd_28990 := by exact prefixLift 28990
  have htrace : WordTrace (prefixWord ++ tailWord_28990) baseStart_28990 baseEnd_28990 := by
    simpa [prefixWord, tailWord_28990, baseEnd_28990] using wordTrace_append hprefix tailTrace_28990
  have hstable : (prefixWord ++ tailWord_28990).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_28990).length < 2 ^ (prefixWord ++ tailWord_28990).sum := by decide
  have hdescent : baseEnd_28990 < baseStart_28990 := by decide
  rcases family_descends (prefixWord ++ tailWord_28990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29173 : List Nat := [1, 3, 5, 1, 2, 2, 2, 1, 4]
def baseStart_29173 : Nat := 118140960795 + 29173 * 2 ^ 59
def prefixEnd_29173 : Nat := 4983230072969 + 3 ^ 40 * 29173 * 2
def baseEnd_29173 : Nat := 6657676059430930757041

theorem tailTrace_29173 : CollatzResearch.WordTrace tailWord_29173 prefixEnd_29173 6657676059430930757041 := by
  unfold tailWord_29173
  simp only [CollatzResearch.WordTrace]
  refine ⟨1064026723318678196844173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 709351148879118797896115 1064026723318678196844173)
  ·
    refine ⟨399010021244504323816565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1064026723318678196844173 399010021244504323816565)
    ·
      refine ⟨37407189491672280357803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 399010021244504323816565 37407189491672280357803)
      ·
        refine ⟨56110784237508420536705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37407189491672280357803 56110784237508420536705)
        ·
          refine ⟨42083088178131315402529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56110784237508420536705 42083088178131315402529)
          ·
            refine ⟨31562316133598486551897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42083088178131315402529 31562316133598486551897)
            ·
              refine ⟨23671737100198864913923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31562316133598486551897 23671737100198864913923)
              ·
                refine ⟨35507605650298297370885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23671737100198864913923 35507605650298297370885)
                ·
                  refine ⟨6657676059430930757041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35507605650298297370885 6657676059430930757041)
                  ·
                    rfl

theorem cell21_29173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 1, 4].length) (baseStart_29173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_29173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_29173 prefixEnd_29173 := by exact prefixLift 29173
  have htrace : WordTrace (prefixWord ++ tailWord_29173) baseStart_29173 baseEnd_29173 := by
    simpa [prefixWord, tailWord_29173, baseEnd_29173] using wordTrace_append hprefix tailTrace_29173
  have hstable : (prefixWord ++ tailWord_29173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29173).length < 2 ^ (prefixWord ++ tailWord_29173).sum := by decide
  have hdescent : baseEnd_29173 < baseStart_29173 := by decide
  rcases family_descends (prefixWord ++ tailWord_29173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29260 : List Nat := [2, 2, 1, 3, 1, 2, 4, 3, 3]
def baseStart_29260 : Nat := 118140960795 + 29260 * 2 ^ 59
def prefixEnd_29260 : Nat := 4983230072969 + 3 ^ 40 * 29260 * 2
def baseEnd_29260 : Nat := 6677530644738112806863

theorem tailTrace_29260 : CollatzResearch.WordTrace tailWord_29260 prefixEnd_29260 6677530644738112806863 := by
  unfold tailWord_29260
  simp only [CollatzResearch.WordTrace]
  refine ⟨533599937001746027630617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 711466582668994703507489 533599937001746027630617)
  ·
    refine ⟨400199952751309520722963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 533599937001746027630617 400199952751309520722963)
    ·
      refine ⟨600299929126964281084445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400199952751309520722963 600299929126964281084445)
      ·
        refine ⟨225112473422611605406667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 600299929126964281084445 225112473422611605406667)
        ·
          refine ⟨337668710133917408110001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225112473422611605406667 337668710133917408110001)
          ·
            refine ⟨253251532600438056082501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 337668710133917408110001 253251532600438056082501)
            ·
              refine ⟨47484662362582135515469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 253251532600438056082501 47484662362582135515469)
              ·
                refine ⟨17806748385968300818301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47484662362582135515469 17806748385968300818301)
                ·
                  refine ⟨6677530644738112806863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17806748385968300818301 6677530644738112806863)
                  ·
                    rfl

theorem cell21_29260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 3, 3].length) (baseStart_29260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_29260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_29260 prefixEnd_29260 := by exact prefixLift 29260
  have htrace : WordTrace (prefixWord ++ tailWord_29260) baseStart_29260 baseEnd_29260 := by
    simpa [prefixWord, tailWord_29260, baseEnd_29260] using wordTrace_append hprefix tailTrace_29260
  have hstable : (prefixWord ++ tailWord_29260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29260).length < 2 ^ (prefixWord ++ tailWord_29260).sum := by decide
  have hdescent : baseEnd_29260 < baseStart_29260 := by decide
  rcases family_descends (prefixWord ++ tailWord_29260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29271 : List Nat := [1, 1, 3, 2, 2, 2, 10]
def baseStart_29271 : Nat := 118140960795 + 29271 * 2 ^ 59
def prefixEnd_29271 : Nat := 4983230072969 + 3 ^ 40 * 29271 * 2
def baseEnd_29271 : Nat := 742226777178282013723

theorem tailTrace_29271 : CollatzResearch.WordTrace tailWord_29271 prefixEnd_29271 742226777178282013723 := by
  unfold tailWord_29271
  simp only [CollatzResearch.WordTrace]
  refine ⟨1067601076963640933911667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 711734051309093955941111 1067601076963640933911667)
  ·
    refine ⟨1601401615445461400867501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1067601076963640933911667 1601401615445461400867501)
    ·
      refine ⟨600525605792048025325313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1601401615445461400867501 600525605792048025325313)
      ·
        refine ⟨450394204344036018993985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 600525605792048025325313 450394204344036018993985)
        ·
          refine ⟨337795653258027014245489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 450394204344036018993985 337795653258027014245489)
          ·
            refine ⟨253346739943520260684117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 337795653258027014245489 253346739943520260684117)
            ·
              refine ⟨742226777178282013723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 253346739943520260684117 742226777178282013723)
              ·
                rfl

theorem cell21_29271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 10].length) (baseStart_29271 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_29271 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_29271 prefixEnd_29271 := by exact prefixLift 29271
  have htrace : WordTrace (prefixWord ++ tailWord_29271) baseStart_29271 baseEnd_29271 := by
    simpa [prefixWord, tailWord_29271, baseEnd_29271] using wordTrace_append hprefix tailTrace_29271
  have hstable : (prefixWord ++ tailWord_29271).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29271).length < 2 ^ (prefixWord ++ tailWord_29271).sum := by decide
  have hdescent : baseEnd_29271 < baseStart_29271 := by decide
  rcases family_descends (prefixWord ++ tailWord_29271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29305 : List Nat := [1, 2, 1, 3, 3, 4, 2, 5]
def baseStart_29305 : Nat := 118140960795 + 29305 * 2 ^ 59
def prefixEnd_29305 : Nat := 4983230072969 + 3 ^ 40 * 29305 * 2
def baseEnd_29305 : Nat := 2229266752609344852257

theorem tailTrace_29305 : CollatzResearch.WordTrace tailWord_29305 prefixEnd_29305 2229266752609344852257 := by
  unfold tailWord_29305
  simp only [CollatzResearch.WordTrace]
  refine ⟨1068841158840464740649369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 712560772560309827099579 1068841158840464740649369)
  ·
    refine ⟨801630869130348555487027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1068841158840464740649369 801630869130348555487027)
    ·
      refine ⟨1202446303695522833230541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 801630869130348555487027 1202446303695522833230541)
      ·
        refine ⟨450917363885821062461453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1202446303695522833230541 450917363885821062461453)
        ·
          refine ⟨169094011457182898423045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 450917363885821062461453 169094011457182898423045)
          ·
            refine ⟨31705127148221793454321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169094011457182898423045 31705127148221793454321)
            ·
              refine ⟨23778845361166345090741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31705127148221793454321 23778845361166345090741)
              ·
                refine ⟨2229266752609344852257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23778845361166345090741 2229266752609344852257)
                ·
                  rfl

theorem cell21_29305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 5].length) (baseStart_29305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_29305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_29305 prefixEnd_29305 := by exact prefixLift 29305
  have htrace : WordTrace (prefixWord ++ tailWord_29305) baseStart_29305 baseEnd_29305 := by
    simpa [prefixWord, tailWord_29305, baseEnd_29305] using wordTrace_append hprefix tailTrace_29305
  have hstable : (prefixWord ++ tailWord_29305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29305).length < 2 ^ (prefixWord ++ tailWord_29305).sum := by decide
  have hdescent : baseEnd_29305 < baseStart_29305 := by decide
  rcases family_descends (prefixWord ++ tailWord_29305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29392 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 10]
def baseStart_29392 : Nat := 118140960795 + 29392 * 2 ^ 59
def prefixEnd_29392 : Nat := 4983230072969 + 3 ^ 40 * 29392 * 2
def baseEnd_29392 : Nat := 6707654843135216606593

theorem tailTrace_29392 : CollatzResearch.WordTrace tailWord_29392 prefixEnd_29392 6707654843135216606593 := by
  unfold tailWord_29392
  simp only [CollatzResearch.WordTrace]
  refine ⟨536007154762639299533215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 714676206350185732710953 536007154762639299533215)
  ·
    refine ⟨804010732143958949299823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 536007154762639299533215 804010732143958949299823)
    ·
      refine ⟨1206016098215938423949735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 804010732143958949299823 1206016098215938423949735)
      ·
        refine ⟨1809024147323907635924603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1206016098215938423949735 1809024147323907635924603)
        ·
          refine ⟨2713536220985861453886905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1809024147323907635924603 2713536220985861453886905)
          ·
            refine ⟨2035152165739396090415179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2713536220985861453886905 2035152165739396090415179)
            ·
              refine ⟨3052728248609094135622769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2035152165739396090415179 3052728248609094135622769)
              ·
                refine ⟨2289546186456820601717077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3052728248609094135622769 2289546186456820601717077)
                ·
                  refine ⟨6707654843135216606593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 2289546186456820601717077 6707654843135216606593)
                  ·
                    rfl

theorem cell21_29392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 10].length) (baseStart_29392 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_29392 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_29392 prefixEnd_29392 := by exact prefixLift 29392
  have htrace : WordTrace (prefixWord ++ tailWord_29392) baseStart_29392 baseEnd_29392 := by
    simpa [prefixWord, tailWord_29392, baseEnd_29392] using wordTrace_append hprefix tailTrace_29392
  have hstable : (prefixWord ++ tailWord_29392).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29392).length < 2 ^ (prefixWord ++ tailWord_29392).sum := by decide
  have hdescent : baseEnd_29392 < baseStart_29392 := by decide
  rcases family_descends (prefixWord ++ tailWord_29392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29505 : List Nat := [1, 2, 5, 3, 1, 2, 1, 1, 5]
def baseStart_29505 : Nat := 118140960795 + 29505 * 2 ^ 59
def prefixEnd_29505 : Nat := 4983230072969 + 3 ^ 40 * 29505 * 2
def baseEnd_29505 : Nat := 6733442982672131223029

theorem tailTrace_29505 : CollatzResearch.WordTrace tailWord_29505 prefixEnd_29505 6733442982672131223029 := by
  unfold tailWord_29505
  simp only [CollatzResearch.WordTrace]
  refine ⟨1076135758115898897929969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 717423838743932598619979 1076135758115898897929969)
  ·
    refine ⟨807101818586924173447477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1076135758115898897929969 807101818586924173447477)
    ·
      refine ⟨75665795492524141260701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 807101818586924173447477 75665795492524141260701)
      ·
        refine ⟨28374673309696552972763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75665795492524141260701 28374673309696552972763)
        ·
          refine ⟨42562009964544829459145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28374673309696552972763 42562009964544829459145)
          ·
            refine ⟨31921507473408622094359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42562009964544829459145 31921507473408622094359)
            ·
              refine ⟨47882261210112933141539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31921507473408622094359 47882261210112933141539)
              ·
                refine ⟨71823391815169399712309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47882261210112933141539 71823391815169399712309)
                ·
                  refine ⟨6733442982672131223029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71823391815169399712309 6733442982672131223029)
                  ·
                    rfl

theorem cell21_29505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 5].length) (baseStart_29505 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_29505 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_29505 prefixEnd_29505 := by exact prefixLift 29505
  have htrace : WordTrace (prefixWord ++ tailWord_29505) baseStart_29505 baseEnd_29505 := by
    simpa [prefixWord, tailWord_29505, baseEnd_29505] using wordTrace_append hprefix tailTrace_29505
  have hstable : (prefixWord ++ tailWord_29505).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29505).length < 2 ^ (prefixWord ++ tailWord_29505).sum := by decide
  have hdescent : baseEnd_29505 < baseStart_29505 := by decide
  rcases family_descends (prefixWord ++ tailWord_29505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29516 : List Nat := [2, 2, 1, 3, 3, 2, 2, 6]
def baseStart_29516 : Nat := 118140960795 + 29516 * 2 ^ 59
def prefixEnd_29516 : Nat := 4983230072969 + 3 ^ 40 * 29516 * 2
def baseEnd_29516 : Nat := 2245317777512852179891

theorem tailTrace_29516 : CollatzResearch.WordTrace tailWord_29516 prefixEnd_29516 2245317777512852179891 := by
  unfold tailWord_29516
  simp only [CollatzResearch.WordTrace]
  refine ⟨538268480538023888290201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 717691307384031851053601 538268480538023888290201)
  ·
    refine ⟨403701360403517916217651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 538268480538023888290201 403701360403517916217651)
    ·
      refine ⟨605552040605276874326477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403701360403517916217651 605552040605276874326477)
      ·
        refine ⟨227082015226978827872429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 605552040605276874326477 227082015226978827872429)
        ·
          refine ⟨85155755710117060452161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227082015226978827872429 85155755710117060452161)
          ·
            refine ⟨63866816782587795339121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85155755710117060452161 63866816782587795339121)
            ·
              refine ⟨47900112586940846504341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63866816782587795339121 47900112586940846504341)
              ·
                refine ⟨2245317777512852179891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47900112586940846504341 2245317777512852179891)
                ·
                  rfl

theorem cell21_29516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 6].length) (baseStart_29516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_29516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_29516 prefixEnd_29516 := by exact prefixLift 29516
  have htrace : WordTrace (prefixWord ++ tailWord_29516) baseStart_29516 baseEnd_29516 := by
    simpa [prefixWord, tailWord_29516, baseEnd_29516] using wordTrace_append hprefix tailTrace_29516
  have hstable : (prefixWord ++ tailWord_29516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29516).length < 2 ^ (prefixWord ++ tailWord_29516).sum := by decide
  have hdescent : baseEnd_29516 < baseStart_29516 := by decide
  rcases family_descends (prefixWord ++ tailWord_29516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29561 : List Nat := [1, 2, 1, 3, 2, 3, 1, 4, 4]
def baseStart_29561 : Nat := 118140960795 + 29561 * 2 ^ 59
def prefixEnd_29561 : Nat := 4983230072969 + 3 ^ 40 * 29561 * 2
def baseEnd_29561 : Nat := 6746222945628478289581

theorem tailTrace_29561 : CollatzResearch.WordTrace tailWord_29561 prefixEnd_29561 6746222945628478289581 := by
  unfold tailWord_29561
  simp only [CollatzResearch.WordTrace]
  refine ⟨1078178245913020461968537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 718785497275346974645691 1078178245913020461968537)
  ·
    refine ⟨808633684434765346476403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1078178245913020461968537 808633684434765346476403)
    ·
      refine ⟨1212950526652148019714605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 808633684434765346476403 1212950526652148019714605)
      ·
        refine ⟨454856447494555507392977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1212950526652148019714605 454856447494555507392977)
        ·
          refine ⟨341142335620916630544733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 454856447494555507392977 341142335620916630544733)
          ·
            refine ⟨127928375857843736454275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 341142335620916630544733 127928375857843736454275)
            ·
              refine ⟨191892563786765604681413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127928375857843736454275 191892563786765604681413)
              ·
                refine ⟨35979855710018550877765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 191892563786765604681413 35979855710018550877765)
                ·
                  refine ⟨6746222945628478289581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35979855710018550877765 6746222945628478289581)
                  ·
                    rfl

theorem cell21_29561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 4, 4].length) (baseStart_29561 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_29561 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_29561 prefixEnd_29561 := by exact prefixLift 29561
  have htrace : WordTrace (prefixWord ++ tailWord_29561) baseStart_29561 baseEnd_29561 := by
    simpa [prefixWord, tailWord_29561, baseEnd_29561] using wordTrace_append hprefix tailTrace_29561
  have hstable : (prefixWord ++ tailWord_29561).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29561).length < 2 ^ (prefixWord ++ tailWord_29561).sum := by decide
  have hdescent : baseEnd_29561 < baseStart_29561 := by decide
  rcases family_descends (prefixWord ++ tailWord_29561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29578 : List Nat := [3, 1, 2, 4, 1, 1, 2, 3, 4]
def baseStart_29578 : Nat := 118140960795 + 29578 * 2 ^ 59
def prefixEnd_29578 : Nat := 4983230072969 + 3 ^ 40 * 29578 * 2
def baseEnd_29578 : Nat := 6750102577240226506213

theorem tailTrace_29578 : CollatzResearch.WordTrace tailWord_29578 prefixEnd_29578 6750102577240226506213 := by
  unfold tailWord_29578
  simp only [CollatzResearch.WordTrace]
  refine ⟨269699571712858091334347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 719198857900954910224925 269699571712858091334347)
  ·
    refine ⟨404549357569287137001521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269699571712858091334347 404549357569287137001521)
    ·
      refine ⟨303412018176965352751141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 404549357569287137001521 303412018176965352751141)
      ·
        refine ⟨56889753408181003640839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 303412018176965352751141 56889753408181003640839)
        ·
          refine ⟨85334630112271505461259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56889753408181003640839 85334630112271505461259)
          ·
            refine ⟨128001945168407258191889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85334630112271505461259 128001945168407258191889)
            ·
              refine ⟨96001458876305443643917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128001945168407258191889 96001458876305443643917)
              ·
                refine ⟨36000547078614541366469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96001458876305443643917 36000547078614541366469)
                ·
                  refine ⟨6750102577240226506213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36000547078614541366469 6750102577240226506213)
                  ·
                    rfl

theorem cell21_29578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 3, 4].length) (baseStart_29578 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_29578 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_29578 prefixEnd_29578 := by exact prefixLift 29578
  have htrace : WordTrace (prefixWord ++ tailWord_29578) baseStart_29578 baseEnd_29578 := by
    simpa [prefixWord, tailWord_29578, baseEnd_29578] using wordTrace_append hprefix tailTrace_29578
  have hstable : (prefixWord ++ tailWord_29578).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29578).length < 2 ^ (prefixWord ++ tailWord_29578).sum := by decide
  have hdescent : baseEnd_29578 < baseStart_29578 := by decide
  rcases family_descends (prefixWord ++ tailWord_29578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29623 : List Nat := [1, 1, 3, 1, 3, 1, 4, 4, 3]
def baseStart_29623 : Nat := 118140960795 + 29623 * 2 ^ 59
def prefixEnd_29623 : Nat := 4983230072969 + 3 ^ 40 * 29623 * 2
def baseEnd_29623 : Nat := 6760372190330148256121

theorem tailTrace_29623 : CollatzResearch.WordTrace tailWord_29623 prefixEnd_29623 6760372190330148256121 := by
  unfold tailWord_29623
  simp only [CollatzResearch.WordTrace]
  refine ⟨1080439571688405050725523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 720293047792270033817015 1080439571688405050725523)
  ·
    refine ⟨1620659357532607576088285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1080439571688405050725523 1620659357532607576088285)
    ·
      refine ⟨607747259074727841033107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1620659357532607576088285 607747259074727841033107)
      ·
        refine ⟨911620888612091761549661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 607747259074727841033107 911620888612091761549661)
        ·
          refine ⟨341857833229534410581123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 911620888612091761549661 341857833229534410581123)
          ·
            refine ⟨512786749844301615871685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341857833229534410581123 512786749844301615871685)
            ·
              refine ⟨96147515595806552975941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 512786749844301615871685 96147515595806552975941)
              ·
                refine ⟨18027659174213728682989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96147515595806552975941 18027659174213728682989)
                ·
                  refine ⟨6760372190330148256121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18027659174213728682989 6760372190330148256121)
                  ·
                    rfl

theorem cell21_29623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 4, 3].length) (baseStart_29623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_29623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_29623 prefixEnd_29623 := by exact prefixLift 29623
  have htrace : WordTrace (prefixWord ++ tailWord_29623) baseStart_29623 baseEnd_29623 := by
    simpa [prefixWord, tailWord_29623, baseEnd_29623] using wordTrace_append hprefix tailTrace_29623
  have hstable : (prefixWord ++ tailWord_29623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29623).length < 2 ^ (prefixWord ++ tailWord_29623).sum := by decide
  have hdescent : baseEnd_29623 < baseStart_29623 := by decide
  rcases family_descends (prefixWord ++ tailWord_29623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29654 : List Nat := [5, 2, 1, 1, 2, 1, 1, 2, 6]
def baseStart_29654 : Nat := 118140960795 + 29654 * 2 ^ 59
def prefixEnd_29654 : Nat := 4983230072969 + 3 ^ 40 * 29654 * 2
def baseEnd_29654 : Nat := 6767446812680983239391

theorem tailTrace_29654 : CollatzResearch.WordTrace tailWord_29654 prefixEnd_29654 6767446812680983239391 := by
  unfold tailWord_29654
  simp only [CollatzResearch.WordTrace]
  refine ⟨67598139661006084069001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 721046823050731563402677 67598139661006084069001)
  ·
    refine ⟨50698604745754563051751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67598139661006084069001 50698604745754563051751)
    ·
      refine ⟨76047907118631844577627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50698604745754563051751 76047907118631844577627)
      ·
        refine ⟨114071860677947766866441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76047907118631844577627 114071860677947766866441)
        ·
          refine ⟨85553895508460825149831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114071860677947766866441 85553895508460825149831)
          ·
            refine ⟨128330843262691237724747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85553895508460825149831 128330843262691237724747)
            ·
              refine ⟨192496264894036856587121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128330843262691237724747 192496264894036856587121)
              ·
                refine ⟨144372198670527642440341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192496264894036856587121 144372198670527642440341)
                ·
                  refine ⟨6767446812680983239391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 144372198670527642440341 6767446812680983239391)
                  ·
                    rfl

theorem cell21_29654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_29654 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_29654 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_29654 prefixEnd_29654 := by exact prefixLift 29654
  have htrace : WordTrace (prefixWord ++ tailWord_29654) baseStart_29654 baseEnd_29654 := by
    simpa [prefixWord, tailWord_29654, baseEnd_29654] using wordTrace_append hprefix tailTrace_29654
  have hstable : (prefixWord ++ tailWord_29654).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29654).length < 2 ^ (prefixWord ++ tailWord_29654).sum := by decide
  have hdescent : baseEnd_29654 < baseStart_29654 := by decide
  rcases family_descends (prefixWord ++ tailWord_29654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29730 : List Nat := [3, 3, 1, 1, 1, 4, 2, 2, 4]
def baseStart_29730 : Nat := 118140960795 + 29730 * 2 ^ 59
def prefixEnd_29730 : Nat := 4983230072969 + 3 ^ 40 * 29730 * 2
def baseEnd_29730 : Nat := 6784791048121739972569

theorem tailTrace_29730 : CollatzResearch.WordTrace tailWord_29730 prefixEnd_29730 6784791048121739972569 := by
  unfold tailWord_29730
  simp only [CollatzResearch.WordTrace]
  refine ⟨271085545575190581217661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 722894788200508216580429 271085545575190581217661)
  ·
    refine ⟨101657079590696467956623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 271085545575190581217661 101657079590696467956623)
    ·
      refine ⟨152485619386044701934935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101657079590696467956623 152485619386044701934935)
      ·
        refine ⟨228728429079067052902403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152485619386044701934935 228728429079067052902403)
        ·
          refine ⟨343092643618600579353605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228728429079067052902403 343092643618600579353605)
          ·
            refine ⟨64329870678487608628801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 343092643618600579353605 64329870678487608628801)
            ·
              refine ⟨48247403008865706471601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64329870678487608628801 48247403008865706471601)
              ·
                refine ⟨36185552256649279853701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48247403008865706471601 36185552256649279853701)
                ·
                  refine ⟨6784791048121739972569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36185552256649279853701 6784791048121739972569)
                  ·
                    rfl

theorem cell21_29730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_29730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_29730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_29730 prefixEnd_29730 := by exact prefixLift 29730
  have htrace : WordTrace (prefixWord ++ tailWord_29730) baseStart_29730 baseEnd_29730 := by
    simpa [prefixWord, tailWord_29730, baseEnd_29730] using wordTrace_append hprefix tailTrace_29730
  have hstable : (prefixWord ++ tailWord_29730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29730).length < 2 ^ (prefixWord ++ tailWord_29730).sum := by decide
  have hdescent : baseEnd_29730 < baseStart_29730 := by decide
  rcases family_descends (prefixWord ++ tailWord_29730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29761 : List Nat := [1, 2, 5, 1, 3, 1, 3, 5]
def baseStart_29761 : Nat := 118140960795 + 29761 * 2 ^ 59
def prefixEnd_29761 : Nat := 4983230072969 + 3 ^ 40 * 29761 * 2
def baseEnd_29761 : Nat := 2263955223490858318613

theorem tailTrace_29761 : CollatzResearch.WordTrace tailWord_29761 prefixEnd_29761 2263955223490858318613 := by
  unfold tailWord_29761
  simp only [CollatzResearch.WordTrace]
  refine ⟨1085472845188454619249137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 723648563458969746166091 1085472845188454619249137)
  ·
    refine ⟨814104633891340964436853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1085472845188454619249137 814104633891340964436853)
    ·
      refine ⟨76322309427313215415955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 814104633891340964436853 76322309427313215415955)
      ·
        refine ⟨114483464140969823123933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76322309427313215415955 114483464140969823123933)
        ·
          refine ⟨42931299052863683671475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114483464140969823123933 42931299052863683671475)
          ·
            refine ⟨64396948579295525507213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42931299052863683671475 64396948579295525507213)
            ·
              refine ⟨24148855717235822065205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64396948579295525507213 24148855717235822065205)
              ·
                refine ⟨2263955223490858318613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24148855717235822065205 2263955223490858318613)
                ·
                  rfl

theorem cell21_29761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 5].length) (baseStart_29761 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_29761 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_29761 prefixEnd_29761 := by exact prefixLift 29761
  have htrace : WordTrace (prefixWord ++ tailWord_29761) baseStart_29761 baseEnd_29761 := by
    simpa [prefixWord, tailWord_29761, baseEnd_29761] using wordTrace_append hprefix tailTrace_29761
  have hstable : (prefixWord ++ tailWord_29761).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29761).length < 2 ^ (prefixWord ++ tailWord_29761).sum := by decide
  have hdescent : baseEnd_29761 < baseStart_29761 := by decide
  rcases family_descends (prefixWord ++ tailWord_29761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29772 : List Nat := [2, 2, 1, 3, 1, 1, 1, 4, 6]
def baseStart_29772 : Nat := 118140960795 + 29772 * 2 ^ 59
def prefixEnd_29772 : Nat := 4983230072969 + 3 ^ 40 * 29772 * 2
def baseEnd_29772 : Nat := 6794376020339000272483

theorem tailTrace_29772 : CollatzResearch.WordTrace tailWord_29772 prefixEnd_29772 6794376020339000272483 := by
  unfold tailWord_29772
  simp only [CollatzResearch.WordTrace]
  refine ⟨542937024074301748949785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 723916032099068998599713 542937024074301748949785)
  ·
    refine ⟨407202768055726311712339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 542937024074301748949785 407202768055726311712339)
    ·
      refine ⟨610804152083589467568509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407202768055726311712339 610804152083589467568509)
      ·
        refine ⟨229051557031346050338191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 610804152083589467568509 229051557031346050338191)
        ·
          refine ⟨343577335547019075507287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229051557031346050338191 343577335547019075507287)
          ·
            refine ⟨515366003320528613260931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343577335547019075507287 515366003320528613260931)
            ·
              refine ⟨773049004980792919891397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 515366003320528613260931 773049004980792919891397)
              ·
                refine ⟨144946688433898672479637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 773049004980792919891397 144946688433898672479637)
                ·
                  refine ⟨6794376020339000272483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 144946688433898672479637 6794376020339000272483)
                  ·
                    rfl

theorem cell21_29772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 6].length) (baseStart_29772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_29772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_29772 prefixEnd_29772 := by exact prefixLift 29772
  have htrace : WordTrace (prefixWord ++ tailWord_29772) baseStart_29772 baseEnd_29772 := by
    simpa [prefixWord, tailWord_29772, baseEnd_29772] using wordTrace_append hprefix tailTrace_29772
  have hstable : (prefixWord ++ tailWord_29772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29772).length < 2 ^ (prefixWord ++ tailWord_29772).sum := by decide
  have hdescent : baseEnd_29772 < baseStart_29772 := by decide
  rcases family_descends (prefixWord ++ tailWord_29772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29902 : List Nat := [4, 1, 1, 1, 6, 1, 2, 2, 3]
def baseStart_29902 : Nat := 118140960795 + 29902 * 2 ^ 59
def prefixEnd_29902 : Nat := 4983230072969 + 3 ^ 40 * 29902 * 2
def baseEnd_29902 : Nat := 6824043791487663105551

theorem tailTrace_29902 : CollatzResearch.WordTrace tailWord_29902 prefixEnd_29902 6824043791487663105551 := by
  unfold tailWord_29902
  simp only [CollatzResearch.WordTrace]
  refine ⟨136326942209704462516495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 727077025118423800087973 136326942209704462516495)
  ·
    refine ⟨204490413314556693774743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136326942209704462516495 204490413314556693774743)
    ·
      refine ⟨306735619971835040662115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204490413314556693774743 306735619971835040662115)
      ·
        refine ⟨460103429957752560993173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306735619971835040662115 460103429957752560993173)
        ·
          refine ⟨21567348279269651296555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 460103429957752560993173 21567348279269651296555)
          ·
            refine ⟨32351022418904476944833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21567348279269651296555 32351022418904476944833)
            ·
              refine ⟨24263266814178357708625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32351022418904476944833 24263266814178357708625)
              ·
                refine ⟨18197450110633768281469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24263266814178357708625 18197450110633768281469)
                ·
                  refine ⟨6824043791487663105551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18197450110633768281469 6824043791487663105551)
                  ·
                    rfl

theorem cell21_29902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 2, 3].length) (baseStart_29902 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_29902 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_29902 prefixEnd_29902 := by exact prefixLift 29902
  have htrace : WordTrace (prefixWord ++ tailWord_29902) baseStart_29902 baseEnd_29902 := by
    simpa [prefixWord, tailWord_29902, baseEnd_29902] using wordTrace_append hprefix tailTrace_29902
  have hstable : (prefixWord ++ tailWord_29902).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29902).length < 2 ^ (prefixWord ++ tailWord_29902).sum := by decide
  have hdescent : baseEnd_29902 < baseStart_29902 := by decide
  rcases family_descends (prefixWord ++ tailWord_29902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_29927 : List Nat := [1, 1, 5, 3, 2, 1, 1, 2, 5]
def baseStart_29927 : Nat := 118140960795 + 29927 * 2 ^ 59
def prefixEnd_29927 : Nat := 4983230072969 + 3 ^ 40 * 29927 * 2
def baseEnd_29927 : Nat := 6829749132093175188833

theorem tailTrace_29927 : CollatzResearch.WordTrace tailWord_29927 prefixEnd_29927 6829749132093175188833 := by
  unfold tailWord_29927
  simp only [CollatzResearch.WordTrace]
  refine ⟨1091527362587064969792035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 727684908391376646528023 1091527362587064969792035)
  ·
    refine ⟨1637291043880597454688053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1091527362587064969792035 1637291043880597454688053)
    ·
      refine ⟨153496035363806011377005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1637291043880597454688053 153496035363806011377005)
      ·
        refine ⟨57561013261427254266377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153496035363806011377005 57561013261427254266377)
        ·
          refine ⟨43170759946070440699783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57561013261427254266377 43170759946070440699783)
          ·
            refine ⟨64756139919105661049675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43170759946070440699783 64756139919105661049675)
            ·
              refine ⟨97134209878658491574513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64756139919105661049675 97134209878658491574513)
              ·
                refine ⟨72850657408993868680885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97134209878658491574513 72850657408993868680885)
                ·
                  refine ⟨6829749132093175188833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72850657408993868680885 6829749132093175188833)
                  ·
                    rfl

theorem cell21_29927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 5].length) (baseStart_29927 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_29927 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_29927 prefixEnd_29927 := by exact prefixLift 29927
  have htrace : WordTrace (prefixWord ++ tailWord_29927) baseStart_29927 baseEnd_29927 := by
    simpa [prefixWord, tailWord_29927, baseEnd_29927] using wordTrace_append hprefix tailTrace_29927
  have hstable : (prefixWord ++ tailWord_29927).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_29927).length < 2 ^ (prefixWord ++ tailWord_29927).sum := by decide
  have hdescent : baseEnd_29927 < baseStart_29927 := by decide
  rcases family_descends (prefixWord ++ tailWord_29927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30003 : List Nat := [1, 1, 1, 2, 5, 2, 3, 3, 3]
def baseStart_30003 : Nat := 118140960795 + 30003 * 2 ^ 59
def prefixEnd_30003 : Nat := 4983230072969 + 3 ^ 40 * 30003 * 2
def baseEnd_30003 : Nat := 6847093367533931922011

theorem tailTrace_30003 : CollatzResearch.WordTrace tailWord_30003 prefixEnd_30003 6847093367533931922011 := by
  unfold tailWord_30003
  simp only [CollatzResearch.WordTrace]
  refine ⟨1094299310311729949558663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 729532873541153299705775 1094299310311729949558663)
  ·
    refine ⟨1641448965467594924337995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1094299310311729949558663 1641448965467594924337995)
    ·
      refine ⟨2462173448201392386506993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1641448965467594924337995 2462173448201392386506993)
      ·
        refine ⟨1846630086151044289880245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2462173448201392386506993 1846630086151044289880245)
        ·
          refine ⟨173121570576660402176273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1846630086151044289880245 173121570576660402176273)
          ·
            refine ⟨129841177932495301632205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173121570576660402176273 129841177932495301632205)
            ·
              refine ⟨48690441724685738112077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129841177932495301632205 48690441724685738112077)
              ·
                refine ⟨18258915646757151792029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48690441724685738112077 18258915646757151792029)
                ·
                  refine ⟨6847093367533931922011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18258915646757151792029 6847093367533931922011)
                  ·
                    rfl

theorem cell21_30003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 3, 3].length) (baseStart_30003 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_30003 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_30003 prefixEnd_30003 := by exact prefixLift 30003
  have htrace : WordTrace (prefixWord ++ tailWord_30003) baseStart_30003 baseEnd_30003 := by
    simpa [prefixWord, tailWord_30003, baseEnd_30003] using wordTrace_append hprefix tailTrace_30003
  have hstable : (prefixWord ++ tailWord_30003).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30003).length < 2 ^ (prefixWord ++ tailWord_30003).sum := by decide
  have hdescent : baseEnd_30003 < baseStart_30003 := by decide
  rcases family_descends (prefixWord ++ tailWord_30003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30006 : List Nat := [5, 1, 2, 3, 2, 1, 7]
def baseStart_30006 : Nat := 118140960795 + 30006 * 2 ^ 59
def prefixEnd_30006 : Nat := 4983230072969 + 3 ^ 40 * 30006 * 2
def baseEnd_30006 : Nat := 760864223156288152445

theorem tailTrace_30006 : CollatzResearch.WordTrace tailWord_30006 prefixEnd_30006 760864223156288152445 := by
  unfold tailWord_30006
  simp only [CollatzResearch.WordTrace]
  refine ⟨68400545581303841369867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 729605819533907641278581 68400545581303841369867)
  ·
    refine ⟨102600818371955762054801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68400545581303841369867 102600818371955762054801)
    ·
      refine ⟨76950613778966821541101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102600818371955762054801 76950613778966821541101)
      ·
        refine ⟨28856480167112558077913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76950613778966821541101 28856480167112558077913)
        ·
          refine ⟨21642360125334418558435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28856480167112558077913 21642360125334418558435)
          ·
            refine ⟨32463540188001627837653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21642360125334418558435 32463540188001627837653)
            ·
              refine ⟨760864223156288152445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 32463540188001627837653 760864223156288152445)
              ·
                rfl

theorem cell21_30006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 7].length) (baseStart_30006 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_30006 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_30006 prefixEnd_30006 := by exact prefixLift 30006
  have htrace : WordTrace (prefixWord ++ tailWord_30006) baseStart_30006 baseEnd_30006 := by
    simpa [prefixWord, tailWord_30006, baseEnd_30006] using wordTrace_append hprefix tailTrace_30006
  have hstable : (prefixWord ++ tailWord_30006).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30006).length < 2 ^ (prefixWord ++ tailWord_30006).sum := by decide
  have hdescent : baseEnd_30006 < baseStart_30006 := by decide
  rcases family_descends (prefixWord ++ tailWord_30006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30017 : List Nat := [1, 2, 5, 2, 1, 1, 2, 1, 6]
def baseStart_30017 : Nat := 118140960795 + 30017 * 2 ^ 59
def prefixEnd_30017 : Nat := 4983230072969 + 3 ^ 40 * 30017 * 2
def baseEnd_30017 : Nat := 6850288358273018688649

theorem tailTrace_30017 : CollatzResearch.WordTrace tailWord_30017 prefixEnd_30017 6850288358273018688649 := by
  unfold tailWord_30017
  simp only [CollatzResearch.WordTrace]
  refine ⟨1094809932261010340568305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 729873288174006893712203 1094809932261010340568305)
  ·
    refine ⟨821107449195757755426229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1094809932261010340568305 821107449195757755426229)
    ·
      refine ⟨76978823362102289571209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 821107449195757755426229 76978823362102289571209)
      ·
        refine ⟨57734117521576717178407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76978823362102289571209 57734117521576717178407)
        ·
          refine ⟨86601176282365075767611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57734117521576717178407 86601176282365075767611)
          ·
            refine ⟨129901764423547613651417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86601176282365075767611 129901764423547613651417)
            ·
              refine ⟨97426323317660710238563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129901764423547613651417 97426323317660710238563)
              ·
                refine ⟨146139484976491065357845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97426323317660710238563 146139484976491065357845)
                ·
                  refine ⟨6850288358273018688649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 146139484976491065357845 6850288358273018688649)
                  ·
                    rfl

theorem cell21_30017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 6].length) (baseStart_30017 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_30017 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_30017 prefixEnd_30017 := by exact prefixLift 30017
  have htrace : WordTrace (prefixWord ++ tailWord_30017) baseStart_30017 baseEnd_30017 := by
    simpa [prefixWord, tailWord_30017, baseEnd_30017] using wordTrace_append hprefix tailTrace_30017
  have hstable : (prefixWord ++ tailWord_30017).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30017).length < 2 ^ (prefixWord ++ tailWord_30017).sum := by decide
  have hdescent : baseEnd_30017 < baseStart_30017 := by decide
  rcases family_descends (prefixWord ++ tailWord_30017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30020 : List Nat := [2, 3, 4, 1, 1, 3, 1, 1, 5]
def baseStart_30020 : Nat := 118140960795 + 30020 * 2 ^ 59
def prefixEnd_30020 : Nat := 4983230072969 + 3 ^ 40 * 30020 * 2
def baseEnd_30020 : Nat := 6850972999145680138643

theorem tailTrace_30020 : CollatzResearch.WordTrace tailWord_30020 prefixEnd_30020 6850972999145680138643 := by
  unfold tailWord_30020
  simp only [CollatzResearch.WordTrace]
  refine ⟨547459675625070926463757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 729946234166761235285009 547459675625070926463757)
  ·
    refine ⟨205297378359401597423909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 547459675625070926463757 205297378359401597423909)
    ·
      refine ⟨38493258442387799516983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205297378359401597423909 38493258442387799516983)
      ·
        refine ⟨57739887663581699275475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38493258442387799516983 57739887663581699275475)
        ·
          refine ⟨86609831495372548913213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57739887663581699275475 86609831495372548913213)
          ·
            refine ⟨32478686810764705842455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86609831495372548913213 32478686810764705842455)
            ·
              refine ⟨48718030216147058763683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32478686810764705842455 48718030216147058763683)
              ·
                refine ⟨73077045324220588145525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48718030216147058763683 73077045324220588145525)
                ·
                  refine ⟨6850972999145680138643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73077045324220588145525 6850972999145680138643)
                  ·
                    rfl

theorem cell21_30020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_30020 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_30020 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_30020 prefixEnd_30020 := by exact prefixLift 30020
  have htrace : WordTrace (prefixWord ++ tailWord_30020) baseStart_30020 baseEnd_30020 := by
    simpa [prefixWord, tailWord_30020, baseEnd_30020] using wordTrace_append hprefix tailTrace_30020
  have hstable : (prefixWord ++ tailWord_30020).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30020).length < 2 ^ (prefixWord ++ tailWord_30020).sum := by decide
  have hdescent : baseEnd_30020 < baseStart_30020 := by decide
  rcases family_descends (prefixWord ++ tailWord_30020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30183 : List Nat := [1, 1, 5, 2, 1, 4, 7]
def baseStart_30183 : Nat := 118140960795 + 30183 * 2 ^ 59
def prefixEnd_30183 : Nat := 4983230072969 + 3 ^ 40 * 30183 * 2
def baseEnd_30183 : Nat := 765352424432624324627

theorem tailTrace_30183 : CollatzResearch.WordTrace tailWord_30183 prefixEnd_30183 765352424432624324627 := by
  unfold tailWord_30183
  simp only [CollatzResearch.WordTrace]
  refine ⟨1100864449659620691111203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 733909633106413794074135 1100864449659620691111203)
  ·
    refine ⟨1651296674489431036666805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1100864449659620691111203 1651296674489431036666805)
    ·
      refine ⟨154809063233384159687513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1651296674489431036666805 154809063233384159687513)
      ·
        refine ⟨116106797425038119765635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154809063233384159687513 116106797425038119765635)
        ·
          refine ⟨174160196137557179648453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116106797425038119765635 174160196137557179648453)
          ·
            refine ⟨32655036775791971184085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174160196137557179648453 32655036775791971184085)
            ·
              refine ⟨765352424432624324627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 32655036775791971184085 765352424432624324627)
              ·
                rfl

theorem cell21_30183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 7].length) (baseStart_30183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_30183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_30183 prefixEnd_30183 := by exact prefixLift 30183
  have htrace : WordTrace (prefixWord ++ tailWord_30183) baseStart_30183 baseEnd_30183 := by
    simpa [prefixWord, tailWord_30183, baseEnd_30183] using wordTrace_append hprefix tailTrace_30183
  have hstable : (prefixWord ++ tailWord_30183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30183).length < 2 ^ (prefixWord ++ tailWord_30183).sum := by decide
  have hdescent : baseEnd_30183 < baseStart_30183 := by decide
  rcases family_descends (prefixWord ++ tailWord_30183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30189 : List Nat := [1, 5, 1, 3, 2, 1, 3, 2, 3]
def baseStart_30189 : Nat := 118140960795 + 30189 * 2 ^ 59
def prefixEnd_30189 : Nat := 4983230072969 + 3 ^ 40 * 30189 * 2
def baseEnd_30189 : Nat := 6889541101638941821631

theorem tailTrace_30189 : CollatzResearch.WordTrace tailWord_30189 prefixEnd_30189 6889541101638941821631 := by
  unfold tailWord_30189
  simp only [CollatzResearch.WordTrace]
  refine ⟨1101083287637883715829621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 734055525091922477219747 1101083287637883715829621)
  ·
    refine ⟨103226558216051598359027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1101083287637883715829621 103226558216051598359027)
    ·
      refine ⟨154839837324077397538541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103226558216051598359027 154839837324077397538541)
      ·
        refine ⟨58064938996529024076953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154839837324077397538541 58064938996529024076953)
        ·
          refine ⟨43548704247396768057715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58064938996529024076953 43548704247396768057715)
          ·
            refine ⟨65323056371095152086573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43548704247396768057715 65323056371095152086573)
            ·
              refine ⟨24496146139160682032465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65323056371095152086573 24496146139160682032465)
              ·
                refine ⟨18372109604370511524349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24496146139160682032465 18372109604370511524349)
                ·
                  refine ⟨6889541101638941821631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18372109604370511524349 6889541101638941821631)
                  ·
                    rfl

theorem cell21_30189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_30189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_30189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_30189 prefixEnd_30189 := by exact prefixLift 30189
  have htrace : WordTrace (prefixWord ++ tailWord_30189) baseStart_30189 baseEnd_30189 := by
    simpa [prefixWord, tailWord_30189, baseEnd_30189] using wordTrace_append hprefix tailTrace_30189
  have hstable : (prefixWord ++ tailWord_30189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30189).length < 2 ^ (prefixWord ++ tailWord_30189).sum := by decide
  have hdescent : baseEnd_30189 < baseStart_30189 := by decide
  rcases family_descends (prefixWord ++ tailWord_30189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30211 : List Nat := [1, 1, 1, 3, 2, 1, 2, 2, 8]
def baseStart_30211 : Nat := 118140960795 + 30211 * 2 ^ 59
def prefixEnd_30211 : Nat := 4983230072969 + 3 ^ 40 * 30211 * 2
def baseEnd_30211 : Nat := 6894561801371792454919

theorem tailTrace_30211 : CollatzResearch.WordTrace tailWord_30211 prefixEnd_30211 6894561801371792454919 := by
  unfold tailWord_30211
  simp only [CollatzResearch.WordTrace]
  refine ⟨1101885693558181473130487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 734590462372120982086991 1101885693558181473130487)
  ·
    refine ⟨1652828540337272209695731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1101885693558181473130487 1652828540337272209695731)
    ·
      refine ⟨2479242810505908314543597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1652828540337272209695731 2479242810505908314543597)
      ·
        refine ⟨929716053939715617953849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2479242810505908314543597 929716053939715617953849)
        ·
          refine ⟨697287040454786713465387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 929716053939715617953849 697287040454786713465387)
          ·
            refine ⟨1045930560682180070198081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 697287040454786713465387 1045930560682180070198081)
            ·
              refine ⟨784447920511635052648561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1045930560682180070198081 784447920511635052648561)
              ·
                refine ⟨588335940383726289486421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 784447920511635052648561 588335940383726289486421)
                ·
                  refine ⟨6894561801371792454919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 588335940383726289486421 6894561801371792454919)
                  ·
                    rfl

theorem cell21_30211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 8].length) (baseStart_30211 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_30211 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_30211 prefixEnd_30211 := by exact prefixLift 30211
  have htrace : WordTrace (prefixWord ++ tailWord_30211) baseStart_30211 baseEnd_30211 := by
    simpa [prefixWord, tailWord_30211, baseEnd_30211] using wordTrace_append hprefix tailTrace_30211
  have hstable : (prefixWord ++ tailWord_30211).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30211).length < 2 ^ (prefixWord ++ tailWord_30211).sum := by decide
  have hdescent : baseEnd_30211 < baseStart_30211 := by decide
  rcases family_descends (prefixWord ++ tailWord_30211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30248 : List Nat := [2, 1, 5, 2, 2, 1, 1, 4, 3]
def baseStart_30248 : Nat := 118140960795 + 30248 * 2 ^ 59
def prefixEnd_30248 : Nat := 4983230072969 + 3 ^ 40 * 30248 * 2
def baseEnd_30248 : Nat := 6903005705467950338177

theorem tailTrace_30248 : CollatzResearch.WordTrace tailWord_30248 prefixEnd_30248 6903005705467950338177 := by
  unfold tailWord_30248
  simp only [CollatzResearch.WordTrace]
  refine ⟨551617597212068396113699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 735490129616091194818265 551617597212068396113699)
  ·
    refine ⟨827426395818102594170549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 551617597212068396113699 827426395818102594170549)
    ·
      refine ⟨77571224607947118203489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 827426395818102594170549 77571224607947118203489)
      ·
        refine ⟨58178418455960338652617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77571224607947118203489 58178418455960338652617)
        ·
          refine ⟨43633813841970253989463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58178418455960338652617 43633813841970253989463)
          ·
            refine ⟨65450720762955380984195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43633813841970253989463 65450720762955380984195)
            ·
              refine ⟨98176081144433071476293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65450720762955380984195 98176081144433071476293)
              ·
                refine ⟨18408015214581200901805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98176081144433071476293 18408015214581200901805)
                ·
                  refine ⟨6903005705467950338177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18408015214581200901805 6903005705467950338177)
                  ·
                    rfl

theorem cell21_30248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 4, 3].length) (baseStart_30248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_30248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_30248 prefixEnd_30248 := by exact prefixLift 30248
  have htrace : WordTrace (prefixWord ++ tailWord_30248) baseStart_30248 baseEnd_30248 := by
    simpa [prefixWord, tailWord_30248, baseEnd_30248] using wordTrace_append hprefix tailTrace_30248
  have hstable : (prefixWord ++ tailWord_30248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30248).length < 2 ^ (prefixWord ++ tailWord_30248).sum := by decide
  have hdescent : baseEnd_30248 < baseStart_30248 := by decide
  rcases family_descends (prefixWord ++ tailWord_30248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30259 : List Nat := [1, 1, 1, 2, 4, 5, 1, 6]
def baseStart_30259 : Nat := 118140960795 + 30259 * 2 ^ 59
def prefixEnd_30259 : Nat := 4983230072969 + 3 ^ 40 * 30259 * 2
def baseEnd_30259 : Nat := 2301838685111458551607

theorem tailTrace_30259 : CollatzResearch.WordTrace tailWord_30259 prefixEnd_30259 2301838685111458551607 := by
  unfold tailWord_30259
  simp only [CollatzResearch.WordTrace]
  refine ⟨1103636397384285670877831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 735757598256190447251887 1103636397384285670877831)
  ·
    refine ⟨1655454596076428506316747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1103636397384285670877831 1655454596076428506316747)
    ·
      refine ⟨2483181894114642759475121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1655454596076428506316747 2483181894114642759475121)
      ·
        refine ⟨1862386420585982069606341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2483181894114642759475121 1862386420585982069606341)
        ·
          refine ⟨349197453859871638051189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1862386420585982069606341 349197453859871638051189)
          ·
            refine ⟨32737261299362966067299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 349197453859871638051189 32737261299362966067299)
            ·
              refine ⟨49105891949044449100949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32737261299362966067299 49105891949044449100949)
              ·
                refine ⟨2301838685111458551607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49105891949044449100949 2301838685111458551607)
                ·
                  rfl

theorem cell21_30259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 6].length) (baseStart_30259 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_30259 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_30259 prefixEnd_30259 := by exact prefixLift 30259
  have htrace : WordTrace (prefixWord ++ tailWord_30259) baseStart_30259 baseEnd_30259 := by
    simpa [prefixWord, tailWord_30259, baseEnd_30259] using wordTrace_append hprefix tailTrace_30259
  have hstable : (prefixWord ++ tailWord_30259).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30259).length < 2 ^ (prefixWord ++ tailWord_30259).sum := by decide
  have hdescent : baseEnd_30259 < baseStart_30259 := by decide
  rcases family_descends (prefixWord ++ tailWord_30259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30287 : List Nat := [1, 1, 2, 1, 1, 2, 3, 4, 6]
def baseStart_30287 : Nat := 118140960795 + 30287 * 2 ^ 59
def prefixEnd_30287 : Nat := 4983230072969 + 3 ^ 40 * 30287 * 2
def baseEnd_30287 : Nat := 6911906036812549188097

theorem tailTrace_30287 : CollatzResearch.WordTrace tailWord_30287 prefixEnd_30287 6911906036812549188097 := by
  unfold tailWord_30287
  simp only [CollatzResearch.WordTrace]
  refine ⟨1104657641282846452897115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 736438427521897635264743 1104657641282846452897115)
  ·
    refine ⟨1656986461924269679345673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1104657641282846452897115 1656986461924269679345673)
    ·
      refine ⟨1242739846443202259509255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1656986461924269679345673 1242739846443202259509255)
      ·
        refine ⟨1864109769664803389263883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1242739846443202259509255 1864109769664803389263883)
        ·
          refine ⟨2796164654497205083895825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1864109769664803389263883 2796164654497205083895825)
          ·
            refine ⟨2097123490872903812921869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2796164654497205083895825 2097123490872903812921869)
            ·
              refine ⟨786421309077338929845701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2097123490872903812921869 786421309077338929845701)
              ·
                refine ⟨147453995452001049346069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 786421309077338929845701 147453995452001049346069)
                ·
                  refine ⟨6911906036812549188097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 147453995452001049346069 6911906036812549188097)
                  ·
                    rfl

theorem cell21_30287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 6].length) (baseStart_30287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_30287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_30287 prefixEnd_30287 := by exact prefixLift 30287
  have htrace : WordTrace (prefixWord ++ tailWord_30287) baseStart_30287 baseEnd_30287 := by
    simpa [prefixWord, tailWord_30287, baseEnd_30287] using wordTrace_append hprefix tailTrace_30287
  have hstable : (prefixWord ++ tailWord_30287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30287).length < 2 ^ (prefixWord ++ tailWord_30287).sum := by decide
  have hdescent : baseEnd_30287 < baseStart_30287 := by decide
  rcases family_descends (prefixWord ++ tailWord_30287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30394 : List Nat := [3, 1, 1, 1, 2, 4, 2, 7]
def baseStart_30394 : Nat := 118140960795 + 30394 * 2 ^ 59
def prefixEnd_30394 : Nat := 4983230072969 + 3 ^ 40 * 30394 * 2
def baseEnd_30394 : Nat := 2312108298201380301515

theorem tailTrace_30394 : CollatzResearch.WordTrace tailWord_30394 prefixEnd_30394 2312108298201380301515 := by
  unfold tailWord_30394
  simp only [CollatzResearch.WordTrace]
  refine ⟨277140062973800931760559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 739040167930135818028157 277140062973800931760559)
  ·
    refine ⟨415710094460701397640839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277140062973800931760559 415710094460701397640839)
    ·
      refine ⟨623565141691052096461259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415710094460701397640839 623565141691052096461259)
      ·
        refine ⟨935347712536578144691889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 623565141691052096461259 935347712536578144691889)
        ·
          refine ⟨701510784402433608518917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 935347712536578144691889 701510784402433608518917)
          ·
            refine ⟨131533272075456301597297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 701510784402433608518917 131533272075456301597297)
            ·
              refine ⟨98649954056592226197973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131533272075456301597297 98649954056592226197973)
              ·
                refine ⟨2312108298201380301515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 98649954056592226197973 2312108298201380301515)
                ·
                  rfl

theorem cell21_30394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 7].length) (baseStart_30394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_30394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_30394 prefixEnd_30394 := by exact prefixLift 30394
  have htrace : WordTrace (prefixWord ++ tailWord_30394) baseStart_30394 baseEnd_30394 := by
    simpa [prefixWord, tailWord_30394, baseEnd_30394] using wordTrace_append hprefix tailTrace_30394
  have hstable : (prefixWord ++ tailWord_30394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30394).length < 2 ^ (prefixWord ++ tailWord_30394).sum := by decide
  have hdescent : baseEnd_30394 < baseStart_30394 := by decide
  rcases family_descends (prefixWord ++ tailWord_30394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30501 : List Nat := [1, 3, 1, 2, 3, 2, 2, 2, 5]
def baseStart_30501 : Nat := 118140960795 + 30501 * 2 ^ 59
def prefixEnd_30501 : Nat := 4983230072969 + 3 ^ 40 * 30501 * 2
def baseEnd_30501 : Nat := 6960743752395732620993

theorem tailTrace_30501 : CollatzResearch.WordTrace tailWord_30501 prefixEnd_30501 6960743752395732620993 := by
  unfold tailWord_30501
  simp only [CollatzResearch.WordTrace]
  refine ⟨1112462862507561001187357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 741641908338374000791571 1112462862507561001187357)
  ·
    refine ⟨417173573440335375445259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1112462862507561001187357 417173573440335375445259)
    ·
      refine ⟨625760360160503063167889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417173573440335375445259 625760360160503063167889)
      ·
        refine ⟨469320270120377297375917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 625760360160503063167889 469320270120377297375917)
        ·
          refine ⟨175995101295141486515969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 469320270120377297375917 175995101295141486515969)
          ·
            refine ⟨131996325971356114886977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175995101295141486515969 131996325971356114886977)
            ·
              refine ⟨98997244478517086165233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131996325971356114886977 98997244478517086165233)
              ·
                refine ⟨74247933358887814623925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98997244478517086165233 74247933358887814623925)
                ·
                  refine ⟨6960743752395732620993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74247933358887814623925 6960743752395732620993)
                  ·
                    rfl

theorem cell21_30501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 5].length) (baseStart_30501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_30501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_30501 prefixEnd_30501 := by exact prefixLift 30501
  have htrace : WordTrace (prefixWord ++ tailWord_30501) baseStart_30501 baseEnd_30501 := by
    simpa [prefixWord, tailWord_30501, baseEnd_30501] using wordTrace_append hprefix tailTrace_30501
  have hstable : (prefixWord ++ tailWord_30501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30501).length < 2 ^ (prefixWord ++ tailWord_30501).sum := by decide
  have hdescent : baseEnd_30501 < baseStart_30501 := by decide
  rcases family_descends (prefixWord ++ tailWord_30501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30504 : List Nat := [2, 1, 5, 1, 1, 4, 2, 5]
def baseStart_30504 : Nat := 118140960795 + 30504 * 2 ^ 59
def prefixEnd_30504 : Nat := 4983230072969 + 3 ^ 40 * 30504 * 2
def baseEnd_30504 : Nat := 2320476131089464690329

theorem tailTrace_30504 : CollatzResearch.WordTrace tailWord_30504 prefixEnd_30504 2320476131089464690329 := by
  unfold tailWord_30504
  simp only [CollatzResearch.WordTrace]
  refine ⟨556286140748346256773283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 741714854331128342364377 556286140748346256773283)
  ·
    refine ⟨834429211122519385159925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 556286140748346256773283 834429211122519385159925)
    ·
      refine ⟨78227738542736192358743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 834429211122519385159925 78227738542736192358743)
      ·
        refine ⟨117341607814104288538115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78227738542736192358743 117341607814104288538115)
        ·
          refine ⟨176012411721156432807173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117341607814104288538115 176012411721156432807173)
          ·
            refine ⟨33002327197716831151345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 176012411721156432807173 33002327197716831151345)
            ·
              refine ⟨24751745398287623363509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33002327197716831151345 24751745398287623363509)
              ·
                refine ⟨2320476131089464690329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24751745398287623363509 2320476131089464690329)
                ·
                  rfl

theorem cell21_30504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 5].length) (baseStart_30504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_30504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_30504 prefixEnd_30504 := by exact prefixLift 30504
  have htrace : WordTrace (prefixWord ++ tailWord_30504) baseStart_30504 baseEnd_30504 := by
    simpa [prefixWord, tailWord_30504, baseEnd_30504] using wordTrace_append hprefix tailTrace_30504
  have hstable : (prefixWord ++ tailWord_30504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30504).length < 2 ^ (prefixWord ++ tailWord_30504).sum := by decide
  have hdescent : baseEnd_30504 < baseStart_30504 := by decide
  rcases family_descends (prefixWord ++ tailWord_30504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30546 : List Nat := [3, 2, 2, 1, 1, 3, 1, 8]
def baseStart_30546 : Nat := 118140960795 + 30546 * 2 ^ 59
def prefixEnd_30546 : Nat := 4983230072969 + 3 ^ 40 * 30546 * 2
def baseEnd_30546 : Nat := 2323671121828551456967

theorem tailTrace_30546 : CollatzResearch.WordTrace tailWord_30546 prefixEnd_30546 2323671121828551456967 := by
  unfold tailWord_30546
  simp only [CollatzResearch.WordTrace]
  refine ⟨278526036836133421643873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 742736098229689124383661 278526036836133421643873)
  ·
    refine ⟨208894527627100066232905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278526036836133421643873 208894527627100066232905)
    ·
      refine ⟨156670895720325049674679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208894527627100066232905 156670895720325049674679)
      ·
        refine ⟨235006343580487574512019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156670895720325049674679 235006343580487574512019)
        ·
          refine ⟨352509515370731361768029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235006343580487574512019 352509515370731361768029)
          ·
            refine ⟨132191068264024260663011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 352509515370731361768029 132191068264024260663011)
            ·
              refine ⟨198286602396036390994517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132191068264024260663011 198286602396036390994517)
              ·
                refine ⟨2323671121828551456967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 198286602396036390994517 2323671121828551456967)
                ·
                  rfl

theorem cell21_30546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 8].length) (baseStart_30546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_30546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_30546 prefixEnd_30546 := by exact prefixLift 30546
  have htrace : WordTrace (prefixWord ++ tailWord_30546) baseStart_30546 baseEnd_30546 := by
    simpa [prefixWord, tailWord_30546, baseEnd_30546] using wordTrace_append hprefix tailTrace_30546
  have hstable : (prefixWord ++ tailWord_30546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30546).length < 2 ^ (prefixWord ++ tailWord_30546).sum := by decide
  have hdescent : baseEnd_30546 < baseStart_30546 := by decide
  rcases family_descends (prefixWord ++ tailWord_30546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30549 : List Nat := [1, 3, 2, 2, 2, 2, 4, 1, 4]
def baseStart_30549 : Nat := 118140960795 + 30549 * 2 ^ 59
def prefixEnd_30549 : Nat := 4983230072969 + 3 ^ 40 * 30549 * 2
def baseEnd_30549 : Nat := 6971698006358315820895

theorem tailTrace_30549 : CollatzResearch.WordTrace tailWord_30549 prefixEnd_30549 6971698006358315820895 := by
  unfold tailWord_30549
  simp only [CollatzResearch.WordTrace]
  refine ⟨1114213566333665198934701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 742809044222443465956467 1114213566333665198934701)
  ·
    refine ⟨417830087375124449600513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1114213566333665198934701 417830087375124449600513)
    ·
      refine ⟨313372565531343337200385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 417830087375124449600513 313372565531343337200385)
      ·
        refine ⟨235029424148507502900289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313372565531343337200385 235029424148507502900289)
        ·
          refine ⟨176272068111380627175217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235029424148507502900289 176272068111380627175217)
          ·
            refine ⟨132204051083535470381413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176272068111380627175217 132204051083535470381413)
            ·
              refine ⟨24788259578162900696515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132204051083535470381413 24788259578162900696515)
              ·
                refine ⟨37182389367244351044773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24788259578162900696515 37182389367244351044773)
                ·
                  refine ⟨6971698006358315820895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37182389367244351044773 6971698006358315820895)
                  ·
                    rfl

theorem cell21_30549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 1, 4].length) (baseStart_30549 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_30549 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_30549 prefixEnd_30549 := by exact prefixLift 30549
  have htrace : WordTrace (prefixWord ++ tailWord_30549) baseStart_30549 baseEnd_30549 := by
    simpa [prefixWord, tailWord_30549, baseEnd_30549] using wordTrace_append hprefix tailTrace_30549
  have hstable : (prefixWord ++ tailWord_30549).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30549).length < 2 ^ (prefixWord ++ tailWord_30549).sum := by decide
  have hdescent : baseEnd_30549 < baseStart_30549 := by decide
  rcases family_descends (prefixWord ++ tailWord_30549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30614 : List Nat := [5, 3, 1, 1, 2, 1, 3, 5]
def baseStart_30614 : Nat := 118140960795 + 30614 * 2 ^ 59
def prefixEnd_30614 : Nat := 4983230072969 + 3 ^ 40 * 30614 * 2
def baseEnd_30614 : Nat := 2328843963977549079143

theorem tailTrace_30614 : CollatzResearch.WordTrace tailWord_30614 prefixEnd_30614 2328843963977549079143 := by
  unfold tailWord_30614
  simp only [CollatzResearch.WordTrace]
  refine ⟨69786519443636331253181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 744389540732120866700597 69786519443636331253181)
  ·
    refine ⟨26169944791363624219943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69786519443636331253181 26169944791363624219943)
    ·
      refine ⟨39254917187045436329915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26169944791363624219943 39254917187045436329915)
      ·
        refine ⟨58882375780568154494873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39254917187045436329915 58882375780568154494873)
        ·
          refine ⟨44161781835426115871155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58882375780568154494873 44161781835426115871155)
          ·
            refine ⟨66242672753139173806733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44161781835426115871155 66242672753139173806733)
            ·
              refine ⟨24841002282427190177525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66242672753139173806733 24841002282427190177525)
              ·
                refine ⟨2328843963977549079143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24841002282427190177525 2328843963977549079143)
                ·
                  rfl

theorem cell21_30614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_30614 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_30614 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_30614 prefixEnd_30614 := by exact prefixLift 30614
  have htrace : WordTrace (prefixWord ++ tailWord_30614) baseStart_30614 baseEnd_30614 := by
    simpa [prefixWord, tailWord_30614, baseEnd_30614] using wordTrace_append hprefix tailTrace_30614
  have hstable : (prefixWord ++ tailWord_30614).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30614).length < 2 ^ (prefixWord ++ tailWord_30614).sum := by decide
  have hdescent : baseEnd_30614 < baseStart_30614 := by decide
  rcases family_descends (prefixWord ++ tailWord_30614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30653 : List Nat := [1, 4, 1, 2, 3, 1, 1, 3, 5]
def baseStart_30653 : Nat := 118140960795 + 30653 * 2 ^ 59
def prefixEnd_30653 : Nat := 4983230072969 + 3 ^ 40 * 30653 * 2
def baseEnd_30653 : Nat := 6995432223277246087349

theorem tailTrace_30653 : CollatzResearch.WordTrace tailWord_30653 prefixEnd_30653 6995432223277246087349 := by
  unfold tailWord_30653
  simp only [CollatzResearch.WordTrace]
  refine ⟨1118006757956890960720613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 745337838637927307147075 1118006757956890960720613)
  ·
    refine ⟨209626267116917055135115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1118006757956890960720613 209626267116917055135115)
    ·
      refine ⟨314439400675375582702673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209626267116917055135115 314439400675375582702673)
      ·
        refine ⟨235829550506531687027005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314439400675375582702673 235829550506531687027005)
        ·
          refine ⟨88436081439949382635127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235829550506531687027005 88436081439949382635127)
          ·
            refine ⟨132654122159924073952691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88436081439949382635127 132654122159924073952691)
            ·
              refine ⟨198981183239886110929037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132654122159924073952691 198981183239886110929037)
              ·
                refine ⟨74617943714957291598389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198981183239886110929037 74617943714957291598389)
                ·
                  refine ⟨6995432223277246087349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74617943714957291598389 6995432223277246087349)
                  ·
                    rfl

theorem cell21_30653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_30653 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_30653 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_30653 prefixEnd_30653 := by exact prefixLift 30653
  have htrace : WordTrace (prefixWord ++ tailWord_30653) baseStart_30653 baseEnd_30653 := by
    simpa [prefixWord, tailWord_30653, baseEnd_30653] using wordTrace_append hprefix tailTrace_30653
  have hstable : (prefixWord ++ tailWord_30653).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30653).length < 2 ^ (prefixWord ++ tailWord_30653).sum := by decide
  have hdescent : baseEnd_30653 < baseStart_30653 := by decide
  rcases family_descends (prefixWord ++ tailWord_30653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30687 : List Nat := [1, 1, 2, 3, 4, 3, 1, 3, 3]
def baseStart_30687 : Nat := 118140960795 + 30687 * 2 ^ 59
def prefixEnd_30687 : Nat := 4983230072969 + 3 ^ 40 * 30687 * 2
def baseEnd_30687 : Nat := 7003191486500742520613

theorem tailTrace_30687 : CollatzResearch.WordTrace tailWord_30687 prefixEnd_30687 7003191486500742520613 := by
  unfold tailWord_30687
  simp only [CollatzResearch.WordTrace]
  refine ⟨1119246839833714767458315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 746164559889143178305543 1119246839833714767458315)
  ·
    refine ⟨1678870259750572151187473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1119246839833714767458315 1678870259750572151187473)
    ·
      refine ⟨1259152694812929113390605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1678870259750572151187473 1259152694812929113390605)
      ·
        refine ⟨472182260554848417521477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1259152694812929113390605 472182260554848417521477)
        ·
          refine ⟨88534173854034078285277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 472182260554848417521477 88534173854034078285277)
          ·
            refine ⟨33200315195262779356979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88534173854034078285277 33200315195262779356979)
            ·
              refine ⟨49800472792894169035469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33200315195262779356979 49800472792894169035469)
              ·
                refine ⟨18675177297335313388301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49800472792894169035469 18675177297335313388301)
                ·
                  refine ⟨7003191486500742520613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18675177297335313388301 7003191486500742520613)
                  ·
                    rfl

theorem cell21_30687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 3, 3].length) (baseStart_30687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_30687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_30687 prefixEnd_30687 := by exact prefixLift 30687
  have htrace : WordTrace (prefixWord ++ tailWord_30687) baseStart_30687 baseEnd_30687 := by
    simpa [prefixWord, tailWord_30687, baseEnd_30687] using wordTrace_append hprefix tailTrace_30687
  have hstable : (prefixWord ++ tailWord_30687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30687).length < 2 ^ (prefixWord ++ tailWord_30687).sum := by decide
  have hdescent : baseEnd_30687 < baseStart_30687 := by decide
  rcases family_descends (prefixWord ++ tailWord_30687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30718 : List Nat := [4, 2, 2, 2, 1, 1, 4, 1, 4]
def baseStart_30718 : Nat := 118140960795 + 30718 * 2 ^ 59
def prefixEnd_30718 : Nat := 4983230072969 + 3 ^ 40 * 30718 * 2
def baseEnd_30718 : Nat := 7010266108851577503883

theorem tailTrace_30718 : CollatzResearch.WordTrace tailWord_30718 prefixEnd_30718 7010266108851577503883 := by
  unfold tailWord_30718
  simp only [CollatzResearch.WordTrace]
  refine ⟨140047187840175882729601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 746918335147604707891205 140047187840175882729601)
  ·
    refine ⟨105035390880131912047201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140047187840175882729601 105035390880131912047201)
    ·
      refine ⟨78776543160098934035401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105035390880131912047201 78776543160098934035401)
      ·
        refine ⟨59082407370074200526551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78776543160098934035401 59082407370074200526551)
        ·
          refine ⟨88623611055111300789827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59082407370074200526551 88623611055111300789827)
          ·
            refine ⟨132935416582666951184741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88623611055111300789827 132935416582666951184741)
            ·
              refine ⟨24925390609250053347139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132935416582666951184741 24925390609250053347139)
              ·
                refine ⟨37388085913875080020709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24925390609250053347139 37388085913875080020709)
                ·
                  refine ⟨7010266108851577503883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37388085913875080020709 7010266108851577503883)
                  ·
                    rfl

theorem cell21_30718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_30718 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_30718 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_30718 prefixEnd_30718 := by exact prefixLift 30718
  have htrace : WordTrace (prefixWord ++ tailWord_30718) baseStart_30718 baseEnd_30718 := by
    simpa [prefixWord, tailWord_30718, baseEnd_30718] using wordTrace_append hprefix tailTrace_30718
  have hstable : (prefixWord ++ tailWord_30718).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30718).length < 2 ^ (prefixWord ++ tailWord_30718).sum := by decide
  have hdescent : baseEnd_30718 < baseStart_30718 := by decide
  rcases family_descends (prefixWord ++ tailWord_30718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30757 : List Nat := [1, 3, 1, 2, 2, 12]
def baseStart_30757 : Nat := 118140960795 + 30757 * 2 ^ 59
def prefixEnd_30757 : Nat := 4983230072969 + 3 ^ 40 * 30757 * 2
def baseEnd_30757 : Nat := 259969127414673198289

theorem tailTrace_30757 : CollatzResearch.WordTrace tailWord_30757 prefixEnd_30757 259969127414673198289 := by
  unfold tailWord_30757
  simp only [CollatzResearch.WordTrace]
  refine ⟨1121799949580116722506525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 747866633053411148337683 1121799949580116722506525)
  ·
    refine ⟨420674981092543770939947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1121799949580116722506525 420674981092543770939947)
    ·
      refine ⟨631012471638815656409921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420674981092543770939947 631012471638815656409921)
      ·
        refine ⟨473259353729111742307441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 631012471638815656409921 473259353729111742307441)
        ·
          refine ⟨354944515296833806730581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 473259353729111742307441 354944515296833806730581)
          ·
            refine ⟨259969127414673198289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 354944515296833806730581 259969127414673198289)
            ·
              rfl

theorem cell21_30757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 12].length) (baseStart_30757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_30757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_30757 prefixEnd_30757 := by exact prefixLift 30757
  have htrace : WordTrace (prefixWord ++ tailWord_30757) baseStart_30757 baseEnd_30757 := by
    simpa [prefixWord, tailWord_30757, baseEnd_30757] using wordTrace_append hprefix tailTrace_30757
  have hstable : (prefixWord ++ tailWord_30757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30757).length < 2 ^ (prefixWord ++ tailWord_30757).sum := by decide
  have hdescent : baseEnd_30757 < baseStart_30757 := by decide
  rcases family_descends (prefixWord ++ tailWord_30757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30833 : List Nat := [1, 2, 2, 2, 1, 1, 4, 8]
def baseStart_30833 : Nat := 118140960795 + 30833 * 2 ^ 59
def prefixEnd_30833 : Nat := 4983230072969 + 3 ^ 40 * 30833 * 2
def baseEnd_30833 : Nat := 2345503558545644362327

theorem tailTrace_30833 : CollatzResearch.WordTrace tailWord_30833 prefixEnd_30833 2345503558545644362327 := by
  unfold tailWord_30833
  simp only [CollatzResearch.WordTrace]
  refine ⟨1124571897304781702273153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 749714598203187801515435 1124571897304781702273153)
  ·
    refine ⟨843428922978586276704865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1124571897304781702273153 843428922978586276704865)
    ·
      refine ⟨632571692233939707528649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 843428922978586276704865 632571692233939707528649)
      ·
        refine ⟨474428769175454780646487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 632571692233939707528649 474428769175454780646487)
        ·
          refine ⟨711643153763182170969731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474428769175454780646487 711643153763182170969731)
          ·
            refine ⟨1067464730644773256454597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 711643153763182170969731 1067464730644773256454597)
            ·
              refine ⟨200149636995894985585237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1067464730644773256454597 200149636995894985585237)
              ·
                refine ⟨2345503558545644362327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 200149636995894985585237 2345503558545644362327)
                ·
                  rfl

theorem cell21_30833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 8].length) (baseStart_30833 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_30833 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_30833 prefixEnd_30833 := by exact prefixLift 30833
  have htrace : WordTrace (prefixWord ++ tailWord_30833) baseStart_30833 baseEnd_30833 := by
    simpa [prefixWord, tailWord_30833, baseEnd_30833] using wordTrace_append hprefix tailTrace_30833
  have hstable : (prefixWord ++ tailWord_30833).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30833).length < 2 ^ (prefixWord ++ tailWord_30833).sum := by decide
  have hdescent : baseEnd_30833 < baseStart_30833 := by decide
  rcases family_descends (prefixWord ++ tailWord_30833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30881 : List Nat := [1, 2, 3, 3, 1, 2, 3, 1, 5]
def baseStart_30881 : Nat := 118140960795 + 30881 * 2 ^ 59
def prefixEnd_30881 : Nat := 4983230072969 + 3 ^ 40 * 30881 * 2
def baseEnd_30881 : Nat := 7047464929599516286883

theorem tailTrace_30881 : CollatzResearch.WordTrace tailWord_30881 prefixEnd_30881 7047464929599516286883 := by
  unfold tailWord_30881
  simp only [CollatzResearch.WordTrace]
  refine ⟨1126322601130885900020497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 750881734087257266680331 1126322601130885900020497)
  ·
    refine ⟨844741950848164425015373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1126322601130885900020497 844741950848164425015373)
    ·
      refine ⟨316778231568061659380765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 844741950848164425015373 316778231568061659380765)
      ·
        refine ⟨118791836838023122267787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 316778231568061659380765 118791836838023122267787)
        ·
          refine ⟨178187755257034683401681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118791836838023122267787 178187755257034683401681)
          ·
            refine ⟨133640816442776012551261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178187755257034683401681 133640816442776012551261)
            ·
              refine ⟨50115306166041004706723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133640816442776012551261 50115306166041004706723)
              ·
                refine ⟨75172959249061507060085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50115306166041004706723 75172959249061507060085)
                ·
                  refine ⟨7047464929599516286883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75172959249061507060085 7047464929599516286883)
                  ·
                    rfl

theorem cell21_30881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 5].length) (baseStart_30881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_30881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_30881 prefixEnd_30881 := by exact prefixLift 30881
  have htrace : WordTrace (prefixWord ++ tailWord_30881) baseStart_30881 baseEnd_30881 := by
    simpa [prefixWord, tailWord_30881, baseEnd_30881] using wordTrace_append hprefix tailTrace_30881
  have hstable : (prefixWord ++ tailWord_30881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30881).length < 2 ^ (prefixWord ++ tailWord_30881).sum := by decide
  have hdescent : baseEnd_30881 < baseStart_30881 := by decide
  rcases family_descends (prefixWord ++ tailWord_30881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30887 : List Nat := [1, 1, 6, 2, 3, 1, 2, 1, 4]
def baseStart_30887 : Nat := 118140960795 + 30887 * 2 ^ 59
def prefixEnd_30887 : Nat := 4983230072969 + 3 ^ 40 * 30887 * 2
def baseEnd_30887 : Nat := 7048834211344839186871

theorem tailTrace_30887 : CollatzResearch.WordTrace tailWord_30887 prefixEnd_30887 7048834211344839186871 := by
  unfold tailWord_30887
  simp only [CollatzResearch.WordTrace]
  refine ⟨1126541439109148924738915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 751027626072765949825943 1126541439109148924738915)
  ·
    refine ⟨1689812158663723387108373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1126541439109148924738915 1689812158663723387108373)
    ·
      refine ⟨79209944937362033770705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1689812158663723387108373 79209944937362033770705)
      ·
        refine ⟨59407458703021525328029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79209944937362033770705 59407458703021525328029)
        ·
          refine ⟨22277797013633071998011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59407458703021525328029 22277797013633071998011)
          ·
            refine ⟨33416695520449607997017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22277797013633071998011 33416695520449607997017)
            ·
              refine ⟨25062521640337205997763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33416695520449607997017 25062521640337205997763)
              ·
                refine ⟨37593782460505808996645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25062521640337205997763 37593782460505808996645)
                ·
                  refine ⟨7048834211344839186871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37593782460505808996645 7048834211344839186871)
                  ·
                    rfl

theorem cell21_30887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 1, 4].length) (baseStart_30887 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_30887 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_30887 prefixEnd_30887 := by exact prefixLift 30887
  have htrace : WordTrace (prefixWord ++ tailWord_30887) baseStart_30887 baseEnd_30887 := by
    simpa [prefixWord, tailWord_30887, baseEnd_30887] using wordTrace_append hprefix tailTrace_30887
  have hstable : (prefixWord ++ tailWord_30887).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30887).length < 2 ^ (prefixWord ++ tailWord_30887).sum := by decide
  have hdescent : baseEnd_30887 < baseStart_30887 := by decide
  rcases family_descends (prefixWord ++ tailWord_30887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_30985 : List Nat := [1, 2, 1, 1, 3, 5, 8]
def baseStart_30985 : Nat := 118140960795 + 30985 * 2 ^ 59
def prefixEnd_30985 : Nat := 4983230072969 + 3 ^ 40 * 30985 * 2
def baseEnd_30985 : Nat := 785688794057605172593

theorem tailTrace_30985 : CollatzResearch.WordTrace tailWord_30985 prefixEnd_30985 785688794057605172593 := by
  unfold tailWord_30985
  simp only [CollatzResearch.WordTrace]
  refine ⟨1130115792754111661806409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 753410528502741107870939 1130115792754111661806409)
  ·
    refine ⟨847586844565583746354807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1130115792754111661806409 847586844565583746354807)
    ·
      refine ⟨1271380266848375619532211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 847586844565583746354807 1271380266848375619532211)
      ·
        refine ⟨1907070400272563429298317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1271380266848375619532211 1907070400272563429298317)
        ·
          refine ⟨715151400102211285986869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1907070400272563429298317 715151400102211285986869)
          ·
            refine ⟨67045443759582308061269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 715151400102211285986869 67045443759582308061269)
            ·
              refine ⟨785688794057605172593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 67045443759582308061269 785688794057605172593)
              ·
                rfl

theorem cell21_30985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 8].length) (baseStart_30985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_30985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_30985 prefixEnd_30985 := by exact prefixLift 30985
  have htrace : WordTrace (prefixWord ++ tailWord_30985) baseStart_30985 baseEnd_30985 := by
    simpa [prefixWord, tailWord_30985, baseEnd_30985] using wordTrace_append hprefix tailTrace_30985
  have hstable : (prefixWord ++ tailWord_30985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_30985).length < 2 ^ (prefixWord ++ tailWord_30985).sum := by decide
  have hdescent : baseEnd_30985 < baseStart_30985 := by decide
  rcases family_descends (prefixWord ++ tailWord_30985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31047 : List Nat := [1, 1, 4, 1, 2, 2, 2, 4, 4]
def baseStart_31047 : Nat := 118140960795 + 31047 * 2 ^ 59
def prefixEnd_31047 : Nat := 4983230072969 + 3 ^ 40 * 31047 * 2
def baseEnd_31047 : Nat := 7085348391220116519877

theorem tailTrace_31047 : CollatzResearch.WordTrace tailWord_31047 prefixEnd_31047 7085348391220116519877 := by
  unfold tailWord_31047
  simp only [CollatzResearch.WordTrace]
  refine ⟨1132377118529496250563395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 754918079019664167042263 1132377118529496250563395)
  ·
    refine ⟨1698565677794244375845093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1132377118529496250563395 1698565677794244375845093)
    ·
      refine ⟨318481064586420820470955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1698565677794244375845093 318481064586420820470955)
      ·
        refine ⟨477721596879631230706433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318481064586420820470955 477721596879631230706433)
        ·
          refine ⟨358291197659723423029825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 477721596879631230706433 358291197659723423029825)
          ·
            refine ⟨268718398244792567272369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 358291197659723423029825 268718398244792567272369)
            ·
              refine ⟨201538798683594425454277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268718398244792567272369 201538798683594425454277)
              ·
                refine ⟨37788524753173954772677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 201538798683594425454277 37788524753173954772677)
                ·
                  refine ⟨7085348391220116519877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37788524753173954772677 7085348391220116519877)
                  ·
                    rfl

theorem cell21_31047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 4, 4].length) (baseStart_31047 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_31047 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_31047 prefixEnd_31047 := by exact prefixLift 31047
  have htrace : WordTrace (prefixWord ++ tailWord_31047) baseStart_31047 baseEnd_31047 := by
    simpa [prefixWord, tailWord_31047, baseEnd_31047] using wordTrace_append hprefix tailTrace_31047
  have hstable : (prefixWord ++ tailWord_31047).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31047).length < 2 ^ (prefixWord ++ tailWord_31047).sum := by decide
  have hdescent : baseEnd_31047 < baseStart_31047 := by decide
  rcases family_descends (prefixWord ++ tailWord_31047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31157 : List Nat := [1, 3, 3, 2, 3, 2, 1, 2, 4]
def baseStart_31157 : Nat := 118140960795 + 31157 * 2 ^ 59
def prefixEnd_31157 : Nat := 4983230072969 + 3 ^ 40 * 31157 * 2
def baseEnd_31157 : Nat := 7110451889884369686319

theorem tailTrace_31157 : CollatzResearch.WordTrace tailWord_31157 prefixEnd_31157 7110451889884369686319 := by
  unfold tailWord_31157
  simp only [CollatzResearch.WordTrace]
  refine ⟨1136389148130985037067725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 757592765420656691378483 1136389148130985037067725)
  ·
    refine ⟨426145930549119388900397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1136389148130985037067725 426145930549119388900397)
    ·
      refine ⟨159804723955919770837649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 426145930549119388900397 159804723955919770837649)
      ·
        refine ⟨119853542966939828128237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159804723955919770837649 119853542966939828128237)
        ·
          refine ⟨44945078612602435548089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119853542966939828128237 44945078612602435548089)
          ·
            refine ⟨33708808959451826661067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44945078612602435548089 33708808959451826661067)
            ·
              refine ⟨50563213439177739991601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33708808959451826661067 50563213439177739991601)
              ·
                refine ⟨37922410079383304993701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50563213439177739991601 37922410079383304993701)
                ·
                  refine ⟨7110451889884369686319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37922410079383304993701 7110451889884369686319)
                  ·
                    rfl

theorem cell21_31157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 2, 4].length) (baseStart_31157 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_31157 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_31157 prefixEnd_31157 := by exact prefixLift 31157
  have htrace : WordTrace (prefixWord ++ tailWord_31157) baseStart_31157 baseEnd_31157 := by
    simpa [prefixWord, tailWord_31157, baseEnd_31157] using wordTrace_append hprefix tailTrace_31157
  have hstable : (prefixWord ++ tailWord_31157).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31157).length < 2 ^ (prefixWord ++ tailWord_31157).sum := by decide
  have hdescent : baseEnd_31157 < baseStart_31157 := by decide
  rcases family_descends (prefixWord ++ tailWord_31157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31233 : List Nat := [1, 2, 4, 1, 3, 3, 2, 1, 4]
def baseStart_31233 : Nat := 118140960795 + 31233 * 2 ^ 59
def prefixEnd_31233 : Nat := 4983230072969 + 3 ^ 40 * 31233 * 2
def baseEnd_31233 : Nat := 7127796125325126419497

theorem tailTrace_31233 : CollatzResearch.WordTrace tailWord_31233 prefixEnd_31233 7127796125325126419497 := by
  unfold tailWord_31233
  simp only [CollatzResearch.WordTrace]
  refine ⟨1139161095855650016834353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 759440730570433344556235 1139161095855650016834353)
  ·
    refine ⟨854370821891737512625765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1139161095855650016834353 854370821891737512625765)
    ·
      refine ⟨160194529104700783617331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 854370821891737512625765 160194529104700783617331)
      ·
        refine ⟨240291793657051175425997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160194529104700783617331 240291793657051175425997)
        ·
          refine ⟨90109422621394190784749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240291793657051175425997 90109422621394190784749)
          ·
            refine ⟨33791033483022821544281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90109422621394190784749 33791033483022821544281)
            ·
              refine ⟨25343275112267116158211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33791033483022821544281 25343275112267116158211)
              ·
                refine ⟨38014912668400674237317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25343275112267116158211 38014912668400674237317)
                ·
                  refine ⟨7127796125325126419497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38014912668400674237317 7127796125325126419497)
                  ·
                    rfl

theorem cell21_31233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 1, 4].length) (baseStart_31233 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_31233 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_31233 prefixEnd_31233 := by exact prefixLift 31233
  have htrace : WordTrace (prefixWord ++ tailWord_31233) baseStart_31233 baseEnd_31233 := by
    simpa [prefixWord, tailWord_31233, baseEnd_31233] using wordTrace_append hprefix tailTrace_31233
  have hstable : (prefixWord ++ tailWord_31233).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31233).length < 2 ^ (prefixWord ++ tailWord_31233).sum := by decide
  have hdescent : baseEnd_31233 < baseStart_31233 := by decide
  rcases family_descends (prefixWord ++ tailWord_31233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31258 : List Nat := [3, 1, 1, 3, 1, 1, 2, 1, 8]
def baseStart_31258 : Nat := 118140960795 + 31258 * 2 ^ 59
def prefixEnd_31258 : Nat := 4983230072969 + 3 ^ 40 * 31258 * 2
def baseEnd_31258 : Nat := 7133501465930638502779

theorem tailTrace_31258 : CollatzResearch.WordTrace tailWord_31258 prefixEnd_31258 7133501465930638502779 := by
  unfold tailWord_31258
  simp only [CollatzResearch.WordTrace]
  refine ⟨285018230191269821623607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 760048613843386190996285 285018230191269821623607)
  ·
    refine ⟨427527345286904732435411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285018230191269821623607 427527345286904732435411)
    ·
      refine ⟨641291017930357098653117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427527345286904732435411 641291017930357098653117)
      ·
        refine ⟨240484131723883911994919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 641291017930357098653117 240484131723883911994919)
        ·
          refine ⟨360726197585825867992379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240484131723883911994919 360726197585825867992379)
          ·
            refine ⟨541089296378738801988569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360726197585825867992379 541089296378738801988569)
            ·
              refine ⟨405816972284054101491427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 541089296378738801988569 405816972284054101491427)
              ·
                refine ⟨608725458426081152237141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 405816972284054101491427 608725458426081152237141)
                ·
                  refine ⟨7133501465930638502779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 608725458426081152237141 7133501465930638502779)
                  ·
                    rfl

theorem cell21_31258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 8].length) (baseStart_31258 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_31258 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_31258 prefixEnd_31258 := by exact prefixLift 31258
  have htrace : WordTrace (prefixWord ++ tailWord_31258) baseStart_31258 baseEnd_31258 := by
    simpa [prefixWord, tailWord_31258, baseEnd_31258] using wordTrace_append hprefix tailTrace_31258
  have hstable : (prefixWord ++ tailWord_31258).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31258).length < 2 ^ (prefixWord ++ tailWord_31258).sum := by decide
  have hdescent : baseEnd_31258 < baseStart_31258 := by decide
  rcases family_descends (prefixWord ++ tailWord_31258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31306 : List Nat := [3, 1, 2, 1, 1, 5, 3, 5]
def baseStart_31306 : Nat := 118140960795 + 31306 * 2 ^ 59
def prefixEnd_31306 : Nat := 4983230072969 + 3 ^ 40 * 31306 * 2
def baseEnd_31306 : Nat := 2381485239964407234227

theorem tailTrace_31306 : CollatzResearch.WordTrace tailWord_31306 prefixEnd_31306 2381485239964407234227 := by
  unfold tailWord_31306
  simp only [CollatzResearch.WordTrace]
  refine ⟨285455906147795871060443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 761215749727455656161181 285455906147795871060443)
  ·
    refine ⟨428183859221693806590665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285455906147795871060443 428183859221693806590665)
    ·
      refine ⟨321137894416270354942999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 428183859221693806590665 321137894416270354942999)
      ·
        refine ⟨481706841624405532414499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321137894416270354942999 481706841624405532414499)
        ·
          refine ⟨722560262436608298621749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481706841624405532414499 722560262436608298621749)
          ·
            refine ⟨67740024603432027995789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 722560262436608298621749 67740024603432027995789)
            ·
              refine ⟨25402509226287010498421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67740024603432027995789 25402509226287010498421)
              ·
                refine ⟨2381485239964407234227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25402509226287010498421 2381485239964407234227)
                ·
                  rfl

theorem cell21_31306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 5].length) (baseStart_31306 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_31306 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_31306 prefixEnd_31306 := by exact prefixLift 31306
  have htrace : WordTrace (prefixWord ++ tailWord_31306) baseStart_31306 baseEnd_31306 := by
    simpa [prefixWord, tailWord_31306, baseEnd_31306] using wordTrace_append hprefix tailTrace_31306
  have hstable : (prefixWord ++ tailWord_31306).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31306).length < 2 ^ (prefixWord ++ tailWord_31306).sum := by decide
  have hdescent : baseEnd_31306 < baseStart_31306 := by decide
  rcases family_descends (prefixWord ++ tailWord_31306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31326 : List Nat := [4, 4, 1, 2, 1, 1, 1, 1, 6]
def baseStart_31326 : Nat := 118140960795 + 31326 * 2 ^ 59
def prefixEnd_31326 : Nat := 4983230072969 + 3 ^ 40 * 31326 * 2
def baseEnd_31326 : Nat := 7149019992377631369307

theorem tailTrace_31326 : CollatzResearch.WordTrace tailWord_31326 prefixEnd_31326 7149019992377631369307 := by
  unfold tailWord_31326
  simp only [CollatzResearch.WordTrace]
  refine ⟨142819135564840862496229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 761702056345817933313221 142819135564840862496229)
  ·
    refine ⟨26778587918407661718043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142819135564840862496229 26778587918407661718043)
    ·
      refine ⟨40167881877611492577065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26778587918407661718043 40167881877611492577065)
      ·
        refine ⟨30125911408208619432799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40167881877611492577065 30125911408208619432799)
        ·
          refine ⟨45188867112312929149199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30125911408208619432799 45188867112312929149199)
          ·
            refine ⟨67783300668469393723799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45188867112312929149199 67783300668469393723799)
            ·
              refine ⟨101674951002704090585699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67783300668469393723799 101674951002704090585699)
              ·
                refine ⟨152512426504056135878549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101674951002704090585699 152512426504056135878549)
                ·
                  refine ⟨7149019992377631369307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 152512426504056135878549 7149019992377631369307)
                  ·
                    rfl

theorem cell21_31326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_31326 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_31326 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_31326 prefixEnd_31326 := by exact prefixLift 31326
  have htrace : WordTrace (prefixWord ++ tailWord_31326) baseStart_31326 baseEnd_31326 := by
    simpa [prefixWord, tailWord_31326, baseEnd_31326] using wordTrace_append hprefix tailTrace_31326
  have hstable : (prefixWord ++ tailWord_31326).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31326).length < 2 ^ (prefixWord ++ tailWord_31326).sum := by decide
  have hdescent : baseEnd_31326 < baseStart_31326 := by decide
  rcases family_descends (prefixWord ++ tailWord_31326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31365 : List Nat := [1, 3, 1, 1, 4, 3, 1, 7]
def baseStart_31365 : Nat := 118140960795 + 31365 * 2 ^ 59
def prefixEnd_31365 : Nat := 4983230072969 + 3 ^ 40 * 31365 * 2
def baseEnd_31365 : Nat := 2385973441240743406409

theorem tailTrace_31365 : CollatzResearch.WordTrace tailWord_31365 prefixEnd_31365 2385973441240743406409 := by
  unfold tailWord_31365
  simp only [CollatzResearch.WordTrace]
  refine ⟨1143975531377436560639549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 762650354251624373759699 1143975531377436560639549)
  ·
    refine ⟨428990824266538710239831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1143975531377436560639549 428990824266538710239831)
    ·
      refine ⟨643486236399808065359747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428990824266538710239831 643486236399808065359747)
      ·
        refine ⟨965229354599712098039621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 643486236399808065359747 965229354599712098039621)
        ·
          refine ⟨180980503987446018382429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 965229354599712098039621 180980503987446018382429)
          ·
            refine ⟨67867688995292256893411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180980503987446018382429 67867688995292256893411)
            ·
              refine ⟨101801533492938385340117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67867688995292256893411 101801533492938385340117)
              ·
                refine ⟨2385973441240743406409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 101801533492938385340117 2385973441240743406409)
                ·
                  rfl

theorem cell21_31365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 7].length) (baseStart_31365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_31365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_31365 prefixEnd_31365 := by exact prefixLift 31365
  have htrace : WordTrace (prefixWord ++ tailWord_31365) baseStart_31365 baseEnd_31365 := by
    simpa [prefixWord, tailWord_31365, baseEnd_31365] using wordTrace_append hprefix tailTrace_31365
  have hstable : (prefixWord ++ tailWord_31365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31365).length < 2 ^ (prefixWord ++ tailWord_31365).sum := by decide
  have hdescent : baseEnd_31365 < baseStart_31365 := by decide
  rcases family_descends (prefixWord ++ tailWord_31365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31399 : List Nat := [1, 1, 6, 3, 1, 1, 2, 6]
def baseStart_31399 : Nat := 118140960795 + 31399 * 2 ^ 59
def prefixEnd_31399 : Nat := 4983230072969 + 3 ^ 40 * 31399 * 2
def baseEnd_31399 : Nat := 2388559862315242217497

theorem tailTrace_31399 : CollatzResearch.WordTrace tailWord_31399 prefixEnd_31399 2388559862315242217497 := by
  unfold tailWord_31399
  simp only [CollatzResearch.WordTrace]
  refine ⟨1145215613254260367377251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 763477075502840244918167 1145215613254260367377251)
  ·
    refine ⟨1717823419881390551065877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1145215613254260367377251 1717823419881390551065877)
    ·
      refine ⟨80522972806940182081213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1717823419881390551065877 80522972806940182081213)
      ·
        refine ⟨30196114802602568280455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80522972806940182081213 30196114802602568280455)
        ·
          refine ⟨45294172203903852420683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30196114802602568280455 45294172203903852420683)
          ·
            refine ⟨67941258305855778631025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45294172203903852420683 67941258305855778631025)
            ·
              refine ⟨50955943729391833973269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67941258305855778631025 50955943729391833973269)
              ·
                refine ⟨2388559862315242217497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50955943729391833973269 2388559862315242217497)
                ·
                  rfl

theorem cell21_31399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 6].length) (baseStart_31399 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_31399 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_31399 prefixEnd_31399 := by exact prefixLift 31399
  have htrace : WordTrace (prefixWord ++ tailWord_31399) baseStart_31399 baseEnd_31399 := by
    simpa [prefixWord, tailWord_31399, baseEnd_31399] using wordTrace_append hprefix tailTrace_31399
  have hstable : (prefixWord ++ tailWord_31399).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31399).length < 2 ^ (prefixWord ++ tailWord_31399).sum := by decide
  have hdescent : baseEnd_31399 < baseStart_31399 := by decide
  rcases family_descends (prefixWord ++ tailWord_31399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31506 : List Nat := [3, 2, 4, 1, 2, 1, 2, 1, 5]
def baseStart_31506 : Nat := 118140960795 + 31506 * 2 ^ 59
def prefixEnd_31506 : Nat := 4983230072969 + 3 ^ 40 * 31506 * 2
def baseEnd_31506 : Nat := 7190098444737318368939

theorem tailTrace_31506 : CollatzResearch.WordTrace tailWord_31506 prefixEnd_31506 7190098444737318368939 := by
  unfold tailWord_31506
  simp only [CollatzResearch.WordTrace]
  refine ⟨287279555966654410380593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 766078815911078427681581 287279555966654410380593)
  ·
    refine ⟨215459666974990807785445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 287279555966654410380593 215459666974990807785445)
    ·
      refine ⟨40398687557810776459771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 215459666974990807785445 40398687557810776459771)
      ·
        refine ⟨60598031336716164689657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40398687557810776459771 60598031336716164689657)
        ·
          refine ⟨45448523502537123517243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60598031336716164689657 45448523502537123517243)
          ·
            refine ⟨68172785253805685275865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45448523502537123517243 68172785253805685275865)
            ·
              refine ⟨51129588940354263956899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68172785253805685275865 51129588940354263956899)
              ·
                refine ⟨76694383410531395935349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51129588940354263956899 76694383410531395935349)
                ·
                  refine ⟨7190098444737318368939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76694383410531395935349 7190098444737318368939)
                  ·
                    rfl

theorem cell21_31506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_31506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_31506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_31506 prefixEnd_31506 := by exact prefixLift 31506
  have htrace : WordTrace (prefixWord ++ tailWord_31506) baseStart_31506 baseEnd_31506 := by
    simpa [prefixWord, tailWord_31506, baseEnd_31506] using wordTrace_append hprefix tailTrace_31506
  have hstable : (prefixWord ++ tailWord_31506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31506).length < 2 ^ (prefixWord ++ tailWord_31506).sum := by decide
  have hdescent : baseEnd_31506 < baseStart_31506 := by decide
  rcases family_descends (prefixWord ++ tailWord_31506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31520 : List Nat := [2, 1, 1, 5, 1, 3, 3, 1, 4]
def baseStart_31520 : Nat := 118140960795 + 31520 * 2 ^ 59
def prefixEnd_31520 : Nat := 4983230072969 + 3 ^ 40 * 31520 * 2
def baseEnd_31520 : Nat := 7193293435476405135577

theorem tailTrace_31520 : CollatzResearch.WordTrace tailWord_31520 prefixEnd_31520 7193293435476405135577 := by
  unfold tailWord_31520
  simp only [CollatzResearch.WordTrace]
  refine ⟨574814422907949016266007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 766419230543932021688009 574814422907949016266007)
  ·
    refine ⟨862221634361923524399011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 574814422907949016266007 862221634361923524399011)
    ·
      refine ⟨1293332451542885286598517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 862221634361923524399011 1293332451542885286598517)
      ·
        refine ⟨121249917332145495618611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1293332451542885286598517 121249917332145495618611)
        ·
          refine ⟨181874875998218243427917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121249917332145495618611 181874875998218243427917)
          ·
            refine ⟨68203078499331841285469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181874875998218243427917 68203078499331841285469)
            ·
              refine ⟨25576154437249440482051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68203078499331841285469 25576154437249440482051)
              ·
                refine ⟨38364231655874160723077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25576154437249440482051 38364231655874160723077)
                ·
                  refine ⟨7193293435476405135577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38364231655874160723077 7193293435476405135577)
                  ·
                    rfl

theorem cell21_31520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 1, 4].length) (baseStart_31520 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_31520 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_31520 prefixEnd_31520 := by exact prefixLift 31520
  have htrace : WordTrace (prefixWord ++ tailWord_31520) baseStart_31520 baseEnd_31520 := by
    simpa [prefixWord, tailWord_31520, baseEnd_31520] using wordTrace_append hprefix tailTrace_31520
  have hstable : (prefixWord ++ tailWord_31520).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31520).length < 2 ^ (prefixWord ++ tailWord_31520).sum := by decide
  have hdescent : baseEnd_31520 < baseStart_31520 := by decide
  rcases family_descends (prefixWord ++ tailWord_31520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31534 : List Nat := [4, 1, 3, 2, 1, 2, 1, 7]
def baseStart_31534 : Nat := 118140960795 + 31534 * 2 ^ 59
def prefixEnd_31534 : Nat := 4983230072969 + 3 ^ 40 * 31534 * 2
def baseEnd_31534 : Nat := 2398829475405163967405

theorem tailTrace_31534 : CollatzResearch.WordTrace tailWord_31534 prefixEnd_31534 2398829475405163967405 := by
  unfold tailWord_31534
  simp only [CollatzResearch.WordTrace]
  refine ⟨143767433470647302942707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 766759645176785615694437 143767433470647302942707)
  ·
    refine ⟨215651150205970954414061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143767433470647302942707 215651150205970954414061)
    ·
      refine ⟨80869181327239107905273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 215651150205970954414061 80869181327239107905273)
      ·
        refine ⟨60651885995429330928955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80869181327239107905273 60651885995429330928955)
        ·
          refine ⟨90977828993143996393433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60651885995429330928955 90977828993143996393433)
          ·
            refine ⟨68233371744857997295075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90977828993143996393433 68233371744857997295075)
            ·
              refine ⟨102350057617286995942613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68233371744857997295075 102350057617286995942613)
              ·
                refine ⟨2398829475405163967405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 102350057617286995942613 2398829475405163967405)
                ·
                  rfl

theorem cell21_31534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 7].length) (baseStart_31534 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_31534 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_31534 prefixEnd_31534 := by exact prefixLift 31534
  have htrace : WordTrace (prefixWord ++ tailWord_31534) baseStart_31534 baseEnd_31534 := by
    simpa [prefixWord, tailWord_31534, baseEnd_31534] using wordTrace_append hprefix tailTrace_31534
  have hstable : (prefixWord ++ tailWord_31534).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31534).length < 2 ^ (prefixWord ++ tailWord_31534).sum := by decide
  have hdescent : baseEnd_31534 < baseStart_31534 := by decide
  rcases family_descends (prefixWord ++ tailWord_31534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31540 : List Nat := [2, 5, 1, 1, 4, 1, 1, 3, 3]
def baseStart_31540 : Nat := 118140960795 + 31540 * 2 ^ 59
def prefixEnd_31540 : Nat := 4983230072969 + 3 ^ 40 * 31540 * 2
def baseEnd_31540 : Nat := 7197857707960814802203

theorem tailTrace_31540 : CollatzResearch.WordTrace tailWord_31540 prefixEnd_31540 7197857707960814802203 := by
  unfold tailWord_31540
  simp only [CollatzResearch.WordTrace]
  refine ⟨575179152871720724130037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 766905537162294298840049 575179152871720724130037)
  ·
    refine ⟨53923045581723817887191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 575179152871720724130037 53923045581723817887191)
    ·
      refine ⟨80884568372585726830787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53923045581723817887191 80884568372585726830787)
      ·
        refine ⟨121326852558878590246181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80884568372585726830787 121326852558878590246181)
        ·
          refine ⟨22748784854789735671159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121326852558878590246181 22748784854789735671159)
          ·
            refine ⟨34123177282184603506739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22748784854789735671159 34123177282184603506739)
            ·
              refine ⟨51184765923276905260109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34123177282184603506739 51184765923276905260109)
              ·
                refine ⟨19194287221228839472541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51184765923276905260109 19194287221228839472541)
                ·
                  refine ⟨7197857707960814802203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19194287221228839472541 7197857707960814802203)
                  ·
                    rfl

theorem cell21_31540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_31540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_31540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_31540 prefixEnd_31540 := by exact prefixLift 31540
  have htrace : WordTrace (prefixWord ++ tailWord_31540) baseStart_31540 baseEnd_31540 := by
    simpa [prefixWord, tailWord_31540, baseEnd_31540] using wordTrace_append hprefix tailTrace_31540
  have hstable : (prefixWord ++ tailWord_31540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31540).length < 2 ^ (prefixWord ++ tailWord_31540).sum := by decide
  have hdescent : baseEnd_31540 < baseStart_31540 := by decide
  rcases family_descends (prefixWord ++ tailWord_31540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31700 : List Nat := [2, 4, 1, 2, 1, 2, 2, 2, 5]
def baseStart_31700 : Nat := 118140960795 + 31700 * 2 ^ 59
def prefixEnd_31700 : Nat := 4983230072969 + 3 ^ 40 * 31700 * 2
def baseEnd_31700 : Nat := 7234371887836092135209

theorem tailTrace_31700 : CollatzResearch.WordTrace tailWord_31700 prefixEnd_31700 7234371887836092135209 := by
  unfold tailWord_31700
  simp only [CollatzResearch.WordTrace]
  refine ⟨578096992581894387042277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 770795990109192516056369 578096992581894387042277)
  ·
    refine ⟨108393186109105197570427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 578096992581894387042277 108393186109105197570427)
    ·
      refine ⟨162589779163657796355641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108393186109105197570427 162589779163657796355641)
      ·
        refine ⟨121942334372743347266731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162589779163657796355641 121942334372743347266731)
        ·
          refine ⟨182913501559115020900097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121942334372743347266731 182913501559115020900097)
          ·
            refine ⟨137185126169336265675073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182913501559115020900097 137185126169336265675073)
            ·
              refine ⟨102888844627002199256305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137185126169336265675073 102888844627002199256305)
              ·
                refine ⟨77166633470251649442229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102888844627002199256305 77166633470251649442229)
                ·
                  refine ⟨7234371887836092135209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77166633470251649442229 7234371887836092135209)
                  ·
                    rfl

theorem cell21_31700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_31700 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_31700 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_31700 prefixEnd_31700 := by exact prefixLift 31700
  have htrace : WordTrace (prefixWord ++ tailWord_31700) baseStart_31700 baseEnd_31700 := by
    simpa [prefixWord, tailWord_31700, baseEnd_31700] using wordTrace_append hprefix tailTrace_31700
  have hstable : (prefixWord ++ tailWord_31700).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31700).length < 2 ^ (prefixWord ++ tailWord_31700).sum := by decide
  have hdescent : baseEnd_31700 < baseStart_31700 := by decide
  rcases family_descends (prefixWord ++ tailWord_31700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31745 : List Nat := [1, 2, 4, 1, 2, 3, 2, 6]
def baseStart_31745 : Nat := 118140960795 + 31745 * 2 ^ 59
def prefixEnd_31745 : Nat := 4983230072969 + 3 ^ 40 * 31745 * 2
def baseEnd_31745 : Nat := 2414880500308671295039

theorem tailTrace_31745 : CollatzResearch.WordTrace tailWord_31745 prefixEnd_31745 2414880500308671295039 := by
  unfold tailWord_31745
  simp only [CollatzResearch.WordTrace]
  refine ⟨1157835270000761459472689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 771890180000507639648459 1157835270000761459472689)
  ·
    refine ⟨868376452500571094604517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1157835270000761459472689 868376452500571094604517)
    ·
      refine ⟨162820584843857080238347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 868376452500571094604517 162820584843857080238347)
      ·
        refine ⟨244230877265785620357521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162820584843857080238347 244230877265785620357521)
        ·
          refine ⟨183173157949339215268141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244230877265785620357521 183173157949339215268141)
          ·
            refine ⟨68689934231002205725553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183173157949339215268141 68689934231002205725553)
            ·
              refine ⟨51517450673251654294165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68689934231002205725553 51517450673251654294165)
              ·
                refine ⟨2414880500308671295039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51517450673251654294165 2414880500308671295039)
                ·
                  rfl

theorem cell21_31745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 6].length) (baseStart_31745 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_31745 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_31745 prefixEnd_31745 := by exact prefixLift 31745
  have htrace : WordTrace (prefixWord ++ tailWord_31745) baseStart_31745 baseEnd_31745 := by
    simpa [prefixWord, tailWord_31745, baseEnd_31745] using wordTrace_append hprefix tailTrace_31745
  have hstable : (prefixWord ++ tailWord_31745).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31745).length < 2 ^ (prefixWord ++ tailWord_31745).sum := by decide
  have hdescent : baseEnd_31745 < baseStart_31745 := by decide
  rcases family_descends (prefixWord ++ tailWord_31745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31852 : List Nat := [2, 2, 1, 1, 3, 2, 1, 6, 3]
def baseStart_31852 : Nat := 118140960795 + 31852 * 2 ^ 59
def prefixEnd_31852 : Nat := 4983230072969 + 3 ^ 40 * 31852 * 2
def baseEnd_31852 : Nat := 7269060358717605601565

theorem tailTrace_31852 : CollatzResearch.WordTrace tailWord_31852 prefixEnd_31852 7269060358717605601565 := by
  unfold tailWord_31852
  simp only [CollatzResearch.WordTrace]
  refine ⟨580868940306559366808905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 774491920408745822411873 580868940306559366808905)
  ·
    refine ⟨435651705229919525106679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 580868940306559366808905 435651705229919525106679)
    ·
      refine ⟨653477557844879287660019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435651705229919525106679 653477557844879287660019)
      ·
        refine ⟨980216336767318931490029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 653477557844879287660019 980216336767318931490029)
        ·
          refine ⟨367581126287744599308761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 980216336767318931490029 367581126287744599308761)
          ·
            refine ⟨275685844715808449481571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 367581126287744599308761 275685844715808449481571)
            ·
              refine ⟨413528767073712674222357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275685844715808449481571 413528767073712674222357)
              ·
                refine ⟨19384160956580281604173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 413528767073712674222357 19384160956580281604173)
                ·
                  refine ⟨7269060358717605601565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19384160956580281604173 7269060358717605601565)
                  ·
                    rfl

theorem cell21_31852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 6, 3].length) (baseStart_31852 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_31852 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_31852 prefixEnd_31852 := by exact prefixLift 31852
  have htrace : WordTrace (prefixWord ++ tailWord_31852) baseStart_31852 baseEnd_31852 := by
    simpa [prefixWord, tailWord_31852, baseEnd_31852] using wordTrace_append hprefix tailTrace_31852
  have hstable : (prefixWord ++ tailWord_31852).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31852).length < 2 ^ (prefixWord ++ tailWord_31852).sum := by decide
  have hdescent : baseEnd_31852 < baseStart_31852 := by decide
  rcases family_descends (prefixWord ++ tailWord_31852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31886 : List Nat := [4, 1, 1, 3, 2, 3, 1, 3, 3]
def baseStart_31886 : Nat := 118140960795 + 31886 * 2 ^ 59
def prefixEnd_31886 : Nat := 4983230072969 + 3 ^ 40 * 31886 * 2
def baseEnd_31886 : Nat := 7276819621941102034829

theorem tailTrace_31886 : CollatzResearch.WordTrace tailWord_31886 prefixEnd_31886 7276819621941102034829 := by
  unfold tailWord_31886
  simp only [CollatzResearch.WordTrace]
  refine ⟨145372245311242817544439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 775318641659961693570341 145372245311242817544439)
  ·
    refine ⟨218058367966864226316659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145372245311242817544439 218058367966864226316659)
    ·
      refine ⟨327087551950296339474989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 218058367966864226316659 327087551950296339474989)
      ·
        refine ⟨122657831981361127303121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 327087551950296339474989 122657831981361127303121)
        ·
          refine ⟨91993373986020845477341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122657831981361127303121 91993373986020845477341)
          ·
            refine ⟨34497515244757817054003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91993373986020845477341 34497515244757817054003)
            ·
              refine ⟨51746272867136725581005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34497515244757817054003 51746272867136725581005)
              ·
                refine ⟨19404852325176272092877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51746272867136725581005 19404852325176272092877)
                ·
                  refine ⟨7276819621941102034829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19404852325176272092877 7276819621941102034829)
                  ·
                    rfl

theorem cell21_31886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 3, 3].length) (baseStart_31886 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_31886 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_31886 prefixEnd_31886 := by exact prefixLift 31886
  have htrace : WordTrace (prefixWord ++ tailWord_31886) baseStart_31886 baseEnd_31886 := by
    simpa [prefixWord, tailWord_31886, baseEnd_31886] using wordTrace_append hprefix tailTrace_31886
  have hstable : (prefixWord ++ tailWord_31886).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31886).length < 2 ^ (prefixWord ++ tailWord_31886).sum := by decide
  have hdescent : baseEnd_31886 < baseStart_31886 := by decide
  rcases family_descends (prefixWord ++ tailWord_31886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31914 : List Nat := [3, 1, 5, 1, 1, 2, 2, 6]
def baseStart_31914 : Nat := 118140960795 + 31914 * 2 ^ 59
def prefixEnd_31914 : Nat := 4983230072969 + 3 ^ 40 * 31914 * 2
def baseEnd_31914 : Nat := 2427736534473091856035

theorem tailTrace_31914 : CollatzResearch.WordTrace tailWord_31914 prefixEnd_31914 2427736534473091856035 := by
  unfold tailWord_31914
  simp only [CollatzResearch.WordTrace]
  refine ⟨290999801597125830593699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 775999470925668881583197 290999801597125830593699)
  ·
    refine ⟨436499702395688745890549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290999801597125830593699 436499702395688745890549)
    ·
      refine ⟨40921847099595819927239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 436499702395688745890549 40921847099595819927239)
      ·
        refine ⟨61382770649393729890859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40921847099595819927239 61382770649393729890859)
        ·
          refine ⟨92074155974090594836289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61382770649393729890859 92074155974090594836289)
          ·
            refine ⟨69055616980567946127217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92074155974090594836289 69055616980567946127217)
            ·
              refine ⟨51791712735425959595413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69055616980567946127217 51791712735425959595413)
              ·
                refine ⟨2427736534473091856035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51791712735425959595413 2427736534473091856035)
                ·
                  rfl

theorem cell21_31914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 6].length) (baseStart_31914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_31914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_31914 prefixEnd_31914 := by exact prefixLift 31914
  have htrace : WordTrace (prefixWord ++ tailWord_31914) baseStart_31914 baseEnd_31914 := by
    simpa [prefixWord, tailWord_31914, baseEnd_31914] using wordTrace_append hprefix tailTrace_31914
  have hstable : (prefixWord ++ tailWord_31914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31914).length < 2 ^ (prefixWord ++ tailWord_31914).sum := by decide
  have hdescent : baseEnd_31914 < baseStart_31914 := by decide
  rcases family_descends (prefixWord ++ tailWord_31914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31917 : List Nat := [1, 5, 2, 1, 3, 2, 2, 1, 4]
def baseStart_31917 : Nat := 118140960795 + 31917 * 2 ^ 59
def prefixEnd_31917 : Nat := 4983230072969 + 3 ^ 40 * 31917 * 2
def baseEnd_31917 : Nat := 7283894244291937018099

theorem tailTrace_31917 : CollatzResearch.WordTrace tailWord_31917 prefixEnd_31917 7283894244291937018099 := by
  unfold tailWord_31917
  simp only [CollatzResearch.WordTrace]
  refine ⟨1164108625377634834734005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 776072416918423223156003 1164108625377634834734005)
  ·
    refine ⟨109135183629153265756313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1164108625377634834734005 109135183629153265756313)
    ·
      refine ⟨81851387721864949317235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109135183629153265756313 81851387721864949317235)
      ·
        refine ⟨122777081582797423975853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81851387721864949317235 122777081582797423975853)
        ·
          refine ⟨46041405593549033990945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122777081582797423975853 46041405593549033990945)
          ·
            refine ⟨34531054195161775493209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46041405593549033990945 34531054195161775493209)
            ·
              refine ⟨25898290646371331619907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34531054195161775493209 25898290646371331619907)
              ·
                refine ⟨38847435969556997429861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25898290646371331619907 38847435969556997429861)
                ·
                  refine ⟨7283894244291937018099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38847435969556997429861 7283894244291937018099)
                  ·
                    rfl

theorem cell21_31917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_31917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_31917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_31917 prefixEnd_31917 := by exact prefixLift 31917
  have htrace : WordTrace (prefixWord ++ tailWord_31917) baseStart_31917 baseEnd_31917 := by
    simpa [prefixWord, tailWord_31917, baseEnd_31917] using wordTrace_append hprefix tailTrace_31917
  have hstable : (prefixWord ++ tailWord_31917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31917).length < 2 ^ (prefixWord ++ tailWord_31917).sum := by decide
  have hdescent : baseEnd_31917 < baseStart_31917 := by decide
  rcases family_descends (prefixWord ++ tailWord_31917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_31987 : List Nat := [1, 1, 1, 2, 2, 6, 1, 2, 5]
def baseStart_31987 : Nat := 118140960795 + 31987 * 2 ^ 59
def prefixEnd_31987 : Nat := 4983230072969 + 3 ^ 40 * 31987 * 2
def baseEnd_31987 : Nat := 7299869197987370851289

theorem tailTrace_31987 : CollatzResearch.WordTrace tailWord_31987 prefixEnd_31987 7299869197987370851289 := by
  unfold tailWord_31987
  simp only [CollatzResearch.WordTrace]
  refine ⟨1166661735124036789782215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 777774490082691193188143 1166661735124036789782215)
  ·
    refine ⟨1749992602686055184673323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1166661735124036789782215 1749992602686055184673323)
    ·
      refine ⟨2624988904029082777009985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1749992602686055184673323 2624988904029082777009985)
      ·
        refine ⟨1968741678021812082757489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2624988904029082777009985 1968741678021812082757489)
        ·
          refine ⟨1476556258516359062068117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1968741678021812082757489 1476556258516359062068117)
          ·
            refine ⟨69213574617954331034443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1476556258516359062068117 69213574617954331034443)
            ·
              refine ⟨103820361926931496551665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69213574617954331034443 103820361926931496551665)
              ·
                refine ⟨77865271445198622413749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103820361926931496551665 77865271445198622413749)
                ·
                  refine ⟨7299869197987370851289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77865271445198622413749 7299869197987370851289)
                  ·
                    rfl

theorem cell21_31987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 5].length) (baseStart_31987 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_31987 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_31987 prefixEnd_31987 := by exact prefixLift 31987
  have htrace : WordTrace (prefixWord ++ tailWord_31987) baseStart_31987 baseEnd_31987 := by
    simpa [prefixWord, tailWord_31987, baseEnd_31987] using wordTrace_append hprefix tailTrace_31987
  have hstable : (prefixWord ++ tailWord_31987).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_31987).length < 2 ^ (prefixWord ++ tailWord_31987).sum := by decide
  have hdescent : baseEnd_31987 < baseStart_31987 := by decide
  rcases family_descends (prefixWord ++ tailWord_31987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32035 : List Nat := [1, 1, 1, 4, 2, 4, 3, 1, 4]
def baseStart_32035 : Nat := 118140960795 + 32035 * 2 ^ 59
def prefixEnd_32035 : Nat := 4983230072969 + 3 ^ 40 * 32035 * 2
def baseEnd_32035 : Nat := 7310823451949954051191

theorem tailTrace_32035 : CollatzResearch.WordTrace tailWord_32035 prefixEnd_32035 7310823451949954051191 := by
  unfold tailWord_32035
  simp only [CollatzResearch.WordTrace]
  refine ⟨1168412438950140987529559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 778941625966760658353039 1168412438950140987529559)
  ·
    refine ⟨1752618658425211481294339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1168412438950140987529559 1752618658425211481294339)
    ·
      refine ⟨2628927987637817221941509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1752618658425211481294339 2628927987637817221941509)
      ·
        refine ⟨492923997682090729114033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2628927987637817221941509 492923997682090729114033)
        ·
          refine ⟨369692998261568046835525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 492923997682090729114033 369692998261568046835525)
          ·
            refine ⟨69317437174044008781661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 369692998261568046835525 69317437174044008781661)
            ·
              refine ⟨25994038940266503293123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69317437174044008781661 25994038940266503293123)
              ·
                refine ⟨38991058410399754939685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25994038940266503293123 38991058410399754939685)
                ·
                  refine ⟨7310823451949954051191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38991058410399754939685 7310823451949954051191)
                  ·
                    rfl

theorem cell21_32035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 1, 4].length) (baseStart_32035 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_32035 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_32035 prefixEnd_32035 := by exact prefixLift 32035
  have htrace : WordTrace (prefixWord ++ tailWord_32035) baseStart_32035 baseEnd_32035 := by
    simpa [prefixWord, tailWord_32035, baseEnd_32035] using wordTrace_append hprefix tailTrace_32035
  have hstable : (prefixWord ++ tailWord_32035).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32035).length < 2 ^ (prefixWord ++ tailWord_32035).sum := by decide
  have hdescent : baseEnd_32035 < baseStart_32035 := by decide
  rcases family_descends (prefixWord ++ tailWord_32035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32049 : List Nat := [1, 2, 2, 3, 3, 1, 4, 5]
def baseStart_32049 : Nat := 118140960795 + 32049 * 2 ^ 59
def prefixEnd_32049 : Nat := 4983230072969 + 3 ^ 40 * 32049 * 2
def baseEnd_32049 : Nat := 2438006147563013605943

theorem tailTrace_32049 : CollatzResearch.WordTrace tailWord_32049 prefixEnd_32049 2438006147563013605943 := by
  unfold tailWord_32049
  simp only [CollatzResearch.WordTrace]
  refine ⟨1168923060899421378539201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 779282040599614252359467 1168923060899421378539201)
  ·
    refine ⟨876692295674566033904401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1168923060899421378539201 876692295674566033904401)
    ·
      refine ⟨657519221755924525428301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 876692295674566033904401 657519221755924525428301)
      ·
        refine ⟨246569708158471697035613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 657519221755924525428301 246569708158471697035613)
        ·
          refine ⟨92463640559426886388355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246569708158471697035613 92463640559426886388355)
          ·
            refine ⟨138695460839140329582533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92463640559426886388355 138695460839140329582533)
            ·
              refine ⟨26005398907338811796725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 138695460839140329582533 26005398907338811796725)
              ·
                refine ⟨2438006147563013605943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26005398907338811796725 2438006147563013605943)
                ·
                  rfl

theorem cell21_32049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 5].length) (baseStart_32049 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_32049 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_32049 prefixEnd_32049 := by exact prefixLift 32049
  have htrace : WordTrace (prefixWord ++ tailWord_32049) baseStart_32049 baseEnd_32049 := by
    simpa [prefixWord, tailWord_32049, baseEnd_32049] using wordTrace_append hprefix tailTrace_32049
  have hstable : (prefixWord ++ tailWord_32049).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32049).length < 2 ^ (prefixWord ++ tailWord_32049).sum := by decide
  have hdescent : baseEnd_32049 < baseStart_32049 := by decide
  rcases family_descends (prefixWord ++ tailWord_32049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32086 : List Nat := [5, 2, 3, 1, 1, 1, 1, 3, 4]
def baseStart_32086 : Nat := 118140960795 + 32086 * 2 ^ 59
def prefixEnd_32086 : Nat := 4983230072969 + 3 ^ 40 * 32086 * 2
def baseEnd_32086 : Nat := 7322462346785198701087

theorem tailTrace_32086 : CollatzResearch.WordTrace tailWord_32086 prefixEnd_32086 7322462346785198701087 := by
  unfold tailWord_32086
  simp only [CollatzResearch.WordTrace]
  refine ⟨73142035110336043602257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 780181707843584465090741 73142035110336043602257)
  ·
    refine ⟨54856526332752032701693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73142035110336043602257 54856526332752032701693)
    ·
      refine ⟨20571197374782012263135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54856526332752032701693 20571197374782012263135)
      ·
        refine ⟨30856796062173018394703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20571197374782012263135 30856796062173018394703)
        ·
          refine ⟨46285194093259527592055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30856796062173018394703 46285194093259527592055)
          ·
            refine ⟨69427791139889291388083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46285194093259527592055 69427791139889291388083)
            ·
              refine ⟨104141686709833937082125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69427791139889291388083 104141686709833937082125)
              ·
                refine ⟨39053132516187726405797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104141686709833937082125 39053132516187726405797)
                ·
                  refine ⟨7322462346785198701087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39053132516187726405797 7322462346785198701087)
                  ·
                    rfl

theorem cell21_32086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_32086 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_32086 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_32086 prefixEnd_32086 := by exact prefixLift 32086
  have htrace : WordTrace (prefixWord ++ tailWord_32086) baseStart_32086 baseEnd_32086 := by
    simpa [prefixWord, tailWord_32086, baseEnd_32086] using wordTrace_append hprefix tailTrace_32086
  have hstable : (prefixWord ++ tailWord_32086).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32086).length < 2 ^ (prefixWord ++ tailWord_32086).sum := by decide
  have hdescent : baseEnd_32086 < baseStart_32086 := by decide
  rcases family_descends (prefixWord ++ tailWord_32086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32108 : List Nat := [2, 2, 1, 1, 5, 1, 2, 7]
def baseStart_32108 : Nat := 118140960795 + 32108 * 2 ^ 59
def prefixEnd_32108 : Nat := 4983230072969 + 3 ^ 40 * 32108 * 2
def baseEnd_32108 : Nat := 2442494348839349778125

theorem tailTrace_32108 : CollatzResearch.WordTrace tailWord_32108 prefixEnd_32108 2442494348839349778125 := by
  unfold tailWord_32108
  simp only [CollatzResearch.WordTrace]
  refine ⟨585537483842837227468489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 780716645123782969957985 585537483842837227468489)
  ·
    refine ⟨439153112882127920601367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 585537483842837227468489 439153112882127920601367)
    ·
      refine ⟨658729669323191880902051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439153112882127920601367 658729669323191880902051)
      ·
        refine ⟨988094503984787821353077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 658729669323191880902051 988094503984787821353077)
        ·
          refine ⟨92633859748573858251851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 988094503984787821353077 92633859748573858251851)
          ·
            refine ⟨138950789622860787377777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92633859748573858251851 138950789622860787377777)
            ·
              refine ⟨104213092217145590533333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 138950789622860787377777 104213092217145590533333)
              ·
                refine ⟨2442494348839349778125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 104213092217145590533333 2442494348839349778125)
                ·
                  rfl

theorem cell21_32108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 7].length) (baseStart_32108 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_32108 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_32108 prefixEnd_32108 := by exact prefixLift 32108
  have htrace : WordTrace (prefixWord ++ tailWord_32108) baseStart_32108 baseEnd_32108 := by
    simpa [prefixWord, tailWord_32108, baseEnd_32108] using wordTrace_append hprefix tailTrace_32108
  have hstable : (prefixWord ++ tailWord_32108).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32108).length < 2 ^ (prefixWord ++ tailWord_32108).sum := by decide
  have hdescent : baseEnd_32108 < baseStart_32108 := by decide
  rcases family_descends (prefixWord ++ tailWord_32108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32122 : List Nat := [3, 1, 1, 1, 1, 1, 2, 4, 7]
def baseStart_32122 : Nat := 118140960795 + 32122 * 2 ^ 59
def prefixEnd_32122 : Nat := 4983230072969 + 3 ^ 40 * 32122 * 2
def baseEnd_32122 : Nat := 7330678037257136101013

theorem tailTrace_32122 : CollatzResearch.WordTrace tailWord_32122 prefixEnd_32122 7330678037257136101013 := by
  unfold tailWord_32122
  simp only [CollatzResearch.WordTrace]
  refine ⟨292896397408738711486655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 781057059756636563964413 292896397408738711486655)
  ·
    refine ⟨439344596113108067229983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292896397408738711486655 439344596113108067229983)
    ·
      refine ⟨659016894169662100844975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439344596113108067229983 659016894169662100844975)
      ·
        refine ⟨988525341254493151267463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659016894169662100844975 988525341254493151267463)
        ·
          refine ⟨1482788011881739726901195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 988525341254493151267463 1482788011881739726901195)
          ·
            refine ⟨2224182017822609590351793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1482788011881739726901195 2224182017822609590351793)
            ·
              refine ⟨1668136513366957192763845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2224182017822609590351793 1668136513366957192763845)
              ·
                refine ⟨312775596256304473643221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1668136513366957192763845 312775596256304473643221)
                ·
                  refine ⟨7330678037257136101013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 312775596256304473643221 7330678037257136101013)
                  ·
                    rfl

theorem cell21_32122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 7].length) (baseStart_32122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_32122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_32122 prefixEnd_32122 := by exact prefixLift 32122
  have htrace : WordTrace (prefixWord ++ tailWord_32122) baseStart_32122 baseEnd_32122 := by
    simpa [prefixWord, tailWord_32122, baseEnd_32122] using wordTrace_append hprefix tailTrace_32122
  have hstable : (prefixWord ++ tailWord_32122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32122).length < 2 ^ (prefixWord ++ tailWord_32122).sum := by decide
  have hdescent : baseEnd_32122 < baseStart_32122 := by decide
  rcases family_descends (prefixWord ++ tailWord_32122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32142 : List Nat := [4, 1, 1, 4, 2, 2, 1, 6]
def baseStart_32142 : Nat := 118140960795 + 32142 * 2 ^ 59
def prefixEnd_32142 : Nat := 4983230072969 + 3 ^ 40 * 32142 * 2
def baseEnd_32142 : Nat := 2445080769913848589213

theorem tailTrace_32142 : CollatzResearch.WordTrace tailWord_32142 prefixEnd_32142 2445080769913848589213 := by
  unfold tailWord_32142
  simp only [CollatzResearch.WordTrace]
  refine ⟨146539381195312282709335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 781543366374998841116453 146539381195312282709335)
  ·
    refine ⟨219809071792968424064003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146539381195312282709335 219809071792968424064003)
    ·
      refine ⟨329713607689452636096005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219809071792968424064003 329713607689452636096005)
      ·
        refine ⟨61821301441772369268001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 329713607689452636096005 61821301441772369268001)
        ·
          refine ⟨46365976081329276951001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61821301441772369268001 46365976081329276951001)
          ·
            refine ⟨34774482060996957713251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46365976081329276951001 34774482060996957713251)
            ·
              refine ⟨52161723091495436569877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34774482060996957713251 52161723091495436569877)
              ·
                refine ⟨2445080769913848589213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52161723091495436569877 2445080769913848589213)
                ·
                  rfl

theorem cell21_32142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 6].length) (baseStart_32142 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_32142 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_32142 prefixEnd_32142 := by exact prefixLift 32142
  have htrace : WordTrace (prefixWord ++ tailWord_32142) baseStart_32142 baseEnd_32142 := by
    simpa [prefixWord, tailWord_32142, baseEnd_32142] using wordTrace_append hprefix tailTrace_32142
  have hstable : (prefixWord ++ tailWord_32142).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32142).length < 2 ^ (prefixWord ++ tailWord_32142).sum := by decide
  have hdescent : baseEnd_32142 < baseStart_32142 := by decide
  rcases family_descends (prefixWord ++ tailWord_32142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32173 : List Nat := [1, 5, 2, 2, 1, 1, 1, 5, 3]
def baseStart_32173 : Nat := 118140960795 + 32173 * 2 ^ 59
def prefixEnd_32173 : Nat := 4983230072969 + 3 ^ 40 * 32173 * 2
def baseEnd_32173 : Nat := 7342316932092380750909

theorem tailTrace_32173 : CollatzResearch.WordTrace tailWord_32173 prefixEnd_32173 7342316932092380750909 := by
  unfold tailWord_32173
  simp only [CollatzResearch.WordTrace]
  refine ⟨1173445712450190556053173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 782297141633460370702115 1173445712450190556053173)
  ·
    refine ⟨110010535542205364629985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1173445712450190556053173 110010535542205364629985)
    ·
      refine ⟨82507901656654023472489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110010535542205364629985 82507901656654023472489)
      ·
        refine ⟨61880926242490517604367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82507901656654023472489 61880926242490517604367)
        ·
          refine ⟨92821389363735776406551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61880926242490517604367 92821389363735776406551)
          ·
            refine ⟨139232084045603664609827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92821389363735776406551 139232084045603664609827)
            ·
              refine ⟨208848126068405496914741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139232084045603664609827 208848126068405496914741)
              ·
                refine ⟨19579511818913015335757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 208848126068405496914741 19579511818913015335757)
                ·
                  refine ⟨7342316932092380750909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19579511818913015335757 7342316932092380750909)
                  ·
                    rfl

theorem cell21_32173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_32173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_32173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_32173 prefixEnd_32173 := by exact prefixLift 32173
  have htrace : WordTrace (prefixWord ++ tailWord_32173) baseStart_32173 baseEnd_32173 := by
    simpa [prefixWord, tailWord_32173, baseEnd_32173] using wordTrace_append hprefix tailTrace_32173
  have hstable : (prefixWord ++ tailWord_32173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32173).length < 2 ^ (prefixWord ++ tailWord_32173).sum := by decide
  have hdescent : baseEnd_32173 < baseStart_32173 := by decide
  rcases family_descends (prefixWord ++ tailWord_32173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32246 : List Nat := [5, 1, 1, 1, 2, 2, 2, 1, 6]
def baseStart_32246 : Nat := 118140960795 + 32246 * 2 ^ 59
def prefixEnd_32246 : Nat := 4983230072969 + 3 ^ 40 * 32246 * 2
def baseEnd_32246 : Nat := 7358976526660476034093

theorem tailTrace_32246 : CollatzResearch.WordTrace tailWord_32246 prefixEnd_32246 7358976526660476034093 := by
  unfold tailWord_32246
  simp only [CollatzResearch.WordTrace]
  refine ⟨73506765074107751466287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 784072160790482682307061 73506765074107751466287)
  ·
    refine ⟨110260147611161627199431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73506765074107751466287 110260147611161627199431)
    ·
      refine ⟨165390221416742440799147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110260147611161627199431 165390221416742440799147)
      ·
        refine ⟨248085332125113661198721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165390221416742440799147 248085332125113661198721)
        ·
          refine ⟨186063999093835245899041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248085332125113661198721 186063999093835245899041)
          ·
            refine ⟨139547999320376434424281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186063999093835245899041 139547999320376434424281)
            ·
              refine ⟨104660999490282325818211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139547999320376434424281 104660999490282325818211)
              ·
                refine ⟨156991499235423488727317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104660999490282325818211 156991499235423488727317)
                ·
                  refine ⟨7358976526660476034093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 156991499235423488727317 7358976526660476034093)
                  ·
                    rfl

theorem cell21_32246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_32246 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_32246 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_32246 prefixEnd_32246 := by exact prefixLift 32246
  have htrace : WordTrace (prefixWord ++ tailWord_32246) baseStart_32246 baseEnd_32246 := by
    simpa [prefixWord, tailWord_32246, baseEnd_32246] using wordTrace_append hprefix tailTrace_32246
  have hstable : (prefixWord ++ tailWord_32246).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32246).length < 2 ^ (prefixWord ++ tailWord_32246).sum := by decide
  have hdescent : baseEnd_32246 < baseStart_32246 := by decide
  rcases family_descends (prefixWord ++ tailWord_32246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32263 : List Nat := [1, 1, 4, 3, 2, 1, 4, 1, 4]
def baseStart_32263 : Nat := 118140960795 + 32263 * 2 ^ 59
def prefixEnd_32263 : Nat := 4983230072969 + 3 ^ 40 * 32263 * 2
def baseEnd_32263 : Nat := 7362856158272224250725

theorem tailTrace_32263 : CollatzResearch.WordTrace tailWord_32263 prefixEnd_32263 7362856158272224250725 := by
  unfold tailWord_32263
  simp only [CollatzResearch.WordTrace]
  refine ⟨1176728282124135926829443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 784485521416090617886295 1176728282124135926829443)
  ·
    refine ⟨1765092423186203890244165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1176728282124135926829443 1765092423186203890244165)
    ·
      refine ⟨330954829347413229420781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1765092423186203890244165 330954829347413229420781)
      ·
        refine ⟨124108061005279961032793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 330954829347413229420781 124108061005279961032793)
        ·
          refine ⟨93081045753959970774595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124108061005279961032793 93081045753959970774595)
          ·
            refine ⟨139621568630939956161893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93081045753959970774595 139621568630939956161893)
            ·
              refine ⟨26179044118301241780355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139621568630939956161893 26179044118301241780355)
              ·
                refine ⟨39268566177451862670533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26179044118301241780355 39268566177451862670533)
                ·
                  refine ⟨7362856158272224250725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39268566177451862670533 7362856158272224250725)
                  ·
                    rfl

theorem cell21_32263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 1, 4].length) (baseStart_32263 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_32263 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_32263 prefixEnd_32263 := by exact prefixLift 32263
  have htrace : WordTrace (prefixWord ++ tailWord_32263) baseStart_32263 baseEnd_32263 := by
    simpa [prefixWord, tailWord_32263, baseEnd_32263] using wordTrace_append hprefix tailTrace_32263
  have hstable : (prefixWord ++ tailWord_32263).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32263).length < 2 ^ (prefixWord ++ tailWord_32263).sum := by decide
  have hdescent : baseEnd_32263 < baseStart_32263 := by decide
  rcases family_descends (prefixWord ++ tailWord_32263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32336 : List Nat := [2, 1, 1, 1, 1, 3, 7, 5]
def baseStart_32336 : Nat := 118140960795 + 32336 * 2 ^ 59
def prefixEnd_32336 : Nat := 4983230072969 + 3 ^ 40 * 32336 * 2
def baseEnd_32336 : Nat := 2459838584280106511303

theorem tailTrace_32336 : CollatzResearch.WordTrace tailWord_32336 prefixEnd_32336 2459838584280106511303 := by
  unfold tailWord_32336
  simp only [CollatzResearch.WordTrace]
  refine ⟨589695405429834697118431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 786260540573112929491241 589695405429834697118431)
  ·
    refine ⟨884543108144752045677647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 589695405429834697118431 884543108144752045677647)
    ·
      refine ⟨1326814662217128068516471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 884543108144752045677647 1326814662217128068516471)
      ·
        refine ⟨1990221993325692102774707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1326814662217128068516471 1990221993325692102774707)
        ·
          refine ⟨2985332989988538154162061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1990221993325692102774707 2985332989988538154162061)
          ·
            refine ⟨1119499871245701807810773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2985332989988538154162061 1119499871245701807810773)
            ·
              refine ⟨26238278232321136120565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1119499871245701807810773 26238278232321136120565)
              ·
                refine ⟨2459838584280106511303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26238278232321136120565 2459838584280106511303)
                ·
                  rfl

theorem cell21_32336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 5].length) (baseStart_32336 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_32336 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_32336 prefixEnd_32336 := by exact prefixLift 32336
  have htrace : WordTrace (prefixWord ++ tailWord_32336) baseStart_32336 baseEnd_32336 := by
    simpa [prefixWord, tailWord_32336, baseEnd_32336] using wordTrace_append hprefix tailTrace_32336
  have hstable : (prefixWord ++ tailWord_32336).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32336).length < 2 ^ (prefixWord ++ tailWord_32336).sum := by decide
  have hdescent : baseEnd_32336 < baseStart_32336 := by decide
  rcases family_descends (prefixWord ++ tailWord_32336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32395 : List Nat := [1, 1, 1, 1, 4, 1, 5, 7]
def baseStart_32395 : Nat := 118140960795 + 32395 * 2 ^ 59
def prefixEnd_32395 : Nat := 4983230072969 + 3 ^ 40 * 32395 * 2
def baseEnd_32395 : Nat := 2464326785556442683485

theorem tailTrace_32395 : CollatzResearch.WordTrace tailWord_32395 prefixEnd_32395 2464326785556442683485 := by
  unfold tailWord_32395
  simp only [CollatzResearch.WordTrace]
  refine ⟨1181542717645922470634639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 787695145097281647089759 1181542717645922470634639)
  ·
    refine ⟨1772314076468883705951959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1181542717645922470634639 1772314076468883705951959)
    ·
      refine ⟨2658471114703325558927939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1772314076468883705951959 2658471114703325558927939)
      ·
        refine ⟨3987706672054988338391909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2658471114703325558927939 3987706672054988338391909)
        ·
          refine ⟨747695001010310313448483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3987706672054988338391909 747695001010310313448483)
          ·
            refine ⟨1121542501515465470172725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747695001010310313448483 1121542501515465470172725)
            ·
              refine ⟨105144609517074887828693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1121542501515465470172725 105144609517074887828693)
              ·
                refine ⟨2464326785556442683485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 105144609517074887828693 2464326785556442683485)
                ·
                  rfl

theorem cell21_32395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 7].length) (baseStart_32395 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_32395 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_32395 prefixEnd_32395 := by exact prefixLift 32395
  have htrace : WordTrace (prefixWord ++ tailWord_32395) baseStart_32395 baseEnd_32395 := by
    simpa [prefixWord, tailWord_32395, baseEnd_32395] using wordTrace_append hprefix tailTrace_32395
  have hstable : (prefixWord ++ tailWord_32395).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32395).length < 2 ^ (prefixWord ++ tailWord_32395).sum := by decide
  have hdescent : baseEnd_32395 < baseStart_32395 := by decide
  rcases family_descends (prefixWord ++ tailWord_32395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32418 : List Nat := [3, 3, 1, 4, 2, 1, 1, 1, 5]
def baseStart_32418 : Nat := 118140960795 + 32418 * 2 ^ 59
def prefixEnd_32418 : Nat := 4983230072969 + 3 ^ 40 * 32418 * 2
def baseEnd_32418 : Nat := 7398229270026399167075

theorem tailTrace_32418 : CollatzResearch.WordTrace tailWord_32418 prefixEnd_32418 7398229270026399167075 := by
  unfold tailWord_32418
  simp only [CollatzResearch.WordTrace]
  refine ⟨295595399140649349680477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 788254397708398265814605 295595399140649349680477)
  ·
    refine ⟨110848274677743506130179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295595399140649349680477 110848274677743506130179)
    ·
      refine ⟨166272412016615259195269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110848274677743506130179 166272412016615259195269)
      ·
        refine ⟨31176077253115361099113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166272412016615259195269 31176077253115361099113)
        ·
          refine ⟨23382057939836520824335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31176077253115361099113 23382057939836520824335)
          ·
            refine ⟨35073086909754781236503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23382057939836520824335 35073086909754781236503)
            ·
              refine ⟨52609630364632171854755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35073086909754781236503 52609630364632171854755)
              ·
                refine ⟨78914445546948257782133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52609630364632171854755 78914445546948257782133)
                ·
                  refine ⟨7398229270026399167075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78914445546948257782133 7398229270026399167075)
                  ·
                    rfl

theorem cell21_32418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_32418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_32418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_32418 prefixEnd_32418 := by exact prefixLift 32418
  have htrace : WordTrace (prefixWord ++ tailWord_32418) baseStart_32418 baseEnd_32418 := by
    simpa [prefixWord, tailWord_32418, baseEnd_32418] using wordTrace_append hprefix tailTrace_32418
  have hstable : (prefixWord ++ tailWord_32418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32418).length < 2 ^ (prefixWord ++ tailWord_32418).sum := by decide
  have hdescent : baseEnd_32418 < baseStart_32418 := by decide
  rcases family_descends (prefixWord ++ tailWord_32418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32474 : List Nat := [3, 1, 1, 2, 2, 4, 2, 2, 4]
def baseStart_32474 : Nat := 118140960795 + 32474 * 2 ^ 59
def prefixEnd_32474 : Nat := 4983230072969 + 3 ^ 40 * 32474 * 2
def baseEnd_32474 : Nat := 7411009232982746233627

theorem tailTrace_32474 : CollatzResearch.WordTrace tailWord_32474 prefixEnd_32474 7411009232982746233627 := by
  unfold tailWord_32474
  simp only [CollatzResearch.WordTrace]
  refine ⟨296106021089929740690119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 789616056239812641840317 296106021089929740690119)
  ·
    refine ⟨444159031634894611035179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296106021089929740690119 444159031634894611035179)
    ·
      refine ⟨666238547452341916552769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444159031634894611035179 666238547452341916552769)
      ·
        refine ⟨499678910589256437414577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 666238547452341916552769 499678910589256437414577)
        ·
          refine ⟨374759182941942328060933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 499678910589256437414577 374759182941942328060933)
          ·
            refine ⟨70267346801614186511425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 374759182941942328060933 70267346801614186511425)
            ·
              refine ⟨52700510101210639883569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70267346801614186511425 52700510101210639883569)
              ·
                refine ⟨39525382575907979912677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52700510101210639883569 39525382575907979912677)
                ·
                  refine ⟨7411009232982746233627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39525382575907979912677 7411009232982746233627)
                  ·
                    rfl

theorem cell21_32474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 2, 4].length) (baseStart_32474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_32474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_32474 prefixEnd_32474 := by exact prefixLift 32474
  have htrace : WordTrace (prefixWord ++ tailWord_32474) baseStart_32474 baseEnd_32474 := by
    simpa [prefixWord, tailWord_32474, baseEnd_32474] using wordTrace_append hprefix tailTrace_32474
  have hstable : (prefixWord ++ tailWord_32474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32474).length < 2 ^ (prefixWord ++ tailWord_32474).sum := by decide
  have hdescent : baseEnd_32474 < baseStart_32474 := by decide
  rcases family_descends (prefixWord ++ tailWord_32474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32488 : List Nat := [2, 1, 4, 1, 3, 1, 3, 6]
def baseStart_32488 : Nat := 118140960795 + 32488 * 2 ^ 59
def prefixEnd_32488 : Nat := 4983230072969 + 3 ^ 40 * 32488 * 2
def baseEnd_32488 : Nat := 2471401407907277666755

theorem tailTrace_32488 : CollatzResearch.WordTrace tailWord_32488 prefixEnd_32488 2471401407907277666755 := by
  unfold tailWord_32488
  simp only [CollatzResearch.WordTrace]
  refine ⟨592467353154499676885059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 789956470872666235846745 592467353154499676885059)
  ·
    refine ⟨888701029731749515327589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 592467353154499676885059 888701029731749515327589)
    ·
      refine ⟨166631443074703034123923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 888701029731749515327589 166631443074703034123923)
      ·
        refine ⟨249947164612054551185885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166631443074703034123923 249947164612054551185885)
        ·
          refine ⟨93730186729520456694707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249947164612054551185885 93730186729520456694707)
          ·
            refine ⟨140595280094280685042061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93730186729520456694707 140595280094280685042061)
            ·
              refine ⟨52723230035355256890773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140595280094280685042061 52723230035355256890773)
              ·
                refine ⟨2471401407907277666755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52723230035355256890773 2471401407907277666755)
                ·
                  rfl

theorem cell21_32488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 6].length) (baseStart_32488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_32488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_32488 prefixEnd_32488 := by exact prefixLift 32488
  have htrace : WordTrace (prefixWord ++ tailWord_32488) baseStart_32488 baseEnd_32488 := by
    simpa [prefixWord, tailWord_32488, baseEnd_32488] using wordTrace_append hprefix tailTrace_32488
  have hstable : (prefixWord ++ tailWord_32488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32488).length < 2 ^ (prefixWord ++ tailWord_32488).sum := by decide
  have hdescent : baseEnd_32488 < baseStart_32488 := by decide
  rcases family_descends (prefixWord ++ tailWord_32488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32525 : List Nat := [1, 7, 2, 1, 1, 1, 1, 1, 6]
def baseStart_32525 : Nat := 118140960795 + 32525 * 2 ^ 59
def prefixEnd_32525 : Nat := 4983230072969 + 3 ^ 40 * 32525 * 2
def baseEnd_32525 : Nat := 7422648127817990883523

theorem tailTrace_32525 : CollatzResearch.WordTrace tailWord_32525 prefixEnd_32525 7422648127817990883523 := by
  unfold tailWord_32525
  simp only [CollatzResearch.WordTrace]
  refine ⟨1186284207174954672867029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 790856138116636448578019 1186284207174954672867029)
  ·
    refine ⟨27803536105663000145321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 1186284207174954672867029 27803536105663000145321)
    ·
      refine ⟨20852652079247250108991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27803536105663000145321 20852652079247250108991)
      ·
        refine ⟨31278978118870875163487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20852652079247250108991 31278978118870875163487)
        ·
          refine ⟨46918467178306312745231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31278978118870875163487 46918467178306312745231)
          ·
            refine ⟨70377700767459469117847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46918467178306312745231 70377700767459469117847)
            ·
              refine ⟨105566551151189203676771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70377700767459469117847 105566551151189203676771)
              ·
                refine ⟨158349826726783805515157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105566551151189203676771 158349826726783805515157)
                ·
                  refine ⟨7422648127817990883523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 158349826726783805515157 7422648127817990883523)
                  ·
                    rfl

theorem cell21_32525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_32525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_32525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_32525 prefixEnd_32525 := by exact prefixLift 32525
  have htrace : WordTrace (prefixWord ++ tailWord_32525) baseStart_32525 baseEnd_32525 := by
    simpa [prefixWord, tailWord_32525, baseEnd_32525] using wordTrace_append hprefix tailTrace_32525
  have hstable : (prefixWord ++ tailWord_32525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32525).length < 2 ^ (prefixWord ++ tailWord_32525).sum := by decide
  have hdescent : baseEnd_32525 < baseStart_32525 := by decide
  rcases family_descends (prefixWord ++ tailWord_32525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32533 : List Nat := [1, 3, 2, 1, 2, 4, 1, 1, 6]
def baseStart_32533 : Nat := 118140960795 + 32533 * 2 ^ 59
def prefixEnd_32533 : Nat := 4983230072969 + 3 ^ 40 * 32533 * 2
def baseEnd_32533 : Nat := 7424473836811754750173

theorem tailTrace_32533 : CollatzResearch.WordTrace tailWord_32533 prefixEnd_32533 7424473836811754750173 := by
  unfold tailWord_32533
  simp only [CollatzResearch.WordTrace]
  refine ⟨1186575991145972039158253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 791050660763981359438835 1186575991145972039158253)
  ·
    refine ⟨444965996679739514684345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1186575991145972039158253 444965996679739514684345)
    ·
      refine ⟨333724497509804636013259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 444965996679739514684345 333724497509804636013259)
      ·
        refine ⟨500586746264706954019889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333724497509804636013259 500586746264706954019889)
        ·
          refine ⟨375440059698530215514917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 500586746264706954019889 375440059698530215514917)
          ·
            refine ⟨70395011193474415409047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 375440059698530215514917 70395011193474415409047)
            ·
              refine ⟨105592516790211623113571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70395011193474415409047 105592516790211623113571)
              ·
                refine ⟨158388775185317434670357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105592516790211623113571 158388775185317434670357)
                ·
                  refine ⟨7424473836811754750173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 158388775185317434670357 7424473836811754750173)
                  ·
                    rfl

theorem cell21_32533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 6].length) (baseStart_32533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_32533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_32533 prefixEnd_32533 := by exact prefixLift 32533
  have htrace : WordTrace (prefixWord ++ tailWord_32533) baseStart_32533 baseEnd_32533 := by
    simpa [prefixWord, tailWord_32533, baseEnd_32533] using wordTrace_append hprefix tailTrace_32533
  have hstable : (prefixWord ++ tailWord_32533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32533).length < 2 ^ (prefixWord ++ tailWord_32533).sum := by decide
  have hdescent : baseEnd_32533 < baseStart_32533 := by decide
  rcases family_descends (prefixWord ++ tailWord_32533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32609 : List Nat := [1, 2, 3, 1, 1, 1, 5, 3, 4]
def baseStart_32609 : Nat := 118140960795 + 32609 * 2 ^ 59
def prefixEnd_32609 : Nat := 4983230072969 + 3 ^ 40 * 32609 * 2
def baseEnd_32609 : Nat := 7441818072252511483351

theorem tailTrace_32609 : CollatzResearch.WordTrace tailWord_32609 prefixEnd_32609 7441818072252511483351 := by
  unfold tailWord_32609
  simp only [CollatzResearch.WordTrace]
  refine ⟨1189347938870637018924881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 792898625913758012616587 1189347938870637018924881)
  ·
    refine ⟨892010954152977764193661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1189347938870637018924881 892010954152977764193661)
    ·
      refine ⟨334504107807366661572623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 892010954152977764193661 334504107807366661572623)
      ·
        refine ⟨501756161711049992358935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334504107807366661572623 501756161711049992358935)
        ·
          refine ⟨752634242566574988538403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501756161711049992358935 752634242566574988538403)
          ·
            refine ⟨1128951363849862482807605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 752634242566574988538403 1128951363849862482807605)
            ·
              refine ⟨105839190360924607763213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1128951363849862482807605 105839190360924607763213)
              ·
                refine ⟨39689696385346727911205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105839190360924607763213 39689696385346727911205)
                ·
                  refine ⟨7441818072252511483351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39689696385346727911205 7441818072252511483351)
                  ·
                    rfl

theorem cell21_32609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 3, 4].length) (baseStart_32609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_32609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_32609 prefixEnd_32609 := by exact prefixLift 32609
  have htrace : WordTrace (prefixWord ++ tailWord_32609) baseStart_32609 baseEnd_32609 := by
    simpa [prefixWord, tailWord_32609, baseEnd_32609] using wordTrace_append hprefix tailTrace_32609
  have hstable : (prefixWord ++ tailWord_32609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32609).length < 2 ^ (prefixWord ++ tailWord_32609).sum := by decide
  have hdescent : baseEnd_32609 < baseStart_32609 := by decide
  rcases family_descends (prefixWord ++ tailWord_32609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32671 : List Nat := [1, 1, 2, 5, 3, 1, 1, 2, 5]
def baseStart_32671 : Nat := 118140960795 + 32671 * 2 ^ 59
def prefixEnd_32671 : Nat := 4983230072969 + 3 ^ 40 * 32671 * 2
def baseEnd_32671 : Nat := 7455967316954181449891

theorem tailTrace_32671 : CollatzResearch.WordTrace tailWord_32671 prefixEnd_32671 7455967316954181449891 := by
  unfold tailWord_32671
  simp only [CollatzResearch.WordTrace]
  refine ⟨1191609264646021607681867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 794406176430681071787911 1191609264646021607681867)
  ·
    refine ⟨1787413896969032411522801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1191609264646021607681867 1787413896969032411522801)
    ·
      refine ⟨1340560422726774308642101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1787413896969032411522801 1340560422726774308642101)
      ·
        refine ⟨125677539630635091435197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1340560422726774308642101 125677539630635091435197)
        ·
          refine ⟨47129077361488159288199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125677539630635091435197 47129077361488159288199)
          ·
            refine ⟨70693616042232238932299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47129077361488159288199 70693616042232238932299)
            ·
              refine ⟨106040424063348358398449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70693616042232238932299 106040424063348358398449)
              ·
                refine ⟨79530318047511268798837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106040424063348358398449 79530318047511268798837)
                ·
                  refine ⟨7455967316954181449891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79530318047511268798837 7455967316954181449891)
                  ·
                    rfl

theorem cell21_32671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 5].length) (baseStart_32671 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_32671 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_32671 prefixEnd_32671 := by exact prefixLift 32671
  have htrace : WordTrace (prefixWord ++ tailWord_32671) baseStart_32671 baseEnd_32671 := by
    simpa [prefixWord, tailWord_32671, baseEnd_32671] using wordTrace_append hprefix tailTrace_32671
  have hstable : (prefixWord ++ tailWord_32671).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32671).length < 2 ^ (prefixWord ++ tailWord_32671).sum := by decide
  have hdescent : baseEnd_32671 < baseStart_32671 := by decide
  rcases family_descends (prefixWord ++ tailWord_32671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32702 : List Nat := [4, 2, 1, 1, 1, 3, 3, 2, 4]
def baseStart_32702 : Nat := 118140960795 + 32702 * 2 ^ 59
def prefixEnd_32702 : Nat := 4983230072969 + 3 ^ 40 * 32702 * 2
def baseEnd_32702 : Nat := 7463041939305016433161

theorem tailTrace_32702 : CollatzResearch.WordTrace tailWord_32702 prefixEnd_32702 7463041939305016433161 := by
  unfold tailWord_32702
  simp only [CollatzResearch.WordTrace]
  refine ⟨149092490941714237757545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 795159951689142601373573 149092490941714237757545)
  ·
    refine ⟨111819368206285678318159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149092490941714237757545 111819368206285678318159)
    ·
      refine ⟨167729052309428517477239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111819368206285678318159 167729052309428517477239)
      ·
        refine ⟨251593578464142776215859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167729052309428517477239 251593578464142776215859)
        ·
          refine ⟨377390367696214164323789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251593578464142776215859 377390367696214164323789)
          ·
            refine ⟨141521387886080311621421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 377390367696214164323789 141521387886080311621421)
            ·
              refine ⟨53070520457280116858033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141521387886080311621421 53070520457280116858033)
              ·
                refine ⟨39802890342960087643525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53070520457280116858033 39802890342960087643525)
                ·
                  refine ⟨7463041939305016433161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39802890342960087643525 7463041939305016433161)
                  ·
                    rfl

theorem cell21_32702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_32702 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_32702 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_32702 prefixEnd_32702 := by exact prefixLift 32702
  have htrace : WordTrace (prefixWord ++ tailWord_32702) baseStart_32702 baseEnd_32702 := by
    simpa [prefixWord, tailWord_32702, baseEnd_32702] using wordTrace_append hprefix tailTrace_32702
  have hstable : (prefixWord ++ tailWord_32702).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32702).length < 2 ^ (prefixWord ++ tailWord_32702).sum := by decide
  have hdescent : baseEnd_32702 < baseStart_32702 := by decide
  rcases family_descends (prefixWord ++ tailWord_32702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32713 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 9]
def baseStart_32713 : Nat := 118140960795 + 32713 * 2 ^ 59
def prefixEnd_32713 : Nat := 4983230072969 + 3 ^ 40 * 32713 * 2
def baseEnd_32713 : Nat := 7465552289171441749805

theorem tailTrace_32713 : CollatzResearch.WordTrace tailWord_32713 prefixEnd_32713 7465552289171441749805 := by
  unfold tailWord_32713
  simp only [CollatzResearch.WordTrace]
  refine ⟨1193141130493862780710793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 795427420329241853807195 1193141130493862780710793)
  ·
    refine ⟨894855847870397085533095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1193141130493862780710793 894855847870397085533095)
    ·
      refine ⟨1342283771805595628299643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 894855847870397085533095 1342283771805595628299643)
      ·
        refine ⟨2013425657708393442449465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1342283771805595628299643 2013425657708393442449465)
        ·
          refine ⟨1510069243281295081837099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2013425657708393442449465 1510069243281295081837099)
          ·
            refine ⟨2265103864921942622755649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1510069243281295081837099 2265103864921942622755649)
            ·
              refine ⟨1698827898691456967066737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2265103864921942622755649 1698827898691456967066737)
              ·
                refine ⟨1274120924018592725300053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1698827898691456967066737 1274120924018592725300053)
                ·
                  refine ⟨7465552289171441749805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1274120924018592725300053 7465552289171441749805)
                  ·
                    rfl

theorem cell21_32713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 9].length) (baseStart_32713 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_32713 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_32713 prefixEnd_32713 := by exact prefixLift 32713
  have htrace : WordTrace (prefixWord ++ tailWord_32713) baseStart_32713 baseEnd_32713 := by
    simpa [prefixWord, tailWord_32713, baseEnd_32713] using wordTrace_append hprefix tailTrace_32713
  have hstable : (prefixWord ++ tailWord_32713).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32713).length < 2 ^ (prefixWord ++ tailWord_32713).sum := by decide
  have hdescent : baseEnd_32713 < baseStart_32713 := by decide
  rcases family_descends (prefixWord ++ tailWord_32713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32764 : List Nat := [2, 2, 2, 1, 2, 2, 5, 2, 3]
def baseStart_32764 : Nat := 118140960795 + 32764 * 2 ^ 59
def prefixEnd_32764 : Nat := 4983230072969 + 3 ^ 40 * 32764 * 2
def baseEnd_32764 : Nat := 7477191184006686399701

theorem tailTrace_32764 : CollatzResearch.WordTrace tailWord_32764 prefixEnd_32764 7477191184006686399701 := by
  unfold tailWord_32764
  simp only [CollatzResearch.WordTrace]
  refine ⟨597500626654549245408673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 796667502206065660544897 597500626654549245408673)
  ·
    refine ⟨448125469990911934056505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 597500626654549245408673 448125469990911934056505)
    ·
      refine ⟨336094102493183950542379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 448125469990911934056505 336094102493183950542379)
      ·
        refine ⟨504141153739775925813569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336094102493183950542379 504141153739775925813569)
        ·
          refine ⟨378105865304831944360177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 504141153739775925813569 378105865304831944360177)
          ·
            refine ⟨283579398978623958270133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 378105865304831944360177 283579398978623958270133)
            ·
              refine ⟨26585568654245996087825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 283579398978623958270133 26585568654245996087825)
              ·
                refine ⟨19939176490684497065869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26585568654245996087825 19939176490684497065869)
                ·
                  refine ⟨7477191184006686399701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19939176490684497065869 7477191184006686399701)
                  ·
                    rfl

theorem cell21_32764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 2, 3].length) (baseStart_32764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_32764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_32764 prefixEnd_32764 := by exact prefixLift 32764
  have htrace : WordTrace (prefixWord ++ tailWord_32764) baseStart_32764 baseEnd_32764 := by
    simpa [prefixWord, tailWord_32764, baseEnd_32764] using wordTrace_append hprefix tailTrace_32764
  have hstable : (prefixWord ++ tailWord_32764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32764).length < 2 ^ (prefixWord ++ tailWord_32764).sum := by decide
  have hdescent : baseEnd_32764 < baseStart_32764 := by decide
  rcases family_descends (prefixWord ++ tailWord_32764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32775 : List Nat := [1, 1, 4, 3, 1, 2, 1, 8]
def baseStart_32775 : Nat := 118140960795 + 32775 * 2 ^ 59
def prefixEnd_32775 : Nat := 4983230072969 + 3 ^ 40 * 32775 * 2
def baseEnd_32775 : Nat := 2493233844624370572115

theorem tailTrace_32775 : CollatzResearch.WordTrace tailWord_32775 prefixEnd_32775 2493233844624370572115 := by
  unfold tailWord_32775
  simp only [CollatzResearch.WordTrace]
  refine ⟨1195402456269247369467779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 796934970846164912978519 1195402456269247369467779)
  ·
    refine ⟨1793103684403871054201669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1195402456269247369467779 1793103684403871054201669)
    ·
      refine ⟨336206940825725822662813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1793103684403871054201669 336206940825725822662813)
      ·
        refine ⟨126077602809647183498555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 336206940825725822662813 126077602809647183498555)
        ·
          refine ⟨189116404214470775247833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126077602809647183498555 189116404214470775247833)
          ·
            refine ⟨141837303160853081435875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189116404214470775247833 141837303160853081435875)
            ·
              refine ⟨212755954741279622153813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141837303160853081435875 212755954741279622153813)
              ·
                refine ⟨2493233844624370572115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 212755954741279622153813 2493233844624370572115)
                ·
                  rfl

theorem cell21_32775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 8].length) (baseStart_32775 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_32775 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_32775 prefixEnd_32775 := by exact prefixLift 32775
  have htrace : WordTrace (prefixWord ++ tailWord_32775) baseStart_32775 baseEnd_32775 := by
    simpa [prefixWord, tailWord_32775, baseEnd_32775] using wordTrace_append hprefix tailTrace_32775
  have hstable : (prefixWord ++ tailWord_32775).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32775).length < 2 ^ (prefixWord ++ tailWord_32775).sum := by decide
  have hdescent : baseEnd_32775 < baseStart_32775 := by decide
  rcases family_descends (prefixWord ++ tailWord_32775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32778 : List Nat := [3, 1, 2, 2, 4, 1, 1, 3, 4]
def baseStart_32778 : Nat := 118140960795 + 32778 * 2 ^ 59
def prefixEnd_32778 : Nat := 4983230072969 + 3 ^ 40 * 32778 * 2
def baseEnd_32778 : Nat := 7480386174745773166339

theorem tailTrace_32778 : CollatzResearch.WordTrace tailWord_32778 prefixEnd_32778 7480386174745773166339 := by
  unfold tailWord_32778
  simp only [CollatzResearch.WordTrace]
  refine ⟨298877968814594720456747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 797007916838919254551325 298877968814594720456747)
  ·
    refine ⟨448316953221892080685121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298877968814594720456747 448316953221892080685121)
    ·
      refine ⟨336237714916419060513841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 448316953221892080685121 336237714916419060513841)
      ·
        refine ⟨252178286187314295385381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336237714916419060513841 252178286187314295385381)
        ·
          refine ⟨47283428660121430384759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 252178286187314295385381 47283428660121430384759)
          ·
            refine ⟨70925142990182145577139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47283428660121430384759 70925142990182145577139)
            ·
              refine ⟨106387714485273218365709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70925142990182145577139 106387714485273218365709)
              ·
                refine ⟨39895392931977456887141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106387714485273218365709 39895392931977456887141)
                ·
                  refine ⟨7480386174745773166339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39895392931977456887141 7480386174745773166339)
                  ·
                    rfl

theorem cell21_32778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 3, 4].length) (baseStart_32778 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_32778 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_32778 prefixEnd_32778 := by exact prefixLift 32778
  have htrace : WordTrace (prefixWord ++ tailWord_32778) baseStart_32778 baseEnd_32778 := by
    simpa [prefixWord, tailWord_32778, baseEnd_32778] using wordTrace_append hprefix tailTrace_32778
  have hstable : (prefixWord ++ tailWord_32778).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32778).length < 2 ^ (prefixWord ++ tailWord_32778).sum := by decide
  have hdescent : baseEnd_32778 < baseStart_32778 := by decide
  rcases family_descends (prefixWord ++ tailWord_32778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32865 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 9]
def baseStart_32865 : Nat := 118140960795 + 32865 * 2 ^ 59
def prefixEnd_32865 : Nat := 4983230072969 + 3 ^ 40 * 32865 * 2
def baseEnd_32865 : Nat := 7500240760052955216161

theorem tailTrace_32865 : CollatzResearch.WordTrace tailWord_32865 prefixEnd_32865 7500240760052955216161 := by
  unfold tailWord_32865
  simp only [CollatzResearch.WordTrace]
  refine ⟨1198685025943192740244049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 799123350628795160162699 1198685025943192740244049)
  ·
    refine ⟨899013769457394555183037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1198685025943192740244049 899013769457394555183037)
    ·
      refine ⟨337130163546522958193639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 899013769457394555183037 337130163546522958193639)
      ·
        refine ⟨505695245319784437290459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337130163546522958193639 505695245319784437290459)
        ·
          refine ⟨758542867979676655935689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 505695245319784437290459 758542867979676655935689)
          ·
            refine ⟨568907150984757491951767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 758542867979676655935689 568907150984757491951767)
            ·
              refine ⟨853360726477136237927651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 568907150984757491951767 853360726477136237927651)
              ·
                refine ⟨1280041089715704356891477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 853360726477136237927651 1280041089715704356891477)
                ·
                  refine ⟨7500240760052955216161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1280041089715704356891477 7500240760052955216161)
                  ·
                    rfl

theorem cell21_32865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 9].length) (baseStart_32865 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_32865 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_32865 prefixEnd_32865 := by exact prefixLift 32865
  have htrace : WordTrace (prefixWord ++ tailWord_32865) baseStart_32865 baseEnd_32865 := by
    simpa [prefixWord, tailWord_32865, baseEnd_32865] using wordTrace_append hprefix tailTrace_32865
  have hstable : (prefixWord ++ tailWord_32865).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32865).length < 2 ^ (prefixWord ++ tailWord_32865).sum := by decide
  have hdescent : baseEnd_32865 < baseStart_32865 := by decide
  rcases family_descends (prefixWord ++ tailWord_32865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32882 : List Nat := [3, 2, 1, 2, 2, 2, 1, 3, 5]
def baseStart_32882 : Nat := 118140960795 + 32882 * 2 ^ 59
def prefixEnd_32882 : Nat := 4983230072969 + 3 ^ 40 * 32882 * 2
def baseEnd_32882 : Nat := 7504120391664703432793

theorem tailTrace_32882 : CollatzResearch.WordTrace tailWord_32882 prefixEnd_32882 7504120391664703432793 := by
  unfold tailWord_32882
  simp only [CollatzResearch.WordTrace]
  refine ⟨299826266720401160903225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 799536711254403095741933 299826266720401160903225)
  ·
    refine ⟨224869700040300870677419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299826266720401160903225 224869700040300870677419)
    ·
      refine ⟨337304550060451306016129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224869700040300870677419 337304550060451306016129)
      ·
        refine ⟨252978412545338479512097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337304550060451306016129 252978412545338479512097)
        ·
          refine ⟨189733809409003859634073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252978412545338479512097 189733809409003859634073)
          ·
            refine ⟨142300357056752894725555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189733809409003859634073 142300357056752894725555)
            ·
              refine ⟨213450535585129342088333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142300357056752894725555 213450535585129342088333)
              ·
                refine ⟨80043950844423503283125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 213450535585129342088333 80043950844423503283125)
                ·
                  refine ⟨7504120391664703432793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80043950844423503283125 7504120391664703432793)
                  ·
                    rfl

theorem cell21_32882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_32882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_32882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_32882 prefixEnd_32882 := by exact prefixLift 32882
  have htrace : WordTrace (prefixWord ++ tailWord_32882) baseStart_32882 baseEnd_32882 := by
    simpa [prefixWord, tailWord_32882, baseEnd_32882] using wordTrace_append hprefix tailTrace_32882
  have hstable : (prefixWord ++ tailWord_32882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32882).length < 2 ^ (prefixWord ++ tailWord_32882).sum := by decide
  have hdescent : baseEnd_32882 < baseStart_32882 := by decide
  rcases family_descends (prefixWord ++ tailWord_32882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_32927 : List Nat := [1, 1, 2, 6, 1, 1, 9]
def baseStart_32927 : Nat := 118140960795 + 32927 * 2 ^ 59
def prefixEnd_32927 : Nat := 4983230072969 + 3 ^ 40 * 32927 * 2
def baseEnd_32927 : Nat := 834932222750513909189

theorem tailTrace_32927 : CollatzResearch.WordTrace tailWord_32927 prefixEnd_32927 834932222750513909189 := by
  unfold tailWord_32927
  simp only [CollatzResearch.WordTrace]
  refine ⟨1200946351718577329001035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 800630901145718219334023 1200946351718577329001035)
  ·
    refine ⟨1801419527577865993501553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1200946351718577329001035 1801419527577865993501553)
    ·
      refine ⟨1351064645683399495126165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1801419527577865993501553 1351064645683399495126165)
      ·
        refine ⟨63331155266409351334039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1351064645683399495126165 63331155266409351334039)
        ·
          refine ⟨94996732899614027001059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63331155266409351334039 94996732899614027001059)
          ·
            refine ⟨142495099349421040501589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94996732899614027001059 142495099349421040501589)
            ·
              refine ⟨834932222750513909189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 142495099349421040501589 834932222750513909189)
              ·
                rfl

theorem cell21_32927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 9].length) (baseStart_32927 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_32927 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_32927 prefixEnd_32927 := by exact prefixLift 32927
  have htrace : WordTrace (prefixWord ++ tailWord_32927) baseStart_32927 baseEnd_32927 := by
    simpa [prefixWord, tailWord_32927, baseEnd_32927] using wordTrace_append hprefix tailTrace_32927
  have hstable : (prefixWord ++ tailWord_32927).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_32927).length < 2 ^ (prefixWord ++ tailWord_32927).sum := by decide
  have hdescent : baseEnd_32927 < baseStart_32927 := by decide
  rcases family_descends (prefixWord ++ tailWord_32927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33020 : List Nat := [2, 2, 2, 1, 4, 2, 3, 5]
def baseStart_33020 : Nat := 118140960795 + 33020 * 2 ^ 59
def prefixEnd_33020 : Nat := 4983230072969 + 3 ^ 40 * 33020 * 2
def baseEnd_33020 : Nat := 2511871290602376710837

theorem tailTrace_33020 : CollatzResearch.WordTrace tailWord_33020 prefixEnd_33020 2511871290602376710837 := by
  unfold tailWord_33020
  simp only [CollatzResearch.WordTrace]
  refine ⟨602169170190827106068257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 802892226921102808091009 602169170190827106068257)
  ·
    refine ⟨451626877643120329551193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 602169170190827106068257 451626877643120329551193)
    ·
      refine ⟨338720158232340247163395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451626877643120329551193 338720158232340247163395)
      ·
        refine ⟨508080237348510370745093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338720158232340247163395 508080237348510370745093)
        ·
          refine ⟨95265044502845694514705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 508080237348510370745093 95265044502845694514705)
          ·
            refine ⟨71448783377134270886029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95265044502845694514705 71448783377134270886029)
            ·
              refine ⟨26793293766425351582261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71448783377134270886029 26793293766425351582261)
              ·
                refine ⟨2511871290602376710837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26793293766425351582261 2511871290602376710837)
                ·
                  rfl

theorem cell21_33020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 5].length) (baseStart_33020 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_33020 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_33020 prefixEnd_33020 := by exact prefixLift 33020
  have htrace : WordTrace (prefixWord ++ tailWord_33020) baseStart_33020 baseEnd_33020 := by
    simpa [prefixWord, tailWord_33020, baseEnd_33020] using wordTrace_append hprefix tailTrace_33020
  have hstable : (prefixWord ++ tailWord_33020).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33020).length < 2 ^ (prefixWord ++ tailWord_33020).sum := by decide
  have hdescent : baseEnd_33020 < baseStart_33020 := by decide
  rcases family_descends (prefixWord ++ tailWord_33020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33048 : List Nat := [2, 1, 2, 3, 1, 2, 3, 1, 6]
def baseStart_33048 : Nat := 118140960795 + 33048 * 2 ^ 59
def prefixEnd_33048 : Nat := 4983230072969 + 3 ^ 40 * 33048 * 2
def baseEnd_33048 : Nat := 7542003853285303665787

theorem tailTrace_33048 : CollatzResearch.WordTrace tailWord_33048 prefixEnd_33048 7542003853285303665787 := by
  unfold tailWord_33048
  simp only [CollatzResearch.WordTrace]
  refine ⟨602679792140107497077899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 803573056186809996103865 602679792140107497077899)
  ·
    refine ⟨904019688210161245616849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 602679792140107497077899 904019688210161245616849)
    ·
      refine ⟨678014766157620934212637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 904019688210161245616849 678014766157620934212637)
      ·
        refine ⟨254255537309107850329739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 678014766157620934212637 254255537309107850329739)
        ·
          refine ⟨381383305963661775494609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254255537309107850329739 381383305963661775494609)
          ·
            refine ⟨286037479472746331620957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 381383305963661775494609 286037479472746331620957)
            ·
              refine ⟨107264054802279874357859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 286037479472746331620957 107264054802279874357859)
              ·
                refine ⟨160896082203419811536789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107264054802279874357859 160896082203419811536789)
                ·
                  refine ⟨7542003853285303665787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 160896082203419811536789 7542003853285303665787)
                  ·
                    rfl

theorem cell21_33048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 6].length) (baseStart_33048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_33048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_33048 prefixEnd_33048 := by exact prefixLift 33048
  have htrace : WordTrace (prefixWord ++ tailWord_33048) baseStart_33048 baseEnd_33048 := by
    simpa [prefixWord, tailWord_33048, baseEnd_33048] using wordTrace_append hprefix tailTrace_33048
  have hstable : (prefixWord ++ tailWord_33048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33048).length < 2 ^ (prefixWord ++ tailWord_33048).sum := by decide
  have hdescent : baseEnd_33048 < baseStart_33048 := by decide
  rcases family_descends (prefixWord ++ tailWord_33048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33116 : List Nat := [2, 2, 4, 3, 1, 2, 2, 1, 4]
def baseStart_33116 : Nat := 118140960795 + 33116 * 2 ^ 59
def prefixEnd_33116 : Nat := 4983230072969 + 3 ^ 40 * 33116 * 2
def baseEnd_33116 : Nat := 7557522379732296532315

theorem tailTrace_33116 : CollatzResearch.WordTrace tailWord_33116 prefixEnd_33116 7557522379732296532315 := by
  unfold tailWord_33116
  simp only [CollatzResearch.WordTrace]
  refine ⟨603919874016931303815601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 805226498689241738420801 603919874016931303815601)
  ·
    refine ⟨452939905512698477861701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 603919874016931303815601 452939905512698477861701)
    ·
      refine ⟨84926232283630964599069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 452939905512698477861701 84926232283630964599069)
      ·
        refine ⟨31847337106361611724651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84926232283630964599069 31847337106361611724651)
        ·
          refine ⟨47771005659542417586977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31847337106361611724651 47771005659542417586977)
          ·
            refine ⟨35828254244656813190233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47771005659542417586977 35828254244656813190233)
            ·
              refine ⟨26871190683492609892675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35828254244656813190233 26871190683492609892675)
              ·
                refine ⟨40306786025238914839013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26871190683492609892675 40306786025238914839013)
                ·
                  refine ⟨7557522379732296532315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40306786025238914839013 7557522379732296532315)
                  ·
                    rfl

theorem cell21_33116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 1, 4].length) (baseStart_33116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_33116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_33116 prefixEnd_33116 := by exact prefixLift 33116
  have htrace : WordTrace (prefixWord ++ tailWord_33116) baseStart_33116 baseEnd_33116 := by
    simpa [prefixWord, tailWord_33116, baseEnd_33116] using wordTrace_append hprefix tailTrace_33116
  have hstable : (prefixWord ++ tailWord_33116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33116).length < 2 ^ (prefixWord ++ tailWord_33116).sum := by decide
  have hdescent : baseEnd_33116 < baseStart_33116 := by decide
  rcases family_descends (prefixWord ++ tailWord_33116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33155 : List Nat := [1, 1, 1, 3, 7, 8]
def baseStart_33155 : Nat := 118140960795 + 33155 * 2 ^ 59
def prefixEnd_33155 : Nat := 4983230072969 + 3 ^ 40 * 33155 * 2
def baseEnd_33155 : Nat := 280237878188033162305

theorem tailTrace_33155 : CollatzResearch.WordTrace tailWord_33155 prefixEnd_33155 280237878188033162305 := by
  unfold tailWord_33155
  simp only [CollatzResearch.WordTrace]
  refine ⟨1209262194892572268300919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 806174796595048178867279 1209262194892572268300919)
  ·
    refine ⟨1813893292338858402451379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1209262194892572268300919 1813893292338858402451379)
    ·
      refine ⟨2720839938508287603677069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1813893292338858402451379 2720839938508287603677069)
      ·
        refine ⟨1020314976940607851378901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2720839938508287603677069 1020314976940607851378901)
        ·
          refine ⟨23913632272045496516693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 1020314976940607851378901 23913632272045496516693)
          ·
            refine ⟨280237878188033162305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 23913632272045496516693 280237878188033162305)
            ·
              rfl

theorem cell21_33155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 8].length) (baseStart_33155 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_33155 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_33155 prefixEnd_33155 := by exact prefixLift 33155
  have htrace : WordTrace (prefixWord ++ tailWord_33155) baseStart_33155 baseEnd_33155 := by
    simpa [prefixWord, tailWord_33155, baseEnd_33155] using wordTrace_append hprefix tailTrace_33155
  have hstable : (prefixWord ++ tailWord_33155).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33155).length < 2 ^ (prefixWord ++ tailWord_33155).sum := by decide
  have hdescent : baseEnd_33155 < baseStart_33155 := by decide
  rcases family_descends (prefixWord ++ tailWord_33155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33186 : List Nat := [3, 3, 1, 2, 1, 1, 3, 2, 5]
def baseStart_33186 : Nat := 118140960795 + 33186 * 2 ^ 59
def prefixEnd_33186 : Nat := 4983230072969 + 3 ^ 40 * 33186 * 2
def baseEnd_33186 : Nat := 7573497333427730365505

theorem tailTrace_33186 : CollatzResearch.WordTrace tailWord_33186 prefixEnd_33186 7573497333427730365505 := by
  unfold tailWord_33186
  simp only [CollatzResearch.WordTrace]
  refine ⟨302598214445066140669853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 806928571853509708452941 302598214445066140669853)
  ·
    refine ⟨113474330416899802751195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302598214445066140669853 113474330416899802751195)
    ·
      refine ⟨170211495625349704126793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113474330416899802751195 170211495625349704126793)
      ·
        refine ⟨127658621719012278095095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170211495625349704126793 127658621719012278095095)
        ·
          refine ⟨191487932578518417142643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127658621719012278095095 191487932578518417142643)
          ·
            refine ⟨287231898867777625713965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191487932578518417142643 287231898867777625713965)
            ·
              refine ⟨107711962075416609642737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 287231898867777625713965 107711962075416609642737)
              ·
                refine ⟨80783971556562457232053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107711962075416609642737 80783971556562457232053)
                ·
                  refine ⟨7573497333427730365505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80783971556562457232053 7573497333427730365505)
                  ·
                    rfl

theorem cell21_33186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_33186 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_33186 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_33186 prefixEnd_33186 := by exact prefixLift 33186
  have htrace : WordTrace (prefixWord ++ tailWord_33186) baseStart_33186 baseEnd_33186 := by
    simpa [prefixWord, tailWord_33186, baseEnd_33186] using wordTrace_append hprefix tailTrace_33186
  have hstable : (prefixWord ++ tailWord_33186).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33186).length < 2 ^ (prefixWord ++ tailWord_33186).sum := by decide
  have hdescent : baseEnd_33186 < baseStart_33186 := by decide
  rcases family_descends (prefixWord ++ tailWord_33186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33259 : List Nat := [1, 1, 1, 1, 2, 3, 3, 1, 8]
def baseStart_33259 : Nat := 118140960795 + 33259 * 2 ^ 59
def prefixEnd_33259 : Nat := 4983230072969 + 3 ^ 40 * 33259 * 2
def baseEnd_33259 : Nat := 7590156927995825648689

theorem tailTrace_33259 : CollatzResearch.WordTrace tailWord_33259 prefixEnd_33259 7590156927995825648689 := by
  unfold tailWord_33259
  simp only [CollatzResearch.WordTrace]
  refine ⟨1213055386515798030086831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 808703591010532020057887 1213055386515798030086831)
  ·
    refine ⟨1819583079773697045130247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1213055386515798030086831 1819583079773697045130247)
    ·
      refine ⟨2729374619660545567695371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1819583079773697045130247 2729374619660545567695371)
      ·
        refine ⟨4094061929490818351543057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2729374619660545567695371 4094061929490818351543057)
        ·
          refine ⟨3070546447118113763657293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4094061929490818351543057 3070546447118113763657293)
          ·
            refine ⟨1151454917669292661371485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3070546447118113763657293 1151454917669292661371485)
            ·
              refine ⟨431795594125984748014307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1151454917669292661371485 431795594125984748014307)
              ·
                refine ⟨647693391188977122021461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 431795594125984748014307 647693391188977122021461)
                ·
                  refine ⟨7590156927995825648689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 647693391188977122021461 7590156927995825648689)
                  ·
                    rfl

theorem cell21_33259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 8].length) (baseStart_33259 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_33259 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_33259 prefixEnd_33259 := by exact prefixLift 33259
  have htrace : WordTrace (prefixWord ++ tailWord_33259) baseStart_33259 baseEnd_33259 := by
    simpa [prefixWord, tailWord_33259, baseEnd_33259] using wordTrace_append hprefix tailTrace_33259
  have hstable : (prefixWord ++ tailWord_33259).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33259).length < 2 ^ (prefixWord ++ tailWord_33259).sum := by decide
  have hdescent : baseEnd_33259 < baseStart_33259 := by decide
  rcases family_descends (prefixWord ++ tailWord_33259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33276 : List Nat := [2, 2, 2, 1, 2, 1, 1, 6, 4]
def baseStart_33276 : Nat := 118140960795 + 33276 * 2 ^ 59
def prefixEnd_33276 : Nat := 4983230072969 + 3 ^ 40 * 33276 * 2
def baseEnd_33276 : Nat := 7594036559607573865321

theorem tailTrace_33276 : CollatzResearch.WordTrace tailWord_33276 prefixEnd_33276 7594036559607573865321 := by
  unfold tailWord_33276
  simp only [CollatzResearch.WordTrace]
  refine ⟨606837713727104966727841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 809116951636139955637121 606837713727104966727841)
  ·
    refine ⟨455128285295328725045881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 606837713727104966727841 455128285295328725045881)
    ·
      refine ⟨341346213971496543784411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455128285295328725045881 341346213971496543784411)
      ·
        refine ⟨512019320957244815676617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341346213971496543784411 512019320957244815676617)
        ·
          refine ⟨384014490717933611757463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 512019320957244815676617 384014490717933611757463)
          ·
            refine ⟨576021736076900417636195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384014490717933611757463 576021736076900417636195)
            ·
              refine ⟨864032604115350626454293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 576021736076900417636195 864032604115350626454293)
              ·
                refine ⟨40501528317907060615045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 864032604115350626454293 40501528317907060615045)
                ·
                  refine ⟨7594036559607573865321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40501528317907060615045 7594036559607573865321)
                  ·
                    rfl

theorem cell21_33276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 6, 4].length) (baseStart_33276 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_33276 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_33276 prefixEnd_33276 := by exact prefixLift 33276
  have htrace : WordTrace (prefixWord ++ tailWord_33276) baseStart_33276 baseEnd_33276 := by
    simpa [prefixWord, tailWord_33276, baseEnd_33276] using wordTrace_append hprefix tailTrace_33276
  have hstable : (prefixWord ++ tailWord_33276).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33276).length < 2 ^ (prefixWord ++ tailWord_33276).sum := by decide
  have hdescent : baseEnd_33276 < baseStart_33276 := by decide
  rcases family_descends (prefixWord ++ tailWord_33276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33279 : List Nat := [1, 1, 2, 2, 1, 2, 7, 2, 3]
def baseStart_33279 : Nat := 118140960795 + 33279 * 2 ^ 59
def prefixEnd_33279 : Nat := 4983230072969 + 3 ^ 40 * 33279 * 2
def baseEnd_33279 : Nat := 7594721200480235315315

theorem tailTrace_33279 : CollatzResearch.WordTrace tailWord_33279 prefixEnd_33279 7594721200480235315315 := by
  unfold tailWord_33279
  simp only [CollatzResearch.WordTrace]
  refine ⟨1213784846443341445814891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 809189897628894297209927 1213784846443341445814891)
  ·
    refine ⟨1820677269665012168722337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1213784846443341445814891 1820677269665012168722337)
    ·
      refine ⟨1365507952248759126541753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1820677269665012168722337 1365507952248759126541753)
      ·
        refine ⟨1024130964186569344906315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1365507952248759126541753 1024130964186569344906315)
        ·
          refine ⟨1536196446279854017359473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1024130964186569344906315 1536196446279854017359473)
          ·
            refine ⟨1152147334709890513019605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1536196446279854017359473 1152147334709890513019605)
            ·
              refine ⟨27003453157263058898897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1152147334709890513019605 27003453157263058898897)
              ·
                refine ⟨20252589867947294174173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27003453157263058898897 20252589867947294174173)
                ·
                  refine ⟨7594721200480235315315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20252589867947294174173 7594721200480235315315)
                  ·
                    rfl

theorem cell21_33279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 2, 3].length) (baseStart_33279 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_33279 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_33279 prefixEnd_33279 := by exact prefixLift 33279
  have htrace : WordTrace (prefixWord ++ tailWord_33279) baseStart_33279 baseEnd_33279 := by
    simpa [prefixWord, tailWord_33279, baseEnd_33279] using wordTrace_append hprefix tailTrace_33279
  have hstable : (prefixWord ++ tailWord_33279).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33279).length < 2 ^ (prefixWord ++ tailWord_33279).sum := by decide
  have hdescent : baseEnd_33279 < baseStart_33279 := by decide
  rcases family_descends (prefixWord ++ tailWord_33279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33372 : List Nat := [2, 2, 4, 1, 3, 1, 2, 3, 3]
def baseStart_33372 : Nat := 118140960795 + 33372 * 2 ^ 59
def prefixEnd_33372 : Nat := 4983230072969 + 3 ^ 40 * 33372 * 2
def baseEnd_33372 : Nat := 7615945067532740265125

theorem tailTrace_33372 : CollatzResearch.WordTrace tailWord_33372 prefixEnd_33372 7615945067532740265125 := by
  unfold tailWord_33372
  simp only [CollatzResearch.WordTrace]
  refine ⟨608588417553209164475185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 811451223404278885966913 608588417553209164475185)
  ·
    refine ⟨456441313164906873356389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 608588417553209164475185 456441313164906873356389)
    ·
      refine ⟨85582746218420038754323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 456441313164906873356389 85582746218420038754323)
      ·
        refine ⟨128374119327630058131485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85582746218420038754323 128374119327630058131485)
        ·
          refine ⟨48140294747861271799307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128374119327630058131485 48140294747861271799307)
          ·
            refine ⟨72210442121791907698961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48140294747861271799307 72210442121791907698961)
            ·
              refine ⟨54157831591343930774221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72210442121791907698961 54157831591343930774221)
              ·
                refine ⟨20309186846753974040333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54157831591343930774221 20309186846753974040333)
                ·
                  refine ⟨7615945067532740265125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20309186846753974040333 7615945067532740265125)
                  ·
                    rfl

theorem cell21_33372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 3, 3].length) (baseStart_33372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_33372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_33372 prefixEnd_33372 := by exact prefixLift 33372
  have htrace : WordTrace (prefixWord ++ tailWord_33372) baseStart_33372 baseEnd_33372 := by
    simpa [prefixWord, tailWord_33372, baseEnd_33372] using wordTrace_append hprefix tailTrace_33372
  have hstable : (prefixWord ++ tailWord_33372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33372).length < 2 ^ (prefixWord ++ tailWord_33372).sum := by decide
  have hdescent : baseEnd_33372 < baseStart_33372 := by decide
  rcases family_descends (prefixWord ++ tailWord_33372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33507 : List Nat := [1, 1, 1, 7, 1, 2, 1, 4, 3]
def baseStart_33507 : Nat := 118140960795 + 33507 * 2 ^ 59
def prefixEnd_33507 : Nat := 4983230072969 + 3 ^ 40 * 33507 * 2
def baseEnd_33507 : Nat := 7646753906802505514849

theorem tailTrace_33507 : CollatzResearch.WordTrace tailWord_33507 prefixEnd_33507 7646753906802505514849 := by
  unfold tailWord_33507
  simp only [CollatzResearch.WordTrace]
  refine ⟨1222100689617336385114775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 814733793078224256743183 1222100689617336385114775)
  ·
    refine ⟨1833151034426004577672163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1222100689617336385114775 1833151034426004577672163)
    ·
      refine ⟨2749726551639006866508245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1833151034426004577672163 2749726551639006866508245)
      ·
        refine ⟨64446716054039223433787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 2749726551639006866508245 64446716054039223433787)
        ·
          refine ⟨96670074081058835150681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64446716054039223433787 96670074081058835150681)
          ·
            refine ⟨72502555560794126363011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96670074081058835150681 72502555560794126363011)
            ·
              refine ⟨108753833341191189544517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72502555560794126363011 108753833341191189544517)
              ·
                refine ⟨20391343751473348039597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108753833341191189544517 20391343751473348039597)
                ·
                  refine ⟨7646753906802505514849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20391343751473348039597 7646753906802505514849)
                  ·
                    rfl

theorem cell21_33507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 4, 3].length) (baseStart_33507 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_33507 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_33507 prefixEnd_33507 := by exact prefixLift 33507
  have htrace : WordTrace (prefixWord ++ tailWord_33507) baseStart_33507 baseEnd_33507 := by
    simpa [prefixWord, tailWord_33507, baseEnd_33507] using wordTrace_append hprefix tailTrace_33507
  have hstable : (prefixWord ++ tailWord_33507).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33507).length < 2 ^ (prefixWord ++ tailWord_33507).sum := by decide
  have hdescent : baseEnd_33507 < baseStart_33507 := by decide
  rcases family_descends (prefixWord ++ tailWord_33507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33524 : List Nat := [2, 6, 1, 1, 2, 1, 1, 2, 5]
def baseStart_33524 : Nat := 118140960795 + 33524 * 2 ^ 59
def prefixEnd_33524 : Nat := 4983230072969 + 3 ^ 40 * 33524 * 2
def baseEnd_33524 : Nat := 7650633538414253731481

theorem tailTrace_33524 : CollatzResearch.WordTrace tailWord_33524 prefixEnd_33524 7650633538414253731481 := by
  unfold tailWord_33524
  simp only [CollatzResearch.WordTrace]
  refine ⟨611360365277874144241813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 815147153703832192322417 611360365277874144241813)
  ·
    refine ⟨28657517122400350511335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 611360365277874144241813 28657517122400350511335)
    ·
      refine ⟨42986275683600525767003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28657517122400350511335 42986275683600525767003)
      ·
        refine ⟨64479413525400788650505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42986275683600525767003 64479413525400788650505)
        ·
          refine ⟨48359560144050591487879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64479413525400788650505 48359560144050591487879)
          ·
            refine ⟨72539340216075887231819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48359560144050591487879 72539340216075887231819)
            ·
              refine ⟨108809010324113830847729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72539340216075887231819 108809010324113830847729)
              ·
                refine ⟨81606757743085373135797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108809010324113830847729 81606757743085373135797)
                ·
                  refine ⟨7650633538414253731481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81606757743085373135797 7650633538414253731481)
                  ·
                    rfl

theorem cell21_33524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_33524 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_33524 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_33524 prefixEnd_33524 := by exact prefixLift 33524
  have htrace : WordTrace (prefixWord ++ tailWord_33524) baseStart_33524 baseEnd_33524 := by
    simpa [prefixWord, tailWord_33524, baseEnd_33524] using wordTrace_append hprefix tailTrace_33524
  have hstable : (prefixWord ++ tailWord_33524).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33524).length < 2 ^ (prefixWord ++ tailWord_33524).sum := by decide
  have hdescent : baseEnd_33524 < baseStart_33524 := by decide
  rcases family_descends (prefixWord ++ tailWord_33524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33625 : List Nat := [1, 2, 1, 2, 2, 4, 3, 1, 5]
def baseStart_33625 : Nat := 118140960795 + 33625 * 2 ^ 59
def prefixEnd_33625 : Nat := 4983230072969 + 3 ^ 40 * 33625 * 2
def baseEnd_33625 : Nat := 7673683114460522547941

theorem tailTrace_33625 : CollatzResearch.WordTrace tailWord_33625 prefixEnd_33625 7673683114460522547941 := by
  unfold tailWord_33625
  simp only [CollatzResearch.WordTrace]
  refine ⟨1226404503189842537910329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 817603002126561691940219 1226404503189842537910329)
  ·
    refine ⟨919803377392381903432747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1226404503189842537910329 919803377392381903432747)
    ·
      refine ⟨1379705066088572855149121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 919803377392381903432747 1379705066088572855149121)
      ·
        refine ⟨1034778799566429641361841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1379705066088572855149121 1034778799566429641361841)
        ·
          refine ⟨776084099674822231021381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1034778799566429641361841 776084099674822231021381)
          ·
            refine ⟨145515768689029168316509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 776084099674822231021381 145515768689029168316509)
            ·
              refine ⟨54568413258385938118691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145515768689029168316509 54568413258385938118691)
              ·
                refine ⟨81852619887578907178037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54568413258385938118691 81852619887578907178037)
                ·
                  refine ⟨7673683114460522547941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81852619887578907178037 7673683114460522547941)
                  ·
                    rfl

theorem cell21_33625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 5].length) (baseStart_33625 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_33625 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_33625 prefixEnd_33625 := by exact prefixLift 33625
  have htrace : WordTrace (prefixWord ++ tailWord_33625) baseStart_33625 baseEnd_33625 := by
    simpa [prefixWord, tailWord_33625, baseEnd_33625] using wordTrace_append hprefix tailTrace_33625
  have hstable : (prefixWord ++ tailWord_33625).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33625).length < 2 ^ (prefixWord ++ tailWord_33625).sum := by decide
  have hdescent : baseEnd_33625 < baseStart_33625 := by decide
  rcases family_descends (prefixWord ++ tailWord_33625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33898 : List Nat := [3, 1, 3, 2, 2, 2, 8]
def baseStart_33898 : Nat := 118140960795 + 33898 * 2 ^ 59
def prefixEnd_33898 : Nat := 4983230072969 + 3 ^ 40 * 33898 * 2
def baseEnd_33898 : Nat := 859553937096968277487

theorem tailTrace_33898 : CollatzResearch.WordTrace tailWord_33898 prefixEnd_33898 859553937096968277487 := by
  unfold tailWord_33898
  simp only [CollatzResearch.WordTrace]
  refine ⟨309090407800202540649587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 824241087467206775065565 309090407800202540649587)
  ·
    refine ⟨463635611700303810974381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 309090407800202540649587 463635611700303810974381)
    ·
      refine ⟨173863354387613929115393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 463635611700303810974381 173863354387613929115393)
      ·
        refine ⟨130397515790710446836545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173863354387613929115393 130397515790710446836545)
        ·
          refine ⟨97798136843032835127409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130397515790710446836545 97798136843032835127409)
          ·
            refine ⟨73348602632274626345557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97798136843032835127409 73348602632274626345557)
            ·
              refine ⟨859553937096968277487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 73348602632274626345557 859553937096968277487)
              ·
                rfl

theorem cell21_33898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 8].length) (baseStart_33898 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_33898 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_33898 prefixEnd_33898 := by exact prefixLift 33898
  have htrace : WordTrace (prefixWord ++ tailWord_33898) baseStart_33898 baseEnd_33898 := by
    simpa [prefixWord, tailWord_33898, baseEnd_33898] using wordTrace_append hprefix tailTrace_33898
  have hstable : (prefixWord ++ tailWord_33898).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33898).length < 2 ^ (prefixWord ++ tailWord_33898).sum := by decide
  have hdescent : baseEnd_33898 < baseStart_33898 := by decide
  rcases family_descends (prefixWord ++ tailWord_33898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33901 : List Nat := [1, 5, 1, 1, 2, 4, 1, 2, 4]
def baseStart_33901 : Nat := 118140960795 + 33901 * 2 ^ 59
def prefixEnd_33901 : Nat := 4983230072969 + 3 ^ 40 * 33901 * 2
def baseEnd_33901 : Nat := 7736670074745375947377

theorem tailTrace_33901 : CollatzResearch.WordTrace tailWord_33901 prefixEnd_33901 7736670074745375947377 := by
  unfold tailWord_33901
  simp only [CollatzResearch.WordTrace]
  refine ⟨1236471050189941674957557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 824314033459961116638371 1236471050189941674957557)
  ·
    refine ⟨115919160955307032027271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1236471050189941674957557 115919160955307032027271)
    ·
      refine ⟨173878741432960548040907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115919160955307032027271 173878741432960548040907)
      ·
        refine ⟨260818112149440822061361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173878741432960548040907 260818112149440822061361)
        ·
          refine ⟨195613584112080616546021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 260818112149440822061361 195613584112080616546021)
          ·
            refine ⟨36677547021015115602379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 195613584112080616546021 36677547021015115602379)
            ·
              refine ⟨55016320531522673403569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36677547021015115602379 55016320531522673403569)
              ·
                refine ⟨41262240398642005052677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55016320531522673403569 41262240398642005052677)
                ·
                  refine ⟨7736670074745375947377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41262240398642005052677 7736670074745375947377)
                  ·
                    rfl

theorem cell21_33901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_33901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_33901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_33901 prefixEnd_33901 := by exact prefixLift 33901
  have htrace : WordTrace (prefixWord ++ tailWord_33901) baseStart_33901 baseEnd_33901 := by
    simpa [prefixWord, tailWord_33901, baseEnd_33901] using wordTrace_append hprefix tailTrace_33901
  have hstable : (prefixWord ++ tailWord_33901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33901).length < 2 ^ (prefixWord ++ tailWord_33901).sum := by decide
  have hdescent : baseEnd_33901 < baseStart_33901 := by decide
  rcases family_descends (prefixWord ++ tailWord_33901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33912 : List Nat := [2, 1, 2, 1, 1, 1, 5, 3, 5]
def baseStart_33912 : Nat := 118140960795 + 33912 * 2 ^ 59
def prefixEnd_33912 : Nat := 4983230072969 + 3 ^ 40 * 33912 * 2
def baseEnd_33912 : Nat := 7739180424611801264021

theorem tailTrace_33912 : CollatzResearch.WordTrace tailWord_33912 prefixEnd_33912 7739180424611801264021 := by
  unfold tailWord_33912
  simp only [CollatzResearch.WordTrace]
  refine ⟨618436126575045276803995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 824581502100060369071993 618436126575045276803995)
  ·
    refine ⟨927654189862567915205993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 618436126575045276803995 927654189862567915205993)
    ·
      refine ⟨695740642396925936404495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 927654189862567915205993 695740642396925936404495)
      ·
        refine ⟨1043610963595388904606743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 695740642396925936404495 1043610963595388904606743)
        ·
          refine ⟨1565416445393083356910115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1043610963595388904606743 1565416445393083356910115)
          ·
            refine ⟨2348124668089625035365173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1565416445393083356910115 2348124668089625035365173)
            ·
              refine ⟨220136687633402347065485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2348124668089625035365173 220136687633402347065485)
              ·
                refine ⟨82551257862525880149557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 220136687633402347065485 82551257862525880149557)
                ·
                  refine ⟨7739180424611801264021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 82551257862525880149557 7739180424611801264021)
                  ·
                    rfl

theorem cell21_33912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 5].length) (baseStart_33912 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_33912 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_33912 prefixEnd_33912 := by exact prefixLift 33912
  have htrace : WordTrace (prefixWord ++ tailWord_33912) baseStart_33912 baseEnd_33912 := by
    simpa [prefixWord, tailWord_33912, baseEnd_33912] using wordTrace_append hprefix tailTrace_33912
  have hstable : (prefixWord ++ tailWord_33912).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33912).length < 2 ^ (prefixWord ++ tailWord_33912).sum := by decide
  have hdescent : baseEnd_33912 < baseStart_33912 := by decide
  rcases family_descends (prefixWord ++ tailWord_33912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33943 : List Nat := [1, 1, 3, 3, 3, 1, 1, 2, 6]
def baseStart_33943 : Nat := 118140960795 + 33943 * 2 ^ 59
def prefixEnd_33943 : Nat := 4983230072969 + 3 ^ 40 * 33943 * 2
def baseEnd_33943 : Nat := 7746255046962636247291

theorem tailTrace_33943 : CollatzResearch.WordTrace tailWord_33943 prefixEnd_33943 7746255046962636247291 := by
  unfold tailWord_33943
  simp only [CollatzResearch.WordTrace]
  refine ⟨1238002916037782847986483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 825335277358521898657655 1238002916037782847986483)
  ·
    refine ⟨1857004374056674271979725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1238002916037782847986483 1857004374056674271979725)
    ·
      refine ⟨696376640271252851992397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1857004374056674271979725 696376640271252851992397)
      ·
        refine ⟨261141240101719819497149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 696376640271252851992397 261141240101719819497149)
        ·
          refine ⟨97927965038144932311431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 261141240101719819497149 97927965038144932311431)
          ·
            refine ⟨146891947557217398467147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97927965038144932311431 146891947557217398467147)
            ·
              refine ⟨220337921335826097700721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146891947557217398467147 220337921335826097700721)
              ·
                refine ⟨165253441001869573275541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 220337921335826097700721 165253441001869573275541)
                ·
                  refine ⟨7746255046962636247291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 165253441001869573275541 7746255046962636247291)
                  ·
                    rfl

theorem cell21_33943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 6].length) (baseStart_33943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_33943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_33943 prefixEnd_33943 := by exact prefixLift 33943
  have htrace : WordTrace (prefixWord ++ tailWord_33943) baseStart_33943 baseEnd_33943 := by
    simpa [prefixWord, tailWord_33943, baseEnd_33943] using wordTrace_append hprefix tailTrace_33943
  have hstable : (prefixWord ++ tailWord_33943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33943).length < 2 ^ (prefixWord ++ tailWord_33943).sum := by decide
  have hdescent : baseEnd_33943 < baseStart_33943 := by decide
  rcases family_descends (prefixWord ++ tailWord_33943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33957 : List Nat := [1, 3, 1, 2, 1, 4, 9]
def baseStart_33957 : Nat := 118140960795 + 33957 * 2 ^ 59
def prefixEnd_33957 : Nat := 4983230072969 + 3 ^ 40 * 33957 * 2
def baseEnd_33957 : Nat := 861050004189080334881

theorem tailTrace_33957 : CollatzResearch.WordTrace tailWord_33957 prefixEnd_33957 861050004189080334881 := by
  unfold tailWord_33957
  simp only [CollatzResearch.WordTrace]
  refine ⟨1238513537987063238996125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 825675691991375492664083 1238513537987063238996125)
  ·
    refine ⟨464442576745148714623547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1238513537987063238996125 464442576745148714623547)
    ·
      refine ⟨696663865117723071935321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 464442576745148714623547 696663865117723071935321)
      ·
        refine ⟨522497898838292303951491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 696663865117723071935321 522497898838292303951491)
        ·
          refine ⟨783746848257438455927237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 522497898838292303951491 783746848257438455927237)
          ·
            refine ⟨146952534048269710486357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 783746848257438455927237 146952534048269710486357)
            ·
              refine ⟨861050004189080334881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 146952534048269710486357 861050004189080334881)
              ·
                rfl

theorem cell21_33957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 9].length) (baseStart_33957 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_33957 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_33957 prefixEnd_33957 := by exact prefixLift 33957
  have htrace : WordTrace (prefixWord ++ tailWord_33957) baseStart_33957 baseEnd_33957 := by
    simpa [prefixWord, tailWord_33957, baseEnd_33957] using wordTrace_append hprefix tailTrace_33957
  have hstable : (prefixWord ++ tailWord_33957).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33957).length < 2 ^ (prefixWord ++ tailWord_33957).sum := by decide
  have hdescent : baseEnd_33957 < baseStart_33957 := by decide
  rcases family_descends (prefixWord ++ tailWord_33957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_33977 : List Nat := [1, 2, 1, 4, 1, 5, 2, 1, 4]
def baseStart_33977 : Nat := 118140960795 + 33977 * 2 ^ 59
def prefixEnd_33977 : Nat := 4983230072969 + 3 ^ 40 * 33977 * 2
def baseEnd_33977 : Nat := 7754014310186132680555

theorem tailTrace_33977 : CollatzResearch.WordTrace tailWord_33977 prefixEnd_33977 7754014310186132680555 := by
  unfold tailWord_33977
  simp only [CollatzResearch.WordTrace]
  refine ⟨1239242997914606654724185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 826161998609737769816123 1239242997914606654724185)
  ·
    refine ⟨929432248435954991043139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1239242997914606654724185 929432248435954991043139)
    ·
      refine ⟨1394148372653932486564709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 929432248435954991043139 1394148372653932486564709)
      ·
        refine ⟨261402819872612341230883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1394148372653932486564709 261402819872612341230883)
        ·
          refine ⟨392104229808918511846325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261402819872612341230883 392104229808918511846325)
          ·
            refine ⟨36759771544586110485593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 392104229808918511846325 36759771544586110485593)
            ·
              refine ⟨27569828658439582864195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36759771544586110485593 27569828658439582864195)
              ·
                refine ⟨41354742987659374296293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27569828658439582864195 41354742987659374296293)
                ·
                  refine ⟨7754014310186132680555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41354742987659374296293 7754014310186132680555)
                  ·
                    rfl

theorem cell21_33977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 1, 4].length) (baseStart_33977 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_33977 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_33977 prefixEnd_33977 := by exact prefixLift 33977
  have htrace : WordTrace (prefixWord ++ tailWord_33977) baseStart_33977 baseEnd_33977 := by
    simpa [prefixWord, tailWord_33977, baseEnd_33977] using wordTrace_append hprefix tailTrace_33977
  have hstable : (prefixWord ++ tailWord_33977).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_33977).length < 2 ^ (prefixWord ++ tailWord_33977).sum := by decide
  have hdescent : baseEnd_33977 < baseStart_33977 := by decide
  rcases family_descends (prefixWord ++ tailWord_33977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34185 : List Nat := [1, 2, 1, 1, 7, 9]
def baseStart_34185 : Nat := 118140960795 + 34185 * 2 ^ 59
def prefixEnd_34185 : Nat := 4983230072969 + 3 ^ 40 * 34185 * 2
def baseEnd_34185 : Nat := 288943805334221970869

theorem tailTrace_34185 : CollatzResearch.WordTrace tailWord_34185 prefixEnd_34185 288943805334221970869 := by
  unfold tailWord_34185
  simp only [CollatzResearch.WordTrace]
  refine ⟨1246829381161058178296009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 831219587440705452197339 1246829381161058178296009)
  ·
    refine ⟨935122035870793633722007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1246829381161058178296009 935122035870793633722007)
    ·
      refine ⟨1402683053806190450583011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 935122035870793633722007 1402683053806190450583011)
      ·
        refine ⟨2104024580709285675874517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1402683053806190450583011 2104024580709285675874517)
        ·
          refine ⟨49313076110373883028309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 2104024580709285675874517 49313076110373883028309)
          ·
            refine ⟨288943805334221970869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 49313076110373883028309 288943805334221970869)
            ·
              rfl

theorem cell21_34185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 9].length) (baseStart_34185 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_34185 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_34185 prefixEnd_34185 := by exact prefixLift 34185
  have htrace : WordTrace (prefixWord ++ tailWord_34185) baseStart_34185 baseEnd_34185 := by
    simpa [prefixWord, tailWord_34185, baseEnd_34185] using wordTrace_append hprefix tailTrace_34185
  have hstable : (prefixWord ++ tailWord_34185).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34185).length < 2 ^ (prefixWord ++ tailWord_34185).sum := by decide
  have hdescent : baseEnd_34185 < baseStart_34185 := by decide
  rcases family_descends (prefixWord ++ tailWord_34185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34261 : List Nat := [1, 3, 2, 3, 1, 1, 2, 8]
def baseStart_34261 : Nat := 118140960795 + 34261 * 2 ^ 59
def prefixEnd_34261 : Nat := 4983230072969 + 3 ^ 40 * 34261 * 2
def baseEnd_34261 : Nat := 2606275659821583315547

theorem tailTrace_34261 : CollatzResearch.WordTrace tailWord_34261 prefixEnd_34261 2606275659821583315547 := by
  unfold tailWord_34261
  simp only [CollatzResearch.WordTrace]
  refine ⟨1249601328885723158062637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 833067552590482105375091 1249601328885723158062637)
  ·
    refine ⟨468600498332146184273489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1249601328885723158062637 468600498332146184273489)
    ·
      refine ⟨351450373749109638205117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 468600498332146184273489 351450373749109638205117)
      ·
        refine ⟨131793890155916114326919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 351450373749109638205117 131793890155916114326919)
        ·
          refine ⟨197690835233874171490379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131793890155916114326919 197690835233874171490379)
          ·
            refine ⟨296536252850811257235569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197690835233874171490379 296536252850811257235569)
            ·
              refine ⟨222402189638108442926677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 296536252850811257235569 222402189638108442926677)
              ·
                refine ⟨2606275659821583315547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 222402189638108442926677 2606275659821583315547)
                ·
                  rfl

theorem cell21_34261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 8].length) (baseStart_34261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_34261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_34261 prefixEnd_34261 := by exact prefixLift 34261
  have htrace : WordTrace (prefixWord ++ tailWord_34261) baseStart_34261 baseEnd_34261 := by
    simpa [prefixWord, tailWord_34261, baseEnd_34261] using wordTrace_append hprefix tailTrace_34261
  have hstable : (prefixWord ++ tailWord_34261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34261).length < 2 ^ (prefixWord ++ tailWord_34261).sum := by decide
  have hdescent : baseEnd_34261 < baseStart_34261 := by decide
  rcases family_descends (prefixWord ++ tailWord_34261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34323 : List Nat := [1, 1, 1, 2, 1, 7, 1, 3, 4]
def baseStart_34323 : Nat := 118140960795 + 34323 * 2 ^ 59
def prefixEnd_34323 : Nat := 4983230072969 + 3 ^ 40 * 34323 * 2
def baseEnd_34323 : Nat := 7832976224166419913181

theorem tailTrace_34323 : CollatzResearch.WordTrace tailWord_34323 prefixEnd_34323 7832976224166419913181 := by
  unfold tailWord_34323
  simp only [CollatzResearch.WordTrace]
  refine ⟨1251862654661107746819623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 834575103107405164546415 1251862654661107746819623)
  ·
    refine ⟨1877793981991661620229435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1251862654661107746819623 1877793981991661620229435)
    ·
      refine ⟨2816690972987492430344153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1877793981991661620229435 2816690972987492430344153)
      ·
        refine ⟨2112518229740619322758115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2816690972987492430344153 2112518229740619322758115)
        ·
          refine ⟨3168777344610928984137173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2112518229740619322758115 3168777344610928984137173)
          ·
            refine ⟨74268219014318648065715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 3168777344610928984137173 74268219014318648065715)
            ·
              refine ⟨111402328521477972098573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74268219014318648065715 111402328521477972098573)
              ·
                refine ⟨41775873195554239536965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111402328521477972098573 41775873195554239536965)
                ·
                  refine ⟨7832976224166419913181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41775873195554239536965 7832976224166419913181)
                  ·
                    rfl

theorem cell21_34323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 3, 4].length) (baseStart_34323 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_34323 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_34323 prefixEnd_34323 := by exact prefixLift 34323
  have htrace : WordTrace (prefixWord ++ tailWord_34323) baseStart_34323 baseEnd_34323 := by
    simpa [prefixWord, tailWord_34323, baseEnd_34323] using wordTrace_append hprefix tailTrace_34323
  have hstable : (prefixWord ++ tailWord_34323).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34323).length < 2 ^ (prefixWord ++ tailWord_34323).sum := by decide
  have hdescent : baseEnd_34323 < baseStart_34323 := by decide
  rcases family_descends (prefixWord ++ tailWord_34323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34337 : List Nat := [1, 2, 3, 2, 2, 2, 2, 7]
def baseStart_34337 : Nat := 118140960795 + 34337 * 2 ^ 59
def prefixEnd_34337 : Nat := 4983230072969 + 3 ^ 40 * 34337 * 2
def baseEnd_34337 : Nat := 2612057071635168893273

theorem tailTrace_34337 : CollatzResearch.WordTrace tailWord_34337 prefixEnd_34337 2612057071635168893273 := by
  unfold tailWord_34337
  simp only [CollatzResearch.WordTrace]
  refine ⟨1252373276610388137829265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 834915517740258758552843 1252373276610388137829265)
  ·
    refine ⟨939279957457791103371949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1252373276610388137829265 939279957457791103371949)
    ·
      refine ⟨352229984046671663764481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 939279957457791103371949 352229984046671663764481)
      ·
        refine ⟨264172488035003747823361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 352229984046671663764481 264172488035003747823361)
        ·
          refine ⟨198129366026252810867521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 264172488035003747823361 198129366026252810867521)
          ·
            refine ⟨148597024519689608150641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 198129366026252810867521 148597024519689608150641)
            ·
              refine ⟨111447768389767206112981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148597024519689608150641 111447768389767206112981)
              ·
                refine ⟨2612057071635168893273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 111447768389767206112981 2612057071635168893273)
                ·
                  rfl

theorem cell21_34337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 7].length) (baseStart_34337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_34337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_34337 prefixEnd_34337 := by exact prefixLift 34337
  have htrace : WordTrace (prefixWord ++ tailWord_34337) baseStart_34337 baseEnd_34337 := by
    simpa [prefixWord, tailWord_34337, baseEnd_34337] using wordTrace_append hprefix tailTrace_34337
  have hstable : (prefixWord ++ tailWord_34337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34337).length < 2 ^ (prefixWord ++ tailWord_34337).sum := by decide
  have hdescent : baseEnd_34337 < baseStart_34337 := by decide
  rcases family_descends (prefixWord ++ tailWord_34337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34382 : List Nat := [4, 1, 1, 1, 1, 2, 1, 2, 8]
def baseStart_34382 : Nat := 118140960795 + 34382 * 2 ^ 59
def prefixEnd_34382 : Nat := 4983230072969 + 3 ^ 40 * 34382 * 2
def baseEnd_34382 : Nat := 7846440827995428429727

theorem tailTrace_34382 : CollatzResearch.WordTrace tailWord_34382 prefixEnd_34382 7846440827995428429727 := by
  unfold tailWord_34382
  simp only [CollatzResearch.WordTrace]
  refine ⟨156751820180920102902175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 836009707631573882144933 156751820180920102902175)
  ·
    refine ⟨235127730271380154353263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156751820180920102902175 235127730271380154353263)
    ·
      refine ⟨352691595407070231529895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235127730271380154353263 352691595407070231529895)
      ·
        refine ⟨529037393110605347294843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 352691595407070231529895 529037393110605347294843)
        ·
          refine ⟨793556089665908020942265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 529037393110605347294843 793556089665908020942265)
          ·
            refine ⟨595167067249431015706699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 793556089665908020942265 595167067249431015706699)
            ·
              refine ⟨892750600874146523560049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 595167067249431015706699 892750600874146523560049)
              ·
                refine ⟨669562950655609892670037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 892750600874146523560049 669562950655609892670037)
                ·
                  refine ⟨7846440827995428429727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 669562950655609892670037 7846440827995428429727)
                  ·
                    rfl

theorem cell21_34382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_34382 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_34382 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_34382 prefixEnd_34382 := by exact prefixLift 34382
  have htrace : WordTrace (prefixWord ++ tailWord_34382) baseStart_34382 baseEnd_34382 := by
    simpa [prefixWord, tailWord_34382, baseEnd_34382] using wordTrace_append hprefix tailTrace_34382
  have hstable : (prefixWord ++ tailWord_34382).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34382).length < 2 ^ (prefixWord ++ tailWord_34382).sum := by decide
  have hdescent : baseEnd_34382 < baseStart_34382 := by decide
  rcases family_descends (prefixWord ++ tailWord_34382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34416 : List Nat := [2, 1, 1, 1, 6, 3, 1, 2, 4]
def baseStart_34416 : Nat := 118140960795 + 34416 * 2 ^ 59
def prefixEnd_34416 : Nat := 4983230072969 + 3 ^ 40 * 34416 * 2
def baseEnd_34416 : Nat := 7854200091218924862991

theorem tailTrace_34416 : CollatzResearch.WordTrace tailWord_34416 prefixEnd_34416 7854200091218924862991 := by
  unfold tailWord_34416
  simp only [CollatzResearch.WordTrace]
  refine ⟨627627321662092314977551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 836836428882789753303401 627627321662092314977551)
  ·
    refine ⟨941440982493138472466327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 627627321662092314977551 941440982493138472466327)
    ·
      refine ⟨1412161473739707708699491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 941440982493138472466327 1412161473739707708699491)
      ·
        refine ⟨2118242210609561563049237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1412161473739707708699491 2118242210609561563049237)
        ·
          refine ⟨99292603622323198267933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2118242210609561563049237 99292603622323198267933)
          ·
            refine ⟨37234726358371199350475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99292603622323198267933 37234726358371199350475)
            ·
              refine ⟨55852089537556799025713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37234726358371199350475 55852089537556799025713)
              ·
                refine ⟨41889067153167599269285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55852089537556799025713 41889067153167599269285)
                ·
                  refine ⟨7854200091218924862991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41889067153167599269285 7854200091218924862991)
                  ·
                    rfl

theorem cell21_34416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 2, 4].length) (baseStart_34416 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_34416 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_34416 prefixEnd_34416 := by exact prefixLift 34416
  have htrace : WordTrace (prefixWord ++ tailWord_34416) baseStart_34416 baseEnd_34416 := by
    simpa [prefixWord, tailWord_34416, baseEnd_34416] using wordTrace_append hprefix tailTrace_34416
  have hstable : (prefixWord ++ tailWord_34416).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34416).length < 2 ^ (prefixWord ++ tailWord_34416).sum := by decide
  have hdescent : baseEnd_34416 < baseStart_34416 := by decide
  rcases family_descends (prefixWord ++ tailWord_34416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34492 : List Nat := [2, 2, 2, 3, 1, 2, 4, 1, 4]
def baseStart_34492 : Nat := 118140960795 + 34492 * 2 ^ 59
def prefixEnd_34492 : Nat := 4983230072969 + 3 ^ 40 * 34492 * 2
def baseEnd_34492 : Nat := 7871544326659681596169

theorem tailTrace_34492 : CollatzResearch.WordTrace tailWord_34492 prefixEnd_34492 7871544326659681596169 := by
  unfold tailWord_34492
  simp only [CollatzResearch.WordTrace]
  refine ⟨629013295524424804860865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 838684394032566406481153 629013295524424804860865)
  ·
    refine ⟨471759971643318603645649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 629013295524424804860865 471759971643318603645649)
    ·
      refine ⟨353819978732488952734237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 471759971643318603645649 353819978732488952734237)
      ·
        refine ⟨132682492024683357275339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 353819978732488952734237 132682492024683357275339)
        ·
          refine ⟨199023738037025035913009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132682492024683357275339 199023738037025035913009)
          ·
            refine ⟨149267803527768776934757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199023738037025035913009 149267803527768776934757)
            ·
              refine ⟨27987713161456645675267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 149267803527768776934757 27987713161456645675267)
              ·
                refine ⟨41981569742184968512901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27987713161456645675267 41981569742184968512901)
                ·
                  refine ⟨7871544326659681596169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41981569742184968512901 7871544326659681596169)
                  ·
                    rfl

theorem cell21_34492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 1, 4].length) (baseStart_34492 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_34492 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_34492 prefixEnd_34492 := by exact prefixLift 34492
  have htrace : WordTrace (prefixWord ++ tailWord_34492) baseStart_34492 baseEnd_34492 := by
    simpa [prefixWord, tailWord_34492, baseEnd_34492] using wordTrace_append hprefix tailTrace_34492
  have hstable : (prefixWord ++ tailWord_34492).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34492).length < 2 ^ (prefixWord ++ tailWord_34492).sum := by decide
  have hdescent : baseEnd_34492 < baseStart_34492 := by decide
  rcases family_descends (prefixWord ++ tailWord_34492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34503 : List Nat := [1, 1, 4, 1, 1, 1, 4, 1, 7]
def baseStart_34503 : Nat := 118140960795 + 34503 * 2 ^ 59
def prefixEnd_34503 : Nat := 4983230072969 + 3 ^ 40 * 34503 * 2
def baseEnd_34503 : Nat := 7874054676526106912813

theorem tailTrace_34503 : CollatzResearch.WordTrace tailWord_34503 prefixEnd_34503 7874054676526106912813 := by
  unfold tailWord_34503
  simp only [CollatzResearch.WordTrace]
  refine ⟨1258427794008998488372163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 838951862672665658914775 1258427794008998488372163)
  ·
    refine ⟨1887641691013497732558245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1258427794008998488372163 1887641691013497732558245)
    ·
      refine ⟨353932817065030824854671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1887641691013497732558245 353932817065030824854671)
      ·
        refine ⟨530899225597546237282007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 353932817065030824854671 530899225597546237282007)
        ·
          refine ⟨796348838396319355923011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 530899225597546237282007 796348838396319355923011)
          ·
            refine ⟨1194523257594479033884517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 796348838396319355923011 1194523257594479033884517)
            ·
              refine ⟨223973110798964818853347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1194523257594479033884517 223973110798964818853347)
              ·
                refine ⟨335959666198447228280021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 223973110798964818853347 335959666198447228280021)
                ·
                  refine ⟨7874054676526106912813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 335959666198447228280021 7874054676526106912813)
                  ·
                    rfl

theorem cell21_34503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 7].length) (baseStart_34503 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_34503 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_34503 prefixEnd_34503 := by exact prefixLift 34503
  have htrace : WordTrace (prefixWord ++ tailWord_34503) baseStart_34503 baseEnd_34503 := by
    simpa [prefixWord, tailWord_34503, baseEnd_34503] using wordTrace_append hprefix tailTrace_34503
  have hstable : (prefixWord ++ tailWord_34503).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34503).length < 2 ^ (prefixWord ++ tailWord_34503).sum := by decide
  have hdescent : baseEnd_34503 < baseStart_34503 := by decide
  rcases family_descends (prefixWord ++ tailWord_34503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34596 : List Nat := [2, 3, 1, 3, 2, 1, 1, 3, 5]
def baseStart_34596 : Nat := 118140960795 + 34596 * 2 ^ 59
def prefixEnd_34596 : Nat := 4983230072969 + 3 ^ 40 * 34596 * 2
def baseEnd_34596 : Nat := 7895278543578611862623

theorem tailTrace_34596 : CollatzResearch.WordTrace tailWord_34596 prefixEnd_34596 7895278543578611862623 := by
  unfold tailWord_34596
  simp only [CollatzResearch.WordTrace]
  refine ⟨630909891336037685753821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 841213188448050247671761 630909891336037685753821)
  ·
    refine ⟨236591209251014132157683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 630909891336037685753821 236591209251014132157683)
    ·
      refine ⟨354886813876521198236525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236591209251014132157683 354886813876521198236525)
      ·
        refine ⟨133082555203695449338697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 354886813876521198236525 133082555203695449338697)
        ·
          refine ⟨99811916402771587004023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133082555203695449338697 99811916402771587004023)
          ·
            refine ⟨149717874604157380506035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99811916402771587004023 149717874604157380506035)
            ·
              refine ⟨224576811906236070759053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149717874604157380506035 224576811906236070759053)
              ·
                refine ⟨84216304464838526534645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 224576811906236070759053 84216304464838526534645)
                ·
                  refine ⟨7895278543578611862623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 84216304464838526534645 7895278543578611862623)
                  ·
                    rfl

theorem cell21_34596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_34596 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_34596 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_34596 prefixEnd_34596 := by exact prefixLift 34596
  have htrace : WordTrace (prefixWord ++ tailWord_34596) baseStart_34596 baseEnd_34596 := by
    simpa [prefixWord, tailWord_34596, baseEnd_34596] using wordTrace_append hprefix tailTrace_34596
  have hstable : (prefixWord ++ tailWord_34596).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34596).length < 2 ^ (prefixWord ++ tailWord_34596).sum := by decide
  have hdescent : baseEnd_34596 < baseStart_34596 := by decide
  rcases family_descends (prefixWord ++ tailWord_34596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34641 : List Nat := [1, 2, 2, 1, 5, 3, 7]
def baseStart_34641 : Nat := 118140960795 + 34641 * 2 ^ 59
def prefixEnd_34641 : Nat := 4983230072969 + 3 ^ 40 * 34641 * 2
def baseEnd_34641 : Nat := 878394239629837068059

theorem tailTrace_34641 : CollatzResearch.WordTrace tailWord_34641 prefixEnd_34641 878394239629837068059 := by
  unfold tailWord_34641
  simp only [CollatzResearch.WordTrace]
  refine ⟨1263461067509048056895777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 842307378339365371263851 1263461067509048056895777)
  ·
    refine ⟨947595800631786042671833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1263461067509048056895777 947595800631786042671833)
    ·
      refine ⟨710696850473839532003875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 947595800631786042671833 710696850473839532003875)
      ·
        refine ⟨1066045275710759298005813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 710696850473839532003875 1066045275710759298005813)
        ·
          refine ⟨99941744597883684188045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1066045275710759298005813 99941744597883684188045)
          ·
            refine ⟨37478154224206381570517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99941744597883684188045 37478154224206381570517)
            ·
              refine ⟨878394239629837068059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 37478154224206381570517 878394239629837068059)
              ·
                rfl

theorem cell21_34641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 7].length) (baseStart_34641 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_34641 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_34641 prefixEnd_34641 := by exact prefixLift 34641
  have htrace : WordTrace (prefixWord ++ tailWord_34641) baseStart_34641 baseEnd_34641 := by
    simpa [prefixWord, tailWord_34641, baseEnd_34641] using wordTrace_append hprefix tailTrace_34641
  have hstable : (prefixWord ++ tailWord_34641).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34641).length < 2 ^ (prefixWord ++ tailWord_34641).sum := by decide
  have hdescent : baseEnd_34641 < baseStart_34641 := by decide
  rcases family_descends (prefixWord ++ tailWord_34641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34658 : List Nat := [3, 3, 2, 1, 2, 2, 2, 6]
def baseStart_34658 : Nat := 118140960795 + 34658 * 2 ^ 59
def prefixEnd_34658 : Nat := 4983230072969 + 3 ^ 40 * 34658 * 2
def baseEnd_34658 : Nat := 2636475929426760609721

theorem tailTrace_34658 : CollatzResearch.WordTrace tailWord_34658 prefixEnd_34658 2636475929426760609721 := by
  unfold tailWord_34658
  simp only [CollatzResearch.WordTrace]
  refine ⟨316020277111864990066157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 842720738964973306843085 316020277111864990066157)
  ·
    refine ⟨118507603916949371274809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 316020277111864990066157 118507603916949371274809)
    ·
      refine ⟨88880702937712028456107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118507603916949371274809 88880702937712028456107)
      ·
        refine ⟨133321054406568042684161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88880702937712028456107 133321054406568042684161)
        ·
          refine ⟨99990790804926032013121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133321054406568042684161 99990790804926032013121)
          ·
            refine ⟨74993093103694524009841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99990790804926032013121 74993093103694524009841)
            ·
              refine ⟨56244819827770893007381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74993093103694524009841 56244819827770893007381)
              ·
                refine ⟨2636475929426760609721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 56244819827770893007381 2636475929426760609721)
                ·
                  rfl

theorem cell21_34658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 6].length) (baseStart_34658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_34658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_34658 prefixEnd_34658 := by exact prefixLift 34658
  have htrace : WordTrace (prefixWord ++ tailWord_34658) baseStart_34658 baseEnd_34658 := by
    simpa [prefixWord, tailWord_34658, baseEnd_34658] using wordTrace_append hprefix tailTrace_34658
  have hstable : (prefixWord ++ tailWord_34658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34658).length < 2 ^ (prefixWord ++ tailWord_34658).sum := by decide
  have hdescent : baseEnd_34658 < baseStart_34658 := by decide
  rcases family_descends (prefixWord ++ tailWord_34658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34706 : List Nat := [3, 2, 3, 2, 1, 2, 1, 4, 3]
def baseStart_34706 : Nat := 118140960795 + 34706 * 2 ^ 59
def prefixEnd_34706 : Nat := 4983230072969 + 3 ^ 40 * 34706 * 2
def baseEnd_34706 : Nat := 7920382042242865029065

theorem tailTrace_34706 : CollatzResearch.WordTrace tailWord_34706 prefixEnd_34706 7920382042242865029065 := by
  unfold tailWord_34706
  simp only [CollatzResearch.WordTrace]
  refine ⟨316457953068391039502993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 843887874849042772007981 316457953068391039502993)
  ·
    refine ⟨237343464801293279627245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 316457953068391039502993 237343464801293279627245)
    ·
      refine ⟨89003799300484979860217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 237343464801293279627245 89003799300484979860217)
      ·
        refine ⟨66752849475363734895163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89003799300484979860217 66752849475363734895163)
        ·
          refine ⟨100129274213045602342745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66752849475363734895163 100129274213045602342745)
          ·
            refine ⟨75096955659784201757059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100129274213045602342745 75096955659784201757059)
            ·
              refine ⟨112645433489676302635589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75096955659784201757059 112645433489676302635589)
              ·
                refine ⟨21121018779314306744173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 112645433489676302635589 21121018779314306744173)
                ·
                  refine ⟨7920382042242865029065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21121018779314306744173 7920382042242865029065)
                  ·
                    rfl

theorem cell21_34706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 4, 3].length) (baseStart_34706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_34706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_34706 prefixEnd_34706 := by exact prefixLift 34706
  have htrace : WordTrace (prefixWord ++ tailWord_34706) baseStart_34706 baseEnd_34706 := by
    simpa [prefixWord, tailWord_34706, baseEnd_34706] using wordTrace_append hprefix tailTrace_34706
  have hstable : (prefixWord ++ tailWord_34706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34706).length < 2 ^ (prefixWord ++ tailWord_34706).sum := by decide
  have hdescent : baseEnd_34706 < baseStart_34706 := by decide
  rcases family_descends (prefixWord ++ tailWord_34706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34717 : List Nat := [1, 4, 2, 1, 2, 2, 3, 6]
def baseStart_34717 : Nat := 118140960795 + 34717 * 2 ^ 59
def prefixEnd_34717 : Nat := 4983230072969 + 3 ^ 40 * 34717 * 2
def baseEnd_34717 : Nat := 2640964130703096781903

theorem tailTrace_34717 : CollatzResearch.WordTrace tailWord_34717 prefixEnd_34717 2640964130703096781903 := by
  unfold tailWord_34717
  simp only [CollatzResearch.WordTrace]
  refine ⟨1266233015233713036662405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 844155343489142024441603 1266233015233713036662405)
  ·
    refine ⟨237418690356321194374201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1266233015233713036662405 237418690356321194374201)
    ·
      refine ⟨178064017767240895780651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237418690356321194374201 178064017767240895780651)
      ·
        refine ⟨267096026650861343670977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178064017767240895780651 267096026650861343670977)
        ·
          refine ⟨200322019988146007753233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 267096026650861343670977 200322019988146007753233)
          ·
            refine ⟨150241514991109505814925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200322019988146007753233 150241514991109505814925)
            ·
              refine ⟨56340568121666064680597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 150241514991109505814925 56340568121666064680597)
              ·
                refine ⟨2640964130703096781903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 56340568121666064680597 2640964130703096781903)
                ·
                  rfl

theorem cell21_34717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 6].length) (baseStart_34717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_34717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_34717 prefixEnd_34717 := by exact prefixLift 34717
  have htrace : WordTrace (prefixWord ++ tailWord_34717) baseStart_34717 baseEnd_34717 := by
    simpa [prefixWord, tailWord_34717, baseEnd_34717] using wordTrace_append hprefix tailTrace_34717
  have hstable : (prefixWord ++ tailWord_34717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34717).length < 2 ^ (prefixWord ++ tailWord_34717).sum := by decide
  have hdescent : baseEnd_34717 < baseStart_34717 := by decide
  rcases family_descends (prefixWord ++ tailWord_34717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34776 : List Nat := [2, 1, 2, 2, 2, 2, 2, 8]
def baseStart_34776 : Nat := 118140960795 + 34776 * 2 ^ 59
def prefixEnd_34776 : Nat := 4983230072969 + 3 ^ 40 * 34776 * 2
def baseEnd_34776 : Nat := 2645452331979432954085

theorem tailTrace_34776 : CollatzResearch.WordTrace tailWord_34776 prefixEnd_34776 2645452331979432954085 := by
  unfold tailWord_34776
  simp only [CollatzResearch.WordTrace]
  refine ⟨634192461009983056530091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 845589948013310742040121 634192461009983056530091)
  ·
    refine ⟨951288691514974584795137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 634192461009983056530091 951288691514974584795137)
    ·
      refine ⟨713466518636230938596353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 951288691514974584795137 713466518636230938596353)
      ·
        refine ⟨535099888977173203947265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 713466518636230938596353 535099888977173203947265)
        ·
          refine ⟨401324916732879902960449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 535099888977173203947265 401324916732879902960449)
          ·
            refine ⟨300993687549659927220337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 401324916732879902960449 300993687549659927220337)
            ·
              refine ⟨225745265662244945415253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 300993687549659927220337 225745265662244945415253)
              ·
                refine ⟨2645452331979432954085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 225745265662244945415253 2645452331979432954085)
                ·
                  rfl

theorem cell21_34776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 8].length) (baseStart_34776 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_34776 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_34776 prefixEnd_34776 := by exact prefixLift 34776
  have htrace : WordTrace (prefixWord ++ tailWord_34776) baseStart_34776 baseEnd_34776 := by
    simpa [prefixWord, tailWord_34776, baseEnd_34776] using wordTrace_append hprefix tailTrace_34776
  have hstable : (prefixWord ++ tailWord_34776).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34776).length < 2 ^ (prefixWord ++ tailWord_34776).sum := by decide
  have hdescent : baseEnd_34776 < baseStart_34776 := by decide
  rcases family_descends (prefixWord ++ tailWord_34776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34897 : List Nat := [1, 2, 2, 1, 3, 1, 1, 2, 8]
def baseStart_34897 : Nat := 118140960795 + 34897 * 2 ^ 59
def prefixEnd_34897 : Nat := 4983230072969 + 3 ^ 40 * 34897 * 2
def baseEnd_34897 : Nat := 7963970844468977345341

theorem tailTrace_34897 : CollatzResearch.WordTrace tailWord_34897 prefixEnd_34897 7963970844468977345341 := by
  unfold tailWord_34897
  simp only [CollatzResearch.WordTrace]
  refine ⟨1272798154581603778214945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 848532103054402518809963 1272798154581603778214945)
  ·
    refine ⟨954598615936202833661209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1272798154581603778214945 954598615936202833661209)
    ·
      refine ⟨715948961952152125245907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 954598615936202833661209 715948961952152125245907)
      ·
        refine ⟨1073923442928228187868861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 715948961952152125245907 1073923442928228187868861)
        ·
          refine ⟨402721291098085570450823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1073923442928228187868861 402721291098085570450823)
          ·
            refine ⟨604081936647128355676235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 402721291098085570450823 604081936647128355676235)
            ·
              refine ⟨906122904970692533514353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 604081936647128355676235 906122904970692533514353)
              ·
                refine ⟨679592178728019400135765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 906122904970692533514353 679592178728019400135765)
                ·
                  refine ⟨7963970844468977345341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 679592178728019400135765 7963970844468977345341)
                  ·
                    rfl

theorem cell21_34897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 8].length) (baseStart_34897 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_34897 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_34897 prefixEnd_34897 := by exact prefixLift 34897
  have htrace : WordTrace (prefixWord ++ tailWord_34897) baseStart_34897 baseEnd_34897 := by
    simpa [prefixWord, tailWord_34897, baseEnd_34897] using wordTrace_append hprefix tailTrace_34897
  have hstable : (prefixWord ++ tailWord_34897).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34897).length < 2 ^ (prefixWord ++ tailWord_34897).sum := by decide
  have hdescent : baseEnd_34897 < baseStart_34897 := by decide
  rcases family_descends (prefixWord ++ tailWord_34897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34917 : List Nat := [1, 3, 1, 3, 2, 3, 2, 3, 3]
def baseStart_34917 : Nat := 118140960795 + 34917 * 2 ^ 59
def prefixEnd_34917 : Nat := 4983230072969 + 3 ^ 40 * 34917 * 2
def baseEnd_34917 : Nat := 7968535116953387011967

theorem tailTrace_34917 : CollatzResearch.WordTrace tailWord_34917 prefixEnd_34917 7968535116953387011967 := by
  unfold tailWord_34917
  simp only [CollatzResearch.WordTrace]
  refine ⟨1273527614509147193943005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 849018409672764795962003 1273527614509147193943005)
  ·
    refine ⟨477572855440930197728627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1273527614509147193943005 477572855440930197728627)
    ·
      refine ⟨716359283161395296592941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 477572855440930197728627 716359283161395296592941)
      ·
        refine ⟨268634731185523236222353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 716359283161395296592941 268634731185523236222353)
        ·
          refine ⟨201476048389142427166765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 268634731185523236222353 201476048389142427166765)
          ·
            refine ⟨75553518145928410187537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 201476048389142427166765 75553518145928410187537)
            ·
              refine ⟨56665138609446307640653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75553518145928410187537 56665138609446307640653)
              ·
                refine ⟨21249426978542365365245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56665138609446307640653 21249426978542365365245)
                ·
                  refine ⟨7968535116953387011967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21249426978542365365245 7968535116953387011967)
                  ·
                    rfl

theorem cell21_34917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3, 3].length) (baseStart_34917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_34917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_34917 prefixEnd_34917 := by exact prefixLift 34917
  have htrace : WordTrace (prefixWord ++ tailWord_34917) baseStart_34917 baseEnd_34917 := by
    simpa [prefixWord, tailWord_34917, baseEnd_34917] using wordTrace_append hprefix tailTrace_34917
  have hstable : (prefixWord ++ tailWord_34917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34917).length < 2 ^ (prefixWord ++ tailWord_34917).sum := by decide
  have hdescent : baseEnd_34917 < baseStart_34917 := by decide
  rcases family_descends (prefixWord ++ tailWord_34917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34928 : List Nat := [2, 1, 1, 1, 5, 3, 8]
def baseStart_34928 : Nat := 118140960795 + 34928 * 2 ^ 59
def prefixEnd_34928 : Nat := 4983230072969 + 3 ^ 40 * 34928 * 2
def baseEnd_34928 : Nat := 885671718535534703179

theorem tailTrace_34928 : CollatzResearch.WordTrace tailWord_34928 prefixEnd_34928 885671718535534703179 := by
  unfold tailWord_34928
  simp only [CollatzResearch.WordTrace]
  refine ⟨636964408734648036296719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 849285878312864048395625 636964408734648036296719)
  ·
    refine ⟨955446613101972054445079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 636964408734648036296719 955446613101972054445079)
    ·
      refine ⟨1433169919652958081667619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 955446613101972054445079 1433169919652958081667619)
      ·
        refine ⟨2149754879479437122501429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1433169919652958081667619 2149754879479437122501429)
        ·
          refine ⟨201539519951197230234509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2149754879479437122501429 201539519951197230234509)
          ·
            refine ⟨75577319981698961337941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 201539519951197230234509 75577319981698961337941)
            ·
              refine ⟨885671718535534703179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 75577319981698961337941 885671718535534703179)
              ·
                rfl

theorem cell21_34928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 8].length) (baseStart_34928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_34928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_34928 prefixEnd_34928 := by exact prefixLift 34928
  have htrace : WordTrace (prefixWord ++ tailWord_34928) baseStart_34928 baseEnd_34928 := by
    simpa [prefixWord, tailWord_34928, baseEnd_34928] using wordTrace_append hprefix tailTrace_34928
  have hstable : (prefixWord ++ tailWord_34928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34928).length < 2 ^ (prefixWord ++ tailWord_34928).sum := by decide
  have hdescent : baseEnd_34928 < baseStart_34928 := by decide
  rcases family_descends (prefixWord ++ tailWord_34928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34993 : List Nat := [1, 2, 2, 5, 2, 2, 1, 1, 5]
def baseStart_34993 : Nat := 118140960795 + 34993 * 2 ^ 59
def prefixEnd_34993 : Nat := 4983230072969 + 3 ^ 40 * 34993 * 2
def baseEnd_34993 : Nat := 7985879352394143745145

theorem tailTrace_34993 : CollatzResearch.WordTrace tailWord_34993 prefixEnd_34993 7985879352394143745145 := by
  unfold tailWord_34993
  simp only [CollatzResearch.WordTrace]
  refine ⟨1276299562233812173709633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 850866374822541449139755 1276299562233812173709633)
  ·
    refine ⟨957224671675359130282225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1276299562233812173709633 957224671675359130282225)
    ·
      refine ⟨717918503756519347711669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 957224671675359130282225 717918503756519347711669)
      ·
        refine ⟨67304859727173688847969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 717918503756519347711669 67304859727173688847969)
        ·
          refine ⟨50478644795380266635977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67304859727173688847969 50478644795380266635977)
          ·
            refine ⟨37858983596535199976983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50478644795380266635977 37858983596535199976983)
            ·
              refine ⟨56788475394802799965475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37858983596535199976983 56788475394802799965475)
              ·
                refine ⟨85182713092204199948213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56788475394802799965475 85182713092204199948213)
                ·
                  refine ⟨7985879352394143745145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 85182713092204199948213 7985879352394143745145)
                  ·
                    rfl

theorem cell21_34993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 5].length) (baseStart_34993 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_34993 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_34993 prefixEnd_34993 := by exact prefixLift 34993
  have htrace : WordTrace (prefixWord ++ tailWord_34993) baseStart_34993 baseEnd_34993 := by
    simpa [prefixWord, tailWord_34993, baseEnd_34993] using wordTrace_append hprefix tailTrace_34993
  have hstable : (prefixWord ++ tailWord_34993).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34993).length < 2 ^ (prefixWord ++ tailWord_34993).sum := by decide
  have hdescent : baseEnd_34993 < baseStart_34993 := by decide
  rcases family_descends (prefixWord ++ tailWord_34993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34996 : List Nat := [2, 5, 3, 1, 1, 1, 2, 6]
def baseStart_34996 : Nat := 118140960795 + 34996 * 2 ^ 59
def prefixEnd_34996 : Nat := 4983230072969 + 3 ^ 40 * 34996 * 2
def baseEnd_34996 : Nat := 2662187997755601731713

theorem tailTrace_34996 : CollatzResearch.WordTrace tailWord_34996 prefixEnd_34996 2662187997755601731713 := by
  unfold tailWord_34996
  simp only [CollatzResearch.WordTrace]
  refine ⟨638204490611471843034421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 850939320815295790712561 638204490611471843034421)
  ·
    refine ⟨59831670994825485284477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 638204490611471843034421 59831670994825485284477)
    ·
      refine ⟨22436876623059556981679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59831670994825485284477 22436876623059556981679)
      ·
        refine ⟨33655314934589335472519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22436876623059556981679 33655314934589335472519)
        ·
          refine ⟨50482972401884003208779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33655314934589335472519 50482972401884003208779)
          ·
            refine ⟨75724458602826004813169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50482972401884003208779 75724458602826004813169)
            ·
              refine ⟨56793343952119503609877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75724458602826004813169 56793343952119503609877)
              ·
                refine ⟨2662187997755601731713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 56793343952119503609877 2662187997755601731713)
                ·
                  rfl

theorem cell21_34996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 6].length) (baseStart_34996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_34996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_34996 prefixEnd_34996 := by exact prefixLift 34996
  have htrace : WordTrace (prefixWord ++ tailWord_34996) baseStart_34996 baseEnd_34996 := by
    simpa [prefixWord, tailWord_34996, baseEnd_34996] using wordTrace_append hprefix tailTrace_34996
  have hstable : (prefixWord ++ tailWord_34996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34996).length < 2 ^ (prefixWord ++ tailWord_34996).sum := by decide
  have hdescent : baseEnd_34996 < baseStart_34996 := by decide
  rcases family_descends (prefixWord ++ tailWord_34996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35052 : List Nat := [2, 2, 1, 1, 2, 3, 3, 4, 3]
def baseStart_35052 : Nat := 118140960795 + 35052 * 2 ^ 59
def prefixEnd_35052 : Nat := 4983230072969 + 3 ^ 40 * 35052 * 2
def baseEnd_35052 : Nat := 7999343956223152261691

theorem tailTrace_35052 : CollatzResearch.WordTrace tailWord_35052 prefixEnd_35052 7999343956223152261691 := by
  unfold tailWord_35052
  simp only [CollatzResearch.WordTrace]
  refine ⟨639225734510032625053705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 852300979346710166738273 639225734510032625053705)
  ·
    refine ⟨479419300882524468790279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 639225734510032625053705 479419300882524468790279)
    ·
      refine ⟨719128951323786703185419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 479419300882524468790279 719128951323786703185419)
      ·
        refine ⟨1078693426985680054778129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 719128951323786703185419 1078693426985680054778129)
        ·
          refine ⟨809020070239260041083597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1078693426985680054778129 809020070239260041083597)
          ·
            refine ⟨303382526339722515406349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 809020070239260041083597 303382526339722515406349)
            ·
              refine ⟨113768447377395943277381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 303382526339722515406349 113768447377395943277381)
              ·
                refine ⟨21331583883261739364509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 113768447377395943277381 21331583883261739364509)
                ·
                  refine ⟨7999343956223152261691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21331583883261739364509 7999343956223152261691)
                  ·
                    rfl

theorem cell21_35052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 4, 3].length) (baseStart_35052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_35052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_35052 prefixEnd_35052 := by exact prefixLift 35052
  have htrace : WordTrace (prefixWord ++ tailWord_35052) baseStart_35052 baseEnd_35052 := by
    simpa [prefixWord, tailWord_35052, baseEnd_35052] using wordTrace_append hprefix tailTrace_35052
  have hstable : (prefixWord ++ tailWord_35052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35052).length < 2 ^ (prefixWord ++ tailWord_35052).sum := by decide
  have hdescent : baseEnd_35052 < baseStart_35052 := by decide
  rcases family_descends (prefixWord ++ tailWord_35052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35066 : List Nat := [3, 1, 1, 1, 1, 5, 2, 3, 4]
def baseStart_35066 : Nat := 118140960795 + 35066 * 2 ^ 59
def prefixEnd_35066 : Nat := 4983230072969 + 3 ^ 40 * 35066 * 2
def baseEnd_35066 : Nat := 8002538946962239028329

theorem tailTrace_35066 : CollatzResearch.WordTrace tailWord_35066 prefixEnd_35066 8002538946962239028329 := by
  unfold tailWord_35066
  simp only [CollatzResearch.WordTrace]
  refine ⟨319740522742336410279263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 852641393979563760744701 319740522742336410279263)
  ·
    refine ⟨479610784113504615418895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 319740522742336410279263 479610784113504615418895)
    ·
      refine ⟨719416176170256923128343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 479610784113504615418895 719416176170256923128343)
      ·
        refine ⟨1079124264255385384692515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 719416176170256923128343 1079124264255385384692515)
        ·
          refine ⟨1618686396383078077038773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1079124264255385384692515 1618686396383078077038773)
          ·
            refine ⟨151751849660913569722385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1618686396383078077038773 151751849660913569722385)
            ·
              refine ⟨113813887245685177291789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151751849660913569722385 113813887245685177291789)
              ·
                refine ⟨42680207717131941484421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 113813887245685177291789 42680207717131941484421)
                ·
                  refine ⟨8002538946962239028329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42680207717131941484421 8002538946962239028329)
                  ·
                    rfl

theorem cell21_35066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 3, 4].length) (baseStart_35066 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_35066 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_35066 prefixEnd_35066 := by exact prefixLift 35066
  have htrace : WordTrace (prefixWord ++ tailWord_35066) baseStart_35066 baseEnd_35066 := by
    simpa [prefixWord, tailWord_35066, baseEnd_35066] using wordTrace_append hprefix tailTrace_35066
  have hstable : (prefixWord ++ tailWord_35066).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35066).length < 2 ^ (prefixWord ++ tailWord_35066).sum := by decide
  have hdescent : baseEnd_35066 < baseStart_35066 := by decide
  rcases family_descends (prefixWord ++ tailWord_35066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35117 : List Nat := [1, 5, 3, 1, 2, 1, 3, 1, 4]
def baseStart_35117 : Nat := 118140960795 + 35117 * 2 ^ 59
def prefixEnd_35117 : Nat := 4983230072969 + 3 ^ 40 * 35117 * 2
def baseEnd_35117 : Nat := 8014177841797483678225

theorem tailTrace_35117 : CollatzResearch.WordTrace tailWord_35117 prefixEnd_35117 8014177841797483678225 := by
  unfold tailWord_35117
  simp only [CollatzResearch.WordTrace]
  refine ⟨1280822213784581351223605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 853881475856387567482403 1280822213784581351223605)
  ·
    refine ⟨120077082542304501677213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1280822213784581351223605 120077082542304501677213)
    ·
      refine ⟨45028905953364188128955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120077082542304501677213 45028905953364188128955)
      ·
        refine ⟨67543358930046282193433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45028905953364188128955 67543358930046282193433)
        ·
          refine ⟨50657519197534711645075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67543358930046282193433 50657519197534711645075)
          ·
            refine ⟨75986278796302067467613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50657519197534711645075 75986278796302067467613)
            ·
              refine ⟨28494854548613275300355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75986278796302067467613 28494854548613275300355)
              ·
                refine ⟨42742281822919912950533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28494854548613275300355 42742281822919912950533)
                ·
                  refine ⟨8014177841797483678225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42742281822919912950533 8014177841797483678225)
                  ·
                    rfl

theorem cell21_35117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_35117 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_35117 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_35117 prefixEnd_35117 := by exact prefixLift 35117
  have htrace : WordTrace (prefixWord ++ tailWord_35117) baseStart_35117 baseEnd_35117 := by
    simpa [prefixWord, tailWord_35117, baseEnd_35117] using wordTrace_append hprefix tailTrace_35117
  have hstable : (prefixWord ++ tailWord_35117).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35117).length < 2 ^ (prefixWord ++ tailWord_35117).sum := by decide
  have hdescent : baseEnd_35117 < baseStart_35117 := by decide
  rcases family_descends (prefixWord ++ tailWord_35117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35156 : List Nat := [2, 4, 1, 1, 2, 2, 9]
def baseStart_35156 : Nat := 118140960795 + 35156 * 2 ^ 59
def prefixEnd_35156 : Nat := 4983230072969 + 3 ^ 40 * 35156 * 2
def baseEnd_35156 : Nat := 891453130349120280905

theorem tailTrace_35156 : CollatzResearch.WordTrace tailWord_35156 prefixEnd_35156 891453130349120280905 := by
  unfold tailWord_35156
  simp only [CollatzResearch.WordTrace]
  refine ⟨641122330321645505946661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 854829773762194007928881 641122330321645505946661)
  ·
    refine ⟨120210436935308532364999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 641122330321645505946661 120210436935308532364999)
    ·
      refine ⟨180315655402962798547499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120210436935308532364999 180315655402962798547499)
      ·
        refine ⟨270473483104444197821249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180315655402962798547499 270473483104444197821249)
        ·
          refine ⟨202855112328333148365937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 270473483104444197821249 202855112328333148365937)
          ·
            refine ⟨152141334246249861274453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 202855112328333148365937 152141334246249861274453)
            ·
              refine ⟨891453130349120280905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 152141334246249861274453 891453130349120280905)
              ·
                rfl

theorem cell21_35156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 9].length) (baseStart_35156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_35156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_35156 prefixEnd_35156 := by exact prefixLift 35156
  have htrace : WordTrace (prefixWord ++ tailWord_35156) baseStart_35156 baseEnd_35156 := by
    simpa [prefixWord, tailWord_35156, baseEnd_35156] using wordTrace_append hprefix tailTrace_35156
  have hstable : (prefixWord ++ tailWord_35156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35156).length < 2 ^ (prefixWord ++ tailWord_35156).sum := by decide
  have hdescent : baseEnd_35156 < baseStart_35156 := by decide
  rcases family_descends (prefixWord ++ tailWord_35156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35176 : List Nat := [2, 1, 4, 2, 2, 3, 2, 1, 4]
def baseStart_35176 : Nat := 118140960795 + 35176 * 2 ^ 59
def prefixEnd_35176 : Nat := 4983230072969 + 3 ^ 40 * 35176 * 2
def baseEnd_35176 : Nat := 8027642445626492194771

theorem tailTrace_35176 : CollatzResearch.WordTrace tailWord_35176 prefixEnd_35176 8027642445626492194771 := by
  unfold tailWord_35176
  simp only [CollatzResearch.WordTrace]
  refine ⟨641487060285417213810691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 855316080380556285080921 641487060285417213810691)
  ·
    refine ⟨962230590428125820716037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 641487060285417213810691 962230590428125820716037)
    ·
      refine ⟨180418235705273591384257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 962230590428125820716037 180418235705273591384257)
      ·
        refine ⟨135313676778955193538193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180418235705273591384257 135313676778955193538193)
        ·
          refine ⟨101485257584216395153645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135313676778955193538193 101485257584216395153645)
          ·
            refine ⟨38056971594081148182617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101485257584216395153645 38056971594081148182617)
            ·
              refine ⟨28542728695560861136963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38056971594081148182617 28542728695560861136963)
              ·
                refine ⟨42814093043341291705445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28542728695560861136963 42814093043341291705445)
                ·
                  refine ⟨8027642445626492194771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42814093043341291705445 8027642445626492194771)
                  ·
                    rfl

theorem cell21_35176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 1, 4].length) (baseStart_35176 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_35176 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_35176 prefixEnd_35176 := by exact prefixLift 35176
  have htrace : WordTrace (prefixWord ++ tailWord_35176) baseStart_35176 baseEnd_35176 := by
    simpa [prefixWord, tailWord_35176, baseEnd_35176] using wordTrace_append hprefix tailTrace_35176
  have hstable : (prefixWord ++ tailWord_35176).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35176).length < 2 ^ (prefixWord ++ tailWord_35176).sum := by decide
  have hdescent : baseEnd_35176 < baseStart_35176 := by decide
  rcases family_descends (prefixWord ++ tailWord_35176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35204 : List Nat := [2, 3, 2, 1, 1, 2, 2, 5, 3]
def baseStart_35204 : Nat := 118140960795 + 35204 * 2 ^ 59
def prefixEnd_35204 : Nat := 4983230072969 + 3 ^ 40 * 35204 * 2
def baseEnd_35204 : Nat := 8034032427104665728047

theorem tailTrace_35204 : CollatzResearch.WordTrace tailWord_35204 prefixEnd_35204 8034032427104665728047 := by
  unfold tailWord_35204
  simp only [CollatzResearch.WordTrace]
  refine ⟨641997682234697604820333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 855996909646263473093777 641997682234697604820333)
  ·
    refine ⟨240749130838011601807625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 641997682234697604820333 240749130838011601807625)
    ·
      refine ⟨180561848128508701355719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240749130838011601807625 180561848128508701355719)
      ·
        refine ⟨270842772192763052033579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180561848128508701355719 270842772192763052033579)
        ·
          refine ⟨406264158289144578050369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270842772192763052033579 406264158289144578050369)
          ·
            refine ⟨304698118716858433537777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 406264158289144578050369 304698118716858433537777)
            ·
              refine ⟨228523589037643825153333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 304698118716858433537777 228523589037643825153333)
              ·
                refine ⟨21424086472279108608125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 228523589037643825153333 21424086472279108608125)
                ·
                  refine ⟨8034032427104665728047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21424086472279108608125 8034032427104665728047)
                  ·
                    rfl

theorem cell21_35204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 5, 3].length) (baseStart_35204 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_35204 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_35204 prefixEnd_35204 := by exact prefixLift 35204
  have htrace : WordTrace (prefixWord ++ tailWord_35204) baseStart_35204 baseEnd_35204 := by
    simpa [prefixWord, tailWord_35204, baseEnd_35204] using wordTrace_append hprefix tailTrace_35204
  have hstable : (prefixWord ++ tailWord_35204).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35204).length < 2 ^ (prefixWord ++ tailWord_35204).sum := by decide
  have hdescent : baseEnd_35204 < baseStart_35204 := by decide
  rcases family_descends (prefixWord ++ tailWord_35204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35232 : List Nat := [2, 1, 1, 4, 1, 3, 3, 6]
def baseStart_35232 : Nat := 118140960795 + 35232 * 2 ^ 59
def prefixEnd_35232 : Nat := 4983230072969 + 3 ^ 40 * 35232 * 2
def baseEnd_35232 : Nat := 2680140802860946420441

theorem tailTrace_35232 : CollatzResearch.WordTrace tailWord_35232 prefixEnd_35232 2680140802860946420441 := by
  unfold tailWord_35232
  simp only [CollatzResearch.WordTrace]
  refine ⟨642508304183977995829975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 856677738911970661106633 642508304183977995829975)
  ·
    refine ⟨963762456275966993744963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 642508304183977995829975 963762456275966993744963)
    ·
      refine ⟨1445643684413950490617445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 963762456275966993744963 1445643684413950490617445)
      ·
        refine ⟨271058190827615716990771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1445643684413950490617445 271058190827615716990771)
        ·
          refine ⟨406587286241423575486157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271058190827615716990771 406587286241423575486157)
          ·
            refine ⟨152470232340533840807309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 406587286241423575486157 152470232340533840807309)
            ·
              refine ⟨57176337127700190302741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 152470232340533840807309 57176337127700190302741)
              ·
                refine ⟨2680140802860946420441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 57176337127700190302741 2680140802860946420441)
                ·
                  rfl

theorem cell21_35232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 6].length) (baseStart_35232 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_35232 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_35232 prefixEnd_35232 := by exact prefixLift 35232
  have htrace : WordTrace (prefixWord ++ tailWord_35232) baseStart_35232 baseEnd_35232 := by
    simpa [prefixWord, tailWord_35232, baseEnd_35232] using wordTrace_append hprefix tailTrace_35232
  have hstable : (prefixWord ++ tailWord_35232).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35232).length < 2 ^ (prefixWord ++ tailWord_35232).sum := by decide
  have hdescent : baseEnd_35232 < baseStart_35232 := by decide
  rcases family_descends (prefixWord ++ tailWord_35232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35249 : List Nat := [1, 2, 2, 4, 1, 3, 3, 5]
def baseStart_35249 : Nat := 118140960795 + 35249 * 2 ^ 59
def prefixEnd_35249 : Nat := 4983230072969 + 3 ^ 40 * 35249 * 2
def baseEnd_35249 : Nat := 2681434013398195825985

theorem tailTrace_35249 : CollatzResearch.WordTrace tailWord_35249 prefixEnd_35249 2681434013398195825985 := by
  unfold tailWord_35249
  simp only [CollatzResearch.WordTrace]
  refine ⟨1285636649306367895028801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 857091099537578596685867 1285636649306367895028801)
  ·
    refine ⟨964227486979775921271601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1285636649306367895028801 964227486979775921271601)
    ·
      refine ⟨723170615234831940953701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 964227486979775921271601 723170615234831940953701)
      ·
        refine ⟨135594490356530988928819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 723170615234831940953701 135594490356530988928819)
        ·
          refine ⟨203391735534796483393229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135594490356530988928819 203391735534796483393229)
          ·
            refine ⟨76271900825548681272461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 203391735534796483393229 76271900825548681272461)
            ·
              refine ⟨28601962809580755477173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76271900825548681272461 28601962809580755477173)
              ·
                refine ⟨2681434013398195825985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28601962809580755477173 2681434013398195825985)
                ·
                  rfl

theorem cell21_35249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 5].length) (baseStart_35249 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_35249 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_35249 prefixEnd_35249 := by exact prefixLift 35249
  have htrace : WordTrace (prefixWord ++ tailWord_35249) baseStart_35249 baseEnd_35249 := by
    simpa [prefixWord, tailWord_35249, baseEnd_35249] using wordTrace_append hprefix tailTrace_35249
  have hstable : (prefixWord ++ tailWord_35249).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35249).length < 2 ^ (prefixWord ++ tailWord_35249).sum := by decide
  have hdescent : baseEnd_35249 < baseStart_35249 := by decide
  rcases family_descends (prefixWord ++ tailWord_35249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35314 : List Nat := [3, 2, 1, 4, 2, 2, 1, 3, 3]
def baseStart_35314 : Nat := 118140960795 + 35314 * 2 ^ 59
def prefixEnd_35314 : Nat := 4983230072969 + 3 ^ 40 * 35314 * 2
def baseEnd_35314 : Nat := 8059135925768918894489

theorem tailTrace_35314 : CollatzResearch.WordTrace tailWord_35314 prefixEnd_35314 8059135925768918894489 := by
  unfold tailWord_35314
  simp only [CollatzResearch.WordTrace]
  refine ⟨322001848517720999036249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 858671596047255997429997 322001848517720999036249)
  ·
    refine ⟨241501386388290749277187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 322001848517720999036249 241501386388290749277187)
    ·
      refine ⟨362252079582436123915781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241501386388290749277187 362252079582436123915781)
      ·
        refine ⟨67922264921706773234209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 362252079582436123915781 67922264921706773234209)
        ·
          refine ⟨50941698691280079925657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67922264921706773234209 50941698691280079925657)
          ·
            refine ⟨38206274018460059944243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50941698691280079925657 38206274018460059944243)
            ·
              refine ⟨57309411027690089916365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38206274018460059944243 57309411027690089916365)
              ·
                refine ⟨21491029135383783718637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57309411027690089916365 21491029135383783718637)
                ·
                  refine ⟨8059135925768918894489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21491029135383783718637 8059135925768918894489)
                  ·
                    rfl

theorem cell21_35314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 3, 3].length) (baseStart_35314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_35314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_35314 prefixEnd_35314 := by exact prefixLift 35314
  have htrace : WordTrace (prefixWord ++ tailWord_35314) baseStart_35314 baseEnd_35314 := by
    simpa [prefixWord, tailWord_35314, baseEnd_35314] using wordTrace_append hprefix tailTrace_35314
  have hstable : (prefixWord ++ tailWord_35314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35314).length < 2 ^ (prefixWord ++ tailWord_35314).sum := by decide
  have hdescent : baseEnd_35314 < baseStart_35314 := by decide
  rcases family_descends (prefixWord ++ tailWord_35314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35339 : List Nat := [1, 1, 1, 1, 7, 1, 3, 1, 5]
def baseStart_35339 : Nat := 118140960795 + 35339 * 2 ^ 59
def prefixEnd_35339 : Nat := 4983230072969 + 3 ^ 40 * 35339 * 2
def baseEnd_35339 : Nat := 8064841266374430977771

theorem tailTrace_35339 : CollatzResearch.WordTrace tailWord_35339 prefixEnd_35339 8064841266374430977771 := by
  unfold tailWord_35339
  simp only [CollatzResearch.WordTrace]
  refine ⟨1288919218980313265805071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 859279479320208843870047 1288919218980313265805071)
  ·
    refine ⟨1933378828470469898707607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1288919218980313265805071 1933378828470469898707607)
    ·
      refine ⟨2900068242705704848061411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1933378828470469898707607 2900068242705704848061411)
      ·
        refine ⟨4350102364058557272092117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2900068242705704848061411 4350102364058557272092117)
        ·
          refine ⟨101955524157622436064659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 4350102364058557272092117 101955524157622436064659)
          ·
            refine ⟨152933286236433654096989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101955524157622436064659 152933286236433654096989)
            ·
              refine ⟨57349982338662620286371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 152933286236433654096989 57349982338662620286371)
              ·
                refine ⟨86024973507993930429557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57349982338662620286371 86024973507993930429557)
                ·
                  refine ⟨8064841266374430977771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 86024973507993930429557 8064841266374430977771)
                  ·
                    rfl

theorem cell21_35339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 5].length) (baseStart_35339 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_35339 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_35339 prefixEnd_35339 := by exact prefixLift 35339
  have htrace : WordTrace (prefixWord ++ tailWord_35339) baseStart_35339 baseEnd_35339 := by
    simpa [prefixWord, tailWord_35339, baseEnd_35339] using wordTrace_append hprefix tailTrace_35339
  have hstable : (prefixWord ++ tailWord_35339).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35339).length < 2 ^ (prefixWord ++ tailWord_35339).sum := by decide
  have hdescent : baseEnd_35339 < baseStart_35339 := by decide
  rcases family_descends (prefixWord ++ tailWord_35339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35353 : List Nat := [1, 2, 1, 2, 1, 1, 2, 7, 4]
def baseStart_35353 : Nat := 118140960795 + 35353 * 2 ^ 59
def prefixEnd_35353 : Nat := 4983230072969 + 3 ^ 40 * 35353 * 2
def baseEnd_35353 : Nat := 8068036257113517744409

theorem tailTrace_35353 : CollatzResearch.WordTrace tailWord_35353 prefixEnd_35353 8068036257113517744409 := by
  unfold tailWord_35353
  simp only [CollatzResearch.WordTrace]
  refine ⟨1289429840929593656814713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 859619893953062437876475 1289429840929593656814713)
  ·
    refine ⟨967072380697195242611035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1289429840929593656814713 967072380697195242611035)
    ·
      refine ⟨1450608571045792863916553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 967072380697195242611035 1450608571045792863916553)
      ·
        refine ⟨1087956428284344647937415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1450608571045792863916553 1087956428284344647937415)
        ·
          refine ⟨1631934642426516971906123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1087956428284344647937415 1631934642426516971906123)
          ·
            refine ⟨2447901963639775457859185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1631934642426516971906123 2447901963639775457859185)
            ·
              refine ⟨1835926472729831593394389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2447901963639775457859185 1835926472729831593394389)
              ·
                refine ⟨43029526704605427970181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1835926472729831593394389 43029526704605427970181)
                ·
                  refine ⟨8068036257113517744409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43029526704605427970181 8068036257113517744409)
                  ·
                    rfl

theorem cell21_35353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 7, 4].length) (baseStart_35353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_35353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_35353 prefixEnd_35353 := by exact prefixLift 35353
  have htrace : WordTrace (prefixWord ++ tailWord_35353) baseStart_35353 baseEnd_35353 := by
    simpa [prefixWord, tailWord_35353, baseEnd_35353] using wordTrace_append hprefix tailTrace_35353
  have hstable : (prefixWord ++ tailWord_35353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35353).length < 2 ^ (prefixWord ++ tailWord_35353).sum := by decide
  have hdescent : baseEnd_35353 < baseStart_35353 := by decide
  rcases family_descends (prefixWord ++ tailWord_35353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35390 : List Nat := [4, 2, 1, 4, 1, 1, 1, 4, 3]
def baseStart_35390 : Nat := 118140960795 + 35390 * 2 ^ 59
def prefixEnd_35390 : Nat := 4983230072969 + 3 ^ 40 * 35390 * 2
def baseEnd_35390 : Nat := 8076480161209675627667

theorem tailTrace_35390 : CollatzResearch.WordTrace tailWord_35390 prefixEnd_35390 8076480161209675627667 := by
  unfold tailWord_35390
  simp only [CollatzResearch.WordTrace]
  refine ⟨161347417724443621988953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 860519561197032650607749 161347417724443621988953)
  ·
    refine ⟨121010563293332716491715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161347417724443621988953 121010563293332716491715)
    ·
      refine ⟨181515844939999074737573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121010563293332716491715 181515844939999074737573)
      ·
        refine ⟨34034220926249826513295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 181515844939999074737573 34034220926249826513295)
        ·
          refine ⟨51051331389374739769943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34034220926249826513295 51051331389374739769943)
          ·
            refine ⟨76576997084062109654915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51051331389374739769943 76576997084062109654915)
            ·
              refine ⟨114865495626093164482373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76576997084062109654915 114865495626093164482373)
              ·
                refine ⟨21537280429892468340445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 114865495626093164482373 21537280429892468340445)
                ·
                  refine ⟨8076480161209675627667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21537280429892468340445 8076480161209675627667)
                  ·
                    rfl

theorem cell21_35390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_35390 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_35390 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_35390 prefixEnd_35390 := by exact prefixLift 35390
  have htrace : WordTrace (prefixWord ++ tailWord_35390) baseStart_35390 baseEnd_35390 := by
    simpa [prefixWord, tailWord_35390, baseEnd_35390] using wordTrace_append hprefix tailTrace_35390
  have hstable : (prefixWord ++ tailWord_35390).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35390).length < 2 ^ (prefixWord ++ tailWord_35390).sum := by decide
  have hdescent : baseEnd_35390 < baseStart_35390 := by decide
  rcases family_descends (prefixWord ++ tailWord_35390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35491 : List Nat := [1, 1, 1, 4, 1, 1, 2, 7, 3]
def baseStart_35491 : Nat := 118140960795 + 35491 * 2 ^ 59
def prefixEnd_35491 : Nat := 4983230072969 + 3 ^ 40 * 35491 * 2
def baseEnd_35491 : Nat := 8099529737255944444127

theorem tailTrace_35491 : CollatzResearch.WordTrace tailWord_35491 prefixEnd_35491 8099529737255944444127 := by
  unfold tailWord_35491
  simp only [CollatzResearch.WordTrace]
  refine ⟨1294463114429643225338327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 862975409619762150225551 1294463114429643225338327)
  ·
    refine ⟨1941694671644464838007491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1294463114429643225338327 1941694671644464838007491)
    ·
      refine ⟨2912542007466697257011237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1941694671644464838007491 2912542007466697257011237)
      ·
        refine ⟨546101626400005735689607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2912542007466697257011237 546101626400005735689607)
        ·
          refine ⟨819152439600008603534411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 546101626400005735689607 819152439600008603534411)
          ·
            refine ⟨1228728659400012905301617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 819152439600008603534411 1228728659400012905301617)
            ·
              refine ⟨921546494550009678976213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1228728659400012905301617 921546494550009678976213)
              ·
                refine ⟨21598745966015851851005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 921546494550009678976213 21598745966015851851005)
                ·
                  refine ⟨8099529737255944444127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21598745966015851851005 8099529737255944444127)
                  ·
                    rfl

theorem cell21_35491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 7, 3].length) (baseStart_35491 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_35491 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_35491 prefixEnd_35491 := by exact prefixLift 35491
  have htrace : WordTrace (prefixWord ++ tailWord_35491) baseStart_35491 baseEnd_35491 := by
    simpa [prefixWord, tailWord_35491, baseEnd_35491] using wordTrace_append hprefix tailTrace_35491
  have hstable : (prefixWord ++ tailWord_35491).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35491).length < 2 ^ (prefixWord ++ tailWord_35491).sum := by decide
  have hdescent : baseEnd_35491 < baseStart_35491 := by decide
  rcases family_descends (prefixWord ++ tailWord_35491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35519 : List Nat := [1, 1, 2, 2, 2, 4, 1, 8]
def baseStart_35519 : Nat := 118140960795 + 35519 * 2 ^ 59
def prefixEnd_35519 : Nat := 4983230072969 + 3 ^ 40 * 35519 * 2
def baseEnd_35519 : Nat := 2701973239578039325801

theorem tailTrace_35519 : CollatzResearch.WordTrace tailWord_35519 prefixEnd_35519 2701973239578039325801 := by
  unfold tailWord_35519
  simp only [CollatzResearch.WordTrace]
  refine ⟨1295484358328204007357611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 863656238885469338238407 1295484358328204007357611)
  ·
    refine ⟨1943226537492306011036417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1295484358328204007357611 1943226537492306011036417)
    ·
      refine ⟨1457419903119229508277313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1943226537492306011036417 1457419903119229508277313)
      ·
        refine ⟨1093064927339422131207985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1457419903119229508277313 1093064927339422131207985)
        ·
          refine ⟨819798695504566598405989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1093064927339422131207985 819798695504566598405989)
          ·
            refine ⟨153712255407106237201123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 819798695504566598405989 153712255407106237201123)
            ·
              refine ⟨230568383110659355801685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153712255407106237201123 230568383110659355801685)
              ·
                refine ⟨2701973239578039325801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 230568383110659355801685 2701973239578039325801)
                ·
                  rfl

theorem cell21_35519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 8].length) (baseStart_35519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_35519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_35519 prefixEnd_35519 := by exact prefixLift 35519
  have htrace : WordTrace (prefixWord ++ tailWord_35519) baseStart_35519 baseEnd_35519 := by
    simpa [prefixWord, tailWord_35519, baseEnd_35519] using wordTrace_append hprefix tailTrace_35519
  have hstable : (prefixWord ++ tailWord_35519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35519).length < 2 ^ (prefixWord ++ tailWord_35519).sum := by decide
  have hdescent : baseEnd_35519 < baseStart_35519 := by decide
  rcases family_descends (prefixWord ++ tailWord_35519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35581 : List Nat := [1, 4, 1, 1, 1, 1, 3, 5, 4]
def baseStart_35581 : Nat := 118140960795 + 35581 * 2 ^ 59
def prefixEnd_35581 : Nat := 4983230072969 + 3 ^ 40 * 35581 * 2
def baseEnd_35581 : Nat := 8120068963435787943943

theorem tailTrace_35581 : CollatzResearch.WordTrace tailWord_35581 prefixEnd_35581 8120068963435787943943 := by
  unfold tailWord_35581
  simp only [CollatzResearch.WordTrace]
  refine ⟨1297745684103588596114597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 865163789402392397409731 1297745684103588596114597)
  ·
    refine ⟨243327315769422861771487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1297745684103588596114597 243327315769422861771487)
    ·
      refine ⟨364990973654134292657231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 243327315769422861771487 364990973654134292657231)
      ·
        refine ⟨547486460481201438985847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 364990973654134292657231 547486460481201438985847)
        ·
          refine ⟨821229690721802158478771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 547486460481201438985847 821229690721802158478771)
          ·
            refine ⟨1231844536082703237718157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 821229690721802158478771 1231844536082703237718157)
            ·
              refine ⟨461941701031013714144309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1231844536082703237718157 461941701031013714144309)
              ·
                refine ⟨43307034471657535701029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 461941701031013714144309 43307034471657535701029)
                ·
                  refine ⟨8120068963435787943943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43307034471657535701029 8120068963435787943943)
                  ·
                    rfl

theorem cell21_35581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_35581 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_35581 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_35581 prefixEnd_35581 := by exact prefixLift 35581
  have htrace : WordTrace (prefixWord ++ tailWord_35581) baseStart_35581 baseEnd_35581 := by
    simpa [prefixWord, tailWord_35581, baseEnd_35581] using wordTrace_append hprefix tailTrace_35581
  have hstable : (prefixWord ++ tailWord_35581).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35581).length < 2 ^ (prefixWord ++ tailWord_35581).sum := by decide
  have hdescent : baseEnd_35581 < baseStart_35581 := by decide
  rcases family_descends (prefixWord ++ tailWord_35581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35646 : List Nat := [4, 2, 1, 2, 3, 2, 2, 5]
def baseStart_35646 : Nat := 118140960795 + 35646 * 2 ^ 59
def prefixEnd_35646 : Nat := 4983230072969 + 3 ^ 40 * 35646 * 2
def baseEnd_35646 : Nat := 2711634283003373120159

theorem tailTrace_35646 : CollatzResearch.WordTrace tailWord_35646 prefixEnd_35646 2711634283003373120159 := by
  unfold tailWord_35646
  simp only [CollatzResearch.WordTrace]
  refine ⟨162514553608513087153849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 866744285912069798153861 162514553608513087153849)
  ·
    refine ⟨121885915206384815365387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 162514553608513087153849 121885915206384815365387)
    ·
      refine ⟨182828872809577223048081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121885915206384815365387 182828872809577223048081)
      ·
        refine ⟨137121654607182917286061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182828872809577223048081 137121654607182917286061)
        ·
          refine ⟨51420620477693593982273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137121654607182917286061 51420620477693593982273)
          ·
            refine ⟨38565465358270195486705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51420620477693593982273 38565465358270195486705)
            ·
              refine ⟨28924099018702646615029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38565465358270195486705 28924099018702646615029)
              ·
                refine ⟨2711634283003373120159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28924099018702646615029 2711634283003373120159)
                ·
                  rfl

theorem cell21_35646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 5].length) (baseStart_35646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_35646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_35646 prefixEnd_35646 := by exact prefixLift 35646
  have htrace : WordTrace (prefixWord ++ tailWord_35646) baseStart_35646 baseEnd_35646 := by
    simpa [prefixWord, tailWord_35646, baseEnd_35646] using wordTrace_append hprefix tailTrace_35646
  have hstable : (prefixWord ++ tailWord_35646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35646).length < 2 ^ (prefixWord ++ tailWord_35646).sum := by decide
  have hdescent : baseEnd_35646 < baseStart_35646 := by decide
  rcases family_descends (prefixWord ++ tailWord_35646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35660 : List Nat := [2, 2, 1, 3, 3, 1, 3, 3, 3]
def baseStart_35660 : Nat := 118140960795 + 35660 * 2 ^ 59
def prefixEnd_35660 : Nat := 4983230072969 + 3 ^ 40 * 35660 * 2
def baseEnd_35660 : Nat := 8138097839749206127115

theorem tailTrace_35660 : CollatzResearch.WordTrace tailWord_35660 prefixEnd_35660 8138097839749206127115 := by
  unfold tailWord_35660
  simp only [CollatzResearch.WordTrace]
  refine ⟨650313525408692544120217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 867084700544923392160289 650313525408692544120217)
  ·
    refine ⟨487735144056519408090163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 650313525408692544120217 487735144056519408090163)
    ·
      refine ⟨731602716084779112135245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 487735144056519408090163 731602716084779112135245)
      ·
        refine ⟨274351018531792167050717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 731602716084779112135245 274351018531792167050717)
        ·
          refine ⟨102881631949422062644019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 274351018531792167050717 102881631949422062644019)
          ·
            refine ⟨154322447924133093966029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102881631949422062644019 154322447924133093966029)
            ·
              refine ⟨57870917971549910237261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 154322447924133093966029 57870917971549910237261)
              ·
                refine ⟨21701594239331216338973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57870917971549910237261 21701594239331216338973)
                ·
                  refine ⟨8138097839749206127115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21701594239331216338973 8138097839749206127115)
                  ·
                    rfl

theorem cell21_35660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 3, 3].length) (baseStart_35660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_35660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_35660 prefixEnd_35660 := by exact prefixLift 35660
  have htrace : WordTrace (prefixWord ++ tailWord_35660) baseStart_35660 baseEnd_35660 := by
    simpa [prefixWord, tailWord_35660, baseEnd_35660] using wordTrace_append hprefix tailTrace_35660
  have hstable : (prefixWord ++ tailWord_35660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35660).length < 2 ^ (prefixWord ++ tailWord_35660).sum := by decide
  have hdescent : baseEnd_35660 < baseStart_35660 := by decide
  rcases family_descends (prefixWord ++ tailWord_35660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35671 : List Nat := [1, 1, 3, 2, 4, 1, 9]
def baseStart_35671 : Nat := 118140960795 + 35671 * 2 ^ 59
def prefixEnd_35671 : Nat := 4983230072969 + 3 ^ 40 * 35671 * 2
def baseEnd_35671 : Nat := 904512021068403493751

theorem tailTrace_35671 : CollatzResearch.WordTrace tailWord_35671 prefixEnd_35671 904512021068403493751 := by
  unfold tailWord_35671
  simp only [CollatzResearch.WordTrace]
  refine ⟨1301028253777533966890867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 867352169185022644593911 1301028253777533966890867)
  ·
    refine ⟨1951542380666300950336301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1301028253777533966890867 1951542380666300950336301)
    ·
      refine ⟨731828392749862856376113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1951542380666300950336301 731828392749862856376113)
      ·
        refine ⟨548871294562397142282085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 731828392749862856376113 548871294562397142282085)
        ·
          refine ⟨102913367730449464177891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 548871294562397142282085 102913367730449464177891)
          ·
            refine ⟨154370051595674196266837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102913367730449464177891 154370051595674196266837)
            ·
              refine ⟨904512021068403493751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 154370051595674196266837 904512021068403493751)
              ·
                rfl

theorem cell21_35671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 9].length) (baseStart_35671 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_35671 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_35671 prefixEnd_35671 := by exact prefixLift 35671
  have htrace : WordTrace (prefixWord ++ tailWord_35671) baseStart_35671 baseEnd_35671 := by
    simpa [prefixWord, tailWord_35671, baseEnd_35671] using wordTrace_append hprefix tailTrace_35671
  have hstable : (prefixWord ++ tailWord_35671).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35671).length < 2 ^ (prefixWord ++ tailWord_35671).sum := by decide
  have hdescent : baseEnd_35671 < baseStart_35671 := by decide
  rcases family_descends (prefixWord ++ tailWord_35671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35688 : List Nat := [2, 1, 4, 2, 1, 3, 2, 6]
def baseStart_35688 : Nat := 118140960795 + 35688 * 2 ^ 59
def prefixEnd_35688 : Nat := 4983230072969 + 3 ^ 40 * 35688 * 2
def baseEnd_35688 : Nat := 2714829273742459886797

theorem tailTrace_35688 : CollatzResearch.WordTrace tailWord_35688 prefixEnd_35688 2714829273742459886797 := by
  unfold tailWord_35688
  simp only [CollatzResearch.WordTrace]
  refine ⟨650824147357972935129859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 867765529810630580173145 650824147357972935129859)
  ·
    refine ⟨976236221036959402694789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 650824147357972935129859 976236221036959402694789)
    ·
      refine ⟨183044291444429888005273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 976236221036959402694789 183044291444429888005273)
      ·
        refine ⟨137283218583322416003955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183044291444429888005273 137283218583322416003955)
        ·
          refine ⟨205924827874983624005933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137283218583322416003955 205924827874983624005933)
          ·
            refine ⟨77221810453118859002225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 205924827874983624005933 77221810453118859002225)
            ·
              refine ⟨57916357839839144251669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77221810453118859002225 57916357839839144251669)
              ·
                refine ⟨2714829273742459886797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 57916357839839144251669 2714829273742459886797)
                ·
                  rfl

theorem cell21_35688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 6].length) (baseStart_35688 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_35688 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_35688 prefixEnd_35688 := by exact prefixLift 35688
  have htrace : WordTrace (prefixWord ++ tailWord_35688) baseStart_35688 baseEnd_35688 := by
    simpa [prefixWord, tailWord_35688, baseEnd_35688] using wordTrace_append hprefix tailTrace_35688
  have hstable : (prefixWord ++ tailWord_35688).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35688).length < 2 ^ (prefixWord ++ tailWord_35688).sum := by decide
  have hdescent : baseEnd_35688 < baseStart_35688 := by decide
  rcases family_descends (prefixWord ++ tailWord_35688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35733 : List Nat := [1, 3, 2, 1, 1, 4, 1, 4, 4]
def baseStart_35733 : Nat := 118140960795 + 35733 * 2 ^ 59
def prefixEnd_35733 : Nat := 4983230072969 + 3 ^ 40 * 35733 * 2
def baseEnd_35733 : Nat := 8154757434317301410299

theorem tailTrace_35733 : CollatzResearch.WordTrace tailWord_35733 prefixEnd_35733 8154757434317301410299 := by
  unfold tailWord_35733
  simp only [CollatzResearch.WordTrace]
  refine ⟨1303289579552918555647853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 868859719701945703765235 1303289579552918555647853)
  ·
    refine ⟨488733592332344458367945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1303289579552918555647853 488733592332344458367945)
    ·
      refine ⟨366550194249258343775959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 488733592332344458367945 366550194249258343775959)
      ·
        refine ⟨549825291373887515663939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 366550194249258343775959 549825291373887515663939)
        ·
          refine ⟨824737937060831273495909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 549825291373887515663939 824737937060831273495909)
          ·
            refine ⟨154638363198905863780483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 824737937060831273495909 154638363198905863780483)
            ·
              refine ⟨231957544798358795670725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154638363198905863780483 231957544798358795670725)
              ·
                refine ⟨43492039649692274188261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 231957544798358795670725 43492039649692274188261)
                ·
                  refine ⟨8154757434317301410299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43492039649692274188261 8154757434317301410299)
                  ·
                    rfl

theorem cell21_35733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 4, 4].length) (baseStart_35733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_35733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_35733 prefixEnd_35733 := by exact prefixLift 35733
  have htrace : WordTrace (prefixWord ++ tailWord_35733) baseStart_35733 baseEnd_35733 := by
    simpa [prefixWord, tailWord_35733, baseEnd_35733] using wordTrace_append hprefix tailTrace_35733
  have hstable : (prefixWord ++ tailWord_35733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35733).length < 2 ^ (prefixWord ++ tailWord_35733).sum := by decide
  have hdescent : baseEnd_35733 < baseStart_35733 := by decide
  rcases family_descends (prefixWord ++ tailWord_35733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35747 : List Nat := [1, 1, 1, 4, 1, 2, 5, 6]
def baseStart_35747 : Nat := 118140960795 + 35747 * 2 ^ 59
def prefixEnd_35747 : Nat := 4983230072969 + 3 ^ 40 * 35747 * 2
def baseEnd_35747 : Nat := 2719317475018796058979

theorem tailTrace_35747 : CollatzResearch.WordTrace tailWord_35747 prefixEnd_35747 2719317475018796058979 := by
  unfold tailWord_35747
  simp only [CollatzResearch.WordTrace]
  refine ⟨1303800201502198946657495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 869200134334799297771663 1303800201502198946657495)
  ·
    refine ⟨1955700302253298419986243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1303800201502198946657495 1955700302253298419986243)
    ·
      refine ⟨2933550453379947629979365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1955700302253298419986243 2933550453379947629979365)
      ·
        refine ⟨550040710008740180621131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2933550453379947629979365 550040710008740180621131)
        ·
          refine ⟨825061065013110270931697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 550040710008740180621131 825061065013110270931697)
          ·
            refine ⟨618795798759832703198773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 825061065013110270931697 618795798759832703198773)
            ·
              refine ⟨58012106133734315924885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 618795798759832703198773 58012106133734315924885)
              ·
                refine ⟨2719317475018796058979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58012106133734315924885 2719317475018796058979)
                ·
                  rfl

theorem cell21_35747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 6].length) (baseStart_35747 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_35747 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_35747 prefixEnd_35747 := by exact prefixLift 35747
  have htrace : WordTrace (prefixWord ++ tailWord_35747) baseStart_35747 baseEnd_35747 := by
    simpa [prefixWord, tailWord_35747, baseEnd_35747] using wordTrace_append hprefix tailTrace_35747
  have hstable : (prefixWord ++ tailWord_35747).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35747).length < 2 ^ (prefixWord ++ tailWord_35747).sum := by decide
  have hdescent : baseEnd_35747 < baseStart_35747 := by decide
  rcases family_descends (prefixWord ++ tailWord_35747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35823 : List Nat := [1, 1, 2, 1, 4, 4, 1, 7]
def baseStart_35823 : Nat := 118140960795 + 35823 * 2 ^ 59
def prefixEnd_35823 : Nat := 4983230072969 + 3 ^ 40 * 35823 * 2
def baseEnd_35823 : Nat := 2725098886832381636705

theorem tailTrace_35823 : CollatzResearch.WordTrace tailWord_35823 prefixEnd_35823 2725098886832381636705 := by
  unfold tailWord_35823
  simp only [CollatzResearch.WordTrace]
  refine ⟨1306572149226863926424123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 871048099484575950949415 1306572149226863926424123)
  ·
    refine ⟨1959858223840295889636185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1306572149226863926424123 1959858223840295889636185)
    ·
      refine ⟨1469893667880221917227139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1959858223840295889636185 1469893667880221917227139)
      ·
        refine ⟨2204840501820332875840709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1469893667880221917227139 2204840501820332875840709)
        ·
          refine ⟨413407594091312414220133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2204840501820332875840709 413407594091312414220133)
          ·
            refine ⟨77513923892121077666275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 413407594091312414220133 77513923892121077666275)
            ·
              refine ⟨116270885838181616499413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77513923892121077666275 116270885838181616499413)
              ·
                refine ⟨2725098886832381636705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 116270885838181616499413 2725098886832381636705)
                ·
                  rfl

theorem cell21_35823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 7].length) (baseStart_35823 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_35823 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_35823 prefixEnd_35823 := by exact prefixLift 35823
  have htrace : WordTrace (prefixWord ++ tailWord_35823) baseStart_35823 baseEnd_35823 := by
    simpa [prefixWord, tailWord_35823, baseEnd_35823] using wordTrace_append hprefix tailTrace_35823
  have hstable : (prefixWord ++ tailWord_35823).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35823).length < 2 ^ (prefixWord ++ tailWord_35823).sum := by decide
  have hdescent : baseEnd_35823 < baseStart_35823 := by decide
  rcases family_descends (prefixWord ++ tailWord_35823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35902 : List Nat := [4, 2, 1, 3, 1, 1, 1, 4, 4]
def baseStart_35902 : Nat := 118140960795 + 35902 * 2 ^ 59
def prefixEnd_35902 : Nat := 4983230072969 + 3 ^ 40 * 35902 * 2
def baseEnd_35902 : Nat := 8193325536810563093287

theorem tailTrace_35902 : CollatzResearch.WordTrace tailWord_35902 prefixEnd_35902 8193325536810563093287 := by
  unfold tailWord_35902
  simp only [CollatzResearch.WordTrace]
  refine ⟨163681689492582552318745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 872969010627106945699973 163681689492582552318745)
  ·
    refine ⟨122761267119436914239059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163681689492582552318745 122761267119436914239059)
    ·
      refine ⟨184141900679155371358589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122761267119436914239059 184141900679155371358589)
      ·
        refine ⟨69053212754683264259471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 184141900679155371358589 69053212754683264259471)
        ·
          refine ⟨103579819132024896389207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69053212754683264259471 103579819132024896389207)
          ·
            refine ⟨155369728698037344583811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103579819132024896389207 155369728698037344583811)
            ·
              refine ⟨233054593047056016875717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155369728698037344583811 233054593047056016875717)
              ·
                refine ⟨43697736196323003164197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 233054593047056016875717 43697736196323003164197)
                ·
                  refine ⟨8193325536810563093287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43697736196323003164197 8193325536810563093287)
                  ·
                    rfl

theorem cell21_35902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_35902 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_35902 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_35902 prefixEnd_35902 := by exact prefixLift 35902
  have htrace : WordTrace (prefixWord ++ tailWord_35902) baseStart_35902 baseEnd_35902 := by
    simpa [prefixWord, tailWord_35902, baseEnd_35902] using wordTrace_append hprefix tailTrace_35902
  have hstable : (prefixWord ++ tailWord_35902).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35902).length < 2 ^ (prefixWord ++ tailWord_35902).sum := by decide
  have hdescent : baseEnd_35902 < baseStart_35902 := by decide
  rcases family_descends (prefixWord ++ tailWord_35902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35961 : List Nat := [1, 2, 1, 3, 5, 1, 1, 1, 6]
def baseStart_35961 : Nat := 118140960795 + 35961 * 2 ^ 59
def prefixEnd_35961 : Nat := 4983230072969 + 3 ^ 40 * 35961 * 2
def baseEnd_35961 : Nat := 8206790140639571609833

theorem tailTrace_35961 : CollatzResearch.WordTrace tailWord_35961 prefixEnd_35961 8206790140639571609833 := by
  unfold tailWord_35961
  simp only [CollatzResearch.WordTrace]
  refine ⟨1311605422726913494947737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 874403615151275663298491 1311605422726913494947737)
  ·
    refine ⟨983704067045185121210803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1311605422726913494947737 983704067045185121210803)
    ·
      refine ⟨1475556100567777681816205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 983704067045185121210803 1475556100567777681816205)
      ·
        refine ⟨553333537712916630681077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1475556100567777681816205 553333537712916630681077)
        ·
          refine ⟨51875019160585934126351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 553333537712916630681077 51875019160585934126351)
          ·
            refine ⟨77812528740878901189527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51875019160585934126351 77812528740878901189527)
            ·
              refine ⟨116718793111318351784291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77812528740878901189527 116718793111318351784291)
              ·
                refine ⟨175078189666977527676437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116718793111318351784291 175078189666977527676437)
                ·
                  refine ⟨8206790140639571609833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 175078189666977527676437 8206790140639571609833)
                  ·
                    rfl

theorem cell21_35961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 6].length) (baseStart_35961 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_35961 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_35961 prefixEnd_35961 := by exact prefixLift 35961
  have htrace : WordTrace (prefixWord ++ tailWord_35961) baseStart_35961 baseEnd_35961 := by
    simpa [prefixWord, tailWord_35961, baseEnd_35961] using wordTrace_append hprefix tailTrace_35961
  have hstable : (prefixWord ++ tailWord_35961).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35961).length < 2 ^ (prefixWord ++ tailWord_35961).sum := by decide
  have hdescent : baseEnd_35961 < baseStart_35961 := by decide
  rcases family_descends (prefixWord ++ tailWord_35961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35978 : List Nat := [3, 1, 2, 3, 1, 1, 5, 1, 4]
def baseStart_35978 : Nat := 118140960795 + 35978 * 2 ^ 59
def prefixEnd_35978 : Nat := 4983230072969 + 3 ^ 40 * 35978 * 2
def baseEnd_35978 : Nat := 8210669772251319826465

theorem tailTrace_35978 : CollatzResearch.WordTrace tailWord_35978 prefixEnd_35978 8210669772251319826465 := by
  unfold tailWord_35978
  simp only [CollatzResearch.WordTrace]
  refine ⟨328056365916331349579147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 874816975776883598877725 328056365916331349579147)
  ·
    refine ⟨492084548874497024368721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 328056365916331349579147 492084548874497024368721)
    ·
      refine ⟨369063411655872768276541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 492084548874497024368721 369063411655872768276541)
      ·
        refine ⟨138398779370952288103703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 369063411655872768276541 138398779370952288103703)
        ·
          refine ⟨207598169056428432155555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138398779370952288103703 207598169056428432155555)
          ·
            refine ⟨311397253584642648233333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207598169056428432155555 311397253584642648233333)
            ·
              refine ⟨29193492523560248271875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 311397253584642648233333 29193492523560248271875)
              ·
                refine ⟨43790238785340372407813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29193492523560248271875 43790238785340372407813)
                ·
                  refine ⟨8210669772251319826465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43790238785340372407813 8210669772251319826465)
                  ·
                    rfl

theorem cell21_35978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 1, 4].length) (baseStart_35978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_35978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_35978 prefixEnd_35978 := by exact prefixLift 35978
  have htrace : WordTrace (prefixWord ++ tailWord_35978) baseStart_35978 baseEnd_35978 := by
    simpa [prefixWord, tailWord_35978, baseEnd_35978] using wordTrace_append hprefix tailTrace_35978
  have hstable : (prefixWord ++ tailWord_35978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35978).length < 2 ^ (prefixWord ++ tailWord_35978).sum := by decide
  have hdescent : baseEnd_35978 < baseStart_35978 := by decide
  rcases family_descends (prefixWord ++ tailWord_35978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35989 : List Nat := [1, 3, 2, 1, 1, 1, 2, 3, 7]
def baseStart_35989 : Nat := 118140960795 + 35989 * 2 ^ 59
def prefixEnd_35989 : Nat := 4983230072969 + 3 ^ 40 * 35989 * 2
def baseEnd_35989 : Nat := 8213180122117745143109

theorem tailTrace_35989 : CollatzResearch.WordTrace tailWord_35989 prefixEnd_35989 8213180122117745143109 := by
  unfold tailWord_35989
  simp only [CollatzResearch.WordTrace]
  refine ⟨1312626666625474276967021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 875084444416982851311347 1312626666625474276967021)
  ·
    refine ⟨492234999984552853862633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1312626666625474276967021 492234999984552853862633)
    ·
      refine ⟨369176249988414640396975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 492234999984552853862633 369176249988414640396975)
      ·
        refine ⟨553764374982621960595463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 369176249988414640396975 553764374982621960595463)
        ·
          refine ⟨830646562473932940893195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 553764374982621960595463 830646562473932940893195)
          ·
            refine ⟨1245969843710899411339793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 830646562473932940893195 1245969843710899411339793)
            ·
              refine ⟨934477382783174558504845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1245969843710899411339793 934477382783174558504845)
              ·
                refine ⟨350429018543690459439317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 934477382783174558504845 350429018543690459439317)
                ·
                  refine ⟨8213180122117745143109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 350429018543690459439317 8213180122117745143109)
                  ·
                    rfl

theorem cell21_35989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 7].length) (baseStart_35989 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_35989 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_35989 prefixEnd_35989 := by exact prefixLift 35989
  have htrace : WordTrace (prefixWord ++ tailWord_35989) baseStart_35989 baseEnd_35989 := by
    simpa [prefixWord, tailWord_35989, baseEnd_35989] using wordTrace_append hprefix tailTrace_35989
  have hstable : (prefixWord ++ tailWord_35989).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35989).length < 2 ^ (prefixWord ++ tailWord_35989).sum := by decide
  have hdescent : baseEnd_35989 < baseStart_35989 := by decide
  rcases family_descends (prefixWord ++ tailWord_35989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35992 : List Nat := [2, 1, 2, 4, 2, 1, 4, 5]
def baseStart_35992 : Nat := 118140960795 + 35992 * 2 ^ 59
def prefixEnd_35992 : Nat := 4983230072969 + 3 ^ 40 * 35992 * 2
def baseEnd_35992 : Nat := 2737954920996802197701

theorem tailTrace_35992 : CollatzResearch.WordTrace tailWord_35992 prefixEnd_35992 2737954920996802197701 := by
  unfold tailWord_35992
  simp only [CollatzResearch.WordTrace]
  refine ⟨656368042807302894663115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 875157390409737192884153 656368042807302894663115)
  ·
    refine ⟨984552064210954341994673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 656368042807302894663115 984552064210954341994673)
    ·
      refine ⟨738414048158215756496005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 984552064210954341994673 738414048158215756496005)
      ·
        refine ⟨138452634029665454343001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 738414048158215756496005 138452634029665454343001)
        ·
          refine ⟨103839475522249090757251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138452634029665454343001 103839475522249090757251)
          ·
            refine ⟨155759213283373636135877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103839475522249090757251 155759213283373636135877)
            ·
              refine ⟨29204852490632556775477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 155759213283373636135877 29204852490632556775477)
              ·
                refine ⟨2737954920996802197701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29204852490632556775477 2737954920996802197701)
                ·
                  rfl

theorem cell21_35992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 5].length) (baseStart_35992 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_35992 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_35992 prefixEnd_35992 := by exact prefixLift 35992
  have htrace : WordTrace (prefixWord ++ tailWord_35992) baseStart_35992 baseEnd_35992 := by
    simpa [prefixWord, tailWord_35992, baseEnd_35992] using wordTrace_append hprefix tailTrace_35992
  have hstable : (prefixWord ++ tailWord_35992).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35992).length < 2 ^ (prefixWord ++ tailWord_35992).sum := by decide
  have hdescent : baseEnd_35992 < baseStart_35992 := by decide
  rcases family_descends (prefixWord ++ tailWord_35992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36127 : List Nat := [1, 1, 2, 4, 4, 1, 8]
def baseStart_36127 : Nat := 118140960795 + 36127 * 2 ^ 59
def prefixEnd_36127 : Nat := 4983230072969 + 3 ^ 40 * 36127 * 2
def baseEnd_36127 : Nat := 916074844695574649203

theorem tailTrace_36127 : CollatzResearch.WordTrace tailWord_36127 prefixEnd_36127 916074844695574649203 := by
  unfold tailWord_36127
  simp only [CollatzResearch.WordTrace]
  refine ⟨1317659940125523845490635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 878439960083682563660423 1317659940125523845490635)
  ·
    refine ⟨1976489910188285768235953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1317659940125523845490635 1976489910188285768235953)
    ·
      refine ⟨1482367432641214326176965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1976489910188285768235953 1482367432641214326176965)
      ·
        refine ⟨277943893620227686158181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1482367432641214326176965 277943893620227686158181)
        ·
          refine ⟨52114480053792691154659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 277943893620227686158181 52114480053792691154659)
          ·
            refine ⟨78171720080689036731989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52114480053792691154659 78171720080689036731989)
            ·
              refine ⟨916074844695574649203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 78171720080689036731989 916074844695574649203)
              ·
                rfl

theorem cell21_36127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 8].length) (baseStart_36127 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_36127 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_36127 prefixEnd_36127 := by exact prefixLift 36127
  have htrace : WordTrace (prefixWord ++ tailWord_36127) baseStart_36127 baseEnd_36127 := by
    simpa [prefixWord, tailWord_36127, baseEnd_36127] using wordTrace_append hprefix tailTrace_36127
  have hstable : (prefixWord ++ tailWord_36127).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36127).length < 2 ^ (prefixWord ++ tailWord_36127).sum := by decide
  have hdescent : baseEnd_36127 < baseStart_36127 := by decide
  rcases family_descends (prefixWord ++ tailWord_36127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36158 : List Nat := [4, 2, 1, 2, 1, 1, 1, 4, 5]
def baseStart_36158 : Nat := 118140960795 + 36158 * 2 ^ 59
def prefixEnd_36158 : Nat := 4983230072969 + 3 ^ 40 * 36158 * 2
def baseEnd_36158 : Nat := 8251748224611006826097

theorem tailTrace_36158 : CollatzResearch.WordTrace tailWord_36158 prefixEnd_36158 8251748224611006826097 := by
  unfold tailWord_36158
  simp only [CollatzResearch.WordTrace]
  refine ⟨164848825376652017483641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 879193735342144093246085 164848825376652017483641)
  ·
    refine ⟨123636619032489013112731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164848825376652017483641 123636619032489013112731)
    ·
      refine ⟨185454928548733519669097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123636619032489013112731 185454928548733519669097)
      ·
        refine ⟨139091196411550139751823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185454928548733519669097 139091196411550139751823)
        ·
          refine ⟨208636794617325209627735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139091196411550139751823 208636794617325209627735)
          ·
            refine ⟨312955191925987814441603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208636794617325209627735 312955191925987814441603)
            ·
              refine ⟨469432787888981721662405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 312955191925987814441603 469432787888981721662405)
              ·
                refine ⟨88018647729184072811701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 469432787888981721662405 88018647729184072811701)
                ·
                  refine ⟨8251748224611006826097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 88018647729184072811701 8251748224611006826097)
                  ·
                    rfl

theorem cell21_36158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_36158 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_36158 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_36158 prefixEnd_36158 := by exact prefixLift 36158
  have htrace : WordTrace (prefixWord ++ tailWord_36158) baseStart_36158 baseEnd_36158 := by
    simpa [prefixWord, tailWord_36158, baseEnd_36158] using wordTrace_append hprefix tailTrace_36158
  have hstable : (prefixWord ++ tailWord_36158).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36158).length < 2 ^ (prefixWord ++ tailWord_36158).sum := by decide
  have hdescent : baseEnd_36158 < baseStart_36158 := by decide
  rcases family_descends (prefixWord ++ tailWord_36158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36161 : List Nat := [1, 2, 5, 2, 1, 3, 2, 5]
def baseStart_36161 : Nat := 118140960795 + 36161 * 2 ^ 59
def prefixEnd_36161 : Nat := 4983230072969 + 3 ^ 40 * 36161 * 2
def baseEnd_36161 : Nat := 2750810955161222758697

theorem tailTrace_36161 : CollatzResearch.WordTrace tailWord_36161 prefixEnd_36161 2750810955161222758697 := by
  unfold tailWord_36161
  simp only [CollatzResearch.WordTrace]
  refine ⟨1318900022002347652228337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 879266681334898434818891 1318900022002347652228337)
  ·
    refine ⟨989175016501760739171253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1318900022002347652228337 989175016501760739171253)
    ·
      refine ⟨92735157797040069297305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 989175016501760739171253 92735157797040069297305)
      ·
        refine ⟨69551368347780051972979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92735157797040069297305 69551368347780051972979)
        ·
          refine ⟨104327052521670077959469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69551368347780051972979 104327052521670077959469)
          ·
            refine ⟨39122644695626279234801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104327052521670077959469 39122644695626279234801)
            ·
              refine ⟨29341983521719709426101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39122644695626279234801 29341983521719709426101)
              ·
                refine ⟨2750810955161222758697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29341983521719709426101 2750810955161222758697)
                ·
                  rfl

theorem cell21_36161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 5].length) (baseStart_36161 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_36161 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_36161 prefixEnd_36161 := by exact prefixLift 36161
  have htrace : WordTrace (prefixWord ++ tailWord_36161) baseStart_36161 baseEnd_36161 := by
    simpa [prefixWord, tailWord_36161, baseEnd_36161] using wordTrace_append hprefix tailTrace_36161
  have hstable : (prefixWord ++ tailWord_36161).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36161).length < 2 ^ (prefixWord ++ tailWord_36161).sum := by decide
  have hdescent : baseEnd_36161 < baseStart_36161 := by decide
  rcases family_descends (prefixWord ++ tailWord_36161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36172 : List Nat := [2, 2, 1, 3, 2, 2, 1, 2, 6]
def baseStart_36172 : Nat := 118140960795 + 36172 * 2 ^ 59
def prefixEnd_36172 : Nat := 4983230072969 + 3 ^ 40 * 36172 * 2
def baseEnd_36172 : Nat := 8254943215350093592735

theorem tailTrace_36172 : CollatzResearch.WordTrace tailWord_36172 prefixEnd_36172 8254943215350093592735 := by
  unfold tailWord_36172
  simp only [CollatzResearch.WordTrace]
  refine ⟨659650612481248265439385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 879534149974997687252513 659650612481248265439385)
  ·
    refine ⟨494737959360936199079539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 659650612481248265439385 494737959360936199079539)
    ·
      refine ⟨742106939041404298619309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 494737959360936199079539 742106939041404298619309)
      ·
        refine ⟨278290102140526611982241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 742106939041404298619309 278290102140526611982241)
        ·
          refine ⟨208717576605394958986681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 278290102140526611982241 208717576605394958986681)
          ·
            refine ⟨156538182454046219240011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 208717576605394958986681 156538182454046219240011)
            ·
              refine ⟨234807273681069328860017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156538182454046219240011 234807273681069328860017)
              ·
                refine ⟨176105455260801996645013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 234807273681069328860017 176105455260801996645013)
                ·
                  refine ⟨8254943215350093592735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 176105455260801996645013 8254943215350093592735)
                  ·
                    rfl

theorem cell21_36172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 6].length) (baseStart_36172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_36172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_36172 prefixEnd_36172 := by exact prefixLift 36172
  have htrace : WordTrace (prefixWord ++ tailWord_36172) baseStart_36172 baseEnd_36172 := by
    simpa [prefixWord, tailWord_36172, baseEnd_36172] using wordTrace_append hprefix tailTrace_36172
  have hstable : (prefixWord ++ tailWord_36172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36172).length < 2 ^ (prefixWord ++ tailWord_36172).sum := by decide
  have hdescent : baseEnd_36172 < baseStart_36172 := by decide
  rcases family_descends (prefixWord ++ tailWord_36172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36186 : List Nat := [3, 1, 1, 2, 1, 2, 11]
def baseStart_36186 : Nat := 118140960795 + 36186 * 2 ^ 59
def prefixEnd_36186 : Nat := 4983230072969 + 3 ^ 40 * 36186 * 2
def baseEnd_36186 : Nat := 917570911787686706597

theorem tailTrace_36186 : CollatzResearch.WordTrace tailWord_36186 prefixEnd_36186 917570911787686706597 := by
  unfold tailWord_36186
  simp only [CollatzResearch.WordTrace]
  refine ⟨329952961727944230472103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 879874564607851281258941 329952961727944230472103)
  ·
    refine ⟨494929442591916345708155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 329952961727944230472103 494929442591916345708155)
    ·
      refine ⟨742394163887874518562233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 494929442591916345708155 742394163887874518562233)
      ·
        refine ⟨556795622915905888921675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 742394163887874518562233 556795622915905888921675)
        ·
          refine ⟨835193434373858833382513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 556795622915905888921675 835193434373858833382513)
          ·
            refine ⟨626395075780394125036885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 835193434373858833382513 626395075780394125036885)
            ·
              refine ⟨917570911787686706597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 626395075780394125036885 917570911787686706597)
              ·
                rfl

theorem cell21_36186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 11].length) (baseStart_36186 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_36186 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_36186 prefixEnd_36186 := by exact prefixLift 36186
  have htrace : WordTrace (prefixWord ++ tailWord_36186) baseStart_36186 baseEnd_36186 := by
    simpa [prefixWord, tailWord_36186, baseEnd_36186] using wordTrace_append hprefix tailTrace_36186
  have hstable : (prefixWord ++ tailWord_36186).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36186).length < 2 ^ (prefixWord ++ tailWord_36186).sum := by decide
  have hdescent : baseEnd_36186 < baseStart_36186 := by decide
  rcases family_descends (prefixWord ++ tailWord_36186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36192 : List Nat := [2, 1, 1, 3, 4, 2, 3, 2, 3]
def baseStart_36192 : Nat := 118140960795 + 36192 * 2 ^ 59
def prefixEnd_36192 : Nat := 4983230072969 + 3 ^ 40 * 36192 * 2
def baseEnd_36192 : Nat := 8259507487834503259361

theorem tailTrace_36192 : CollatzResearch.WordTrace tailWord_36192 prefixEnd_36192 8259507487834503259361 := by
  unfold tailWord_36192
  simp only [CollatzResearch.WordTrace]
  refine ⟨660015342445019973303415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 880020456593359964404553 660015342445019973303415)
  ·
    refine ⟨990023013667529959955123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 660015342445019973303415 990023013667529959955123)
    ·
      refine ⟨1485034520501294939932685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 990023013667529959955123 1485034520501294939932685)
      ·
        refine ⟨556887945187985602474757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1485034520501294939932685 556887945187985602474757)
        ·
          refine ⟨104416489722747300464017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 556887945187985602474757 104416489722747300464017)
          ·
            refine ⟨78312367292060475348013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104416489722747300464017 78312367292060475348013)
            ·
              refine ⟨29367137734522678255505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78312367292060475348013 29367137734522678255505)
              ·
                refine ⟨22025353300892008691629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29367137734522678255505 22025353300892008691629)
                ·
                  refine ⟨8259507487834503259361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22025353300892008691629 8259507487834503259361)
                  ·
                    rfl

theorem cell21_36192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 2, 3].length) (baseStart_36192 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_36192 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_36192 prefixEnd_36192 := by exact prefixLift 36192
  have htrace : WordTrace (prefixWord ++ tailWord_36192) baseStart_36192 baseEnd_36192 := by
    simpa [prefixWord, tailWord_36192, baseEnd_36192] using wordTrace_append hprefix tailTrace_36192
  have hstable : (prefixWord ++ tailWord_36192).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36192).length < 2 ^ (prefixWord ++ tailWord_36192).sum := by decide
  have hdescent : baseEnd_36192 < baseStart_36192 := by decide
  rcases family_descends (prefixWord ++ tailWord_36192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36217 : List Nat := [1, 2, 1, 3, 2, 1, 2, 4, 5]
def baseStart_36217 : Nat := 118140960795 + 36217 * 2 ^ 59
def prefixEnd_36217 : Nat := 4983230072969 + 3 ^ 40 * 36217 * 2
def baseEnd_36217 : Nat := 8265212828440015342643

theorem tailTrace_36217 : CollatzResearch.WordTrace tailWord_36217 prefixEnd_36217 8265212828440015342643 := by
  unfold tailWord_36217
  simp only [CollatzResearch.WordTrace]
  refine ⟨1320942509799469216266905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 880628339866312810844603 1320942509799469216266905)
  ·
    refine ⟨990706882349601912200179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1320942509799469216266905 990706882349601912200179)
    ·
      refine ⟨1486060323524402868300269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 990706882349601912200179 1486060323524402868300269)
      ·
        refine ⟨557272621321651075612601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1486060323524402868300269 557272621321651075612601)
        ·
          refine ⟨417954465991238306709451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 557272621321651075612601 417954465991238306709451)
          ·
            refine ⟨626931698986857460064177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 417954465991238306709451 626931698986857460064177)
            ·
              refine ⟨470198774240143095048133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 626931698986857460064177 470198774240143095048133)
              ·
                refine ⟨88162270170026830321525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 470198774240143095048133 88162270170026830321525)
                ·
                  refine ⟨8265212828440015342643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 88162270170026830321525 8265212828440015342643)
                  ·
                    rfl

theorem cell21_36217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 5].length) (baseStart_36217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_36217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_36217 prefixEnd_36217 := by exact prefixLift 36217
  have htrace : WordTrace (prefixWord ++ tailWord_36217) baseStart_36217 baseEnd_36217 := by
    simpa [prefixWord, tailWord_36217, baseEnd_36217] using wordTrace_append hprefix tailTrace_36217
  have hstable : (prefixWord ++ tailWord_36217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36217).length < 2 ^ (prefixWord ++ tailWord_36217).sum := by decide
  have hdescent : baseEnd_36217 < baseStart_36217 := by decide
  rcases family_descends (prefixWord ++ tailWord_36217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36254 : List Nat := [4, 3, 1, 2, 3, 1, 1, 6]
def baseStart_36254 : Nat := 118140960795 + 36254 * 2 ^ 59
def prefixEnd_36254 : Nat := 4983230072969 + 3 ^ 40 * 36254 * 2
def baseEnd_36254 : Nat := 2757885577512057741967

theorem tailTrace_36254 : CollatzResearch.WordTrace tailWord_36254 prefixEnd_36254 2757885577512057741967 := by
  unfold tailWord_36254
  simp only [CollatzResearch.WordTrace]
  refine ⟨165286501333178066920477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 881528007110283023575877 165286501333178066920477)
  ·
    refine ⟨61982437999941775095179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165286501333178066920477 61982437999941775095179)
    ·
      refine ⟨92973656999912662642769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61982437999941775095179 92973656999912662642769)
      ·
        refine ⟨69730242749934496982077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92973656999912662642769 69730242749934496982077)
        ·
          refine ⟨26148841031225436368279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69730242749934496982077 26148841031225436368279)
          ·
            refine ⟨39223261546838154552419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26148841031225436368279 39223261546838154552419)
            ·
              refine ⟨58834892320257231828629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39223261546838154552419 58834892320257231828629)
              ·
                refine ⟨2757885577512057741967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58834892320257231828629 2757885577512057741967)
                ·
                  rfl

theorem cell21_36254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 6].length) (baseStart_36254 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_36254 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_36254 prefixEnd_36254 := by exact prefixLift 36254
  have htrace : WordTrace (prefixWord ++ tailWord_36254) baseStart_36254 baseEnd_36254 := by
    simpa [prefixWord, tailWord_36254, baseEnd_36254] using wordTrace_append hprefix tailTrace_36254
  have hstable : (prefixWord ++ tailWord_36254).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36254).length < 2 ^ (prefixWord ++ tailWord_36254).sum := by decide
  have hdescent : baseEnd_36254 < baseStart_36254 := by decide
  rcases family_descends (prefixWord ++ tailWord_36254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36279 : List Nat := [1, 1, 3, 1, 3, 2, 5, 5]
def baseStart_36279 : Nat := 118140960795 + 36279 * 2 ^ 59
def prefixEnd_36279 : Nat := 4983230072969 + 3 ^ 40 * 36279 * 2
def baseEnd_36279 : Nat := 2759787357713895103061

theorem tailTrace_36279 : CollatzResearch.WordTrace tailWord_36279 prefixEnd_36279 2759787357713895103061 := by
  unfold tailWord_36279
  simp only [CollatzResearch.WordTrace]
  refine ⟨1323203835574853805023891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 882135890383235870015927 1323203835574853805023891)
  ·
    refine ⟨1984805753362280707535837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1323203835574853805023891 1984805753362280707535837)
    ·
      refine ⟨744302157510855265325939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1984805753362280707535837 744302157510855265325939)
      ·
        refine ⟨1116453236266282897988909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 744302157510855265325939 1116453236266282897988909)
        ·
          refine ⟨418669963599856086745841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1116453236266282897988909 418669963599856086745841)
          ·
            refine ⟨314002472699892065059381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 418669963599856086745841 314002472699892065059381)
            ·
              refine ⟨29437731815614881099317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 314002472699892065059381 29437731815614881099317)
              ·
                refine ⟨2759787357713895103061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29437731815614881099317 2759787357713895103061)
                ·
                  rfl

theorem cell21_36279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 5].length) (baseStart_36279 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_36279 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_36279 prefixEnd_36279 := by exact prefixLift 36279
  have htrace : WordTrace (prefixWord ++ tailWord_36279) baseStart_36279 baseEnd_36279 := by
    simpa [prefixWord, tailWord_36279, baseEnd_36279] using wordTrace_append hprefix tailTrace_36279
  have hstable : (prefixWord ++ tailWord_36279).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36279).length < 2 ^ (prefixWord ++ tailWord_36279).sum := by decide
  have hdescent : baseEnd_36279 < baseStart_36279 := by decide
  rcases family_descends (prefixWord ++ tailWord_36279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36324 : List Nat := [2, 3, 1, 1, 1, 1, 1, 7, 4]
def baseStart_36324 : Nat := 118140960795 + 36324 * 2 ^ 59
def prefixEnd_36324 : Nat := 4983230072969 + 3 ^ 40 * 36324 * 2
def baseEnd_36324 : Nat := 8289631686231607059091

theorem tailTrace_36324 : CollatzResearch.WordTrace tailWord_36324 prefixEnd_36324 8289631686231607059091 := by
  unfold tailWord_36324
  simp only [CollatzResearch.WordTrace]
  refine ⟨662422560205913245206013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 883230080274550993608017 662422560205913245206013)
  ·
    refine ⟨248408460077217466952255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 662422560205913245206013 248408460077217466952255)
    ·
      refine ⟨372612690115826200428383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248408460077217466952255 372612690115826200428383)
      ·
        refine ⟨558919035173739300642575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 372612690115826200428383 558919035173739300642575)
        ·
          refine ⟨838378552760608950963863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 558919035173739300642575 838378552760608950963863)
          ·
            refine ⟨1257567829140913426445795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 838378552760608950963863 1257567829140913426445795)
            ·
              refine ⟨1886351743711370139668693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1257567829140913426445795 1886351743711370139668693)
              ·
                refine ⟨44211368993235237648485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1886351743711370139668693 44211368993235237648485)
                ·
                  refine ⟨8289631686231607059091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44211368993235237648485 8289631686231607059091)
                  ·
                    rfl

theorem cell21_36324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_36324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_36324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_36324 prefixEnd_36324 := by exact prefixLift 36324
  have htrace : WordTrace (prefixWord ++ tailWord_36324) baseStart_36324 baseEnd_36324 := by
    simpa [prefixWord, tailWord_36324, baseEnd_36324] using wordTrace_append hprefix tailTrace_36324
  have hstable : (prefixWord ++ tailWord_36324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36324).length < 2 ^ (prefixWord ++ tailWord_36324).sum := by decide
  have hdescent : baseEnd_36324 < baseStart_36324 := by decide
  rcases family_descends (prefixWord ++ tailWord_36324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36341 : List Nat := [1, 3, 5, 1, 1, 1, 1, 2, 6]
def baseStart_36341 : Nat := 118140960795 + 36341 * 2 ^ 59
def prefixEnd_36341 : Nat := 4983230072969 + 3 ^ 40 * 36341 * 2
def baseEnd_36341 : Nat := 8293511317843355275723

theorem tailTrace_36341 : CollatzResearch.WordTrace tailWord_36341 prefixEnd_36341 8293511317843355275723 := by
  unfold tailWord_36341
  simp only [CollatzResearch.WordTrace]
  refine ⟨1325465161350238393780877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 883643440900158929187251 1325465161350238393780877)
  ·
    refine ⟨497049435506339397667829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1325465161350238393780877 497049435506339397667829)
    ·
      refine ⟨46598384578719318531359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 497049435506339397667829 46598384578719318531359)
      ·
        refine ⟨69897576868078977797039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46598384578719318531359 69897576868078977797039)
        ·
          refine ⟨104846365302118466695559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69897576868078977797039 104846365302118466695559)
          ·
            refine ⟨157269547953177700043339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104846365302118466695559 157269547953177700043339)
            ·
              refine ⟨235904321929766550065009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157269547953177700043339 235904321929766550065009)
              ·
                refine ⟨176928241447324912548757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 235904321929766550065009 176928241447324912548757)
                ·
                  refine ⟨8293511317843355275723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 176928241447324912548757 8293511317843355275723)
                  ·
                    rfl

theorem cell21_36341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 6].length) (baseStart_36341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_36341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_36341 prefixEnd_36341 := by exact prefixLift 36341
  have htrace : WordTrace (prefixWord ++ tailWord_36341) baseStart_36341 baseEnd_36341 := by
    simpa [prefixWord, tailWord_36341, baseEnd_36341] using wordTrace_append hprefix tailTrace_36341
  have hstable : (prefixWord ++ tailWord_36341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36341).length < 2 ^ (prefixWord ++ tailWord_36341).sum := by decide
  have hdescent : baseEnd_36341 < baseStart_36341 := by decide
  rcases family_descends (prefixWord ++ tailWord_36341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36414 : List Nat := [4, 2, 1, 14]
def baseStart_36414 : Nat := 118140960795 + 36414 * 2 ^ 59
def prefixEnd_36414 : Nat := 4983230072969 + 3 ^ 40 * 36414 * 2
def baseEnd_36414 : Nat := 34198234207454529049

theorem tailTrace_36414 : CollatzResearch.WordTrace tailWord_36414 prefixEnd_36414 34198234207454529049 := by
  unfold tailWord_36414
  simp only [CollatzResearch.WordTrace]
  refine ⟨166015961260721482648537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 885418460057181240792197 166015961260721482648537)
  ·
    refine ⟨124511970945541111986403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166015961260721482648537 124511970945541111986403)
    ·
      refine ⟨186767956418311667979605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124511970945541111986403 186767956418311667979605)
      ·
        refine ⟨34198234207454529049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 186767956418311667979605 34198234207454529049)
        ·
          rfl

theorem cell21_36414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 14].length) (baseStart_36414 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_36414 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_36414 prefixEnd_36414 := by exact prefixLift 36414
  have htrace : WordTrace (prefixWord ++ tailWord_36414) baseStart_36414 baseEnd_36414 := by
    simpa [prefixWord, tailWord_36414, baseEnd_36414] using wordTrace_append hprefix tailTrace_36414
  have hstable : (prefixWord ++ tailWord_36414).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36414).length < 2 ^ (prefixWord ++ tailWord_36414).sum := by decide
  have hdescent : baseEnd_36414 < baseStart_36414 := by decide
  rcases family_descends (prefixWord ++ tailWord_36414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36417 : List Nat := [1, 2, 5, 1, 1, 1, 4, 2, 4]
def baseStart_36417 : Nat := 118140960795 + 36417 * 2 ^ 59
def prefixEnd_36417 : Nat := 4983230072969 + 3 ^ 40 * 36417 * 2
def baseEnd_36417 : Nat := 8310855553284112008901

theorem tailTrace_36417 : CollatzResearch.WordTrace tailWord_36417 prefixEnd_36417 8310855553284112008901 := by
  unfold tailWord_36417
  simp only [CollatzResearch.WordTrace]
  refine ⟨1328237109074903373547505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 885491406049935582365003 1328237109074903373547505)
  ·
    refine ⟨996177831806177530160629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1328237109074903373547505 996177831806177530160629)
    ·
      refine ⟨93391671731829143452559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 996177831806177530160629 93391671731829143452559)
      ·
        refine ⟨140087507597743715178839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93391671731829143452559 140087507597743715178839)
        ·
          refine ⟨210131261396615572768259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140087507597743715178839 210131261396615572768259)
          ·
            refine ⟨315196892094923359152389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210131261396615572768259 315196892094923359152389)
            ·
              refine ⟨59099417267798129841073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 315196892094923359152389 59099417267798129841073)
              ·
                refine ⟨44324562950848597380805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59099417267798129841073 44324562950848597380805)
                ·
                  refine ⟨8310855553284112008901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44324562950848597380805 8310855553284112008901)
                  ·
                    rfl

theorem cell21_36417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 2, 4].length) (baseStart_36417 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_36417 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_36417 prefixEnd_36417 := by exact prefixLift 36417
  have htrace : WordTrace (prefixWord ++ tailWord_36417) baseStart_36417 baseEnd_36417 := by
    simpa [prefixWord, tailWord_36417, baseEnd_36417] using wordTrace_append hprefix tailTrace_36417
  have hstable : (prefixWord ++ tailWord_36417).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36417).length < 2 ^ (prefixWord ++ tailWord_36417).sum := by decide
  have hdescent : baseEnd_36417 < baseStart_36417 := by decide
  rcases family_descends (prefixWord ++ tailWord_36417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36538 : List Nat := [3, 1, 1, 1, 2, 6, 1, 1, 5]
def baseStart_36538 : Nat := 118140960795 + 36538 * 2 ^ 59
def prefixEnd_36538 : Nat := 4983230072969 + 3 ^ 40 * 36538 * 2
def baseEnd_36538 : Nat := 8338469401814790491987

theorem tailTrace_36538 : CollatzResearch.WordTrace tailWord_36538 prefixEnd_36538 8338469401814790491987 := by
  unfold tailWord_36538
  simp only [CollatzResearch.WordTrace]
  refine ⟨333162585409135259675567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 888433561091027359134845 333162585409135259675567)
  ·
    refine ⟨499743878113702889513351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 333162585409135259675567 499743878113702889513351)
    ·
      refine ⟨749615817170554334270027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 499743878113702889513351 749615817170554334270027)
      ·
        refine ⟨1124423725755831501405041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 749615817170554334270027 1124423725755831501405041)
        ·
          refine ⟨843317794316873626053781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1124423725755831501405041 843317794316873626053781)
          ·
            refine ⟨39530521608603451221271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 843317794316873626053781 39530521608603451221271)
            ·
              refine ⟨59295782412905176831907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39530521608603451221271 59295782412905176831907)
              ·
                refine ⟨88943673619357765247861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59295782412905176831907 88943673619357765247861)
                ·
                  refine ⟨8338469401814790491987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 88943673619357765247861 8338469401814790491987)
                  ·
                    rfl

theorem cell21_36538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 5].length) (baseStart_36538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_36538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_36538 prefixEnd_36538 := by exact prefixLift 36538
  have htrace : WordTrace (prefixWord ++ tailWord_36538) baseStart_36538 baseEnd_36538 := by
    simpa [prefixWord, tailWord_36538, baseEnd_36538] using wordTrace_append hprefix tailTrace_36538
  have hstable : (prefixWord ++ tailWord_36538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36538).length < 2 ^ (prefixWord ++ tailWord_36538).sum := by decide
  have hdescent : baseEnd_36538 < baseStart_36538 := by decide
  rcases family_descends (prefixWord ++ tailWord_36538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36552 : List Nat := [2, 1, 3, 1, 2, 2, 3, 3, 4]
def baseStart_36552 : Nat := 118140960795 + 36552 * 2 ^ 59
def prefixEnd_36552 : Nat := 4983230072969 + 3 ^ 40 * 36552 * 2
def baseEnd_36552 : Nat := 8341664392553877258625

theorem tailTrace_36552 : CollatzResearch.WordTrace tailWord_36552 prefixEnd_36552 8341664392553877258625 := by
  unfold tailWord_36552
  simp only [CollatzResearch.WordTrace]
  refine ⟨666580481792910714855955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 888773975723880953141273 666580481792910714855955)
  ·
    refine ⟨999870722689366072283933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 666580481792910714855955 999870722689366072283933)
    ·
      refine ⟨374951521008512277106475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 999870722689366072283933 374951521008512277106475)
      ·
        refine ⟨562427281512768415659713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 374951521008512277106475 562427281512768415659713)
        ·
          refine ⟨421820461134576311744785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 562427281512768415659713 421820461134576311744785)
          ·
            refine ⟨316365345850932233808589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 421820461134576311744785 316365345850932233808589)
            ·
              refine ⟨118637004694099587678221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 316365345850932233808589 118637004694099587678221)
              ·
                refine ⟨44488876760287345379333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118637004694099587678221 44488876760287345379333)
                ·
                  refine ⟨8341664392553877258625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44488876760287345379333 8341664392553877258625)
                  ·
                    rfl

theorem cell21_36552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 3, 4].length) (baseStart_36552 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_36552 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_36552 prefixEnd_36552 := by exact prefixLift 36552
  have htrace : WordTrace (prefixWord ++ tailWord_36552) baseStart_36552 baseEnd_36552 := by
    simpa [prefixWord, tailWord_36552, baseEnd_36552] using wordTrace_append hprefix tailTrace_36552
  have hstable : (prefixWord ++ tailWord_36552).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36552).length < 2 ^ (prefixWord ++ tailWord_36552).sum := by decide
  have hdescent : baseEnd_36552 < baseStart_36552 := by decide
  rcases family_descends (prefixWord ++ tailWord_36552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36583 : List Nat := [1, 1, 5, 4, 1, 9]
def baseStart_36583 : Nat := 118140960795 + 36583 * 2 ^ 59
def prefixEnd_36583 : Nat := 4983230072969 + 3 ^ 40 * 36583 * 2
def baseEnd_36583 : Nat := 309212556107581934885

theorem tailTrace_36583 : CollatzResearch.WordTrace tailWord_36583 prefixEnd_36583 309212556107581934885 := by
  unfold tailWord_36583
  simp only [CollatzResearch.WordTrace]
  refine ⟨1334291626473513724090403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 889527750982342482726935 1334291626473513724090403)
  ·
    refine ⟨2001437439710270586135605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1334291626473513724090403 2001437439710270586135605)
    ·
      refine ⟨187634759972837867450213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2001437439710270586135605 187634759972837867450213)
      ·
        refine ⟨35181517494907100146915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 187634759972837867450213 35181517494907100146915)
        ·
          refine ⟨52772276242360650220373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35181517494907100146915 52772276242360650220373)
          ·
            refine ⟨309212556107581934885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 52772276242360650220373 309212556107581934885)
            ·
              rfl

theorem cell21_36583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 9].length) (baseStart_36583 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_36583 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_36583 prefixEnd_36583 := by exact prefixLift 36583
  have htrace : WordTrace (prefixWord ++ tailWord_36583) baseStart_36583 baseEnd_36583 := by
    simpa [prefixWord, tailWord_36583, baseEnd_36583] using wordTrace_append hprefix tailTrace_36583
  have hstable : (prefixWord ++ tailWord_36583).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36583).length < 2 ^ (prefixWord ++ tailWord_36583).sum := by decide
  have hdescent : baseEnd_36583 < baseStart_36583 := by decide
  rcases family_descends (prefixWord ++ tailWord_36583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36631 : List Nat := [1, 1, 3, 4, 2, 2, 2, 3, 3]
def baseStart_36631 : Nat := 118140960795 + 36631 * 2 ^ 59
def prefixEnd_36631 : Nat := 4983230072969 + 3 ^ 40 * 36631 * 2
def baseEnd_36631 : Nat := 8359693268867295441797

theorem tailTrace_36631 : CollatzResearch.WordTrace tailWord_36631 prefixEnd_36631 8359693268867295441797 := by
  unfold tailWord_36631
  simp only [CollatzResearch.WordTrace]
  refine ⟨1336042330299617921837747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 890694886866411947891831 1336042330299617921837747)
  ·
    refine ⟨2004063495449426882756621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1336042330299617921837747 2004063495449426882756621)
    ·
      refine ⟨751523810793535081033733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2004063495449426882756621 751523810793535081033733)
      ·
        refine ⟨140910714523787827693825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 751523810793535081033733 140910714523787827693825)
        ·
          refine ⟨105683035892840870770369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140910714523787827693825 105683035892840870770369)
          ·
            refine ⟨79262276919630653077777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105683035892840870770369 79262276919630653077777)
            ·
              refine ⟨59446707689722989808333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79262276919630653077777 59446707689722989808333)
              ·
                refine ⟨22292515383646121178125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59446707689722989808333 22292515383646121178125)
                ·
                  refine ⟨8359693268867295441797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22292515383646121178125 8359693268867295441797)
                  ·
                    rfl

theorem cell21_36631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 3, 3].length) (baseStart_36631 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_36631 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_36631 prefixEnd_36631 := by exact prefixLift 36631
  have htrace : WordTrace (prefixWord ++ tailWord_36631) baseStart_36631 baseEnd_36631 := by
    simpa [prefixWord, tailWord_36631, baseEnd_36631] using wordTrace_append hprefix tailTrace_36631
  have hstable : (prefixWord ++ tailWord_36631).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36631).length < 2 ^ (prefixWord ++ tailWord_36631).sum := by decide
  have hdescent : baseEnd_36631 < baseStart_36631 := by decide
  rcases family_descends (prefixWord ++ tailWord_36631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36642 : List Nat := [3, 3, 1, 1, 2, 1, 10]
def baseStart_36642 : Nat := 118140960795 + 36642 * 2 ^ 59
def prefixEnd_36642 : Nat := 4983230072969 + 3 ^ 40 * 36642 * 2
def baseEnd_36642 : Nat := 929133735414857862049

theorem tailTrace_36642 : CollatzResearch.WordTrace tailWord_36642 prefixEnd_36642 929133735414857862049 := by
  unfold tailWord_36642
  simp only [CollatzResearch.WordTrace]
  refine ⟨334110883314941700122045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 890962355506511200325453 334110883314941700122045)
  ·
    refine ⟨125291581243103137545767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 334110883314941700122045 125291581243103137545767)
    ·
      refine ⟨187937371864654706318651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125291581243103137545767 187937371864654706318651)
      ·
        refine ⟨281906057796982059477977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187937371864654706318651 281906057796982059477977)
        ·
          refine ⟨211429543347736544608483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 281906057796982059477977 211429543347736544608483)
          ·
            refine ⟨317144315021604816912725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211429543347736544608483 317144315021604816912725)
            ·
              refine ⟨929133735414857862049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 317144315021604816912725 929133735414857862049)
              ·
                rfl

theorem cell21_36642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 10].length) (baseStart_36642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_36642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_36642 prefixEnd_36642 := by exact prefixLift 36642
  have htrace : WordTrace (prefixWord ++ tailWord_36642) baseStart_36642 baseEnd_36642 := by
    simpa [prefixWord, tailWord_36642, baseEnd_36642] using wordTrace_append hprefix tailTrace_36642
  have hstable : (prefixWord ++ tailWord_36642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36642).length < 2 ^ (prefixWord ++ tailWord_36642).sum := by decide
  have hdescent : baseEnd_36642 < baseStart_36642 := by decide
  rcases family_descends (prefixWord ++ tailWord_36642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36645 : List Nat := [1, 3, 1, 2, 3, 4, 1, 2, 4]
def baseStart_36645 : Nat := 118140960795 + 36645 * 2 ^ 59
def prefixEnd_36645 : Nat := 4983230072969 + 3 ^ 40 * 36645 * 2
def baseEnd_36645 : Nat := 8362888259606382208435

theorem tailTrace_36645 : CollatzResearch.WordTrace tailWord_36645 prefixEnd_36645 8362888259606382208435 := by
  unfold tailWord_36645
  simp only [CollatzResearch.WordTrace]
  refine ⟨1336552952248898312847389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 891035301499265541898259 1336552952248898312847389)
  ·
    refine ⟨501207357093336867317771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1336552952248898312847389 501207357093336867317771)
    ·
      refine ⟨751811035640005300976657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 501207357093336867317771 751811035640005300976657)
      ·
        refine ⟨563858276730003975732493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 751811035640005300976657 563858276730003975732493)
        ·
          refine ⟨211446853773751490899685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 563858276730003975732493 211446853773751490899685)
          ·
            refine ⟨39646285082578404543691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 211446853773751490899685 39646285082578404543691)
            ·
              refine ⟨59469427623867606815537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39646285082578404543691 59469427623867606815537)
              ·
                refine ⟨44602070717900705111653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59469427623867606815537 44602070717900705111653)
                ·
                  refine ⟨8362888259606382208435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44602070717900705111653 8362888259606382208435)
                  ·
                    rfl

theorem cell21_36645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 2, 4].length) (baseStart_36645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_36645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_36645 prefixEnd_36645 := by exact prefixLift 36645
  have htrace : WordTrace (prefixWord ++ tailWord_36645) baseStart_36645 baseEnd_36645 := by
    simpa [prefixWord, tailWord_36645, baseEnd_36645] using wordTrace_append hprefix tailTrace_36645
  have hstable : (prefixWord ++ tailWord_36645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36645).length < 2 ^ (prefixWord ++ tailWord_36645).sum := by decide
  have hdescent : baseEnd_36645 < baseStart_36645 := by decide
  rcases family_descends (prefixWord ++ tailWord_36645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36707 : List Nat := [1, 1, 1, 5, 5, 1, 1, 1, 5]
def baseStart_36707 : Nat := 118140960795 + 36707 * 2 ^ 59
def prefixEnd_36707 : Nat := 4983230072969 + 3 ^ 40 * 36707 * 2
def baseEnd_36707 : Nat := 8377037504308052174975

theorem tailTrace_36707 : CollatzResearch.WordTrace tailWord_36707 prefixEnd_36707 8377037504308052174975 := by
  unfold tailWord_36707
  simp only [CollatzResearch.WordTrace]
  refine ⟨1338814278024282901604375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 892542852016188601069583 1338814278024282901604375)
  ·
    refine ⟨2008221417036424352406563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1338814278024282901604375 2008221417036424352406563)
    ·
      refine ⟨3012332125554636528609845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2008221417036424352406563 3012332125554636528609845)
      ·
        refine ⟨282406136770747174557173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3012332125554636528609845 282406136770747174557173)
        ·
          refine ⟨26475575322257547614735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 282406136770747174557173 26475575322257547614735)
          ·
            refine ⟨39713362983386321422103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26475575322257547614735 39713362983386321422103)
            ·
              refine ⟨59570044475079482133155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39713362983386321422103 59570044475079482133155)
              ·
                refine ⟨89355066712619223199733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59570044475079482133155 89355066712619223199733)
                ·
                  refine ⟨8377037504308052174975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 89355066712619223199733 8377037504308052174975)
                  ·
                    rfl

theorem cell21_36707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 5].length) (baseStart_36707 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_36707 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_36707 prefixEnd_36707 := by exact prefixLift 36707
  have htrace : WordTrace (prefixWord ++ tailWord_36707) baseStart_36707 baseEnd_36707 := by
    simpa [prefixWord, tailWord_36707, baseEnd_36707] using wordTrace_append hprefix tailTrace_36707
  have hstable : (prefixWord ++ tailWord_36707).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36707).length < 2 ^ (prefixWord ++ tailWord_36707).sum := by decide
  have hdescent : baseEnd_36707 < baseStart_36707 := by decide
  rcases family_descends (prefixWord ++ tailWord_36707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36777 : List Nat := [1, 2, 1, 1, 1, 1, 4, 10]
def baseStart_36777 : Nat := 118140960795 + 36777 * 2 ^ 59
def prefixEnd_36777 : Nat := 4983230072969 + 3 ^ 40 * 36777 * 2
def baseEnd_36777 : Nat := 2797670819334495336055

theorem tailTrace_36777 : CollatzResearch.WordTrace tailWord_36777 prefixEnd_36777 2797670819334495336055 := by
  unfold tailWord_36777
  simp only [CollatzResearch.WordTrace]
  refine ⟨1341367387770684856652585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 894244925180456571101723 1341367387770684856652585)
  ·
    refine ⟨1006025540828013642489439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1341367387770684856652585 1006025540828013642489439)
    ·
      refine ⟨1509038311242020463734159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1006025540828013642489439 1509038311242020463734159)
      ·
        refine ⟨2263557466863030695601239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1509038311242020463734159 2263557466863030695601239)
        ·
          refine ⟨3395336200294546043401859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2263557466863030695601239 3395336200294546043401859)
          ·
            refine ⟨5093004300441819065102789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3395336200294546043401859 5093004300441819065102789)
            ·
              refine ⟨954938306332841074706773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5093004300441819065102789 954938306332841074706773)
              ·
                refine ⟨2797670819334495336055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 954938306332841074706773 2797670819334495336055)
                ·
                  rfl

theorem cell21_36777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 10].length) (baseStart_36777 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_36777 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_36777 prefixEnd_36777 := by exact prefixLift 36777
  have htrace : WordTrace (prefixWord ++ tailWord_36777) baseStart_36777 baseEnd_36777 := by
    simpa [prefixWord, tailWord_36777, baseEnd_36777] using wordTrace_append hprefix tailTrace_36777
  have hstable : (prefixWord ++ tailWord_36777).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36777).length < 2 ^ (prefixWord ++ tailWord_36777).sum := by decide
  have hdescent : baseEnd_36777 < baseStart_36777 := by decide
  rcases family_descends (prefixWord ++ tailWord_36777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36845 : List Nat := [1, 5, 1, 4, 1, 2, 2, 5]
def baseStart_36845 : Nat := 118140960795 + 36845 * 2 ^ 59
def prefixEnd_36845 : Nat := 4983230072969 + 3 ^ 40 * 36845 * 2
def baseEnd_36845 : Nat := 2802843661483492958231

theorem tailTrace_36845 : CollatzResearch.WordTrace tailWord_36845 prefixEnd_36845 2802843661483492958231 := by
  unfold tailWord_36845
  simp only [CollatzResearch.WordTrace]
  refine ⟨1343847551524332470127989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 895898367682888313418659 1343847551524332470127989)
  ·
    refine ⟨125985707955406169074499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1343847551524332470127989 125985707955406169074499)
    ·
      refine ⟨188978561933109253611749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125985707955406169074499 188978561933109253611749)
      ·
        refine ⟨35433480362457985052203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 188978561933109253611749 35433480362457985052203)
        ·
          refine ⟨53150220543686977578305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35433480362457985052203 53150220543686977578305)
          ·
            refine ⟨39862665407765233183729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53150220543686977578305 39862665407765233183729)
            ·
              refine ⟨29896999055823924887797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39862665407765233183729 29896999055823924887797)
              ·
                refine ⟨2802843661483492958231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29896999055823924887797 2802843661483492958231)
                ·
                  rfl

theorem cell21_36845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 5].length) (baseStart_36845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_36845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_36845 prefixEnd_36845 := by exact prefixLift 36845
  have htrace : WordTrace (prefixWord ++ tailWord_36845) baseStart_36845 baseEnd_36845 := by
    simpa [prefixWord, tailWord_36845, baseEnd_36845] using wordTrace_append hprefix tailTrace_36845
  have hstable : (prefixWord ++ tailWord_36845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36845).length < 2 ^ (prefixWord ++ tailWord_36845).sum := by decide
  have hdescent : baseEnd_36845 < baseStart_36845 := by decide
  rcases family_descends (prefixWord ++ tailWord_36845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36887 : List Nat := [1, 1, 3, 5, 2, 1, 2, 6]
def baseStart_36887 : Nat := 118140960795 + 36887 * 2 ^ 59
def prefixEnd_36887 : Nat := 4983230072969 + 3 ^ 40 * 36887 * 2
def baseEnd_36887 : Nat := 2806038652222579724869

theorem tailTrace_36887 : CollatzResearch.WordTrace tailWord_36887 prefixEnd_36887 2806038652222579724869 := by
  unfold tailWord_36887
  simp only [CollatzResearch.WordTrace]
  refine ⟨1345379417372173643156915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 896919611581449095437943 1345379417372173643156915)
  ·
    refine ⟨2018069126058260464735373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1345379417372173643156915 2018069126058260464735373)
    ·
      refine ⟨756775922271847674275765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2018069126058260464735373 756775922271847674275765)
      ·
        refine ⟨70947742712985719463353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 756775922271847674275765 70947742712985719463353)
        ·
          refine ⟨53210807034739289597515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70947742712985719463353 53210807034739289597515)
          ·
            refine ⟨79816210552108934396273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53210807034739289597515 79816210552108934396273)
            ·
              refine ⟨59862157914081700797205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79816210552108934396273 59862157914081700797205)
              ·
                refine ⟨2806038652222579724869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 59862157914081700797205 2806038652222579724869)
                ·
                  rfl

theorem cell21_36887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 6].length) (baseStart_36887 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_36887 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_36887 prefixEnd_36887 := by exact prefixLift 36887
  have htrace : WordTrace (prefixWord ++ tailWord_36887) baseStart_36887 baseEnd_36887 := by
    simpa [prefixWord, tailWord_36887, baseEnd_36887] using wordTrace_append hprefix tailTrace_36887
  have hstable : (prefixWord ++ tailWord_36887).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36887).length < 2 ^ (prefixWord ++ tailWord_36887).sum := by decide
  have hdescent : baseEnd_36887 < baseStart_36887 := by decide
  rcases family_descends (prefixWord ++ tailWord_36887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36960 : List Nat := [2, 1, 1, 3, 2, 3, 1, 1, 7]
def baseStart_36960 : Nat := 118140960795 + 36960 * 2 ^ 59
def prefixEnd_36960 : Nat := 4983230072969 + 3 ^ 40 * 36960 * 2
def baseEnd_36960 : Nat := 8434775551235834457791

theorem tailTrace_36960 : CollatzResearch.WordTrace tailWord_36960 prefixEnd_36960 8434775551235834457791 := by
  unfold tailWord_36960
  simp only [CollatzResearch.WordTrace]
  refine ⟨674020973053853555282167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 898694630738471407042889 674020973053853555282167)
  ·
    refine ⟨1011031459580780332923251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 674020973053853555282167 1011031459580780332923251)
    ·
      refine ⟨1516547189371170499384877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1011031459580780332923251 1516547189371170499384877)
      ·
        refine ⟨568705196014188937269329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1516547189371170499384877 568705196014188937269329)
        ·
          refine ⟨426528897010641702951997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 568705196014188937269329 426528897010641702951997)
          ·
            refine ⟨159948336378990638606999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 426528897010641702951997 159948336378990638606999)
            ·
              refine ⟨239922504568485957910499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159948336378990638606999 239922504568485957910499)
              ·
                refine ⟨359883756852728936865749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 239922504568485957910499 359883756852728936865749)
                ·
                  refine ⟨8434775551235834457791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 359883756852728936865749 8434775551235834457791)
                  ·
                    rfl

theorem cell21_36960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 7].length) (baseStart_36960 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_36960 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_36960 prefixEnd_36960 := by exact prefixLift 36960
  have htrace : WordTrace (prefixWord ++ tailWord_36960) baseStart_36960 baseEnd_36960 := by
    simpa [prefixWord, tailWord_36960, baseEnd_36960] using wordTrace_append hprefix tailTrace_36960
  have hstable : (prefixWord ++ tailWord_36960).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36960).length < 2 ^ (prefixWord ++ tailWord_36960).sum := by decide
  have hdescent : baseEnd_36960 < baseStart_36960 := by decide
  rcases family_descends (prefixWord ++ tailWord_36960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37008 : List Nat := [2, 1, 1, 1, 1, 1, 9, 1, 4]
def baseStart_37008 : Nat := 118140960795 + 37008 * 2 ^ 59
def prefixEnd_37008 : Nat := 4983230072969 + 3 ^ 40 * 37008 * 2
def baseEnd_37008 : Nat := 8445729805198417657693

theorem tailTrace_37008 : CollatzResearch.WordTrace tailWord_37008 prefixEnd_37008 8445729805198417657693 := by
  unfold tailWord_37008
  simp only [CollatzResearch.WordTrace]
  refine ⟨674896324966905654155839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 899861766622540872207785 674896324966905654155839)
  ·
    refine ⟨1012344487450358481233759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 674896324966905654155839 1012344487450358481233759)
    ·
      refine ⟨1518516731175537721850639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1012344487450358481233759 1518516731175537721850639)
      ·
        refine ⟨2277775096763306582775959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1518516731175537721850639 2277775096763306582775959)
        ·
          refine ⟨3416662645144959874163939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2277775096763306582775959 3416662645144959874163939)
          ·
            refine ⟨5124993967717439811245909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3416662645144959874163939 5124993967717439811245909)
            ·
              refine ⟨30029261529594373894019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5124993967717439811245909 30029261529594373894019)
              ·
                refine ⟨45043892294391560841029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30029261529594373894019 45043892294391560841029)
                ·
                  refine ⟨8445729805198417657693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45043892294391560841029 8445729805198417657693)
                  ·
                    rfl

theorem cell21_37008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 1, 4].length) (baseStart_37008 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_37008 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_37008 prefixEnd_37008 := by exact prefixLift 37008
  have htrace : WordTrace (prefixWord ++ tailWord_37008) baseStart_37008 baseEnd_37008 := by
    simpa [prefixWord, tailWord_37008, baseEnd_37008] using wordTrace_append hprefix tailTrace_37008
  have hstable : (prefixWord ++ tailWord_37008).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37008).length < 2 ^ (prefixWord ++ tailWord_37008).sum := by decide
  have hdescent : baseEnd_37008 < baseStart_37008 := by decide
  rcases family_descends (prefixWord ++ tailWord_37008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37014 : List Nat := [5, 3, 2, 1, 1, 1, 1, 7]
def baseStart_37014 : Nat := 118140960795 + 37014 * 2 ^ 59
def prefixEnd_37014 : Nat := 4983230072969 + 3 ^ 40 * 37014 * 2
def baseEnd_37014 : Nat := 2815699695647913519227

theorem tailTrace_37014 : CollatzResearch.WordTrace tailWord_37014 prefixEnd_37014 2815699695647913519227 := by
  unfold tailWord_37014
  simp only [CollatzResearch.WordTrace]
  refine ⟨84375717994504645814381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 900007658608049555353397 84375717994504645814381)
  ·
    refine ⟨31640894247939242180393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84375717994504645814381 31640894247939242180393)
    ·
      refine ⟨23730670685954431635295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31640894247939242180393 23730670685954431635295)
      ·
        refine ⟨35596006028931647452943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23730670685954431635295 35596006028931647452943)
        ·
          refine ⟨53394009043397471179415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35596006028931647452943 53394009043397471179415)
          ·
            refine ⟨80091013565096206769123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53394009043397471179415 80091013565096206769123)
            ·
              refine ⟨120136520347644310153685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80091013565096206769123 120136520347644310153685)
              ·
                refine ⟨2815699695647913519227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 120136520347644310153685 2815699695647913519227)
                ·
                  rfl

theorem cell21_37014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_37014 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_37014 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_37014 prefixEnd_37014 := by exact prefixLift 37014
  have htrace : WordTrace (prefixWord ++ tailWord_37014) baseStart_37014 baseEnd_37014 := by
    simpa [prefixWord, tailWord_37014, baseEnd_37014] using wordTrace_append hprefix tailTrace_37014
  have hstable : (prefixWord ++ tailWord_37014).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37014).length < 2 ^ (prefixWord ++ tailWord_37014).sum := by decide
  have hdescent : baseEnd_37014 < baseStart_37014 := by decide
  rcases family_descends (prefixWord ++ tailWord_37014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37028 : List Nat := [2, 3, 1, 2, 5, 1, 1, 3, 3]
def baseStart_37028 : Nat := 118140960795 + 37028 * 2 ^ 59
def prefixEnd_37028 : Nat := 4983230072969 + 3 ^ 40 * 37028 * 2
def baseEnd_37028 : Nat := 8450294077682827324319

theorem tailTrace_37028 : CollatzResearch.WordTrace tailWord_37028 prefixEnd_37028 8450294077682827324319 := by
  unfold tailWord_37028
  simp only [CollatzResearch.WordTrace]
  refine ⟨675261054930677362019869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 900348073240903149359825 675261054930677362019869)
  ·
    refine ⟨253222895599004010757451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 675261054930677362019869 253222895599004010757451)
    ·
      refine ⟨379834343398506016136177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253222895599004010757451 379834343398506016136177)
      ·
        refine ⟨284875757548879512102133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 379834343398506016136177 284875757548879512102133)
        ·
          refine ⟨26707102270207454259575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 284875757548879512102133 26707102270207454259575)
          ·
            refine ⟨40060653405311181389363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26707102270207454259575 40060653405311181389363)
            ·
              refine ⟨60090980107966772084045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40060653405311181389363 60090980107966772084045)
              ·
                refine ⟨22534117540487539531517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60090980107966772084045 22534117540487539531517)
                ·
                  refine ⟨8450294077682827324319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22534117540487539531517 8450294077682827324319)
                  ·
                    rfl

theorem cell21_37028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 3, 3].length) (baseStart_37028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_37028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_37028 prefixEnd_37028 := by exact prefixLift 37028
  have htrace : WordTrace (prefixWord ++ tailWord_37028) baseStart_37028 baseEnd_37028 := by
    simpa [prefixWord, tailWord_37028, baseEnd_37028] using wordTrace_append hprefix tailTrace_37028
  have hstable : (prefixWord ++ tailWord_37028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37028).length < 2 ^ (prefixWord ++ tailWord_37028).sum := by decide
  have hdescent : baseEnd_37028 < baseStart_37028 := by decide
  rcases family_descends (prefixWord ++ tailWord_37028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37067 : List Nat := [1, 1, 1, 1, 3, 2, 5, 3, 4]
def baseStart_37067 : Nat := 118140960795 + 37067 * 2 ^ 59
def prefixEnd_37067 : Nat := 4983230072969 + 3 ^ 40 * 37067 * 2
def baseEnd_37067 : Nat := 8459194409027426174239

theorem tailTrace_37067 : CollatzResearch.WordTrace tailWord_37067 prefixEnd_37067 8459194409027426174239 := by
  unfold tailWord_37067
  simp only [CollatzResearch.WordTrace]
  refine ⟨1351944556720064384709455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 901296371146709589806303 1351944556720064384709455)
  ·
    refine ⟨2027916835080096577064183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1351944556720064384709455 2027916835080096577064183)
    ·
      refine ⟨3041875252620144865596275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2027916835080096577064183 3041875252620144865596275)
      ·
        refine ⟨4562812878930217298394413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3041875252620144865596275 4562812878930217298394413)
        ·
          refine ⟨1711054829598831486897905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4562812878930217298394413 1711054829598831486897905)
          ·
            refine ⟨1283291122199123615173429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1711054829598831486897905 1283291122199123615173429)
            ·
              refine ⟨120308542706167838922509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1283291122199123615173429 120308542706167838922509)
              ·
                refine ⟨45115703514812939595941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120308542706167838922509 45115703514812939595941)
                ·
                  refine ⟨8459194409027426174239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45115703514812939595941 8459194409027426174239)
                  ·
                    rfl

theorem cell21_37067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 3, 4].length) (baseStart_37067 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_37067 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_37067 prefixEnd_37067 := by exact prefixLift 37067
  have htrace : WordTrace (prefixWord ++ tailWord_37067) baseStart_37067 baseEnd_37067 := by
    simpa [prefixWord, tailWord_37067, baseEnd_37067] using wordTrace_append hprefix tailTrace_37067
  have hstable : (prefixWord ++ tailWord_37067).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37067).length < 2 ^ (prefixWord ++ tailWord_37067).sum := by decide
  have hdescent : baseEnd_37067 < baseStart_37067 := by decide
  rcases family_descends (prefixWord ++ tailWord_37067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37081 : List Nat := [1, 2, 1, 2, 3, 1, 4, 7]
def baseStart_37081 : Nat := 118140960795 + 37081 * 2 ^ 59
def prefixEnd_37081 : Nat := 4983230072969 + 3 ^ 40 * 37081 * 2
def baseEnd_37081 : Nat := 2820796466588837646959

theorem tailTrace_37081 : CollatzResearch.WordTrace tailWord_37081 prefixEnd_37081 2820796466588837646959 := by
  unfold tailWord_37081
  simp only [CollatzResearch.WordTrace]
  refine ⟨1352455178669344775719097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 901636785779563183812731 1352455178669344775719097)
  ·
    refine ⟨1014341384002008581789323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1352455178669344775719097 1014341384002008581789323)
    ·
      refine ⟨1521512076003012872683985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1014341384002008581789323 1521512076003012872683985)
      ·
        refine ⟨1141134057002259654512989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1521512076003012872683985 1141134057002259654512989)
        ·
          refine ⟨427925271375847370442371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1141134057002259654512989 427925271375847370442371)
          ·
            refine ⟨641887907063771055663557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 427925271375847370442371 641887907063771055663557)
            ·
              refine ⟨120353982574457072936917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 641887907063771055663557 120353982574457072936917)
              ·
                refine ⟨2820796466588837646959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 120353982574457072936917 2820796466588837646959)
                ·
                  rfl

theorem cell21_37081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 7].length) (baseStart_37081 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_37081 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_37081 prefixEnd_37081 := by exact prefixLift 37081
  have htrace : WordTrace (prefixWord ++ tailWord_37081) baseStart_37081 baseEnd_37081 := by
    simpa [prefixWord, tailWord_37081, baseEnd_37081] using wordTrace_append hprefix tailTrace_37081
  have hstable : (prefixWord ++ tailWord_37081).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37081).length < 2 ^ (prefixWord ++ tailWord_37081).sum := by decide
  have hdescent : baseEnd_37081 < baseStart_37081 := by decide
  rcases family_descends (prefixWord ++ tailWord_37081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37101 : List Nat := [1, 5, 1, 2, 3, 1, 2, 2, 4]
def baseStart_37101 : Nat := 118140960795 + 37101 * 2 ^ 59
def prefixEnd_37101 : Nat := 4983230072969 + 3 ^ 40 * 37101 * 2
def baseEnd_37101 : Nat := 8466953672250922607503

theorem tailTrace_37101 : CollatzResearch.WordTrace tailWord_37101 prefixEnd_37101 8466953672250922607503 := by
  unfold tailWord_37101
  simp only [CollatzResearch.WordTrace]
  refine ⟨1353184638596888191447157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 902123092397925460964771 1353184638596888191447157)
  ·
    refine ⟨126861059868458267948171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1353184638596888191447157 126861059868458267948171)
    ·
      refine ⟨190291589802687401922257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126861059868458267948171 190291589802687401922257)
      ·
        refine ⟨142718692352015551441693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190291589802687401922257 142718692352015551441693)
        ·
          refine ⟨53519509632005831790635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142718692352015551441693 53519509632005831790635)
          ·
            refine ⟨80279264448008747685953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53519509632005831790635 80279264448008747685953)
            ·
              refine ⟨60209448336006560764465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80279264448008747685953 60209448336006560764465)
              ·
                refine ⟨45157086252004920573349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60209448336006560764465 45157086252004920573349)
                ·
                  refine ⟨8466953672250922607503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45157086252004920573349 8466953672250922607503)
                  ·
                    rfl

theorem cell21_37101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_37101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_37101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_37101 prefixEnd_37101 := by exact prefixLift 37101
  have htrace : WordTrace (prefixWord ++ tailWord_37101) baseStart_37101 baseEnd_37101 := by
    simpa [prefixWord, tailWord_37101, baseEnd_37101] using wordTrace_append hprefix tailTrace_37101
  have hstable : (prefixWord ++ tailWord_37101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37101).length < 2 ^ (prefixWord ++ tailWord_37101).sum := by decide
  have hdescent : baseEnd_37101 < baseStart_37101 := by decide
  rcases family_descends (prefixWord ++ tailWord_37101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37160 : List Nat := [2, 1, 5, 1, 3, 1, 1, 1, 6]
def baseStart_37160 : Nat := 118140960795 + 37160 * 2 ^ 59
def prefixEnd_37160 : Nat := 4983230072969 + 3 ^ 40 * 37160 * 2
def baseEnd_37160 : Nat := 8480418276079931124049

theorem tailTrace_37160 : CollatzResearch.WordTrace tailWord_37160 prefixEnd_37160 8480418276079931124049 := by
  unfold tailWord_37160
  simp only [CollatzResearch.WordTrace]
  refine ⟨677668272691570633922467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 903557696922094178563289 677668272691570633922467)
  ·
    refine ⟨1016502409037355950883701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 677668272691570633922467 1016502409037355950883701)
    ·
      refine ⟨95297100847252120395347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1016502409037355950883701 95297100847252120395347)
      ·
        refine ⟨142945651270878180593021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95297100847252120395347 142945651270878180593021)
        ·
          refine ⟨53604619226579317722383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142945651270878180593021 53604619226579317722383)
          ·
            refine ⟨80406928839868976583575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53604619226579317722383 80406928839868976583575)
            ·
              refine ⟨120610393259803464875363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80406928839868976583575 120610393259803464875363)
              ·
                refine ⟨180915589889705197313045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120610393259803464875363 180915589889705197313045)
                ·
                  refine ⟨8480418276079931124049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 180915589889705197313045 8480418276079931124049)
                  ·
                    rfl

theorem cell21_37160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 6].length) (baseStart_37160 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_37160 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_37160 prefixEnd_37160 := by exact prefixLift 37160
  have htrace : WordTrace (prefixWord ++ tailWord_37160) baseStart_37160 baseEnd_37160 := by
    simpa [prefixWord, tailWord_37160, baseEnd_37160] using wordTrace_append hprefix tailTrace_37160
  have hstable : (prefixWord ++ tailWord_37160).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37160).length < 2 ^ (prefixWord ++ tailWord_37160).sum := by decide
  have hdescent : baseEnd_37160 < baseStart_37160 := by decide
  rcases family_descends (prefixWord ++ tailWord_37160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37177 : List Nat := [1, 2, 1, 6, 1, 2, 3, 1, 4]
def baseStart_37177 : Nat := 118140960795 + 37177 * 2 ^ 59
def prefixEnd_37177 : Nat := 4983230072969 + 3 ^ 40 * 37177 * 2
def baseEnd_37177 : Nat := 8484297907691679340681

theorem tailTrace_37177 : CollatzResearch.WordTrace tailWord_37177 prefixEnd_37177 8484297907691679340681 := by
  unfold tailWord_37177
  simp only [CollatzResearch.WordTrace]
  refine ⟨1355956586321553171213785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 903971057547702114142523 1355956586321553171213785)
  ·
    refine ⟨1016967439741164878410339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1355956586321553171213785 1016967439741164878410339)
    ·
      refine ⟨1525451159611747317615509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1016967439741164878410339 1525451159611747317615509)
      ·
        refine ⟨71505523106800655513227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1525451159611747317615509 71505523106800655513227)
        ·
          refine ⟨107258284660200983269841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71505523106800655513227 107258284660200983269841)
          ·
            refine ⟨80443713495150737452381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107258284660200983269841 80443713495150737452381)
            ·
              refine ⟨30166392560681526544643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80443713495150737452381 30166392560681526544643)
              ·
                refine ⟨45249588841022289816965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30166392560681526544643 45249588841022289816965)
                ·
                  refine ⟨8484297907691679340681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45249588841022289816965 8484297907691679340681)
                  ·
                    rfl

theorem cell21_37177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 1, 4].length) (baseStart_37177 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_37177 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_37177 prefixEnd_37177 := by exact prefixLift 37177
  have htrace : WordTrace (prefixWord ++ tailWord_37177) baseStart_37177 baseEnd_37177 := by
    simpa [prefixWord, tailWord_37177, baseEnd_37177] using wordTrace_append hprefix tailTrace_37177
  have hstable : (prefixWord ++ tailWord_37177).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37177).length < 2 ^ (prefixWord ++ tailWord_37177).sum := by decide
  have hdescent : baseEnd_37177 < baseStart_37177 := by decide
  rcases family_descends (prefixWord ++ tailWord_37177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37214 : List Nat := [4, 4, 2, 1, 2, 1, 1, 1, 5]
def baseStart_37214 : Nat := 118140960795 + 37214 * 2 ^ 59
def prefixEnd_37214 : Nat := 4983230072969 + 3 ^ 40 * 37214 * 2
def baseEnd_37214 : Nat := 8492741811787837223939

theorem tailTrace_37214 : CollatzResearch.WordTrace tailWord_37214 prefixEnd_37214 8492741811787837223939 := by
  unfold tailWord_37214
  simp only [CollatzResearch.WordTrace]
  refine ⟨169663260898438561288837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 904870724791672326873797 169663260898438561288837)
  ·
    refine ⟨31811861418457230241657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 169663260898438561288837 31811861418457230241657)
    ·
      refine ⟨23858896063842922681243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31811861418457230241657 23858896063842922681243)
      ·
        refine ⟨35788344095764384021865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23858896063842922681243 35788344095764384021865)
        ·
          refine ⟨26841258071823288016399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35788344095764384021865 26841258071823288016399)
          ·
            refine ⟨40261887107734932024599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26841258071823288016399 40261887107734932024599)
            ·
              refine ⟨60392830661602398036899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40261887107734932024599 60392830661602398036899)
              ·
                refine ⟨90589245992403597055349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60392830661602398036899 90589245992403597055349)
                ·
                  refine ⟨8492741811787837223939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 90589245992403597055349 8492741811787837223939)
                  ·
                    rfl

theorem cell21_37214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_37214 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_37214 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_37214 prefixEnd_37214 := by exact prefixLift 37214
  have htrace : WordTrace (prefixWord ++ tailWord_37214) baseStart_37214 baseEnd_37214 := by
    simpa [prefixWord, tailWord_37214, baseEnd_37214] using wordTrace_append hprefix tailTrace_37214
  have hstable : (prefixWord ++ tailWord_37214).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37214).length < 2 ^ (prefixWord ++ tailWord_37214).sum := by decide
  have hdescent : baseEnd_37214 < baseStart_37214 := by decide
  rcases family_descends (prefixWord ++ tailWord_37214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37219 : List Nat := [1, 1, 1, 5, 2, 1, 2, 4, 4]
def baseStart_37219 : Nat := 118140960795 + 37219 * 2 ^ 59
def prefixEnd_37219 : Nat := 4983230072969 + 3 ^ 40 * 37219 * 2
def baseEnd_37219 : Nat := 8493882879908939640595

theorem tailTrace_37219 : CollatzResearch.WordTrace tailWord_37219 prefixEnd_37219 8493882879908939640595 := by
  unfold tailWord_37219
  simp only [CollatzResearch.WordTrace]
  refine ⟨1357488452169394344242711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 904992301446262896161807 1357488452169394344242711)
  ·
    refine ⟨2036232678254091516364067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1357488452169394344242711 2036232678254091516364067)
    ·
      refine ⟨3054349017381137274546101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2036232678254091516364067 3054349017381137274546101)
      ·
        refine ⟨286345220379481619488697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3054349017381137274546101 286345220379481619488697)
        ·
          refine ⟨214758915284611214616523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 286345220379481619488697 214758915284611214616523)
          ·
            refine ⟨322138372926916821924785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214758915284611214616523 322138372926916821924785)
            ·
              refine ⟨241603779695187616443589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 322138372926916821924785 241603779695187616443589)
              ·
                refine ⟨45300708692847678083173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 241603779695187616443589 45300708692847678083173)
                ·
                  refine ⟨8493882879908939640595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45300708692847678083173 8493882879908939640595)
                  ·
                    rfl

theorem cell21_37219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 4, 4].length) (baseStart_37219 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_37219 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_37219 prefixEnd_37219 := by exact prefixLift 37219
  have htrace : WordTrace (prefixWord ++ tailWord_37219) baseStart_37219 baseEnd_37219 := by
    simpa [prefixWord, tailWord_37219, baseEnd_37219] using wordTrace_append hprefix tailTrace_37219
  have hstable : (prefixWord ++ tailWord_37219).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37219).length < 2 ^ (prefixWord ++ tailWord_37219).sum := by decide
  have hdescent : baseEnd_37219 < baseStart_37219 := by decide
  rcases family_descends (prefixWord ++ tailWord_37219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
