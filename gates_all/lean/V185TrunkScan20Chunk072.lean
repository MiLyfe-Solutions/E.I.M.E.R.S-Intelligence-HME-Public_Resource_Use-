import V185TrunkScan20Chunk071

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_437984 : List Nat := [2, 1, 1, 3, 1, 2, 2, 8]
def baseStart_437984 : Nat := 118140960795 + 437984 * 2 ^ 59
def prefixEnd_437984 : Nat := 4983230072969 + 3 ^ 40 * 437984 * 2
def baseEnd_437984 : Nat := 66635943993753961269853

theorem tailTrace_437984 : CollatzResearch.WordTrace tailWord_437984 prefixEnd_437984 66635943993753961269853 := by
  unfold tailWord_437984
  simp only [CollatzResearch.WordTrace]
  refine ⟨7987294422633122278520503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10649725896844163038027337 7987294422633122278520503)
  ·
    refine ⟨11980941633949683417780755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7987294422633122278520503 11980941633949683417780755)
    ·
      refine ⟨17971412450924525126671133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11980941633949683417780755 17971412450924525126671133)
      ·
        refine ⟨6739279669096696922501675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17971412450924525126671133 6739279669096696922501675)
        ·
          refine ⟨10108919503645045383752513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6739279669096696922501675 10108919503645045383752513)
          ·
            refine ⟨7581689627733784037814385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10108919503645045383752513 7581689627733784037814385)
            ·
              refine ⟨5686267220800338028360789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7581689627733784037814385 5686267220800338028360789)
              ·
                refine ⟨66635943993753961269853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5686267220800338028360789 66635943993753961269853)
                ·
                  rfl

theorem cell20_437984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 8].length) (baseStart_437984 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_437984 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_437984 prefixEnd_437984 := by exact prefixLift 437984
  have htrace : WordTrace (prefixWord ++ tailWord_437984) baseStart_437984 baseEnd_437984 := by
    simpa [prefixWord, tailWord_437984, baseEnd_437984] using wordTrace_append hprefix tailTrace_437984
  have hstable : (prefixWord ++ tailWord_437984).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437984).length < 2 ^ (prefixWord ++ tailWord_437984).sum := by decide
  have hdescent : baseEnd_437984 < baseStart_437984 := by decide
  rcases family_descends (prefixWord ++ tailWord_437984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438008 : List Nat := [2, 1, 2, 1, 1, 2, 2, 6, 3]
def baseStart_438008 : Nat := 118140960795 + 438008 * 2 ^ 59
def prefixEnd_438008 : Nat := 4983230072969 + 3 ^ 40 * 438008 * 2
def baseEnd_438008 : Nat := 199918786235224467009461

theorem tailTrace_438008 : CollatzResearch.WordTrace tailWord_438008 prefixEnd_438008 199918786235224467009461 := by
  unfold tailWord_438008
  simp only [CollatzResearch.WordTrace]
  refine ⟨7987732098589648327957339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10650309464786197770609785 7987732098589648327957339)
  ·
    refine ⟨11981598147884472491936009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7987732098589648327957339 11981598147884472491936009)
    ·
      refine ⟨8986198610913354368952007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11981598147884472491936009 8986198610913354368952007)
      ·
        refine ⟨13479297916370031553428011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8986198610913354368952007 13479297916370031553428011)
        ·
          refine ⟨20218946874555047330142017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13479297916370031553428011 20218946874555047330142017)
          ·
            refine ⟨15164210155916285497606513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20218946874555047330142017 15164210155916285497606513)
            ·
              refine ⟨11373157616937214123204885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15164210155916285497606513 11373157616937214123204885)
              ·
                refine ⟨533116763293931912025229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11373157616937214123204885 533116763293931912025229)
                ·
                  refine ⟨199918786235224467009461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 533116763293931912025229 199918786235224467009461)
                  ·
                    rfl

theorem cell20_438008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 6, 3].length) (baseStart_438008 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_438008 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_438008 prefixEnd_438008 := by exact prefixLift 438008
  have htrace : WordTrace (prefixWord ++ tailWord_438008) baseStart_438008 baseEnd_438008 := by
    simpa [prefixWord, tailWord_438008, baseEnd_438008] using wordTrace_append hprefix tailTrace_438008
  have hstable : (prefixWord ++ tailWord_438008).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438008).length < 2 ^ (prefixWord ++ tailWord_438008).sum := by decide
  have hdescent : baseEnd_438008 < baseStart_438008 := by decide
  rcases family_descends (prefixWord ++ tailWord_438008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438015 : List Nat := [1, 1, 2, 2, 1, 3, 3, 3, 4]
def baseStart_438015 : Nat := 118140960795 + 438015 * 2 ^ 59
def prefixEnd_438015 : Nat := 4983230072969 + 3 ^ 40 * 438015 * 2
def baseEnd_438015 : Nat := 199921981225963553776099

theorem tailTrace_438015 : CollatzResearch.WordTrace tailWord_438015 prefixEnd_438015 199921981225963553776099 := by
  unfold tailWord_438015
  simp only [CollatzResearch.WordTrace]
  refine ⟨15975719508153936851419499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10650479672102624567612999 15975719508153936851419499)
  ·
    refine ⟨23963579262230905277129249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15975719508153936851419499 23963579262230905277129249)
    ·
      refine ⟨17972684446673178957846937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23963579262230905277129249 17972684446673178957846937)
      ·
        refine ⟨13479513335004884218385203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17972684446673178957846937 13479513335004884218385203)
        ·
          refine ⟨20219270002507326327577805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13479513335004884218385203 20219270002507326327577805)
          ·
            refine ⟨7582226250940247372841677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20219270002507326327577805 7582226250940247372841677)
            ·
              refine ⟨2843334844102592764815629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7582226250940247372841677 2843334844102592764815629)
              ·
                refine ⟨1066250566538472286805861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2843334844102592764815629 1066250566538472286805861)
                ·
                  refine ⟨199921981225963553776099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1066250566538472286805861 199921981225963553776099)
                  ·
                    rfl

theorem cell20_438015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 4].length) (baseStart_438015 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_438015 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_438015 prefixEnd_438015 := by exact prefixLift 438015
  have htrace : WordTrace (prefixWord ++ tailWord_438015) baseStart_438015 baseEnd_438015 := by
    simpa [prefixWord, tailWord_438015, baseEnd_438015] using wordTrace_append hprefix tailTrace_438015
  have hstable : (prefixWord ++ tailWord_438015).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438015).length < 2 ^ (prefixWord ++ tailWord_438015).sum := by decide
  have hdescent : baseEnd_438015 < baseStart_438015 := by decide
  rcases family_descends (prefixWord ++ tailWord_438015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438039 : List Nat := [1, 1, 3, 4, 2, 2, 1, 6]
def baseStart_438039 : Nat := 118140960795 + 438039 * 2 ^ 59
def prefixEnd_438039 : Nat := 4983230072969 + 3 ^ 40 * 438039 * 2
def baseEnd_438039 : Nat := 66644311826642045658667

theorem tailTrace_438039 : CollatzResearch.WordTrace tailWord_438039 prefixEnd_438039 66644311826642045658667 := by
  unfold tailWord_438039
  simp only [CollatzResearch.WordTrace]
  refine ⟨15976594860066988950293171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10651063240044659300195447 15976594860066988950293171)
  ·
    refine ⟨23964892290100483425439757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15976594860066988950293171 23964892290100483425439757)
    ·
      refine ⟨8986834608787681284539909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23964892290100483425439757 8986834608787681284539909)
      ·
        refine ⟨1685031489147690240851233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8986834608787681284539909 1685031489147690240851233)
        ·
          refine ⟨1263773616860767680638425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1685031489147690240851233 1263773616860767680638425)
          ·
            refine ⟨947830212645575760478819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1263773616860767680638425 947830212645575760478819)
            ·
              refine ⟨1421745318968363640718229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 947830212645575760478819 1421745318968363640718229)
              ·
                refine ⟨66644311826642045658667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1421745318968363640718229 66644311826642045658667)
                ·
                  rfl

theorem cell20_438039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 6].length) (baseStart_438039 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_438039 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_438039 prefixEnd_438039 := by exact prefixLift 438039
  have htrace : WordTrace (prefixWord ++ tailWord_438039) baseStart_438039 baseEnd_438039 := by
    simpa [prefixWord, tailWord_438039, baseEnd_438039] using wordTrace_append hprefix tailTrace_438039
  have hstable : (prefixWord ++ tailWord_438039).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438039).length < 2 ^ (prefixWord ++ tailWord_438039).sum := by decide
  have hdescent : baseEnd_438039 < baseStart_438039 := by decide
  rcases family_descends (prefixWord ++ tailWord_438039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438049 : List Nat := [1, 2, 3, 2, 1, 3, 3, 3, 2]
def baseStart_438049 : Nat := 118140960795 + 438049 * 2 ^ 59
def prefixEnd_438049 : Nat := 4983230072969 + 3 ^ 40 * 438049 * 2
def baseEnd_438049 : Nat := 199937499752410546642627

theorem tailTrace_438049 : CollatzResearch.WordTrace tailWord_438049 prefixEnd_438049 199937499752410546642627 := by
  unfold tailWord_438049
  simp only [CollatzResearch.WordTrace]
  refine ⟨15976959590030760658157201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10651306393353840438771467 15976959590030760658157201)
  ·
    refine ⟨11982719692523070493617901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15976959590030760658157201 11982719692523070493617901)
    ·
      refine ⟨4493519884696151435106713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11982719692523070493617901 4493519884696151435106713)
      ·
        refine ⟨3370139913522113576330035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4493519884696151435106713 3370139913522113576330035)
        ·
          refine ⟨5055209870283170364495053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3370139913522113576330035 5055209870283170364495053)
          ·
            refine ⟨1895703701356188886685645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5055209870283170364495053 1895703701356188886685645)
            ·
              refine ⟨710888888008570832507117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1895703701356188886685645 710888888008570832507117)
              ·
                refine ⟨266583333003214062190169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 710888888008570832507117 266583333003214062190169)
                ·
                  refine ⟨199937499752410546642627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 266583333003214062190169 199937499752410546642627)
                  ·
                    rfl

theorem cell20_438049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 3, 2].length) (baseStart_438049 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_438049 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_438049 prefixEnd_438049 := by exact prefixLift 438049
  have htrace : WordTrace (prefixWord ++ tailWord_438049) baseStart_438049 baseEnd_438049 := by
    simpa [prefixWord, tailWord_438049, baseEnd_438049] using wordTrace_append hprefix tailTrace_438049
  have hstable : (prefixWord ++ tailWord_438049).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438049).length < 2 ^ (prefixWord ++ tailWord_438049).sum := by decide
  have hdescent : baseEnd_438049 < baseStart_438049 := by decide
  rcases family_descends (prefixWord ++ tailWord_438049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438060 : List Nat := [2, 2, 1, 1, 1, 5, 8]
def baseStart_438060 : Nat := 118140960795 + 438060 * 2 ^ 59
def prefixEnd_438060 : Nat := 4983230072969 + 3 ^ 40 * 438060 * 2
def baseEnd_438060 : Nat := 22215835605793710808435

theorem tailTrace_438060 : CollatzResearch.WordTrace tailWord_438060 prefixEnd_438060 22215835605793710808435 := by
  unfold tailWord_438060
  simp only [CollatzResearch.WordTrace]
  refine ⟨7988680396495454768403817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10651573861993939691205089 7988680396495454768403817)
  ·
    refine ⟨5991510297371591076302863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7988680396495454768403817 5991510297371591076302863)
    ·
      refine ⟨8987265446057386614454295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5991510297371591076302863 8987265446057386614454295)
      ·
        refine ⟨13480898169086079921681443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8987265446057386614454295 13480898169086079921681443)
        ·
          refine ⟨20221347253629119882522165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13480898169086079921681443 20221347253629119882522165)
          ·
            refine ⟨1895751305027729988986453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20221347253629119882522165 1895751305027729988986453)
            ·
              refine ⟨22215835605793710808435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1895751305027729988986453 22215835605793710808435)
              ·
                rfl

theorem cell20_438060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 8].length) (baseStart_438060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_438060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_438060 prefixEnd_438060 := by exact prefixLift 438060
  have htrace : WordTrace (prefixWord ++ tailWord_438060) baseStart_438060 baseEnd_438060 := by
    simpa [prefixWord, tailWord_438060, baseEnd_438060] using wordTrace_append hprefix tailTrace_438060
  have hstable : (prefixWord ++ tailWord_438060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438060).length < 2 ^ (prefixWord ++ tailWord_438060).sum := by decide
  have hdescent : baseEnd_438060 < baseStart_438060 := by decide
  rcases family_descends (prefixWord ++ tailWord_438060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438066 : List Nat := [3, 2, 1, 1, 3, 3, 3, 2, 2]
def baseStart_438066 : Nat := 118140960795 + 438066 * 2 ^ 59
def prefixEnd_438066 : Nat := 4983230072969 + 3 ^ 40 * 438066 * 2
def baseEnd_438066 : Nat := 199945259015634043075891

theorem tailTrace_438066 : CollatzResearch.WordTrace tailWord_438066 prefixEnd_438066 199945259015634043075891 := by
  unfold tailWord_438066
  simp only [CollatzResearch.WordTrace]
  refine ⟨3994394907742293140381513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10651719753979448374350701 3994394907742293140381513)
  ·
    refine ⟨2995796180806719855286135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3994394907742293140381513 2995796180806719855286135)
    ·
      refine ⟨4493694271210079782929203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2995796180806719855286135 4493694271210079782929203)
      ·
        refine ⟨6740541406815119674393805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4493694271210079782929203 6740541406815119674393805)
        ·
          refine ⟨2527703027555669877897677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6740541406815119674393805 2527703027555669877897677)
          ·
            refine ⟨947888635333376204211629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2527703027555669877897677 947888635333376204211629)
            ·
              refine ⟨355458238250016076579361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 947888635333376204211629 355458238250016076579361)
              ·
                refine ⟨266593678687512057434521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 355458238250016076579361 266593678687512057434521)
                ·
                  refine ⟨199945259015634043075891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 266593678687512057434521 199945259015634043075891)
                  ·
                    rfl

theorem cell20_438066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 2, 2].length) (baseStart_438066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_438066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_438066 prefixEnd_438066 := by exact prefixLift 438066
  have htrace : WordTrace (prefixWord ++ tailWord_438066) baseStart_438066 baseEnd_438066 := by
    simpa [prefixWord, tailWord_438066, baseEnd_438066] using wordTrace_append hprefix tailTrace_438066
  have hstable : (prefixWord ++ tailWord_438066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438066).length < 2 ^ (prefixWord ++ tailWord_438066).sum := by decide
  have hdescent : baseEnd_438066 < baseStart_438066 := by decide
  rcases family_descends (prefixWord ++ tailWord_438066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438077 : List Nat := [1, 4, 1, 4, 1, 1, 1, 7]
def baseStart_438077 : Nat := 118140960795 + 438077 * 2 ^ 59
def prefixEnd_438077 : Nat := 4983230072969 + 3 ^ 40 * 438077 * 2
def baseEnd_438077 : Nat := 66650093238455631236393

theorem tailTrace_438077 : CollatzResearch.WordTrace tailWord_438077 prefixEnd_438077 66650093238455631236393 := by
  unfold tailWord_438077
  simp only [CollatzResearch.WordTrace]
  refine ⟨15977980833929321440176485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10651987222619547626784323 15977980833929321440176485)
  ·
    refine ⟨2995871406361747770033091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15977980833929321440176485 2995871406361747770033091)
    ·
      refine ⟨4493807109542621655049637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2995871406361747770033091 4493807109542621655049637)
      ·
        refine ⟨842588833039241560321807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4493807109542621655049637 842588833039241560321807)
        ·
          refine ⟨1263883249558862340482711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 842588833039241560321807 1263883249558862340482711)
          ·
            refine ⟨1895824874338293510724067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1263883249558862340482711 1895824874338293510724067)
            ·
              refine ⟨2843737311507440266086101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1895824874338293510724067 2843737311507440266086101)
              ·
                refine ⟨66650093238455631236393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2843737311507440266086101 66650093238455631236393)
                ·
                  rfl

theorem cell20_438077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 7].length) (baseStart_438077 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_438077 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_438077 prefixEnd_438077 := by exact prefixLift 438077
  have htrace : WordTrace (prefixWord ++ tailWord_438077) baseStart_438077 baseEnd_438077 := by
    simpa [prefixWord, tailWord_438077, baseEnd_438077] using wordTrace_append hprefix tailTrace_438077
  have hstable : (prefixWord ++ tailWord_438077).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438077).length < 2 ^ (prefixWord ++ tailWord_438077).sum := by decide
  have hdescent : baseEnd_438077 < baseStart_438077 := by decide
  rcases family_descends (prefixWord ++ tailWord_438077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438115 : List Nat := [1, 1, 1, 5, 5, 7]
def baseStart_438115 : Nat := 118140960795 + 438115 * 2 ^ 59
def prefixEnd_438115 : Nat := 4983230072969 + 3 ^ 40 * 438115 * 2
def baseEnd_438115 : Nat := 7406208294474357423791

theorem tailTrace_438115 : CollatzResearch.WordTrace tailWord_438115 prefixEnd_438115 7406208294474357423791 := by
  unfold tailWord_438115
  simp only [CollatzResearch.WordTrace]
  refine ⟨15979366807791653930059799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10652911205194435953373199 15979366807791653930059799)
  ·
    refine ⟨23969050211687480895089699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15979366807791653930059799 23969050211687480895089699)
    ·
      refine ⟨35953575317531221342634549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23969050211687480895089699 35953575317531221342634549)
      ·
        refine ⟨3370647686018552000871989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35953575317531221342634549 3370647686018552000871989)
        ·
          refine ⟨315998220564239250081749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3370647686018552000871989 315998220564239250081749)
          ·
            refine ⟨7406208294474357423791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 315998220564239250081749 7406208294474357423791)
            ·
              rfl

theorem cell20_438115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 7].length) (baseStart_438115 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_438115 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_438115 prefixEnd_438115 := by exact prefixLift 438115
  have htrace : WordTrace (prefixWord ++ tailWord_438115) baseStart_438115 baseEnd_438115 := by
    simpa [prefixWord, tailWord_438115, baseEnd_438115] using wordTrace_append hprefix tailTrace_438115
  have hstable : (prefixWord ++ tailWord_438115).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438115).length < 2 ^ (prefixWord ++ tailWord_438115).sum := by decide
  have hdescent : baseEnd_438115 < baseStart_438115 := by decide
  rcases family_descends (prefixWord ++ tailWord_438115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438129 : List Nat := [1, 2, 2, 2, 1, 3, 2, 3, 4]
def baseStart_438129 : Nat := 118140960795 + 438129 * 2 ^ 59
def prefixEnd_438129 : Nat := 4983230072969 + 3 ^ 40 * 438129 * 2
def baseEnd_438129 : Nat := 199974013932285823975633

theorem tailTrace_438129 : CollatzResearch.WordTrace tailWord_438129 prefixEnd_438129 199974013932285823975633 := by
  unfold tailWord_438129
  simp only [CollatzResearch.WordTrace]
  refine ⟨15979877429740934321069441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10653251619827289547379627 15979877429740934321069441)
  ·
    refine ⟨11984908072305700740802081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15979877429740934321069441 11984908072305700740802081)
    ·
      refine ⟨8988681054229275555601561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11984908072305700740802081 8988681054229275555601561)
      ·
        refine ⟨6741510790671956666701171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8988681054229275555601561 6741510790671956666701171)
        ·
          refine ⟨10112266186007935000051757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6741510790671956666701171 10112266186007935000051757)
          ·
            refine ⟨3792099819752975625019409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10112266186007935000051757 3792099819752975625019409)
            ·
              refine ⟨2844074864814731718764557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3792099819752975625019409 2844074864814731718764557)
              ·
                refine ⟨1066528074305524394536709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2844074864814731718764557 1066528074305524394536709)
                ·
                  refine ⟨199974013932285823975633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1066528074305524394536709 199974013932285823975633)
                  ·
                    rfl

theorem cell20_438129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 4].length) (baseStart_438129 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_438129 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_438129 prefixEnd_438129 := by exact prefixLift 438129
  have htrace : WordTrace (prefixWord ++ tailWord_438129) baseStart_438129 baseEnd_438129 := by
    simpa [prefixWord, tailWord_438129, baseEnd_438129] using wordTrace_append hprefix tailTrace_438129
  have hstable : (prefixWord ++ tailWord_438129).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438129).length < 2 ^ (prefixWord ++ tailWord_438129).sum := by decide
  have hdescent : baseEnd_438129 < baseStart_438129 := by decide
  rcases family_descends (prefixWord ++ tailWord_438129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438143 : List Nat := [1, 1, 2, 2, 1, 1, 3, 2, 7]
def baseStart_438143 : Nat := 118140960795 + 438143 * 2 ^ 59
def prefixEnd_438143 : Nat := 4983230072969 + 3 ^ 40 * 438143 * 2
def baseEnd_438143 : Nat := 199980403913763997508909

theorem tailTrace_438143 : CollatzResearch.WordTrace tailWord_438143 prefixEnd_438143 199980403913763997508909 := by
  unfold tailWord_438143
  simp only [CollatzResearch.WordTrace]
  refine ⟨15980388051690214712079083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10653592034460143141386055 15980388051690214712079083)
  ·
    refine ⟨23970582077535322068118625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15980388051690214712079083 23970582077535322068118625)
    ·
      refine ⟨17977936558151491551088969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23970582077535322068118625 17977936558151491551088969)
      ·
        refine ⟨13483452418613618663316727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17977936558151491551088969 13483452418613618663316727)
        ·
          refine ⟨20225178627920427994975091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13483452418613618663316727 20225178627920427994975091)
          ·
            refine ⟨30337767941880641992462637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20225178627920427994975091 30337767941880641992462637)
            ·
              refine ⟨11376662978205240747173489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30337767941880641992462637 11376662978205240747173489)
              ·
                refine ⟨8532497233653930560380117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11376662978205240747173489 8532497233653930560380117)
                ·
                  refine ⟨199980403913763997508909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8532497233653930560380117 199980403913763997508909)
                  ·
                    rfl

theorem cell20_438143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 7].length) (baseStart_438143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_438143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_438143 prefixEnd_438143 := by exact prefixLift 438143
  have htrace : WordTrace (prefixWord ++ tailWord_438143) baseStart_438143 baseEnd_438143 := by
    simpa [prefixWord, tailWord_438143, baseEnd_438143] using wordTrace_append hprefix tailTrace_438143
  have hstable : (prefixWord ++ tailWord_438143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438143).length < 2 ^ (prefixWord ++ tailWord_438143).sum := by decide
  have hdescent : baseEnd_438143 < baseStart_438143 := by decide
  rcases family_descends (prefixWord ++ tailWord_438143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438153 : List Nat := [1, 2, 1, 1, 5, 1, 5, 4]
def baseStart_438153 : Nat := 118140960795 + 438153 * 2 ^ 59
def prefixEnd_438153 : Nat := 4983230072969 + 3 ^ 40 * 438153 * 2
def baseEnd_438153 : Nat := 66661656062082802391845

theorem tailTrace_438153 : CollatzResearch.WordTrace tailWord_438153 prefixEnd_438153 66661656062082802391845 := by
  unfold tailWord_438153
  simp only [CollatzResearch.WordTrace]
  refine ⟨15980752781653986419943113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10653835187769324279962075 15980752781653986419943113)
  ·
    refine ⟨11985564586240489814957335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15980752781653986419943113 11985564586240489814957335)
    ·
      refine ⟨17978346879360734722436003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11985564586240489814957335 17978346879360734722436003)
      ·
        refine ⟨26967520319041102083654005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17978346879360734722436003 26967520319041102083654005)
        ·
          refine ⟨2528205029910103320342563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26967520319041102083654005 2528205029910103320342563)
          ·
            refine ⟨3792307544865154980513845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2528205029910103320342563 3792307544865154980513845)
            ·
              refine ⟨355528832331108279423173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3792307544865154980513845 355528832331108279423173)
              ·
                refine ⟨66661656062082802391845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 355528832331108279423173 66661656062082802391845)
                ·
                  rfl

theorem cell20_438153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 4].length) (baseStart_438153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_438153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_438153 prefixEnd_438153 := by exact prefixLift 438153
  have htrace : WordTrace (prefixWord ++ tailWord_438153) baseStart_438153 baseEnd_438153 := by
    simpa [prefixWord, tailWord_438153, baseEnd_438153] using wordTrace_append hprefix tailTrace_438153
  have hstable : (prefixWord ++ tailWord_438153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438153).length < 2 ^ (prefixWord ++ tailWord_438153).sum := by decide
  have hdescent : baseEnd_438153 < baseStart_438153 := by decide
  rcases family_descends (prefixWord ++ tailWord_438153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438177 : List Nat := [1, 2, 3, 4, 2, 1, 1, 1, 5]
def baseStart_438177 : Nat := 118140960795 + 438177 * 2 ^ 59
def prefixEnd_438177 : Nat := 4983230072969 + 3 ^ 40 * 438177 * 2
def baseEnd_438177 : Nat := 199995922440210990375437

theorem tailTrace_438177 : CollatzResearch.WordTrace tailWord_438177 prefixEnd_438177 199995922440210990375437 := by
  unfold tailWord_438177
  simp only [CollatzResearch.WordTrace]
  refine ⟨15981628133567038518816785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10654418755711359012544523 15981628133567038518816785)
  ·
    refine ⟨11986221100175278889112589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15981628133567038518816785 11986221100175278889112589)
    ·
      refine ⟨4494832912565729583417221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11986221100175278889112589 4494832912565729583417221)
      ·
        refine ⟨842781171106074296890729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4494832912565729583417221 842781171106074296890729)
        ·
          refine ⟨632085878329555722668047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 842781171106074296890729 632085878329555722668047)
          ·
            refine ⟨948128817494333584002071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 632085878329555722668047 948128817494333584002071)
            ·
              refine ⟨1422193226241500376003107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 948128817494333584002071 1422193226241500376003107)
              ·
                refine ⟨2133289839362250564004661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1422193226241500376003107 2133289839362250564004661)
                ·
                  refine ⟨199995922440210990375437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2133289839362250564004661 199995922440210990375437)
                  ·
                    rfl

theorem cell20_438177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 5].length) (baseStart_438177 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_438177 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_438177 prefixEnd_438177 := by exact prefixLift 438177
  have htrace : WordTrace (prefixWord ++ tailWord_438177) baseStart_438177 baseEnd_438177 := by
    simpa [prefixWord, tailWord_438177, baseEnd_438177] using wordTrace_append hprefix tailTrace_438177
  have hstable : (prefixWord ++ tailWord_438177).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438177).length < 2 ^ (prefixWord ++ tailWord_438177).sum := by decide
  have hdescent : baseEnd_438177 < baseStart_438177 := by decide
  rcases family_descends (prefixWord ++ tailWord_438177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438204 : List Nat := [2, 2, 2, 5, 2, 1, 2, 4]
def baseStart_438204 : Nat := 118140960795 + 438204 * 2 ^ 59
def prefixEnd_438204 : Nat := 4983230072969 + 3 ^ 40 * 438204 * 2
def baseEnd_438204 : Nat := 66669415325306298825109

theorem tailTrace_438204 : CollatzResearch.WordTrace tailWord_438204 prefixEnd_438204 66669415325306298825109 := by
  unfold tailWord_438204
  simp only [CollatzResearch.WordTrace]
  refine ⟨7991306452234611065024833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10655075269646148086699777 7991306452234611065024833)
  ·
    refine ⟨5993479839175958298768625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7991306452234611065024833 5993479839175958298768625)
    ·
      refine ⟨4495109879381968724076469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5993479839175958298768625 4495109879381968724076469)
      ·
        refine ⟨421416551192059567882169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4495109879381968724076469 421416551192059567882169)
        ·
          refine ⟨316062413394044675911627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 421416551192059567882169 316062413394044675911627)
          ·
            refine ⟨474093620091067013867441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316062413394044675911627 474093620091067013867441)
            ·
              refine ⟨355570215068300260400581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 474093620091067013867441 355570215068300260400581)
              ·
                refine ⟨66669415325306298825109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 355570215068300260400581 66669415325306298825109)
                ·
                  rfl

theorem cell20_438204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 4].length) (baseStart_438204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_438204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_438204 prefixEnd_438204 := by exact prefixLift 438204
  have htrace : WordTrace (prefixWord ++ tailWord_438204) baseStart_438204 baseEnd_438204 := by
    simpa [prefixWord, tailWord_438204, baseEnd_438204] using wordTrace_append hprefix tailTrace_438204
  have hstable : (prefixWord ++ tailWord_438204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438204).length < 2 ^ (prefixWord ++ tailWord_438204).sum := by decide
  have hdescent : baseEnd_438204 < baseStart_438204 := by decide
  rcases family_descends (prefixWord ++ tailWord_438204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438219 : List Nat := [1, 1, 1, 1, 3, 4, 1, 1, 7]
def baseStart_438219 : Nat := 118140960795 + 438219 * 2 ^ 59
def prefixEnd_438219 : Nat := 4983230072969 + 3 ^ 40 * 438219 * 2
def baseEnd_438219 : Nat := 200015092384645510975265

theorem tailTrace_438219 : CollatzResearch.WordTrace tailWord_438219 prefixEnd_438219 200015092384645510975265 := by
  unfold tailWord_438219
  simp only [CollatzResearch.WordTrace]
  refine ⟨15983159999414879691845711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10655439999609919794563807 15983159999414879691845711)
  ·
    refine ⟨23974739999122319537768567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15983159999414879691845711 23974739999122319537768567)
    ·
      refine ⟨35962109998683479306652851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23974739999122319537768567 35962109998683479306652851)
      ·
        refine ⟨53943164998025218959979277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35962109998683479306652851 53943164998025218959979277)
        ·
          refine ⟨20228686874259457109992229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53943164998025218959979277 20228686874259457109992229)
          ·
            refine ⟨3792878788923648208123543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20228686874259457109992229 3792878788923648208123543)
            ·
              refine ⟨5689318183385472312185315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3792878788923648208123543 5689318183385472312185315)
              ·
                refine ⟨8533977275078208468277973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5689318183385472312185315 8533977275078208468277973)
                ·
                  refine ⟨200015092384645510975265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8533977275078208468277973 200015092384645510975265)
                  ·
                    rfl

theorem cell20_438219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 7].length) (baseStart_438219 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_438219 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_438219 prefixEnd_438219 := by exact prefixLift 438219
  have htrace : WordTrace (prefixWord ++ tailWord_438219) baseStart_438219 baseEnd_438219 := by
    simpa [prefixWord, tailWord_438219, baseEnd_438219] using wordTrace_append hprefix tailTrace_438219
  have hstable : (prefixWord ++ tailWord_438219).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438219).length < 2 ^ (prefixWord ++ tailWord_438219).sum := by decide
  have hdescent : baseEnd_438219 < baseStart_438219 := by decide
  rcases family_descends (prefixWord ++ tailWord_438219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438229 : List Nat := [1, 3, 2, 3, 2, 3, 6]
def baseStart_438229 : Nat := 118140960795 + 438229 * 2 ^ 59
def prefixEnd_438229 : Nat := 4983230072969 + 3 ^ 40 * 438229 * 2
def baseEnd_438229 : Nat := 22224406295236657849099

theorem tailTrace_438229 : CollatzResearch.WordTrace tailWord_438229 prefixEnd_438229 22224406295236657849099 := by
  unfold tailWord_438229
  simp only [CollatzResearch.WordTrace]
  refine ⟨15983524729378651399709741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10655683152919100933139827 15983524729378651399709741)
  ·
    refine ⟨5993821773516994274891153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15983524729378651399709741 5993821773516994274891153)
    ·
      refine ⟨4495366330137745706168365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5993821773516994274891153 4495366330137745706168365)
      ·
        refine ⟨1685762373801654639813137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4495366330137745706168365 1685762373801654639813137)
        ·
          refine ⟨1264321780351240979859853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1685762373801654639813137 1264321780351240979859853)
          ·
            refine ⟨474120667631715367447445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1264321780351240979859853 474120667631715367447445)
            ·
              refine ⟨22224406295236657849099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 474120667631715367447445 22224406295236657849099)
              ·
                rfl

theorem cell20_438229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 6].length) (baseStart_438229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_438229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_438229 prefixEnd_438229 := by exact prefixLift 438229
  have htrace : WordTrace (prefixWord ++ tailWord_438229) baseStart_438229 baseEnd_438229 := by
    simpa [prefixWord, tailWord_438229, baseEnd_438229] using wordTrace_append hprefix tailTrace_438229
  have hstable : (prefixWord ++ tailWord_438229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438229).length < 2 ^ (prefixWord ++ tailWord_438229).sum := by decide
  have hdescent : baseEnd_438229 < baseStart_438229 := by decide
  rcases family_descends (prefixWord ++ tailWord_438229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438336 : List Nat := [2, 1, 1, 2, 2, 4, 1, 5, 2]
def baseStart_438336 : Nat := 118140960795 + 438336 * 2 ^ 59
def prefixEnd_438336 : Nat := 4983230072969 + 3 ^ 40 * 438336 * 2
def baseEnd_438336 : Nat := 200068494372713104074787

theorem tailTrace_438336 : CollatzResearch.WordTrace tailWord_438336 prefixEnd_438336 200068494372713104074787 := by
  unfold tailWord_438336
  simp only [CollatzResearch.WordTrace]
  refine ⟨7993713669995504336927431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10658284893327339115903241 7993713669995504336927431)
  ·
    refine ⟨11990570504993256505391147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7993713669995504336927431 11990570504993256505391147)
    ·
      refine ⟨17985855757489884758086721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11990570504993256505391147 17985855757489884758086721)
      ·
        refine ⟨13489391818117413568565041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17985855757489884758086721 13489391818117413568565041)
        ·
          refine ⟨10117043863588060176423781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13489391818117413568565041 10117043863588060176423781)
          ·
            refine ⟨1896945724422761283079459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10117043863588060176423781 1896945724422761283079459)
            ·
              refine ⟨2845418586634141924619189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1896945724422761283079459 2845418586634141924619189)
              ·
                refine ⟨266757992496950805433049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2845418586634141924619189 266757992496950805433049)
                ·
                  refine ⟨200068494372713104074787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 266757992496950805433049 200068494372713104074787)
                  ·
                    rfl

theorem cell20_438336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 5, 2].length) (baseStart_438336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_438336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_438336 prefixEnd_438336 := by exact prefixLift 438336
  have htrace : WordTrace (prefixWord ++ tailWord_438336) baseStart_438336 baseEnd_438336 := by
    simpa [prefixWord, tailWord_438336, baseEnd_438336] using wordTrace_append hprefix tailTrace_438336
  have hstable : (prefixWord ++ tailWord_438336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438336).length < 2 ^ (prefixWord ++ tailWord_438336).sum := by decide
  have hdescent : baseEnd_438336 < baseStart_438336 := by decide
  rcases family_descends (prefixWord ++ tailWord_438336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438350 : List Nat := [4, 1, 1, 1, 1, 5, 1, 1, 5]
def baseStart_438350 : Nat := 118140960795 + 438350 * 2 ^ 59
def prefixEnd_438350 : Nat := 4983230072969 + 3 ^ 40 * 438350 * 2
def baseEnd_438350 : Nat := 200074884354191277608063

theorem tailTrace_438350 : CollatzResearch.WordTrace tailWord_438350 prefixEnd_438350 200074884354191277608063 := by
  unfold tailWord_438350
  simp only [CollatzResearch.WordTrace]
  refine ⟨1998492245242536133108063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10658625307960192709909669 1998492245242536133108063)
  ·
    refine ⟨2997738367863804199662095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1998492245242536133108063 2997738367863804199662095)
    ·
      refine ⟨4496607551795706299493143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2997738367863804199662095 4496607551795706299493143)
      ·
        refine ⟨6744911327693559449239715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4496607551795706299493143 6744911327693559449239715)
        ·
          refine ⟨10117366991540339173859573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6744911327693559449239715 10117366991540339173859573)
          ·
            refine ⟨948503155456906797549335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10117366991540339173859573 948503155456906797549335)
            ·
              refine ⟨1422754733185360196324003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 948503155456906797549335 1422754733185360196324003)
              ·
                refine ⟨2134132099778040294486005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1422754733185360196324003 2134132099778040294486005)
                ·
                  refine ⟨200074884354191277608063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2134132099778040294486005 200074884354191277608063)
                  ·
                    rfl

theorem cell20_438350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_438350 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_438350 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_438350 prefixEnd_438350 := by exact prefixLift 438350
  have htrace : WordTrace (prefixWord ++ tailWord_438350) baseStart_438350 baseEnd_438350 := by
    simpa [prefixWord, tailWord_438350, baseEnd_438350] using wordTrace_append hprefix tailTrace_438350
  have hstable : (prefixWord ++ tailWord_438350).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438350).length < 2 ^ (prefixWord ++ tailWord_438350).sum := by decide
  have hdescent : baseEnd_438350 < baseStart_438350 := by decide
  rcases family_descends (prefixWord ++ tailWord_438350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438357 : List Nat := [1, 3, 2, 2, 1, 3, 1, 3, 4]
def baseStart_438357 : Nat := 118140960795 + 438357 * 2 ^ 59
def prefixEnd_438357 : Nat := 4983230072969 + 3 ^ 40 * 438357 * 2
def baseEnd_438357 : Nat := 200078079344930364374701

theorem tailTrace_438357 : CollatzResearch.WordTrace tailWord_438357 prefixEnd_438357 200078079344930364374701 := by
  unfold tailWord_438357
  simp only [CollatzResearch.WordTrace]
  refine ⟨15988193272914929260369325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10658795515276619506912883 15988193272914929260369325)
  ·
    refine ⟨5995572477343098472638497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15988193272914929260369325 5995572477343098472638497)
    ·
      refine ⟨4496679358007323854478873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5995572477343098472638497 4496679358007323854478873)
      ·
        refine ⟨3372509518505492890859155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4496679358007323854478873 3372509518505492890859155)
        ·
          refine ⟨5058764277758239336288733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3372509518505492890859155 5058764277758239336288733)
          ·
            refine ⟨1897036604159339751108275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5058764277758239336288733 1897036604159339751108275)
            ·
              refine ⟨2845554906239009626662413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1897036604159339751108275 2845554906239009626662413)
              ·
                refine ⟨1067083089839628609998405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2845554906239009626662413 1067083089839628609998405)
                ·
                  refine ⟨200078079344930364374701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1067083089839628609998405 200078079344930364374701)
                  ·
                    rfl

theorem cell20_438357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_438357 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_438357 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_438357 prefixEnd_438357 := by exact prefixLift 438357
  have htrace : WordTrace (prefixWord ++ tailWord_438357) baseStart_438357 baseEnd_438357 := by
    simpa [prefixWord, tailWord_438357, baseEnd_438357] using wordTrace_append hprefix tailTrace_438357
  have hstable : (prefixWord ++ tailWord_438357).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438357).length < 2 ^ (prefixWord ++ tailWord_438357).sum := by decide
  have hdescent : baseEnd_438357 < baseStart_438357 := by decide
  rcases family_descends (prefixWord ++ tailWord_438357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438391 : List Nat := [1, 1, 3, 1, 1, 7, 1, 3, 2]
def baseStart_438391 : Nat := 118140960795 + 438391 * 2 ^ 59
def prefixEnd_438391 : Nat := 4983230072969 + 3 ^ 40 * 438391 * 2
def baseEnd_438391 : Nat := 200093597871377357241229

theorem tailTrace_438391 : CollatzResearch.WordTrace tailWord_438391 prefixEnd_438391 200093597871377357241229 := by
  unfold tailWord_438391
  simp only [CollatzResearch.WordTrace]
  refine ⟨15989433354791753067107027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10659622236527835378071351 15989433354791753067107027)
  ·
    refine ⟨23984150032187629600660541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15989433354791753067107027 23984150032187629600660541)
    ·
      refine ⟨8994056262070361100247703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23984150032187629600660541 8994056262070361100247703)
      ·
        refine ⟨13491084393105541650371555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8994056262070361100247703 13491084393105541650371555)
        ·
          refine ⟨20236626589658312475557333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13491084393105541650371555 20236626589658312475557333)
          ·
            refine ⟨474295935695116698645875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 20236626589658312475557333 474295935695116698645875)
            ·
              refine ⟨711443903542675047968813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 474295935695116698645875 711443903542675047968813)
              ·
                refine ⟨266791463828503142988305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 711443903542675047968813 266791463828503142988305)
                ·
                  refine ⟨200093597871377357241229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 266791463828503142988305 200093597871377357241229)
                  ·
                    rfl

theorem cell20_438391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 3, 2].length) (baseStart_438391 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_438391 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_438391 prefixEnd_438391 := by exact prefixLift 438391
  have htrace : WordTrace (prefixWord ++ tailWord_438391) baseStart_438391 baseEnd_438391 := by
    simpa [prefixWord, tailWord_438391, baseEnd_438391] using wordTrace_append hprefix tailTrace_438391
  have hstable : (prefixWord ++ tailWord_438391).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438391).length < 2 ^ (prefixWord ++ tailWord_438391).sum := by decide
  have hdescent : baseEnd_438391 < baseStart_438391 := by decide
  rcases family_descends (prefixWord ++ tailWord_438391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438408 : List Nat := [2, 1, 3, 4, 1, 2, 3, 2, 2]
def baseStart_438408 : Nat := 118140960795 + 438408 * 2 ^ 59
def prefixEnd_438408 : Nat := 4983230072969 + 3 ^ 40 * 438408 * 2
def baseEnd_438408 : Nat := 200101357134600853674493

theorem tailTrace_438408 : CollatzResearch.WordTrace tailWord_438408 prefixEnd_438408 200101357134600853674493 := by
  unfold tailWord_438408
  simp only [CollatzResearch.WordTrace]
  refine ⟨7995026697865082485237939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10660035597153443313650585 7995026697865082485237939)
  ·
    refine ⟨11992540046797623727856909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7995026697865082485237939 11992540046797623727856909)
    ·
      refine ⟨4497202517549108897946341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11992540046797623727856909 4497202517549108897946341)
      ·
        refine ⟨843225472040457918364939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4497202517549108897946341 843225472040457918364939)
        ·
          refine ⟨1264838208060686877547409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 843225472040457918364939 1264838208060686877547409)
          ·
            refine ⟨948628656045515158160557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1264838208060686877547409 948628656045515158160557)
            ·
              refine ⟨355735746017068184310209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 948628656045515158160557 355735746017068184310209)
              ·
                refine ⟨266801809512801138232657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 355735746017068184310209 266801809512801138232657)
                ·
                  refine ⟨200101357134600853674493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 266801809512801138232657 200101357134600853674493)
                  ·
                    rfl

theorem cell20_438408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 2, 2].length) (baseStart_438408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_438408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_438408 prefixEnd_438408 := by exact prefixLift 438408
  have htrace : WordTrace (prefixWord ++ tailWord_438408) baseStart_438408 baseEnd_438408 := by
    simpa [prefixWord, tailWord_438408, baseEnd_438408] using wordTrace_append hprefix tailTrace_438408
  have hstable : (prefixWord ++ tailWord_438408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438408).length < 2 ^ (prefixWord ++ tailWord_438408).sum := by decide
  have hdescent : baseEnd_438408 < baseStart_438408 := by decide
  rcases family_descends (prefixWord ++ tailWord_438408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438409 : List Nat := [1, 2, 1, 1, 4, 2, 1, 3, 5]
def baseStart_438409 : Nat := 118140960795 + 438409 * 2 ^ 59
def prefixEnd_438409 : Nat := 4983230072969 + 3 ^ 40 * 438409 * 2
def baseEnd_438409 : Nat := 200101813561849294641155

theorem tailTrace_438409 : CollatzResearch.WordTrace tailWord_438409 prefixEnd_438409 200101813561849294641155 := by
  unfold tailWord_438409
  simp only [CollatzResearch.WordTrace]
  refine ⟨15990089868726542141262281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10660059912484361427508187 15990089868726542141262281)
  ·
    refine ⟨11992567401544906605946711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15990089868726542141262281 11992567401544906605946711)
    ·
      refine ⟨17988851102317359908920067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11992567401544906605946711 17988851102317359908920067)
      ·
        refine ⟨26983276653476039863380101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17988851102317359908920067 26983276653476039863380101)
        ·
          refine ⟨5059364372526757474383769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26983276653476039863380101 5059364372526757474383769)
          ·
            refine ⟨3794523279395068105787827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5059364372526757474383769 3794523279395068105787827)
            ·
              refine ⟨5691784919092602158681741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3794523279395068105787827 5691784919092602158681741)
              ·
                refine ⟨2134419344659725809505653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5691784919092602158681741 2134419344659725809505653)
                ·
                  refine ⟨200101813561849294641155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2134419344659725809505653 200101813561849294641155)
                  ·
                    rfl

theorem cell20_438409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 5].length) (baseStart_438409 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_438409 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_438409 prefixEnd_438409 := by exact prefixLift 438409
  have htrace : WordTrace (prefixWord ++ tailWord_438409) baseStart_438409 baseEnd_438409 := by
    simpa [prefixWord, tailWord_438409, baseEnd_438409] using wordTrace_append hprefix tailTrace_438409
  have hstable : (prefixWord ++ tailWord_438409).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438409).length < 2 ^ (prefixWord ++ tailWord_438409).sum := by decide
  have hdescent : baseEnd_438409 < baseStart_438409 := by decide
  rcases family_descends (prefixWord ++ tailWord_438409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438450 : List Nat := [3, 2, 1, 1, 1, 3, 2, 5, 2]
def baseStart_438450 : Nat := 118140960795 + 438450 * 2 ^ 59
def prefixEnd_438450 : Nat := 4983230072969 + 3 ^ 40 * 438450 * 2
def baseEnd_438450 : Nat := 200120527079035374274321

theorem tailTrace_438450 : CollatzResearch.WordTrace tailWord_438450 prefixEnd_438450 200120527079035374274321 := by
  unfold tailWord_438450
  simp only [CollatzResearch.WordTrace]
  refine ⟨3997896315394501535876201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10661056841052004095669869 3997896315394501535876201)
  ·
    refine ⟨2998422236545876151907151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3997896315394501535876201 2998422236545876151907151)
    ·
      refine ⟨4497633354818814227860727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2998422236545876151907151 4497633354818814227860727)
      ·
        refine ⟨6746450032228221341791091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4497633354818814227860727 6746450032228221341791091)
        ·
          refine ⟨10119675048342332012686637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6746450032228221341791091 10119675048342332012686637)
          ·
            refine ⟨3794878143128374504757489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10119675048342332012686637 3794878143128374504757489)
            ·
              refine ⟨2846158607346280878568117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3794878143128374504757489 2846158607346280878568117)
              ·
                refine ⟨266827369438713832365761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2846158607346280878568117 266827369438713832365761)
                ·
                  refine ⟨200120527079035374274321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 266827369438713832365761 200120527079035374274321)
                  ·
                    rfl

theorem cell20_438450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 5, 2].length) (baseStart_438450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_438450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_438450 prefixEnd_438450 := by exact prefixLift 438450
  have htrace : WordTrace (prefixWord ++ tailWord_438450) baseStart_438450 baseEnd_438450 := by
    simpa [prefixWord, tailWord_438450, baseEnd_438450] using wordTrace_append hprefix tailTrace_438450
  have hstable : (prefixWord ++ tailWord_438450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438450).length < 2 ^ (prefixWord ++ tailWord_438450).sum := by decide
  have hdescent : baseEnd_438450 < baseStart_438450 := by decide
  rcases family_descends (prefixWord ++ tailWord_438450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438464 : List Nat := [2, 1, 1, 2, 5, 1, 1, 4, 3]
def baseStart_438464 : Nat := 118140960795 + 438464 * 2 ^ 59
def prefixEnd_438464 : Nat := 4983230072969 + 3 ^ 40 * 438464 * 2
def baseEnd_438464 : Nat := 200126917060513547807597

theorem tailTrace_438464 : CollatzResearch.WordTrace tailWord_438464 prefixEnd_438464 200126917060513547807597 := by
  unfold tailWord_438464
  simp only [CollatzResearch.WordTrace]
  refine ⟨7996047941763643267257223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10661397255684857689676297 7996047941763643267257223)
  ·
    refine ⟨11994071912645464900885835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7996047941763643267257223 11994071912645464900885835)
    ·
      refine ⟨17991107868968197351328753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11994071912645464900885835 17991107868968197351328753)
      ·
        refine ⟨13493330901726148013496565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17991107868968197351328753 13493330901726148013496565)
        ·
          refine ⟨1264999772036826376265303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13493330901726148013496565 1264999772036826376265303)
          ·
            refine ⟨1897499658055239564397955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1264999772036826376265303 1897499658055239564397955)
            ·
              refine ⟨2846249487082859346596933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1897499658055239564397955 2846249487082859346596933)
              ·
                refine ⟨533671778828036127486925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2846249487082859346596933 533671778828036127486925)
                ·
                  refine ⟨200126917060513547807597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 533671778828036127486925 200126917060513547807597)
                  ·
                    rfl

theorem cell20_438464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 4, 3].length) (baseStart_438464 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_438464 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_438464 prefixEnd_438464 := by exact prefixLift 438464
  have htrace : WordTrace (prefixWord ++ tailWord_438464) baseStart_438464 baseEnd_438464 := by
    simpa [prefixWord, tailWord_438464, baseEnd_438464] using wordTrace_append hprefix tailTrace_438464
  have hstable : (prefixWord ++ tailWord_438464).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438464).length < 2 ^ (prefixWord ++ tailWord_438464).sum := by decide
  have hdescent : baseEnd_438464 < baseStart_438464 := by decide
  rcases family_descends (prefixWord ++ tailWord_438464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438526 : List Nat := [4, 2, 2, 1, 1, 1, 4, 1, 4]
def baseStart_438526 : Nat := 118140960795 + 438526 * 2 ^ 59
def prefixEnd_438526 : Nat := 4983230072969 + 3 ^ 40 * 438526 * 2
def baseEnd_438526 : Nat := 200155215549916887740677

theorem tailTrace_438526 : CollatzResearch.WordTrace tailWord_438526 prefixEnd_438526 200155215549916887740677 := by
  unfold tailWord_438526
  simp only [CollatzResearch.WordTrace]
  refine ⟨1999294651162833890408929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10662904806201780748847621 1999294651162833890408929)
  ·
    refine ⟨1499470988372125417806697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1999294651162833890408929 1499470988372125417806697)
    ·
      refine ⟨1124603241279094063355023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1499470988372125417806697 1124603241279094063355023)
      ·
        refine ⟨1686904861918641095032535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1124603241279094063355023 1686904861918641095032535)
        ·
          refine ⟨2530357292877961642548803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1686904861918641095032535 2530357292877961642548803)
          ·
            refine ⟨3795535939316942463823205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2530357292877961642548803 3795535939316942463823205)
            ·
              refine ⟨711662988621926711966851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3795535939316942463823205 711662988621926711966851)
              ·
                refine ⟨1067494482932890067950277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 711662988621926711966851 1067494482932890067950277)
                ·
                  refine ⟨200155215549916887740677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1067494482932890067950277 200155215549916887740677)
                  ·
                    rfl

theorem cell20_438526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_438526 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_438526 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_438526 prefixEnd_438526 := by exact prefixLift 438526
  have htrace : WordTrace (prefixWord ++ tailWord_438526) baseStart_438526 baseEnd_438526 := by
    simpa [prefixWord, tailWord_438526, baseEnd_438526] using wordTrace_append hprefix tailTrace_438526
  have hstable : (prefixWord ++ tailWord_438526).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438526).length < 2 ^ (prefixWord ++ tailWord_438526).sum := by decide
  have hdescent : baseEnd_438526 < baseStart_438526 := by decide
  rcases family_descends (prefixWord ++ tailWord_438526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438561 : List Nat := [1, 2, 3, 2, 1, 1, 3, 2, 5]
def baseStart_438561 : Nat := 118140960795 + 438561 * 2 ^ 59
def prefixEnd_438561 : Nat := 4983230072969 + 3 ^ 40 * 438561 * 2
def baseEnd_438561 : Nat := 200171190503612321573867

theorem tailTrace_438561 : CollatzResearch.WordTrace tailWord_438561 prefixEnd_438561 200171190503612321573867 := by
  unfold tailWord_438561
  simp only [CollatzResearch.WordTrace]
  refine ⟨15995633764175872100795537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10663755842783914733863691 15995633764175872100795537)
  ·
    refine ⟨11996725323131904075596653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15995633764175872100795537 11996725323131904075596653)
    ·
      refine ⟨4498771996174464028348745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11996725323131904075596653 4498771996174464028348745)
      ·
        refine ⟨3374078997130848021261559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4498771996174464028348745 3374078997130848021261559)
        ·
          refine ⟨5061118495696272031892339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3374078997130848021261559 5061118495696272031892339)
          ·
            refine ⟨7591677743544408047838509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5061118495696272031892339 7591677743544408047838509)
            ·
              refine ⟨2846879153829153017939441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7591677743544408047838509 2846879153829153017939441)
              ·
                refine ⟨2135159365371864763454581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2846879153829153017939441 2135159365371864763454581)
                ·
                  refine ⟨200171190503612321573867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2135159365371864763454581 200171190503612321573867)
                  ·
                    rfl

theorem cell20_438561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 5].length) (baseStart_438561 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_438561 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_438561 prefixEnd_438561 := by exact prefixLift 438561
  have htrace : WordTrace (prefixWord ++ tailWord_438561) baseStart_438561 baseEnd_438561 := by
    simpa [prefixWord, tailWord_438561, baseEnd_438561] using wordTrace_append hprefix tailTrace_438561
  have hstable : (prefixWord ++ tailWord_438561).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438561).length < 2 ^ (prefixWord ++ tailWord_438561).sum := by decide
  have hdescent : baseEnd_438561 < baseStart_438561 := by decide
  rcases family_descends (prefixWord ++ tailWord_438561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438567 : List Nat := [1, 1, 8, 1, 1, 2, 6]
def baseStart_438567 : Nat := 118140960795 + 438567 * 2 ^ 59
def prefixEnd_438567 : Nat := 4983230072969 + 3 ^ 40 * 438567 * 2
def baseEnd_438567 : Nat := 22241547674122551930427

theorem tailTrace_438567 : CollatzResearch.WordTrace tailWord_438567 prefixEnd_438567 22241547674122551930427 := by
  unfold tailWord_438567
  simp only [CollatzResearch.WordTrace]
  refine ⟨15995852602154135125513955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10663901734769423417009303 15995852602154135125513955)
  ·
    refine ⟨23993778903231202688270933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15995852602154135125513955 23993778903231202688270933)
    ·
      refine ⟨281177096522240656503175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 23993778903231202688270933 281177096522240656503175)
      ·
        refine ⟨421765644783360984754763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281177096522240656503175 421765644783360984754763)
        ·
          refine ⟨632648467175041477132145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 421765644783360984754763 632648467175041477132145)
          ·
            refine ⟨474486350381281107849109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 632648467175041477132145 474486350381281107849109)
            ·
              refine ⟨22241547674122551930427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 474486350381281107849109 22241547674122551930427)
              ·
                rfl

theorem cell20_438567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 6].length) (baseStart_438567 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_438567 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_438567 prefixEnd_438567 := by exact prefixLift 438567
  have htrace : WordTrace (prefixWord ++ tailWord_438567) baseStart_438567 baseEnd_438567 := by
    simpa [prefixWord, tailWord_438567, baseEnd_438567] using wordTrace_append hprefix tailTrace_438567
  have hstable : (prefixWord ++ tailWord_438567).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438567).length < 2 ^ (prefixWord ++ tailWord_438567).sum := by decide
  have hdescent : baseEnd_438567 < baseStart_438567 := by decide
  rcases family_descends (prefixWord ++ tailWord_438567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438575 : List Nat := [1, 1, 2, 1, 2, 1, 12]
def baseStart_438575 : Nat := 118140960795 + 438575 * 2 ^ 59
def prefixEnd_438575 : Nat := 4983230072969 + 3 ^ 40 * 438575 * 2
def baseEnd_438575 : Nat := 22241953387232277234127

theorem tailTrace_438575 : CollatzResearch.WordTrace tailWord_438575 prefixEnd_438575 22241953387232277234127 := by
  unfold tailWord_438575
  simp only [CollatzResearch.WordTrace]
  refine ⟨15996144386125152491805179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10664096257416768327870119 15996144386125152491805179)
  ·
    refine ⟨23994216579187728737707769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15996144386125152491805179 23994216579187728737707769)
    ·
      refine ⟨17995662434390796553280827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23994216579187728737707769 17995662434390796553280827)
      ·
        refine ⟨26993493651586194829921241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17995662434390796553280827 26993493651586194829921241)
        ·
          refine ⟨20245120238689646122440931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26993493651586194829921241 20245120238689646122440931)
          ·
            refine ⟨30367680358034469183661397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20245120238689646122440931 30367680358034469183661397)
            ·
              refine ⟨22241953387232277234127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 30367680358034469183661397 22241953387232277234127)
              ·
                rfl

theorem cell20_438575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 12].length) (baseStart_438575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_438575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_438575 prefixEnd_438575 := by exact prefixLift 438575
  have htrace : WordTrace (prefixWord ++ tailWord_438575) baseStart_438575 baseEnd_438575 := by
    simpa [prefixWord, tailWord_438575, baseEnd_438575] using wordTrace_append hprefix tailTrace_438575
  have hstable : (prefixWord ++ tailWord_438575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438575).length < 2 ^ (prefixWord ++ tailWord_438575).sum := by decide
  have hdescent : baseEnd_438575 < baseStart_438575 := by decide
  rcases family_descends (prefixWord ++ tailWord_438575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438581 : List Nat := [1, 3, 3, 1, 2, 1, 5, 2, 2]
def baseStart_438581 : Nat := 118140960795 + 438581 * 2 ^ 59
def prefixEnd_438581 : Nat := 4983230072969 + 3 ^ 40 * 438581 * 2
def baseEnd_438581 : Nat := 200180319048581140907119

theorem tailTrace_438581 : CollatzResearch.WordTrace tailWord_438581 prefixEnd_438581 200180319048581140907119 := by
  unfold tailWord_438581
  simp only [CollatzResearch.WordTrace]
  refine ⟨15996363224103415516523597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10664242149402277011015731 15996363224103415516523597)
  ·
    refine ⟨5998636209038780818696349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15996363224103415516523597 5998636209038780818696349)
    ·
      refine ⟨2249488578389542807011131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5998636209038780818696349 2249488578389542807011131)
      ·
        refine ⟨3374232867584314210516697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2249488578389542807011131 3374232867584314210516697)
        ·
          refine ⟨2530674650688235657887523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3374232867584314210516697 2530674650688235657887523)
          ·
            refine ⟨3796011976032353486831285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2530674650688235657887523 3796011976032353486831285)
            ·
              refine ⟨355876122753033139390433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3796011976032353486831285 355876122753033139390433)
              ·
                refine ⟨266907092064774854542825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 355876122753033139390433 266907092064774854542825)
                ·
                  refine ⟨200180319048581140907119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 266907092064774854542825 200180319048581140907119)
                  ·
                    rfl

theorem cell20_438581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 2, 2].length) (baseStart_438581 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_438581 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_438581 prefixEnd_438581 := by exact prefixLift 438581
  have htrace : WordTrace (prefixWord ++ tailWord_438581) baseStart_438581 baseEnd_438581 := by
    simpa [prefixWord, tailWord_438581, baseEnd_438581] using wordTrace_append hprefix tailTrace_438581
  have hstable : (prefixWord ++ tailWord_438581).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438581).length < 2 ^ (prefixWord ++ tailWord_438581).sum := by decide
  have hdescent : baseEnd_438581 < baseStart_438581 := by decide
  rcases family_descends (prefixWord ++ tailWord_438581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438622 : List Nat := [4, 4, 2, 1, 2, 7]
def baseStart_438622 : Nat := 118140960795 + 438622 * 2 ^ 59
def prefixEnd_438622 : Nat := 4983230072969 + 3 ^ 40 * 438622 * 2
def baseEnd_438622 : Nat := 7414778983917304464455

theorem tailTrace_438622 : CollatzResearch.WordTrace tailWord_438622 prefixEnd_438622 7414778983917304464455 := by
  unfold tailWord_438622
  simp only [CollatzResearch.WordTrace]
  refine ⟨1999732327119359939845765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10665239077969919679177413 1999732327119359939845765)
  ·
    refine ⟨374949811334879988721081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1999732327119359939845765 374949811334879988721081)
    ·
      refine ⟨281212358501159991540811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374949811334879988721081 281212358501159991540811)
      ·
        refine ⟨421818537751739987311217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281212358501159991540811 421818537751739987311217)
        ·
          refine ⟨316363903313804990483413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 421818537751739987311217 316363903313804990483413)
          ·
            refine ⟨7414778983917304464455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 316363903313804990483413 7414778983917304464455)
            ·
              rfl

theorem cell20_438622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 7].length) (baseStart_438622 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_438622 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_438622 prefixEnd_438622 := by exact prefixLift 438622
  have htrace : WordTrace (prefixWord ++ tailWord_438622) baseStart_438622 baseEnd_438622 := by
    simpa [prefixWord, tailWord_438622, baseEnd_438622] using wordTrace_append hprefix tailTrace_438622
  have hstable : (prefixWord ++ tailWord_438622).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438622).length < 2 ^ (prefixWord ++ tailWord_438622).sum := by decide
  have hdescent : baseEnd_438622 < baseStart_438622 := by decide
  rcases family_descends (prefixWord ++ tailWord_438622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438636 : List Nat := [2, 2, 1, 1, 6, 2, 2, 2, 2]
def baseStart_438636 : Nat := 118140960795 + 438636 * 2 ^ 59
def prefixEnd_438636 : Nat := 4983230072969 + 3 ^ 40 * 438636 * 2
def baseEnd_438636 : Nat := 200205422547245394073561

theorem tailTrace_438636 : CollatzResearch.WordTrace tailWord_438636 prefixEnd_438636 200205422547245394073561 := by
  unfold tailWord_438636
  simp only [CollatzResearch.WordTrace]
  refine ⟨7999184619452079954887881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10665579492602773273183841 7999184619452079954887881)
  ·
    refine ⟨5999388464589059966165911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7999184619452079954887881 5999388464589059966165911)
    ·
      refine ⟨8999082696883589949248867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5999388464589059966165911 8999082696883589949248867)
      ·
        refine ⟨13498624045325384923873301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8999082696883589949248867 13498624045325384923873301)
        ·
          refine ⟨632748002124627418306561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13498624045325384923873301 632748002124627418306561)
          ·
            refine ⟨474561001593470563729921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 632748002124627418306561 474561001593470563729921)
            ·
              refine ⟨355920751195102922797441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 474561001593470563729921 355920751195102922797441)
              ·
                refine ⟨266940563396327192098081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 355920751195102922797441 266940563396327192098081)
                ·
                  refine ⟨200205422547245394073561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 266940563396327192098081 200205422547245394073561)
                  ·
                    rfl

theorem cell20_438636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 2, 2].length) (baseStart_438636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_438636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_438636 prefixEnd_438636 := by exact prefixLift 438636
  have htrace : WordTrace (prefixWord ++ tailWord_438636) baseStart_438636 baseEnd_438636 := by
    simpa [prefixWord, tailWord_438636, baseEnd_438636] using wordTrace_append hprefix tailTrace_438636
  have hstable : (prefixWord ++ tailWord_438636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438636).length < 2 ^ (prefixWord ++ tailWord_438636).sum := by decide
  have hdescent : baseEnd_438636 < baseStart_438636 := by decide
  rcases family_descends (prefixWord ++ tailWord_438636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438640 : List Nat := [2, 1, 1, 1, 4, 4, 1, 4, 2]
def baseStart_438640 : Nat := 118140960795 + 438640 * 2 ^ 59
def prefixEnd_438640 : Nat := 4983230072969 + 3 ^ 40 * 438640 * 2
def baseEnd_438640 : Nat := 200207248256239157940211

theorem tailTrace_438640 : CollatzResearch.WordTrace tailWord_438640 prefixEnd_438640 200207248256239157940211 := by
  unfold tailWord_438640
  simp only [CollatzResearch.WordTrace]
  refine ⟨7999257565444834296460687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10665676753926445728614249 7999257565444834296460687)
  ·
    refine ⟨11998886348167251444691031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7999257565444834296460687 11998886348167251444691031)
    ·
      refine ⟨17998329522250877167036547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11998886348167251444691031 17998329522250877167036547)
      ·
        refine ⟨26997494283376315750554821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17998329522250877167036547 26997494283376315750554821)
        ·
          refine ⟨5062030178133059203229029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26997494283376315750554821 5062030178133059203229029)
          ·
            refine ⟨949130658399948600605443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5062030178133059203229029 949130658399948600605443)
            ·
              refine ⟨1423695987599922900908165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 949130658399948600605443 1423695987599922900908165)
              ·
                refine ⟨266942997674985543920281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1423695987599922900908165 266942997674985543920281)
                ·
                  refine ⟨200207248256239157940211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 266942997674985543920281 200207248256239157940211)
                  ·
                    rfl

theorem cell20_438640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 4, 2].length) (baseStart_438640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_438640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_438640 prefixEnd_438640 := by exact prefixLift 438640
  have htrace : WordTrace (prefixWord ++ tailWord_438640) baseStart_438640 baseEnd_438640 := by
    simpa [prefixWord, tailWord_438640, baseEnd_438640] using wordTrace_append hprefix tailTrace_438640
  have hstable : (prefixWord ++ tailWord_438640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438640).length < 2 ^ (prefixWord ++ tailWord_438640).sum := by decide
  have hdescent : baseEnd_438640 < baseStart_438640 := by decide
  rcases family_descends (prefixWord ++ tailWord_438640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438692 : List Nat := [2, 3, 1, 2, 1, 1, 5, 2, 3]
def baseStart_438692 : Nat := 118140960795 + 438692 * 2 ^ 59
def prefixEnd_438692 : Nat := 4983230072969 + 3 ^ 40 * 438692 * 2
def baseEnd_438692 : Nat := 200230982473158088206665

theorem tailTrace_438692 : CollatzResearch.WordTrace tailWord_438692 prefixEnd_438692 200230982473158088206665 := by
  unfold tailWord_438692
  simp only [CollatzResearch.WordTrace]
  refine ⟨8000205863350640736907165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10666941151134187649209553 8000205863350640736907165)
  ·
    refine ⟨3000077198756490276340187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8000205863350640736907165 3000077198756490276340187)
    ·
      refine ⟨4500115798134735414510281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3000077198756490276340187 4500115798134735414510281)
      ·
        refine ⟨3375086848601051560882711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4500115798134735414510281 3375086848601051560882711)
        ·
          refine ⟨5062630272901577341324067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3375086848601051560882711 5062630272901577341324067)
          ·
            refine ⟨7593945409352366011986101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5062630272901577341324067 7593945409352366011986101)
            ·
              refine ⟨711932382126784313623697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7593945409352366011986101 711932382126784313623697)
              ·
                refine ⟨533949286595088235217773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 711932382126784313623697 533949286595088235217773)
                ·
                  refine ⟨200230982473158088206665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 533949286595088235217773 200230982473158088206665)
                  ·
                    rfl

theorem cell20_438692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_438692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_438692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_438692 prefixEnd_438692 := by exact prefixLift 438692
  have htrace : WordTrace (prefixWord ++ tailWord_438692) baseStart_438692 baseEnd_438692 := by
    simpa [prefixWord, tailWord_438692, baseEnd_438692] using wordTrace_append hprefix tailTrace_438692
  have hstable : (prefixWord ++ tailWord_438692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438692).length < 2 ^ (prefixWord ++ tailWord_438692).sum := by decide
  have hdescent : baseEnd_438692 < baseStart_438692 := by decide
  rcases family_descends (prefixWord ++ tailWord_438692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438751 : List Nat := [1, 1, 2, 3, 3, 2, 2, 1, 5]
def baseStart_438751 : Nat := 118140960795 + 438751 * 2 ^ 59
def prefixEnd_438751 : Nat := 4983230072969 + 3 ^ 40 * 438751 * 2
def baseEnd_438751 : Nat := 200257911680816105239757

theorem tailTrace_438751 : CollatzResearch.WordTrace tailWord_438751 prefixEnd_438751 200257911680816105239757 := by
  unfold tailWord_438751
  simp only [CollatzResearch.WordTrace]
  refine ⟨16002563633487534550212107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10668375755658356366808071 16002563633487534550212107)
  ·
    refine ⟨24003845450231301825318161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16002563633487534550212107 24003845450231301825318161)
    ·
      refine ⟨18002884087673476368988621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24003845450231301825318161 18002884087673476368988621)
      ·
        refine ⟨6751081532877553638370733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18002884087673476368988621 6751081532877553638370733)
        ·
          refine ⟨2531655574829082614389025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6751081532877553638370733 2531655574829082614389025)
          ·
            refine ⟨1898741681121811960791769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2531655574829082614389025 1898741681121811960791769)
            ·
              refine ⟨1424056260841358970593827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1898741681121811960791769 1424056260841358970593827)
              ·
                refine ⟨2136084391262038455890741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1424056260841358970593827 2136084391262038455890741)
                ·
                  refine ⟨200257911680816105239757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2136084391262038455890741 200257911680816105239757)
                  ·
                    rfl

theorem cell20_438751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 5].length) (baseStart_438751 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_438751 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_438751 prefixEnd_438751 := by exact prefixLift 438751
  have htrace : WordTrace (prefixWord ++ tailWord_438751) baseStart_438751 baseEnd_438751 := by
    simpa [prefixWord, tailWord_438751, baseEnd_438751] using wordTrace_append hprefix tailTrace_438751
  have hstable : (prefixWord ++ tailWord_438751).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438751).length < 2 ^ (prefixWord ++ tailWord_438751).sum := by decide
  have hdescent : baseEnd_438751 < baseStart_438751 := by decide
  rcases family_descends (prefixWord ++ tailWord_438751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438816 : List Nat := [2, 1, 1, 6, 3, 1, 1, 5]
def baseStart_438816 : Nat := 118140960795 + 438816 * 2 ^ 59
def prefixEnd_438816 : Nat := 4983230072969 + 3 ^ 40 * 438816 * 2
def baseEnd_438816 : Nat := 66762526483988256024275

theorem tailTrace_438816 : CollatzResearch.WordTrace tailWord_438816 prefixEnd_438816 66762526483988256024275 := by
  unfold tailWord_438816
  simp only [CollatzResearch.WordTrace]
  refine ⟨8002467189126025325664151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10669956252168033767552201 8002467189126025325664151)
  ·
    refine ⟨12003700783689037988496227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8002467189126025325664151 12003700783689037988496227)
    ·
      refine ⟨18005551175533556982744341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12003700783689037988496227 18005551175533556982744341)
      ·
        refine ⟨844010211353135483566141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18005551175533556982744341 844010211353135483566141)
        ·
          refine ⟨316503829257425806337303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 844010211353135483566141 316503829257425806337303)
          ·
            refine ⟨474755743886138709505955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316503829257425806337303 474755743886138709505955)
            ·
              refine ⟨712133615829208064258933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 474755743886138709505955 712133615829208064258933)
              ·
                refine ⟨66762526483988256024275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 712133615829208064258933 66762526483988256024275)
                ·
                  rfl

theorem cell20_438816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 5].length) (baseStart_438816 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_438816 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_438816 prefixEnd_438816 := by exact prefixLift 438816
  have htrace : WordTrace (prefixWord ++ tailWord_438816) baseStart_438816 baseEnd_438816 := by
    simpa [prefixWord, tailWord_438816, baseEnd_438816] using wordTrace_append hprefix tailTrace_438816
  have hstable : (prefixWord ++ tailWord_438816).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438816).length < 2 ^ (prefixWord ++ tailWord_438816).sum := by decide
  have hdescent : baseEnd_438816 < baseStart_438816 := by decide
  rcases family_descends (prefixWord ++ tailWord_438816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438830 : List Nat := [4, 1, 3, 1, 3, 1, 1, 2, 4]
def baseStart_438830 : Nat := 118140960795 + 438830 * 2 ^ 59
def prefixEnd_438830 : Nat := 4983230072969 + 3 ^ 40 * 438830 * 2
def baseEnd_438830 : Nat := 200293969433442941606101

theorem tailTrace_438830 : CollatzResearch.WordTrace tailWord_438830 prefixEnd_438830 200293969433442941606101 := by
  unfold tailWord_438830
  simp only [CollatzResearch.WordTrace]
  refine ⟨2000680625025166380292243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10670296666800887361558629 2000680625025166380292243)
  ·
    refine ⟨3001020937537749570438365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2000680625025166380292243 3001020937537749570438365)
    ·
      refine ⟨1125382851576656088914387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3001020937537749570438365 1125382851576656088914387)
      ·
        refine ⟨1688074277364984133371581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1125382851576656088914387 1688074277364984133371581)
        ·
          refine ⟨633027854011869050014343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1688074277364984133371581 633027854011869050014343)
          ·
            refine ⟨949541781017803575021515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 633027854011869050014343 949541781017803575021515)
            ·
              refine ⟨1424312671526705362532273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 949541781017803575021515 1424312671526705362532273)
              ·
                refine ⟨1068234503645029021899205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1424312671526705362532273 1068234503645029021899205)
                ·
                  refine ⟨200293969433442941606101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1068234503645029021899205 200293969433442941606101)
                  ·
                    rfl

theorem cell20_438830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_438830 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_438830 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_438830 prefixEnd_438830 := by exact prefixLift 438830
  have htrace : WordTrace (prefixWord ++ tailWord_438830) baseStart_438830 baseEnd_438830 := by
    simpa [prefixWord, tailWord_438830, baseEnd_438830] using wordTrace_append hprefix tailTrace_438830
  have hstable : (prefixWord ++ tailWord_438830).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438830).length < 2 ^ (prefixWord ++ tailWord_438830).sum := by decide
  have hdescent : baseEnd_438830 < baseStart_438830 := by decide
  rcases family_descends (prefixWord ++ tailWord_438830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438834 : List Nat := [3, 2, 1, 1, 2, 1, 3, 1, 6]
def baseStart_438834 : Nat := 118140960795 + 438834 * 2 ^ 59
def prefixEnd_438834 : Nat := 4983230072969 + 3 ^ 40 * 438834 * 2
def baseEnd_438834 : Nat := 200295795142436705472751

theorem tailTrace_438834 : CollatzResearch.WordTrace tailWord_438834 prefixEnd_438834 200295795142436705472751 := by
  unfold tailWord_438834
  simp only [CollatzResearch.WordTrace]
  refine ⟨4001397723046709931370889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10670393928124559816989037 4001397723046709931370889)
  ·
    refine ⟨3001048292285032448528167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4001397723046709931370889 3001048292285032448528167)
    ·
      refine ⟨4501572438427548672792251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3001048292285032448528167 4501572438427548672792251)
      ·
        refine ⟨6752358657641323009188377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4501572438427548672792251 6752358657641323009188377)
        ·
          refine ⟨5064268993230992256891283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6752358657641323009188377 5064268993230992256891283)
          ·
            refine ⟨7596403489846488385336925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5064268993230992256891283 7596403489846488385336925)
            ·
              refine ⟨2848651308692433144501347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7596403489846488385336925 2848651308692433144501347)
              ·
                refine ⟨4272976963038649716752021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2848651308692433144501347 4272976963038649716752021)
                ·
                  refine ⟨200295795142436705472751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4272976963038649716752021 200295795142436705472751)
                  ·
                    rfl

theorem cell20_438834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_438834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_438834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_438834 prefixEnd_438834 := by exact prefixLift 438834
  have htrace : WordTrace (prefixWord ++ tailWord_438834) baseStart_438834 baseEnd_438834 := by
    simpa [prefixWord, tailWord_438834, baseEnd_438834] using wordTrace_append hprefix tailTrace_438834
  have hstable : (prefixWord ++ tailWord_438834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438834).length < 2 ^ (prefixWord ++ tailWord_438834).sum := by decide
  have hdescent : baseEnd_438834 < baseStart_438834 := by decide
  rcases family_descends (prefixWord ++ tailWord_438834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438861 : List Nat := [1, 6, 1, 1, 2, 1, 3, 2, 3]
def baseStart_438861 : Nat := 118140960795 + 438861 * 2 ^ 59
def prefixEnd_438861 : Nat := 4983230072969 + 3 ^ 40 * 438861 * 2
def baseEnd_438861 : Nat := 200308118678144611572641

theorem tailTrace_438861 : CollatzResearch.WordTrace tailWord_438861 prefixEnd_438861 200308118678144611572641 := by
  unfold tailWord_438861
  simp only [CollatzResearch.WordTrace]
  refine ⟨16006575663089023336716437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10671050442059348891144291 16006575663089023336716437)
  ·
    refine ⟨750308234207297968908583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16006575663089023336716437 750308234207297968908583)
    ·
      refine ⟨1125462351310946953362875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 750308234207297968908583 1125462351310946953362875)
      ·
        refine ⟨1688193526966420430044313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1125462351310946953362875 1688193526966420430044313)
        ·
          refine ⟨1266145145224815322533235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1688193526966420430044313 1266145145224815322533235)
          ·
            refine ⟨1899217717837222983799853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1266145145224815322533235 1899217717837222983799853)
            ·
              refine ⟨712206644188958618924945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1899217717837222983799853 712206644188958618924945)
              ·
                refine ⟨534154983141718964193709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 712206644188958618924945 534154983141718964193709)
                ·
                  refine ⟨200308118678144611572641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 534154983141718964193709 200308118678144611572641)
                  ·
                    rfl

theorem cell20_438861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_438861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_438861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_438861 prefixEnd_438861 := by exact prefixLift 438861
  have htrace : WordTrace (prefixWord ++ tailWord_438861) baseStart_438861 baseEnd_438861 := by
    simpa [prefixWord, tailWord_438861, baseEnd_438861] using wordTrace_append hprefix tailTrace_438861
  have hstable : (prefixWord ++ tailWord_438861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438861).length < 2 ^ (prefixWord ++ tailWord_438861).sum := by decide
  have hdescent : baseEnd_438861 < baseStart_438861 := by decide
  rcases family_descends (prefixWord ++ tailWord_438861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438865 : List Nat := [1, 2, 2, 1, 3, 4, 1, 1, 5]
def baseStart_438865 : Nat := 118140960795 + 438865 * 2 ^ 59
def prefixEnd_438865 : Nat := 4983230072969 + 3 ^ 40 * 438865 * 2
def baseEnd_438865 : Nat := 200309944387138375439291

theorem tailTrace_438865 : CollatzResearch.WordTrace tailWord_438865 prefixEnd_438865 200309944387138375439291 := by
  unfold tailWord_438865
  simp only [CollatzResearch.WordTrace]
  refine ⟨16006721555074532019862049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10671147703383021346574699 16006721555074532019862049)
  ·
    refine ⟨12005041166305899014896537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16006721555074532019862049 12005041166305899014896537)
    ·
      refine ⟨9003780874729424261172403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12005041166305899014896537 9003780874729424261172403)
      ·
        refine ⟨13505671312094136391758605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9003780874729424261172403 13505671312094136391758605)
        ·
          refine ⟨5064626742035301146909477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13505671312094136391758605 5064626742035301146909477)
          ·
            refine ⟨949617514131618965045527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5064626742035301146909477 949617514131618965045527)
            ·
              refine ⟨1424426271197428447568291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 949617514131618965045527 1424426271197428447568291)
              ·
                refine ⟨2136639406796142671352437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1424426271197428447568291 2136639406796142671352437)
                ·
                  refine ⟨200309944387138375439291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2136639406796142671352437 200309944387138375439291)
                  ·
                    rfl

theorem cell20_438865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 5].length) (baseStart_438865 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_438865 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_438865 prefixEnd_438865 := by exact prefixLift 438865
  have htrace : WordTrace (prefixWord ++ tailWord_438865) baseStart_438865 baseEnd_438865 := by
    simpa [prefixWord, tailWord_438865, baseEnd_438865] using wordTrace_append hprefix tailTrace_438865
  have hstable : (prefixWord ++ tailWord_438865).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438865).length < 2 ^ (prefixWord ++ tailWord_438865).sum := by decide
  have hdescent : baseEnd_438865 < baseStart_438865 := by decide
  rcases family_descends (prefixWord ++ tailWord_438865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438868 : List Nat := [2, 4, 1, 1, 1, 3, 2, 4, 2]
def baseStart_438868 : Nat := 118140960795 + 438868 * 2 ^ 59
def prefixEnd_438868 : Nat := 4983230072969 + 3 ^ 40 * 438868 * 2
def baseEnd_438868 : Nat := 200311313668883698339279

theorem tailTrace_438868 : CollatzResearch.WordTrace tailWord_438868 prefixEnd_438868 200311313668883698339279 := by
  unfold tailWord_438868
  simp only [CollatzResearch.WordTrace]
  refine ⟨8003415487031831766110629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10671220649375775688147505 8003415487031831766110629)
  ·
    refine ⟨1500640403818468456145743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8003415487031831766110629 1500640403818468456145743)
    ·
      refine ⟨2250960605727702684218615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1500640403818468456145743 2250960605727702684218615)
      ·
        refine ⟨3376440908591554026327923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2250960605727702684218615 3376440908591554026327923)
        ·
          refine ⟨5064661362887331039491885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3376440908591554026327923 5064661362887331039491885)
          ·
            refine ⟨1899248011082749139809457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5064661362887331039491885 1899248011082749139809457)
            ·
              refine ⟨1424436008312061854857093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1899248011082749139809457 1424436008312061854857093)
              ·
                refine ⟨267081751558511597785705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1424436008312061854857093 267081751558511597785705)
                ·
                  refine ⟨200311313668883698339279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 267081751558511597785705 200311313668883698339279)
                  ·
                    rfl

theorem cell20_438868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_438868 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_438868 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_438868 prefixEnd_438868 := by exact prefixLift 438868
  have htrace : WordTrace (prefixWord ++ tailWord_438868) baseStart_438868 baseEnd_438868 := by
    simpa [prefixWord, tailWord_438868, baseEnd_438868] using wordTrace_append hprefix tailTrace_438868
  have hstable : (prefixWord ++ tailWord_438868).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438868).length < 2 ^ (prefixWord ++ tailWord_438868).sum := by decide
  have hdescent : baseEnd_438868 < baseStart_438868 := by decide
  rcases family_descends (prefixWord ++ tailWord_438868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438872 : List Nat := [2, 1, 2, 2, 1, 2, 3, 3, 4]
def baseStart_438872 : Nat := 118140960795 + 438872 * 2 ^ 59
def prefixEnd_438872 : Nat := 4983230072969 + 3 ^ 40 * 438872 * 2
def baseEnd_438872 : Nat := 200313139377877462205929

theorem tailTrace_438872 : CollatzResearch.WordTrace tailWord_438872 prefixEnd_438872 200313139377877462205929 := by
  unfold tailWord_438872
  simp only [CollatzResearch.WordTrace]
  refine ⟨8003488433024586107683435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10671317910699448143577913 8003488433024586107683435)
  ·
    refine ⟨12005232649536879161525153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8003488433024586107683435 12005232649536879161525153)
    ·
      refine ⟨9003924487152659371143865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12005232649536879161525153 9003924487152659371143865)
      ·
        refine ⟨6752943365364494528357899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9003924487152659371143865 6752943365364494528357899)
        ·
          refine ⟨10129415048046741792536849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6752943365364494528357899 10129415048046741792536849)
          ·
            refine ⟨7597061286035056344402637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10129415048046741792536849 7597061286035056344402637)
            ·
              refine ⟨2848897982263146129150989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7597061286035056344402637 2848897982263146129150989)
              ·
                refine ⟨1068336743348679798431621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2848897982263146129150989 1068336743348679798431621)
                ·
                  refine ⟨200313139377877462205929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1068336743348679798431621 200313139377877462205929)
                  ·
                    rfl

theorem cell20_438872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 4].length) (baseStart_438872 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_438872 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_438872 prefixEnd_438872 := by exact prefixLift 438872
  have htrace : WordTrace (prefixWord ++ tailWord_438872) baseStart_438872 baseEnd_438872 := by
    simpa [prefixWord, tailWord_438872, baseEnd_438872] using wordTrace_append hprefix tailTrace_438872
  have hstable : (prefixWord ++ tailWord_438872).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438872).length < 2 ^ (prefixWord ++ tailWord_438872).sum := by decide
  have hdescent : baseEnd_438872 < baseStart_438872 := by decide
  rcases family_descends (prefixWord ++ tailWord_438872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438896 : List Nat := [2, 1, 1, 1, 7, 1, 1, 6]
def baseStart_438896 : Nat := 118140960795 + 438896 * 2 ^ 59
def prefixEnd_438896 : Nat := 4983230072969 + 3 ^ 40 * 438896 * 2
def baseEnd_438896 : Nat := 66774697877280015135277

theorem tailTrace_438896 : CollatzResearch.WordTrace tailWord_438896 prefixEnd_438896 66774697877280015135277 := by
  unfold tailWord_438896
  simp only [CollatzResearch.WordTrace]
  refine ⟨8003926108981112157120271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10671901478641482876160361 8003926108981112157120271)
  ·
    refine ⟨12005889163471668235680407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8003926108981112157120271 12005889163471668235680407)
    ·
      refine ⟨18008833745207502353520611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12005889163471668235680407 18008833745207502353520611)
      ·
        refine ⟨27013250617811253530280917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18008833745207502353520611 27013250617811253530280917)
        ·
          refine ⟨633123061354951254615959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 27013250617811253530280917 633123061354951254615959)
          ·
            refine ⟨949684592032426881923939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 633123061354951254615959 949684592032426881923939)
            ·
              refine ⟨1424526888048640322885909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 949684592032426881923939 1424526888048640322885909)
              ·
                refine ⟨66774697877280015135277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1424526888048640322885909 66774697877280015135277)
                ·
                  rfl

theorem cell20_438896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 6].length) (baseStart_438896 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_438896 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_438896 prefixEnd_438896 := by exact prefixLift 438896
  have htrace : WordTrace (prefixWord ++ tailWord_438896) baseStart_438896 baseEnd_438896 := by
    simpa [prefixWord, tailWord_438896, baseEnd_438896] using wordTrace_append hprefix tailTrace_438896
  have hstable : (prefixWord ++ tailWord_438896).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438896).length < 2 ^ (prefixWord ++ tailWord_438896).sum := by decide
  have hdescent : baseEnd_438896 < baseStart_438896 := by decide
  rcases family_descends (prefixWord ++ tailWord_438896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438902 : List Nat := [5, 1, 1, 2, 3, 2, 1, 3, 2]
def baseStart_438902 : Nat := 118140960795 + 438902 * 2 ^ 59
def prefixEnd_438902 : Nat := 4983230072969 + 3 ^ 40 * 438902 * 2
def baseEnd_438902 : Nat := 200326832195330691205807

theorem tailTrace_438902 : CollatzResearch.WordTrace tailWord_438902 prefixEnd_438902 200326832195330691205807 := by
  unfold tailWord_438902
  simp only [CollatzResearch.WordTrace]
  refine ⟨1000504440996280458684935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10672047370626991559305973 1000504440996280458684935)
  ·
    refine ⟨1500756661494420688027403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1000504440996280458684935 1500756661494420688027403)
    ·
      refine ⟨2251134992241631032041105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1500756661494420688027403 2251134992241631032041105)
      ·
        refine ⟨1688351244181223274030829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2251134992241631032041105 1688351244181223274030829)
        ·
          refine ⟨633131716567958727761561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1688351244181223274030829 633131716567958727761561)
          ·
            refine ⟨474848787425969045821171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 633131716567958727761561 474848787425969045821171)
            ·
              refine ⟨712273181138953568731757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 474848787425969045821171 712273181138953568731757)
              ·
                refine ⟨267102442927107588274409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 712273181138953568731757 267102442927107588274409)
                ·
                  refine ⟨200326832195330691205807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 267102442927107588274409 200326832195330691205807)
                  ·
                    rfl

theorem cell20_438902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_438902 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_438902 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_438902 prefixEnd_438902 := by exact prefixLift 438902
  have htrace : WordTrace (prefixWord ++ tailWord_438902) baseStart_438902 baseEnd_438902 := by
    simpa [prefixWord, tailWord_438902, baseEnd_438902] using wordTrace_append hprefix tailTrace_438902
  have hstable : (prefixWord ++ tailWord_438902).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438902).length < 2 ^ (prefixWord ++ tailWord_438902).sum := by decide
  have hdescent : baseEnd_438902 < baseStart_438902 := by decide
  rcases family_descends (prefixWord ++ tailWord_438902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438917 : List Nat := [1, 3, 1, 1, 4, 2, 8]
def baseStart_438917 : Nat := 118140960795 + 438917 * 2 ^ 59
def prefixEnd_438917 : Nat := 4983230072969 + 3 ^ 40 * 438917 * 2
def baseEnd_438917 : Nat := 22259297622673033967305

theorem tailTrace_438917 : CollatzResearch.WordTrace tailWord_438917 prefixEnd_438917 22259297622673033967305 := by
  unfold tailWord_438917
  simp only [CollatzResearch.WordTrace]
  refine ⟨16008618150886144900755005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10672412100590763267170003 16008618150886144900755005)
  ·
    refine ⟨6003231806582304337783127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16008618150886144900755005 6003231806582304337783127)
    ·
      refine ⟨9004847709873456506674691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6003231806582304337783127 9004847709873456506674691)
      ·
        refine ⟨13507271564810184760012037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9004847709873456506674691 13507271564810184760012037)
        ·
          refine ⟨2532613418401909642502257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13507271564810184760012037 2532613418401909642502257)
          ·
            refine ⟨1899460063801432231876693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2532613418401909642502257 1899460063801432231876693)
            ·
              refine ⟨22259297622673033967305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1899460063801432231876693 22259297622673033967305)
              ·
                rfl

theorem cell20_438917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 8].length) (baseStart_438917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_438917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_438917 prefixEnd_438917 := by exact prefixLift 438917
  have htrace : WordTrace (prefixWord ++ tailWord_438917) baseStart_438917 baseEnd_438917 := by
    simpa [prefixWord, tailWord_438917, baseEnd_438917] using wordTrace_append hprefix tailTrace_438917
  have hstable : (prefixWord ++ tailWord_438917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438917).length < 2 ^ (prefixWord ++ tailWord_438917).sum := by decide
  have hdescent : baseEnd_438917 < baseStart_438917 := by decide
  rcases family_descends (prefixWord ++ tailWord_438917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438948 : List Nat := [2, 3, 1, 2, 2, 1, 2, 1, 6]
def baseStart_438948 : Nat := 118140960795 + 438948 * 2 ^ 59
def prefixEnd_438948 : Nat := 4983230072969 + 3 ^ 40 * 438948 * 2
def baseEnd_438948 : Nat := 200347827848758975672285

theorem tailTrace_438948 : CollatzResearch.WordTrace tailWord_438948 prefixEnd_438948 200347827848758975672285 := by
  unfold tailWord_438948
  simp only [CollatzResearch.WordTrace]
  refine ⟨8004874406886918597566749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10673165875849224796755665 8004874406886918597566749)
  ·
    refine ⟨3001827902582594474087531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8004874406886918597566749 3001827902582594474087531)
    ·
      refine ⟨4502741853873891711131297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3001827902582594474087531 4502741853873891711131297)
      ·
        refine ⟨3377056390405418783348473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4502741853873891711131297 3377056390405418783348473)
        ·
          refine ⟨2532792292804064087511355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3377056390405418783348473 2532792292804064087511355)
          ·
            refine ⟨3799188439206096131267033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2532792292804064087511355 3799188439206096131267033)
            ·
              refine ⟨2849391329404572098450275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3799188439206096131267033 2849391329404572098450275)
              ·
                refine ⟨4274086994106858147675413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2849391329404572098450275 4274086994106858147675413)
                ·
                  refine ⟨200347827848758975672285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4274086994106858147675413 200347827848758975672285)
                  ·
                    rfl

theorem cell20_438948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_438948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_438948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_438948 prefixEnd_438948 := by exact prefixLift 438948
  have htrace : WordTrace (prefixWord ++ tailWord_438948) baseStart_438948 baseEnd_438948 := by
    simpa [prefixWord, tailWord_438948, baseEnd_438948] using wordTrace_append hprefix tailTrace_438948
  have hstable : (prefixWord ++ tailWord_438948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438948).length < 2 ^ (prefixWord ++ tailWord_438948).sum := by decide
  have hdescent : baseEnd_438948 < baseStart_438948 := by decide
  rcases family_descends (prefixWord ++ tailWord_438948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439082 : List Nat := [3, 1, 4, 3, 2, 1, 6]
def baseStart_439082 : Nat := 118140960795 + 439082 * 2 ^ 59
def prefixEnd_439082 : Nat := 4983230072969 + 3 ^ 40 * 439082 * 2
def baseEnd_439082 : Nat := 22267665455561118356119

theorem tailTrace_439082 : CollatzResearch.WordTrace tailWord_439082 prefixEnd_439082 22267665455561118356119 := by
  unfold tailWord_439082
  simp only [CollatzResearch.WordTrace]
  refine ⟨4003659048822094520127875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10676424130192252053674333 4003659048822094520127875)
  ·
    refine ⟨6005488573233141780191813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4003659048822094520127875 6005488573233141780191813)
    ·
      refine ⟨1126029107481214083785965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6005488573233141780191813 1126029107481214083785965)
      ·
        refine ⟨422260915305455281419737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1126029107481214083785965 422260915305455281419737)
        ·
          refine ⟨316695686479091461064803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 422260915305455281419737 316695686479091461064803)
          ·
            refine ⟨475043529718637191597205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316695686479091461064803 475043529718637191597205)
            ·
              refine ⟨22267665455561118356119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 475043529718637191597205 22267665455561118356119)
              ·
                rfl

theorem cell20_439082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 6].length) (baseStart_439082 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_439082 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_439082 prefixEnd_439082 := by exact prefixLift 439082
  have htrace : WordTrace (prefixWord ++ tailWord_439082) baseStart_439082 baseEnd_439082 := by
    simpa [prefixWord, tailWord_439082, baseEnd_439082] using wordTrace_append hprefix tailTrace_439082
  have hstable : (prefixWord ++ tailWord_439082).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439082).length < 2 ^ (prefixWord ++ tailWord_439082).sum := by decide
  have hdescent : baseEnd_439082 < baseStart_439082 := by decide
  rcases family_descends (prefixWord ++ tailWord_439082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439083 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 8]
def baseStart_439083 : Nat := 118140960795 + 439083 * 2 ^ 59
def prefixEnd_439083 : Nat := 4983230072969 + 3 ^ 40 * 439083 * 2
def baseEnd_439083 : Nat := 200409445527298506171733

theorem tailTrace_439083 : CollatzResearch.WordTrace tailWord_439083 prefixEnd_439083 200409445527298506171733 := by
  unfold tailWord_439083
  simp only [CollatzResearch.WordTrace]
  refine ⟨16014672668284755251297903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10676448445523170167531935 16014672668284755251297903)
  ·
    refine ⟨24022009002427132876946855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16014672668284755251297903 24022009002427132876946855)
    ·
      refine ⟨36033013503640699315420283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24022009002427132876946855 36033013503640699315420283)
      ·
        refine ⟨54049520255461048973130425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36033013503640699315420283 54049520255461048973130425)
        ·
          refine ⟨40537140191595786729847819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54049520255461048973130425 40537140191595786729847819)
          ·
            refine ⟨60805710287393680094771729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40537140191595786729847819 60805710287393680094771729)
            ·
              refine ⟨45604282715545260071078797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60805710287393680094771729 45604282715545260071078797)
              ·
                refine ⟨17101606018329472526654549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45604282715545260071078797 17101606018329472526654549)
                ·
                  refine ⟨200409445527298506171733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17101606018329472526654549 200409445527298506171733)
                  ·
                    rfl

theorem cell20_439083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 8].length) (baseStart_439083 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_439083 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_439083 prefixEnd_439083 := by exact prefixLift 439083
  have htrace : WordTrace (prefixWord ++ tailWord_439083) baseStart_439083 baseEnd_439083 := by
    simpa [prefixWord, tailWord_439083, baseEnd_439083] using wordTrace_append hprefix tailTrace_439083
  have hstable : (prefixWord ++ tailWord_439083).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439083).length < 2 ^ (prefixWord ++ tailWord_439083).sum := by decide
  have hdescent : baseEnd_439083 < baseStart_439083 := by decide
  rcases family_descends (prefixWord ++ tailWord_439083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439086 : List Nat := [4, 1, 3, 2, 1, 1, 8]
def baseStart_439086 : Nat := 118140960795 + 439086 * 2 ^ 59
def prefixEnd_439086 : Nat := 4983230072969 + 3 ^ 40 * 439086 * 2
def baseEnd_439086 : Nat := 22267868312115981007969

theorem tailTrace_439086 : CollatzResearch.WordTrace tailWord_439086 prefixEnd_439086 22267868312115981007969 := by
  unfold tailWord_439086
  simp only [CollatzResearch.WordTrace]
  refine ⟨2001847760909235845457139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10676521391515924509104741 2001847760909235845457139)
  ·
    refine ⟨3002771641363853768185709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2001847760909235845457139 3002771641363853768185709)
    ·
      refine ⟨1126039365511445163069641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3002771641363853768185709 1126039365511445163069641)
      ·
        refine ⟨844529524133583872302231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1126039365511445163069641 844529524133583872302231)
        ·
          refine ⟨1266794286200375808453347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 844529524133583872302231 1266794286200375808453347)
          ·
            refine ⟨1900191429300563712680021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1266794286200375808453347 1900191429300563712680021)
            ·
              refine ⟨22267868312115981007969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1900191429300563712680021 22267868312115981007969)
              ·
                rfl

theorem cell20_439086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 8].length) (baseStart_439086 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_439086 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_439086 prefixEnd_439086 := by exact prefixLift 439086
  have htrace : WordTrace (prefixWord ++ tailWord_439086) baseStart_439086 baseEnd_439086 := by
    simpa [prefixWord, tailWord_439086, baseEnd_439086] using wordTrace_append hprefix tailTrace_439086
  have hstable : (prefixWord ++ tailWord_439086).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439086).length < 2 ^ (prefixWord ++ tailWord_439086).sum := by decide
  have hdescent : baseEnd_439086 < baseStart_439086 := by decide
  rcases family_descends (prefixWord ++ tailWord_439086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439092 : List Nat := [2, 5, 1, 1, 3, 1, 3, 2, 2]
def baseStart_439092 : Nat := 118140960795 + 439092 * 2 ^ 59
def prefixEnd_439092 : Nat := 4983230072969 + 3 ^ 40 * 439092 * 2
def baseEnd_439092 : Nat := 200413553372534474871697

theorem tailTrace_439092 : CollatzResearch.WordTrace tailWord_439092 prefixEnd_439092 200413553372534474871697 := by
  unfold tailWord_439092
  simp only [CollatzResearch.WordTrace]
  refine ⟨8007500462626074894187765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10676667283501433192250353 8007500462626074894187765)
  ·
    refine ⟨750703168371194521330103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8007500462626074894187765 750703168371194521330103)
    ·
      refine ⟨1126054752556791781995155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 750703168371194521330103 1126054752556791781995155)
      ·
        refine ⟨1689082128835187672992733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1126054752556791781995155 1689082128835187672992733)
        ·
          refine ⟨633405798313195377372275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1689082128835187672992733 633405798313195377372275)
          ·
            refine ⟨950108697469793066058413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 633405798313195377372275 950108697469793066058413)
            ·
              refine ⟨356290761551172399771905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 950108697469793066058413 356290761551172399771905)
              ·
                refine ⟨267218071163379299828929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 356290761551172399771905 267218071163379299828929)
                ·
                  refine ⟨200413553372534474871697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 267218071163379299828929 200413553372534474871697)
                  ·
                    rfl

theorem cell20_439092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_439092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_439092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_439092 prefixEnd_439092 := by exact prefixLift 439092
  have htrace : WordTrace (prefixWord ++ tailWord_439092) baseStart_439092 baseEnd_439092 := by
    simpa [prefixWord, tailWord_439092, baseEnd_439092] using wordTrace_append hprefix tailTrace_439092
  have hstable : (prefixWord ++ tailWord_439092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439092).length < 2 ^ (prefixWord ++ tailWord_439092).sum := by decide
  have hdescent : baseEnd_439092 < baseStart_439092 := by decide
  rcases family_descends (prefixWord ++ tailWord_439092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439093 : List Nat := [1, 3, 3, 1, 3, 1, 2, 1, 5]
def baseStart_439093 : Nat := 118140960795 + 439093 * 2 ^ 59
def prefixEnd_439093 : Nat := 4983230072969 + 3 ^ 40 * 439093 * 2
def baseEnd_439093 : Nat := 200414009799782915838359

theorem tailTrace_439093 : CollatzResearch.WordTrace tailWord_439093 prefixEnd_439093 200414009799782915838359 := by
  unfold tailWord_439093
  simp only [CollatzResearch.WordTrace]
  refine ⟨16015037398248526959161933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10676691598832351306107955 16015037398248526959161933)
  ·
    refine ⟨6005639024343197609685725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16015037398248526959161933 6005639024343197609685725)
    ·
      refine ⟨2252114634128699103632147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6005639024343197609685725 2252114634128699103632147)
      ·
        refine ⟨3378171951193048655448221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2252114634128699103632147 3378171951193048655448221)
        ·
          refine ⟨1266814481697393245793083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3378171951193048655448221 1266814481697393245793083)
          ·
            refine ⟨1900221722546089868689625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1266814481697393245793083 1900221722546089868689625)
            ·
              refine ⟨1425166291909567401517219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1900221722546089868689625 1425166291909567401517219)
              ·
                refine ⟨2137749437864351102275829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1425166291909567401517219 2137749437864351102275829)
                ·
                  refine ⟨200414009799782915838359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2137749437864351102275829 200414009799782915838359)
                  ·
                    rfl

theorem cell20_439093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_439093 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_439093 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_439093 prefixEnd_439093 := by exact prefixLift 439093
  have htrace : WordTrace (prefixWord ++ tailWord_439093) baseStart_439093 baseEnd_439093 := by
    simpa [prefixWord, tailWord_439093, baseEnd_439093] using wordTrace_append hprefix tailTrace_439093
  have hstable : (prefixWord ++ tailWord_439093).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439093).length < 2 ^ (prefixWord ++ tailWord_439093).sum := by decide
  have hdescent : baseEnd_439093 < baseStart_439093 := by decide
  rcases family_descends (prefixWord ++ tailWord_439093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439096 : List Nat := [2, 1, 2, 1, 3, 2, 5, 2, 2]
def baseStart_439096 : Nat := 118140960795 + 439096 * 2 ^ 59
def prefixEnd_439096 : Nat := 4983230072969 + 3 ^ 40 * 439096 * 2
def baseEnd_439096 : Nat := 200415379081528238738347

theorem tailTrace_439096 : CollatzResearch.WordTrace tailWord_439096 prefixEnd_439096 200415379081528238738347 := by
  unfold tailWord_439096
  simp only [CollatzResearch.WordTrace]
  refine ⟨8007573408618829235760571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10676764544825105647680761 8007573408618829235760571)
  ·
    refine ⟨12011360112928243853640857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8007573408618829235760571 12011360112928243853640857)
    ·
      refine ⟨9008520084696182890230643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12011360112928243853640857 9008520084696182890230643)
      ·
        refine ⟨13512780127044274335345965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9008520084696182890230643 13512780127044274335345965)
        ·
          refine ⟨5067292547641602875754737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13512780127044274335345965 5067292547641602875754737)
          ·
            refine ⟨3800469410731202156816053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5067292547641602875754737 3800469410731202156816053)
            ·
              refine ⟨356294007256050202201505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3800469410731202156816053 356294007256050202201505)
              ·
                refine ⟨267220505442037651651129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 356294007256050202201505 267220505442037651651129)
                ·
                  refine ⟨200415379081528238738347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 267220505442037651651129 200415379081528238738347)
                  ·
                    rfl

theorem cell20_439096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 2, 2].length) (baseStart_439096 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_439096 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_439096 prefixEnd_439096 := by exact prefixLift 439096
  have htrace : WordTrace (prefixWord ++ tailWord_439096) baseStart_439096 baseEnd_439096 := by
    simpa [prefixWord, tailWord_439096, baseEnd_439096] using wordTrace_append hprefix tailTrace_439096
  have hstable : (prefixWord ++ tailWord_439096).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439096).length < 2 ^ (prefixWord ++ tailWord_439096).sum := by decide
  have hdescent : baseEnd_439096 < baseStart_439096 := by decide
  rcases family_descends (prefixWord ++ tailWord_439096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439107 : List Nat := [1, 1, 1, 3, 1, 4, 4, 5]
def baseStart_439107 : Nat := 118140960795 + 439107 * 2 ^ 59
def prefixEnd_439107 : Nat := 4983230072969 + 3 ^ 40 * 439107 * 2
def baseEnd_439107 : Nat := 66806799927087029790545

theorem tailTrace_439107 : CollatzResearch.WordTrace tailWord_439107 prefixEnd_439107 66806799927087029790545 := by
  unfold tailWord_439107
  simp only [CollatzResearch.WordTrace]
  refine ⟨16015548020197807350171575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10677032013465204900114383 16015548020197807350171575)
  ·
    refine ⟨24023322030296711025257363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16015548020197807350171575 24023322030296711025257363)
    ·
      refine ⟨36034983045445066537886045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24023322030296711025257363 36034983045445066537886045)
      ·
        refine ⟨13513118642041899951707267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36034983045445066537886045 13513118642041899951707267)
        ·
          refine ⟨20269677963062849927560901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13513118642041899951707267 20269677963062849927560901)
          ·
            refine ⟨3800564618074284361417669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20269677963062849927560901 3800564618074284361417669)
            ·
              refine ⟨712605865888928317765813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3800564618074284361417669 712605865888928317765813)
              ·
                refine ⟨66806799927087029790545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 712605865888928317765813 66806799927087029790545)
                ·
                  rfl

theorem cell20_439107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 5].length) (baseStart_439107 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_439107 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_439107 prefixEnd_439107 := by exact prefixLift 439107
  have htrace : WordTrace (prefixWord ++ tailWord_439107) baseStart_439107 baseEnd_439107 := by
    simpa [prefixWord, tailWord_439107, baseEnd_439107] using wordTrace_append hprefix tailTrace_439107
  have hstable : (prefixWord ++ tailWord_439107).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439107).length < 2 ^ (prefixWord ++ tailWord_439107).sum := by decide
  have hdescent : baseEnd_439107 < baseStart_439107 := by decide
  rcases family_descends (prefixWord ++ tailWord_439107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439114 : List Nat := [3, 1, 2, 1, 1, 1, 2, 2, 7]
def baseStart_439114 : Nat := 118140960795 + 439114 * 2 ^ 59
def prefixEnd_439114 : Nat := 4983230072969 + 3 ^ 40 * 439114 * 2
def baseEnd_439114 : Nat := 200423594772000176138273

theorem tailTrace_439114 : CollatzResearch.WordTrace tailWord_439114 prefixEnd_439114 200423594772000176138273 := by
  unfold tailWord_439114
  simp only [CollatzResearch.WordTrace]
  refine ⟨4003950832793111886419099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10677202220781631697117597 4003950832793111886419099)
  ·
    refine ⟨6005926249189667829628649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4003950832793111886419099 6005926249189667829628649)
    ·
      refine ⟨4504444686892250872221487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6005926249189667829628649 4504444686892250872221487)
      ·
        refine ⟨6756667030338376308332231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4504444686892250872221487 6756667030338376308332231)
        ·
          refine ⟨10135000545507564462498347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6756667030338376308332231 10135000545507564462498347)
          ·
            refine ⟨15202500818261346693747521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10135000545507564462498347 15202500818261346693747521)
            ·
              refine ⟨11401875613696010020310641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15202500818261346693747521 11401875613696010020310641)
              ·
                refine ⟨8551406710272007515232981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11401875613696010020310641 8551406710272007515232981)
                ·
                  refine ⟨200423594772000176138273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8551406710272007515232981 200423594772000176138273)
                  ·
                    rfl

theorem cell20_439114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_439114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_439114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_439114 prefixEnd_439114 := by exact prefixLift 439114
  have htrace : WordTrace (prefixWord ++ tailWord_439114) baseStart_439114 baseEnd_439114 := by
    simpa [prefixWord, tailWord_439114, baseEnd_439114] using wordTrace_append hprefix tailTrace_439114
  have hstable : (prefixWord ++ tailWord_439114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439114).length < 2 ^ (prefixWord ++ tailWord_439114).sum := by decide
  have hdescent : baseEnd_439114 < baseStart_439114 := by decide
  rcases family_descends (prefixWord ++ tailWord_439114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439152 : List Nat := [2, 1, 1, 1, 4, 1, 2, 3, 5]
def baseStart_439152 : Nat := 118140960795 + 439152 * 2 ^ 59
def prefixEnd_439152 : Nat := 4983230072969 + 3 ^ 40 * 439152 * 2
def baseEnd_439152 : Nat := 200440939007440932871451

theorem tailTrace_439152 : CollatzResearch.WordTrace tailWord_439152 prefixEnd_439152 200440939007440932871451 := by
  unfold tailWord_439152
  simp only [CollatzResearch.WordTrace]
  refine ⟨8008594652517390017779855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10678126203356520023706473 8008594652517390017779855)
  ·
    refine ⟨12012891978776085026669783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8008594652517390017779855 12012891978776085026669783)
    ·
      refine ⟨18019337968164127540004675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12012891978776085026669783 18019337968164127540004675)
      ·
        refine ⟨27029006952246191310007013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18019337968164127540004675 27029006952246191310007013)
        ·
          refine ⟨5067938803546160870626315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27029006952246191310007013 5067938803546160870626315)
          ·
            refine ⟨7601908205319241305939473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5067938803546160870626315 7601908205319241305939473)
            ·
              refine ⟨5701431153989430979454605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7601908205319241305939473 5701431153989430979454605)
              ·
                refine ⟨2138036682746036617295477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5701431153989430979454605 2138036682746036617295477)
                ·
                  refine ⟨200440939007440932871451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2138036682746036617295477 200440939007440932871451)
                  ·
                    rfl

theorem cell20_439152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 5].length) (baseStart_439152 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_439152 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_439152 prefixEnd_439152 := by exact prefixLift 439152
  have htrace : WordTrace (prefixWord ++ tailWord_439152) baseStart_439152 baseEnd_439152 := by
    simpa [prefixWord, tailWord_439152, baseEnd_439152] using wordTrace_append hprefix tailTrace_439152
  have hstable : (prefixWord ++ tailWord_439152).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439152).length < 2 ^ (prefixWord ++ tailWord_439152).sum := by decide
  have hdescent : baseEnd_439152 < baseStart_439152 := by decide
  rcases family_descends (prefixWord ++ tailWord_439152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439159 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 8]
def baseStart_439159 : Nat := 118140960795 + 439159 * 2 ^ 59
def prefixEnd_439159 : Nat := 4983230072969 + 3 ^ 40 * 439159 * 2
def baseEnd_439159 : Nat := 200444133998180019638089

theorem tailTrace_439159 : CollatzResearch.WordTrace tailWord_439159 prefixEnd_439159 200444133998180019638089 := by
  unfold tailWord_439159
  simp only [CollatzResearch.WordTrace]
  refine ⟨16017444616009420231064531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10678296410672946820709687 16017444616009420231064531)
  ·
    refine ⟨24026166924014130346596797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16017444616009420231064531 24026166924014130346596797)
    ·
      refine ⟨9009812596505298879973799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24026166924014130346596797 9009812596505298879973799)
      ·
        refine ⟨13514718894757948319960699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9009812596505298879973799 13514718894757948319960699)
        ·
          refine ⟨20272078342136922479941049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13514718894757948319960699 20272078342136922479941049)
          ·
            refine ⟨15204058756602691859955787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20272078342136922479941049 15204058756602691859955787)
            ·
              refine ⟨22806088134904037789933681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15204058756602691859955787 22806088134904037789933681)
              ·
                refine ⟨17104566101178028342450261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22806088134904037789933681 17104566101178028342450261)
                ·
                  refine ⟨200444133998180019638089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17104566101178028342450261 200444133998180019638089)
                  ·
                    rfl

theorem cell20_439159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 8].length) (baseStart_439159 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_439159 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_439159 prefixEnd_439159 := by exact prefixLift 439159
  have htrace : WordTrace (prefixWord ++ tailWord_439159) baseStart_439159 baseEnd_439159 := by
    simpa [prefixWord, tailWord_439159, baseEnd_439159] using wordTrace_append hprefix tailTrace_439159
  have hstable : (prefixWord ++ tailWord_439159).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439159).length < 2 ^ (prefixWord ++ tailWord_439159).sum := by decide
  have hdescent : baseEnd_439159 < baseStart_439159 := by decide
  rcases family_descends (prefixWord ++ tailWord_439159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439176 : List Nat := [2, 1, 3, 3, 2, 1, 1, 1, 6]
def baseStart_439176 : Nat := 118140960795 + 439176 * 2 ^ 59
def prefixEnd_439176 : Nat := 4983230072969 + 3 ^ 40 * 439176 * 2
def baseEnd_439176 : Nat := 200451893261403516071353

theorem tailTrace_439176 : CollatzResearch.WordTrace tailWord_439176 prefixEnd_439176 200451893261403516071353 := by
  unfold tailWord_439176
  simp only [CollatzResearch.WordTrace]
  refine ⟨8009032328473916067216691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10678709771298554756288921 8009032328473916067216691)
  ·
    refine ⟨12013548492710874100825037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8009032328473916067216691 12013548492710874100825037)
    ·
      refine ⟨4505080684766577787809389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12013548492710874100825037 4505080684766577787809389)
      ·
        refine ⟨1689405256787466670428521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4505080684766577787809389 1689405256787466670428521)
        ·
          refine ⟨1267053942590600002821391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1689405256787466670428521 1267053942590600002821391)
          ·
            refine ⟨1900580913885900004232087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1267053942590600002821391 1900580913885900004232087)
            ·
              refine ⟨2850871370828850006348131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1900580913885900004232087 2850871370828850006348131)
              ·
                refine ⟨4276307056243275009522197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2850871370828850006348131 4276307056243275009522197)
                ·
                  refine ⟨200451893261403516071353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4276307056243275009522197 200451893261403516071353)
                  ·
                    rfl

theorem cell20_439176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 6].length) (baseStart_439176 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_439176 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_439176 prefixEnd_439176 := by exact prefixLift 439176
  have htrace : WordTrace (prefixWord ++ tailWord_439176) baseStart_439176 baseEnd_439176 := by
    simpa [prefixWord, tailWord_439176, baseEnd_439176] using wordTrace_append hprefix tailTrace_439176
  have hstable : (prefixWord ++ tailWord_439176).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439176).length < 2 ^ (prefixWord ++ tailWord_439176).sum := by decide
  have hdescent : baseEnd_439176 < baseStart_439176 := by decide
  rcases family_descends (prefixWord ++ tailWord_439176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439220 : List Nat := [2, 5, 2, 1, 1, 2, 3, 1, 3]
def baseStart_439220 : Nat := 118140960795 + 439220 * 2 ^ 59
def prefixEnd_439220 : Nat := 4983230072969 + 3 ^ 40 * 439220 * 2
def baseEnd_439220 : Nat := 200471976060334918604507

theorem tailTrace_439220 : CollatzResearch.WordTrace tailWord_439220 prefixEnd_439220 200471976060334918604507 := by
  unfold tailWord_439220
  simp only [CollatzResearch.WordTrace]
  refine ⟨8009834734394213824517557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10679779645858951766023409 8009834734394213824517557)
  ·
    refine ⟨750922006349457546048521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8009834734394213824517557 750922006349457546048521)
    ·
      refine ⟨563191504762093159536391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 750922006349457546048521 563191504762093159536391)
      ·
        refine ⟨844787257143139739304587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 563191504762093159536391 844787257143139739304587)
        ·
          refine ⟨1267180885714709608956881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 844787257143139739304587 1267180885714709608956881)
          ·
            refine ⟨950385664286032206717661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1267180885714709608956881 950385664286032206717661)
            ·
              refine ⟨356394624107262077519123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 950385664286032206717661 356394624107262077519123)
              ·
                refine ⟨534591936160893116278685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 356394624107262077519123 534591936160893116278685)
                ·
                  refine ⟨200471976060334918604507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 534591936160893116278685 200471976060334918604507)
                  ·
                    rfl

theorem cell20_439220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_439220 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_439220 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_439220 prefixEnd_439220 := by exact prefixLift 439220
  have htrace : WordTrace (prefixWord ++ tailWord_439220) baseStart_439220 baseEnd_439220 := by
    simpa [prefixWord, tailWord_439220, baseEnd_439220] using wordTrace_append hprefix tailTrace_439220
  have hstable : (prefixWord ++ tailWord_439220).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439220).length < 2 ^ (prefixWord ++ tailWord_439220).sum := by decide
  have hdescent : baseEnd_439220 < baseStart_439220 := by decide
  rcases family_descends (prefixWord ++ tailWord_439220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439221 : List Nat := [1, 3, 3, 2, 1, 1, 2, 7]
def baseStart_439221 : Nat := 118140960795 + 439221 * 2 ^ 59
def prefixEnd_439221 : Nat := 4983230072969 + 3 ^ 40 * 439221 * 2
def baseEnd_439221 : Nat := 66824144162527786523723

theorem tailTrace_439221 : CollatzResearch.WordTrace tailWord_439221 prefixEnd_439221 66824144162527786523723 := by
  unfold tailWord_439221
  simp only [CollatzResearch.WordTrace]
  refine ⟨16019705941784804819821517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10679803961189869879881011 16019705941784804819821517)
  ·
    refine ⟨6007389728169301807433069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16019705941784804819821517 6007389728169301807433069)
    ·
      refine ⟨2252771148063488177787401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6007389728169301807433069 2252771148063488177787401)
      ·
        refine ⟨1689578361047616133340551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2252771148063488177787401 1689578361047616133340551)
        ·
          refine ⟨2534367541571424200010827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1689578361047616133340551 2534367541571424200010827)
          ·
            refine ⟨3801551312357136300016241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2534367541571424200010827 3801551312357136300016241)
            ·
              refine ⟨2851163484267852225012181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3801551312357136300016241 2851163484267852225012181)
              ·
                refine ⟨66824144162527786523723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2851163484267852225012181 66824144162527786523723)
                ·
                  rfl

theorem cell20_439221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 7].length) (baseStart_439221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_439221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_439221 prefixEnd_439221 := by exact prefixLift 439221
  have htrace : WordTrace (prefixWord ++ tailWord_439221) baseStart_439221 baseEnd_439221 := by
    simpa [prefixWord, tailWord_439221, baseEnd_439221] using wordTrace_append hprefix tailTrace_439221
  have hstable : (prefixWord ++ tailWord_439221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439221).length < 2 ^ (prefixWord ++ tailWord_439221).sum := by decide
  have hdescent : baseEnd_439221 < baseStart_439221 := by decide
  rcases family_descends (prefixWord ++ tailWord_439221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439224 : List Nat := [2, 1, 2, 1, 2, 5, 3, 1, 3]
def baseStart_439224 : Nat := 118140960795 + 439224 * 2 ^ 59
def prefixEnd_439224 : Nat := 4983230072969 + 3 ^ 40 * 439224 * 2
def baseEnd_439224 : Nat := 200473801769328682471157

theorem tailTrace_439224 : CollatzResearch.WordTrace tailWord_439224 prefixEnd_439224 200473801769328682471157 := by
  unfold tailWord_439224
  simp only [CollatzResearch.WordTrace]
  refine ⟨8009907680386968166090363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10679876907182624221453817 8009907680386968166090363)
  ·
    refine ⟨12014861520580452249135545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8009907680386968166090363 12014861520580452249135545)
    ·
      refine ⟨9011146140435339186851659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12014861520580452249135545 9011146140435339186851659)
      ·
        refine ⟨13516719210653008780277489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9011146140435339186851659 13516719210653008780277489)
        ·
          refine ⟨10137539407989756585208117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13516719210653008780277489 10137539407989756585208117)
          ·
            refine ⟨950394319499039679863261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10137539407989756585208117 950394319499039679863261)
            ·
              refine ⟨356397869812139879948723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 950394319499039679863261 356397869812139879948723)
              ·
                refine ⟨534596804718209819923085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 356397869812139879948723 534596804718209819923085)
                ·
                  refine ⟨200473801769328682471157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 534596804718209819923085 200473801769328682471157)
                  ·
                    rfl

theorem cell20_439224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 1, 3].length) (baseStart_439224 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_439224 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_439224 prefixEnd_439224 := by exact prefixLift 439224
  have htrace : WordTrace (prefixWord ++ tailWord_439224) baseStart_439224 baseEnd_439224 := by
    simpa [prefixWord, tailWord_439224, baseEnd_439224] using wordTrace_append hprefix tailTrace_439224
  have hstable : (prefixWord ++ tailWord_439224).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439224).length < 2 ^ (prefixWord ++ tailWord_439224).sum := by decide
  have hdescent : baseEnd_439224 < baseStart_439224 := by decide
  rcases family_descends (prefixWord ++ tailWord_439224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439297 : List Nat := [1, 2, 4, 1, 2, 2, 2, 6]
def baseStart_439297 : Nat := 118140960795 + 439297 * 2 ^ 59
def prefixEnd_439297 : Nat := 4983230072969 + 3 ^ 40 * 439297 * 2
def baseEnd_439297 : Nat := 66835706986154957679175

theorem tailTrace_439297 : CollatzResearch.WordTrace tailWord_439297 prefixEnd_439297 66835706986154957679175 := by
  unfold tailWord_439297
  simp only [CollatzResearch.WordTrace]
  refine ⟨16022477889509469799588145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10681651926339646533058763 16022477889509469799588145)
  ·
    refine ⟨12016858417132102349691109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16022477889509469799588145 12016858417132102349691109)
    ·
      refine ⟨2253160953212269190567083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12016858417132102349691109 2253160953212269190567083)
      ·
        refine ⟨3379741429818403785850625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2253160953212269190567083 3379741429818403785850625)
        ·
          refine ⟨2534806072363802839387969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3379741429818403785850625 2534806072363802839387969)
          ·
            refine ⟨1901104554272852129540977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2534806072363802839387969 1901104554272852129540977)
            ·
              refine ⟨1425828415704639097155733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1901104554272852129540977 1425828415704639097155733)
              ·
                refine ⟨66835706986154957679175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1425828415704639097155733 66835706986154957679175)
                ·
                  rfl

theorem cell20_439297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 6].length) (baseStart_439297 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_439297 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_439297 prefixEnd_439297 := by exact prefixLift 439297
  have htrace : WordTrace (prefixWord ++ tailWord_439297) baseStart_439297 baseEnd_439297 := by
    simpa [prefixWord, tailWord_439297, baseEnd_439297] using wordTrace_append hprefix tailTrace_439297
  have hstable : (prefixWord ++ tailWord_439297).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439297).length < 2 ^ (prefixWord ++ tailWord_439297).sum := by decide
  have hdescent : baseEnd_439297 < baseStart_439297 := by decide
  rcases family_descends (prefixWord ++ tailWord_439297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439324 : List Nat := [2, 2, 3, 1, 4, 1, 1, 4, 2]
def baseStart_439324 : Nat := 118140960795 + 439324 * 2 ^ 59
def prefixEnd_439324 : Nat := 4983230072969 + 3 ^ 40 * 439324 * 2
def baseEnd_439324 : Nat := 200519444494172779137415

theorem tailTrace_439324 : CollatzResearch.WordTrace tailWord_439324 prefixEnd_439324 200519444494172779137415 := by
  unfold tailWord_439324
  simp only [CollatzResearch.WordTrace]
  refine ⟨8011731330205826705410513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10682308440274435607214017 8011731330205826705410513)
  ·
    refine ⟨6008798497654370029057885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8011731330205826705410513 6008798497654370029057885)
    ·
      refine ⟨2253299436620388760896707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6008798497654370029057885 2253299436620388760896707)
      ·
        refine ⟨3379949154930583141345061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2253299436620388760896707 3379949154930583141345061)
        ·
          refine ⟨633740466549484339002199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3379949154930583141345061 633740466549484339002199)
          ·
            refine ⟨950610699824226508503299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 633740466549484339002199 950610699824226508503299)
            ·
              refine ⟨1425916049736339762754949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 950610699824226508503299 1425916049736339762754949)
              ·
                refine ⟨267359259325563705516553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1425916049736339762754949 267359259325563705516553)
                ·
                  refine ⟨200519444494172779137415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 267359259325563705516553 200519444494172779137415)
                  ·
                    rfl

theorem cell20_439324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 4, 2].length) (baseStart_439324 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_439324 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_439324 prefixEnd_439324 := by exact prefixLift 439324
  have htrace : WordTrace (prefixWord ++ tailWord_439324) baseStart_439324 baseEnd_439324 := by
    simpa [prefixWord, tailWord_439324, baseEnd_439324] using wordTrace_append hprefix tailTrace_439324
  have hstable : (prefixWord ++ tailWord_439324).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439324).length < 2 ^ (prefixWord ++ tailWord_439324).sum := by decide
  have hdescent : baseEnd_439324 < baseStart_439324 := by decide
  rcases family_descends (prefixWord ++ tailWord_439324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439352 : List Nat := [2, 1, 2, 1, 5, 2, 3, 4]
def baseStart_439352 : Nat := 118140960795 + 439352 * 2 ^ 59
def prefixEnd_439352 : Nat := 4983230072969 + 3 ^ 40 * 439352 * 2
def baseEnd_439352 : Nat := 66844074819043042067989

theorem tailTrace_439352 : CollatzResearch.WordTrace tailWord_439352 prefixEnd_439352 66844074819043042067989 := by
  unfold tailWord_439352
  simp only [CollatzResearch.WordTrace]
  refine ⟨8012241952155107096420155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10682989269540142795226873 8012241952155107096420155)
  ·
    refine ⟨12018362928232660644630233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8012241952155107096420155 12018362928232660644630233)
    ·
      refine ⟨9013772196174495483472675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12018362928232660644630233 9013772196174495483472675)
      ·
        refine ⟨13520658294261743225209013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9013772196174495483472675 13520658294261743225209013)
        ·
          refine ⟨1267561715087038427363345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13520658294261743225209013 1267561715087038427363345)
          ·
            refine ⟨950671286315278820522509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1267561715087038427363345 950671286315278820522509)
            ·
              refine ⟨356501732368229557695941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 950671286315278820522509 356501732368229557695941)
              ·
                refine ⟨66844074819043042067989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 356501732368229557695941 66844074819043042067989)
                ·
                  rfl

theorem cell20_439352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 4].length) (baseStart_439352 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_439352 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_439352 prefixEnd_439352 := by exact prefixLift 439352
  have htrace : WordTrace (prefixWord ++ tailWord_439352) baseStart_439352 baseEnd_439352 := by
    simpa [prefixWord, tailWord_439352, baseEnd_439352] using wordTrace_append hprefix tailTrace_439352
  have hstable : (prefixWord ++ tailWord_439352).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439352).length < 2 ^ (prefixWord ++ tailWord_439352).sum := by decide
  have hdescent : baseEnd_439352 < baseStart_439352 := by decide
  rcases family_descends (prefixWord ++ tailWord_439352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439417 : List Nat := [1, 2, 1, 3, 6, 1, 1, 3, 2]
def baseStart_439417 : Nat := 118140960795 + 439417 * 2 ^ 59
def prefixEnd_439417 : Nat := 4983230072969 + 3 ^ 40 * 439417 * 2
def baseEnd_439417 : Nat := 200561892228277789037035

theorem tailTrace_439417 : CollatzResearch.WordTrace tailWord_439417 prefixEnd_439417 200561892228277789037035 := by
  unfold tailWord_439417
  simp only [CollatzResearch.WordTrace]
  refine ⟨16026854649074730293956505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10684569766049820195971003 16026854649074730293956505)
  ·
    refine ⟨12020140986806047720467379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16026854649074730293956505 12020140986806047720467379)
    ·
      refine ⟨18030211480209071580701069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12020140986806047720467379 18030211480209071580701069)
      ·
        refine ⟨6761329305078401842762901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18030211480209071580701069 6761329305078401842762901)
        ·
          refine ⟨316937311175550086379511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6761329305078401842762901 316937311175550086379511)
          ·
            refine ⟨475405966763325129569267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316937311175550086379511 475405966763325129569267)
            ·
              refine ⟨713108950144987694353901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 475405966763325129569267 713108950144987694353901)
              ·
                refine ⟨267415856304370385382713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 713108950144987694353901 267415856304370385382713)
                ·
                  refine ⟨200561892228277789037035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 267415856304370385382713 200561892228277789037035)
                  ·
                    rfl

theorem cell20_439417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 3, 2].length) (baseStart_439417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_439417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_439417 prefixEnd_439417 := by exact prefixLift 439417
  have htrace : WordTrace (prefixWord ++ tailWord_439417) baseStart_439417 baseEnd_439417 := by
    simpa [prefixWord, tailWord_439417, baseEnd_439417] using wordTrace_append hprefix tailTrace_439417
  have hstable : (prefixWord ++ tailWord_439417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439417).length < 2 ^ (prefixWord ++ tailWord_439417).sum := by decide
  have hdescent : baseEnd_439417 < baseStart_439417 := by decide
  rcases family_descends (prefixWord ++ tailWord_439417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439452 : List Nat := [2, 2, 3, 2, 1, 2, 4, 1, 3]
def baseStart_439452 : Nat := 118140960795 + 439452 * 2 ^ 59
def prefixEnd_439452 : Nat := 4983230072969 + 3 ^ 40 * 439452 * 2
def baseEnd_439452 : Nat := 200577867181973222870225

theorem tailTrace_439452 : CollatzResearch.WordTrace tailWord_439452 prefixEnd_439452 200577867181973222870225 := by
  unfold tailWord_439452
  simp only [CollatzResearch.WordTrace]
  refine ⟨8014065601973965635740305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10685420802631954180987073 8014065601973965635740305)
  ·
    refine ⟨6010549201480474226805229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8014065601973965635740305 6010549201480474226805229)
    ·
      refine ⟨2253955950555177835051961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6010549201480474226805229 2253955950555177835051961)
      ·
        refine ⟨1690466962916383376288971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2253955950555177835051961 1690466962916383376288971)
        ·
          refine ⟨2535700444374575064433457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1690466962916383376288971 2535700444374575064433457)
          ·
            refine ⟨1901775333280931298325093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2535700444374575064433457 1901775333280931298325093)
            ·
              refine ⟨356582874990174618435955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1901775333280931298325093 356582874990174618435955)
              ·
                refine ⟨534874312485261927653933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 356582874990174618435955 534874312485261927653933)
                ·
                  refine ⟨200577867181973222870225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 534874312485261927653933 200577867181973222870225)
                  ·
                    rfl

theorem cell20_439452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 1, 3].length) (baseStart_439452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_439452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_439452 prefixEnd_439452 := by exact prefixLift 439452
  have htrace : WordTrace (prefixWord ++ tailWord_439452) baseStart_439452 baseEnd_439452 := by
    simpa [prefixWord, tailWord_439452, baseEnd_439452] using wordTrace_append hprefix tailTrace_439452
  have hstable : (prefixWord ++ tailWord_439452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439452).length < 2 ^ (prefixWord ++ tailWord_439452).sum := by decide
  have hdescent : baseEnd_439452 < baseStart_439452 := by decide
  rcases family_descends (prefixWord ++ tailWord_439452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439466 : List Nat := [3, 1, 5, 1, 1, 1, 2, 6]
def baseStart_439466 : Nat := 118140960795 + 439466 * 2 ^ 59
def prefixEnd_439466 : Nat := 4983230072969 + 3 ^ 40 * 439466 * 2
def baseEnd_439466 : Nat := 66861419054483798801167

theorem tailTrace_439466 : CollatzResearch.WordTrace tailWord_439466 prefixEnd_439466 66861419054483798801167 := by
  unfold tailWord_439466
  simp only [CollatzResearch.WordTrace]
  refine ⟨4007160456474302915622563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10685761217264807774993501 4007160456474302915622563)
  ·
    refine ⟨6010740684711454373433845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4007160456474302915622563 6010740684711454373433845)
    ·
      refine ⟨563506939191698847509423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6010740684711454373433845 563506939191698847509423)
      ·
        refine ⟨845260408787548271264135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 563506939191698847509423 845260408787548271264135)
        ·
          refine ⟨1267890613181322406896203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 845260408787548271264135 1267890613181322406896203)
          ·
            refine ⟨1901835919771983610344305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1267890613181322406896203 1901835919771983610344305)
            ·
              refine ⟨1426376939828987707758229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1901835919771983610344305 1426376939828987707758229)
              ·
                refine ⟨66861419054483798801167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1426376939828987707758229 66861419054483798801167)
                ·
                  rfl

theorem cell20_439466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 6].length) (baseStart_439466 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_439466 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_439466 prefixEnd_439466 := by exact prefixLift 439466
  have htrace : WordTrace (prefixWord ++ tailWord_439466) baseStart_439466 baseEnd_439466 := by
    simpa [prefixWord, tailWord_439466, baseEnd_439466] using wordTrace_append hprefix tailTrace_439466
  have hstable : (prefixWord ++ tailWord_439466).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439466).length < 2 ^ (prefixWord ++ tailWord_439466).sum := by decide
  have hdescent : baseEnd_439466 < baseStart_439466 := by decide
  rcases family_descends (prefixWord ++ tailWord_439466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439546 : List Nat := [3, 1, 1, 1, 1, 4, 9]
def baseStart_439546 : Nat := 118140960795 + 439546 * 2 ^ 59
def prefixEnd_439546 : Nat := 4983230072969 + 3 ^ 40 * 439546 * 2
def baseEnd_439546 : Nat := 22291196815925185970723

theorem tailTrace_439546 : CollatzResearch.WordTrace tailWord_439546 prefixEnd_439546 22291196815925185970723 := by
  unfold tailWord_439546
  simp only [CollatzResearch.WordTrace]
  refine ⟨4007889916401846331350623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10687706443738256883601661 4007889916401846331350623)
  ·
    refine ⟨6011834874602769497025935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4007889916401846331350623 6011834874602769497025935)
    ·
      refine ⟨9017752311904154245538903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6011834874602769497025935 9017752311904154245538903)
      ·
        refine ⟨13526628467856231368308355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9017752311904154245538903 13526628467856231368308355)
        ·
          refine ⟨20289942701784347052462533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13526628467856231368308355 20289942701784347052462533)
          ·
            refine ⟨3804364256584565072336725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20289942701784347052462533 3804364256584565072336725)
            ·
              refine ⟨22291196815925185970723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3804364256584565072336725 22291196815925185970723)
              ·
                rfl

theorem cell20_439546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 9].length) (baseStart_439546 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_439546 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_439546 prefixEnd_439546 := by exact prefixLift 439546
  have htrace : WordTrace (prefixWord ++ tailWord_439546) baseStart_439546 baseEnd_439546 := by
    simpa [prefixWord, tailWord_439546, baseEnd_439546] using wordTrace_append hprefix tailTrace_439546
  have hstable : (prefixWord ++ tailWord_439546).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439546).length < 2 ^ (prefixWord ++ tailWord_439546).sum := by decide
  have hdescent : baseEnd_439546 < baseStart_439546 := by decide
  rcases family_descends (prefixWord ++ tailWord_439546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439556 : List Nat := [2, 3, 2, 2, 2, 1, 1, 3, 4]
def baseStart_439556 : Nat := 118140960795 + 439556 * 2 ^ 59
def prefixEnd_439556 : Nat := 4983230072969 + 3 ^ 40 * 439556 * 2
def baseEnd_439556 : Nat := 200625335615811083403133

theorem tailTrace_439556 : CollatzResearch.WordTrace tailWord_439556 prefixEnd_439556 200625335615811083403133 := by
  unfold tailWord_439556
  simp only [CollatzResearch.WordTrace]
  refine ⟨8015962197785578516633261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10687949597047438022177681 8015962197785578516633261)
  ·
    refine ⟨3005985824169591943737473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8015962197785578516633261 3005985824169591943737473)
    ·
      refine ⟨2254489368127193957803105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3005985824169591943737473 2254489368127193957803105)
      ·
        refine ⟨1690867026095395468352329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2254489368127193957803105 1690867026095395468352329)
        ·
          refine ⟨1268150269571546601264247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1690867026095395468352329 1268150269571546601264247)
          ·
            refine ⟨1902225404357319901896371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1268150269571546601264247 1902225404357319901896371)
            ·
              refine ⟨2853338106535979852844557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1902225404357319901896371 2853338106535979852844557)
              ·
                refine ⟨1070001789950992444816709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2853338106535979852844557 1070001789950992444816709)
                ·
                  refine ⟨200625335615811083403133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1070001789950992444816709 200625335615811083403133)
                  ·
                    rfl

theorem cell20_439556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_439556 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_439556 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_439556 prefixEnd_439556 := by exact prefixLift 439556
  have htrace : WordTrace (prefixWord ++ tailWord_439556) baseStart_439556 baseEnd_439556 := by
    simpa [prefixWord, tailWord_439556, baseEnd_439556] using wordTrace_append hprefix tailTrace_439556
  have hstable : (prefixWord ++ tailWord_439556).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439556).length < 2 ^ (prefixWord ++ tailWord_439556).sum := by decide
  have hdescent : baseEnd_439556 < baseStart_439556 := by decide
  rcases family_descends (prefixWord ++ tailWord_439556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439566 : List Nat := [4, 1, 1, 2, 1, 4, 3, 1, 3]
def baseStart_439566 : Nat := 118140960795 + 439566 * 2 ^ 59
def prefixEnd_439566 : Nat := 4983230072969 + 3 ^ 40 * 439566 * 2
def baseEnd_439566 : Nat := 200629899888295493069759

theorem tailTrace_439566 : CollatzResearch.WordTrace tailWord_439566 prefixEnd_439566 200629899888295493069759 := by
  unfold tailWord_439566
  simp only [CollatzResearch.WordTrace]
  refine ⟨2004036140691866092641319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10688192750356619160753701 2004036140691866092641319)
  ·
    refine ⟨3006054211037799138961979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2004036140691866092641319 3006054211037799138961979)
    ·
      refine ⟨4509081316556698708442969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3006054211037799138961979 4509081316556698708442969)
      ·
        refine ⟨3381810987417524031332227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4509081316556698708442969 3381810987417524031332227)
        ·
          refine ⟨5072716481126286046998341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3381810987417524031332227 5072716481126286046998341)
          ·
            refine ⟨951134340211178633812189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5072716481126286046998341 951134340211178633812189)
            ·
              refine ⟨356675377579191987679571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 951134340211178633812189 356675377579191987679571)
              ·
                refine ⟨535013066368787981519357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 356675377579191987679571 535013066368787981519357)
                ·
                  refine ⟨200629899888295493069759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 535013066368787981519357 200629899888295493069759)
                  ·
                    rfl

theorem cell20_439566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_439566 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_439566 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_439566 prefixEnd_439566 := by exact prefixLift 439566
  have htrace : WordTrace (prefixWord ++ tailWord_439566) baseStart_439566 baseEnd_439566 := by
    simpa [prefixWord, tailWord_439566, baseEnd_439566] using wordTrace_append hprefix tailTrace_439566
  have hstable : (prefixWord ++ tailWord_439566).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439566).length < 2 ^ (prefixWord ++ tailWord_439566).sum := by decide
  have hdescent : baseEnd_439566 < baseStart_439566 := by decide
  rcases family_descends (prefixWord ++ tailWord_439566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439601 : List Nat := [1, 2, 2, 3, 3, 3, 6]
def baseStart_439601 : Nat := 118140960795 + 439601 * 2 ^ 59
def prefixEnd_439601 : Nat := 4983230072969 + 3 ^ 40 * 439601 * 2
def baseEnd_439601 : Nat := 22293986093554547433661

theorem tailTrace_439601 : CollatzResearch.WordTrace tailWord_439601 prefixEnd_439601 22293986093554547433661 := by
  unfold tailWord_439601
  simp only [CollatzResearch.WordTrace]
  refine ⟨16033565680408129718654657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10689043786938753145769771 16033565680408129718654657)
  ·
    refine ⟨12025174260306097288990993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16033565680408129718654657 12025174260306097288990993)
    ·
      refine ⟨9018880695229572966743245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12025174260306097288990993 9018880695229572966743245)
      ·
        refine ⟨3382080260711089862528717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9018880695229572966743245 3382080260711089862528717)
        ·
          refine ⟨1268280097766658698448269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3382080260711089862528717 1268280097766658698448269)
          ·
            refine ⟨475605036662497011918101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1268280097766658698448269 475605036662497011918101)
            ·
              refine ⟨22293986093554547433661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 475605036662497011918101 22293986093554547433661)
              ·
                rfl

theorem cell20_439601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 6].length) (baseStart_439601 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_439601 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_439601 prefixEnd_439601 := by exact prefixLift 439601
  have htrace : WordTrace (prefixWord ++ tailWord_439601) baseStart_439601 baseEnd_439601 := by
    simpa [prefixWord, tailWord_439601, baseEnd_439601] using wordTrace_append hprefix tailTrace_439601
  have hstable : (prefixWord ++ tailWord_439601).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439601).length < 2 ^ (prefixWord ++ tailWord_439601).sum := by decide
  have hdescent : baseEnd_439601 < baseStart_439601 := by decide
  rcases family_descends (prefixWord ++ tailWord_439601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439608 : List Nat := [2, 1, 2, 1, 3, 1, 1, 6, 3]
def baseStart_439608 : Nat := 118140960795 + 439608 * 2 ^ 59
def prefixEnd_439608 : Nat := 4983230072969 + 3 ^ 40 * 439608 * 2
def baseEnd_439608 : Nat := 200649069832730013669587

theorem tailTrace_439608 : CollatzResearch.WordTrace tailWord_439608 prefixEnd_439608 200649069832730013669587 := by
  unfold tailWord_439608
  simp only [CollatzResearch.WordTrace]
  refine ⟨8016910495691384957079739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10689213994255179942772985 8016910495691384957079739)
  ·
    refine ⟨12025365743537077435619609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8016910495691384957079739 12025365743537077435619609)
    ·
      refine ⟨9019024307652808076714707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12025365743537077435619609 9019024307652808076714707)
      ·
        refine ⟨13528536461479212115072061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9019024307652808076714707 13528536461479212115072061)
        ·
          refine ⟨5073201173054704543152023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13528536461479212115072061 5073201173054704543152023)
          ·
            refine ⟨7609801759582056814728035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5073201173054704543152023 7609801759582056814728035)
            ·
              refine ⟨11414702639373085222092053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7609801759582056814728035 11414702639373085222092053)
              ·
                refine ⟨535064186220613369785565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11414702639373085222092053 535064186220613369785565)
                ·
                  refine ⟨200649069832730013669587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 535064186220613369785565 200649069832730013669587)
                  ·
                    rfl

theorem cell20_439608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 6, 3].length) (baseStart_439608 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_439608 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_439608 prefixEnd_439608 := by exact prefixLift 439608
  have htrace : WordTrace (prefixWord ++ tailWord_439608) baseStart_439608 baseEnd_439608 := by
    simpa [prefixWord, tailWord_439608, baseEnd_439608] using wordTrace_append hprefix tailTrace_439608
  have hstable : (prefixWord ++ tailWord_439608).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439608).length < 2 ^ (prefixWord ++ tailWord_439608).sum := by decide
  have hdescent : baseEnd_439608 < baseStart_439608 := by decide
  rcases family_descends (prefixWord ++ tailWord_439608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439625 : List Nat := [1, 2, 1, 1, 2, 3, 6, 1, 3]
def baseStart_439625 : Nat := 118140960795 + 439625 * 2 ^ 59
def prefixEnd_439625 : Nat := 4983230072969 + 3 ^ 40 * 439625 * 2
def baseEnd_439625 : Nat := 200656829095953510102851

theorem tailTrace_439625 : CollatzResearch.WordTrace tailWord_439625 prefixEnd_439625 200656829095953510102851 := by
  unfold tailWord_439625
  simp only [CollatzResearch.WordTrace]
  refine ⟨16034441032321181817528329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10689627354880787878352219 16034441032321181817528329)
  ·
    refine ⟨12025830774240886363146247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16034441032321181817528329 12025830774240886363146247)
    ·
      refine ⟨18038746161361329544719371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12025830774240886363146247 18038746161361329544719371)
      ·
        refine ⟨27058119242041994317079057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18038746161361329544719371 27058119242041994317079057)
        ·
          refine ⟨20293589431531495737809293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27058119242041994317079057 20293589431531495737809293)
          ·
            refine ⟨7610096036824310901678485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20293589431531495737809293 7610096036824310901678485)
            ·
              refine ⟨356723251726139573516179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7610096036824310901678485 356723251726139573516179)
              ·
                refine ⟨535084877589209360274269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 356723251726139573516179 535084877589209360274269)
                ·
                  refine ⟨200656829095953510102851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 535084877589209360274269 200656829095953510102851)
                  ·
                    rfl

theorem cell20_439625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 1, 3].length) (baseStart_439625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_439625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_439625 prefixEnd_439625 := by exact prefixLift 439625
  have htrace : WordTrace (prefixWord ++ tailWord_439625) baseStart_439625 baseEnd_439625 := by
    simpa [prefixWord, tailWord_439625, baseEnd_439625] using wordTrace_append hprefix tailTrace_439625
  have hstable : (prefixWord ++ tailWord_439625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439625).length < 2 ^ (prefixWord ++ tailWord_439625).sum := by decide
  have hdescent : baseEnd_439625 < baseStart_439625 := by decide
  rcases family_descends (prefixWord ++ tailWord_439625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439660 : List Nat := [2, 2, 1, 1, 5, 9]
def baseStart_439660 : Nat := 118140960795 + 439660 * 2 ^ 59
def prefixEnd_439660 : Nat := 4983230072969 + 3 ^ 40 * 439660 * 2
def baseEnd_439660 : Nat := 7432326075912923849483

theorem tailTrace_439660 : CollatzResearch.WordTrace tailWord_439660 prefixEnd_439660 7432326075912923849483 := by
  unfold tailWord_439660
  simp only [CollatzResearch.WordTrace]
  refine ⟨8017858793597191397526217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10690478391462921863368289 8017858793597191397526217)
  ·
    refine ⟨6013394095197893548144663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8017858793597191397526217 6013394095197893548144663)
    ·
      refine ⟨9020091142796840322216995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6013394095197893548144663 9020091142796840322216995)
      ·
        refine ⟨13530136714195260483325493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9020091142796840322216995 13530136714195260483325493)
        ·
          refine ⟨1268450316955805670311765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13530136714195260483325493 1268450316955805670311765)
          ·
            refine ⟨7432326075912923849483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1268450316955805670311765 7432326075912923849483)
            ·
              rfl

theorem cell20_439660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 9].length) (baseStart_439660 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_439660 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_439660 prefixEnd_439660 := by exact prefixLift 439660
  have htrace : WordTrace (prefixWord ++ tailWord_439660) baseStart_439660 baseEnd_439660 := by
    simpa [prefixWord, tailWord_439660, baseEnd_439660] using wordTrace_append hprefix tailTrace_439660
  have hstable : (prefixWord ++ tailWord_439660).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439660).length < 2 ^ (prefixWord ++ tailWord_439660).sum := by decide
  have hdescent : baseEnd_439660 < baseStart_439660 := by decide
  rcases family_descends (prefixWord ++ tailWord_439660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439662 : List Nat := [4, 1, 2, 4, 1, 2, 2, 2, 2]
def baseStart_439662 : Nat := 118140960795 + 439662 * 2 ^ 59
def prefixEnd_439662 : Nat := 4983230072969 + 3 ^ 40 * 439662 * 2
def baseEnd_439662 : Nat := 200673716904145825869367

theorem tailTrace_439662 : CollatzResearch.WordTrace tailWord_439662 prefixEnd_439662 200673716904145825869367 := by
  unfold tailWord_439662
  simp only [CollatzResearch.WordTrace]
  refine ⟨2004473816648392142078155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10690527022124758091083493 2004473816648392142078155)
  ·
    refine ⟨3006710724972588213117233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2004473816648392142078155 3006710724972588213117233)
    ·
      refine ⟨2255033043729441159837925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3006710724972588213117233 2255033043729441159837925)
      ·
        refine ⟨422818695699270217469611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2255033043729441159837925 422818695699270217469611)
        ·
          refine ⟨634228043548905326204417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422818695699270217469611 634228043548905326204417)
          ·
            refine ⟨475671032661678994653313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 634228043548905326204417 475671032661678994653313)
            ·
              refine ⟨356753274496259245989985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 475671032661678994653313 356753274496259245989985)
              ·
                refine ⟨267564955872194434492489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 356753274496259245989985 267564955872194434492489)
                ·
                  refine ⟨200673716904145825869367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 267564955872194434492489 200673716904145825869367)
                  ·
                    rfl

theorem cell20_439662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 2, 2].length) (baseStart_439662 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_439662 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_439662 prefixEnd_439662 := by exact prefixLift 439662
  have htrace : WordTrace (prefixWord ++ tailWord_439662) baseStart_439662 baseEnd_439662 := by
    simpa [prefixWord, tailWord_439662, baseEnd_439662] using wordTrace_append hprefix tailTrace_439662
  have hstable : (prefixWord ++ tailWord_439662).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439662).length < 2 ^ (prefixWord ++ tailWord_439662).sum := by decide
  have hdescent : baseEnd_439662 < baseStart_439662 := by decide
  rcases family_descends (prefixWord ++ tailWord_439662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439691 : List Nat := [1, 1, 1, 1, 4, 3, 3, 2, 4]
def baseStart_439691 : Nat := 118140960795 + 439691 * 2 ^ 59
def prefixEnd_439691 : Nat := 4983230072969 + 3 ^ 40 * 439691 * 2
def baseEnd_439691 : Nat := 200686953294350613902581

theorem tailTrace_439691 : CollatzResearch.WordTrace tailWord_439691 prefixEnd_439691 200686953294350613902581 := by
  unfold tailWord_439691
  simp only [CollatzResearch.WordTrace]
  refine ⟨16036848250082075089430927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10691232166721383392953951 16036848250082075089430927)
  ·
    refine ⟨24055272375123112634146391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16036848250082075089430927 24055272375123112634146391)
    ·
      refine ⟨36082908562684668951219587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24055272375123112634146391 36082908562684668951219587)
      ·
        refine ⟨54124362844027003426829381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36082908562684668951219587 54124362844027003426829381)
        ·
          refine ⟨10148318033255063142530509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54124362844027003426829381 10148318033255063142530509)
          ·
            refine ⟨3805619262470648678448941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10148318033255063142530509 3805619262470648678448941)
            ·
              refine ⟨1427107223426493254418353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3805619262470648678448941 1427107223426493254418353)
              ·
                refine ⟨1070330417569869940813765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1427107223426493254418353 1070330417569869940813765)
                ·
                  refine ⟨200686953294350613902581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1070330417569869940813765 200686953294350613902581)
                  ·
                    rfl

theorem cell20_439691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 4].length) (baseStart_439691 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_439691 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_439691 prefixEnd_439691 := by exact prefixLift 439691
  have htrace : WordTrace (prefixWord ++ tailWord_439691) baseStart_439691 baseEnd_439691 := by
    simpa [prefixWord, tailWord_439691, baseEnd_439691] using wordTrace_append hprefix tailTrace_439691
  have hstable : (prefixWord ++ tailWord_439691).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439691).length < 2 ^ (prefixWord ++ tailWord_439691).sum := by decide
  have hdescent : baseEnd_439691 < baseStart_439691 := by decide
  rcases family_descends (prefixWord ++ tailWord_439691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439704 : List Nat := [2, 1, 2, 5, 2, 1, 2, 3, 2]
def baseStart_439704 : Nat := 118140960795 + 439704 * 2 ^ 59
def prefixEnd_439704 : Nat := 4983230072969 + 3 ^ 40 * 439704 * 2
def baseEnd_439704 : Nat := 200692886848580346469195

theorem tailTrace_439704 : CollatzResearch.WordTrace tailWord_439704 prefixEnd_439704 200692886848580346469195 := by
  unfold tailWord_439704
  simp only [CollatzResearch.WordTrace]
  refine ⟨8018661199517489154827083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10691548266023318873102777 8018661199517489154827083)
  ·
    refine ⟨12027991799276233732240625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8018661199517489154827083 12027991799276233732240625)
    ·
      refine ⟨9020993849457175299180469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12027991799276233732240625 9020993849457175299180469)
      ·
        refine ⟨845718173386610184298169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9020993849457175299180469 845718173386610184298169)
        ·
          refine ⟨634288630039957638223627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 845718173386610184298169 634288630039957638223627)
          ·
            refine ⟨951432945059936457335441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 634288630039957638223627 951432945059936457335441)
            ·
              refine ⟨713574708794952343001581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 951432945059936457335441 713574708794952343001581)
              ·
                refine ⟨267590515798107128625593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 713574708794952343001581 267590515798107128625593)
                ·
                  refine ⟨200692886848580346469195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 267590515798107128625593 200692886848580346469195)
                  ·
                    rfl

theorem cell20_439704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 3, 2].length) (baseStart_439704 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_439704 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_439704 prefixEnd_439704 := by exact prefixLift 439704
  have htrace : WordTrace (prefixWord ++ tailWord_439704) baseStart_439704 baseEnd_439704 := by
    simpa [prefixWord, tailWord_439704, baseEnd_439704] using wordTrace_append hprefix tailTrace_439704
  have hstable : (prefixWord ++ tailWord_439704).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439704).length < 2 ^ (prefixWord ++ tailWord_439704).sum := by decide
  have hdescent : baseEnd_439704 < baseStart_439704 := by decide
  rcases family_descends (prefixWord ++ tailWord_439704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439725 : List Nat := [1, 5, 2, 2, 1, 2, 2, 1, 4]
def baseStart_439725 : Nat := 118140960795 + 439725 * 2 ^ 59
def prefixEnd_439725 : Nat := 4983230072969 + 3 ^ 40 * 439725 * 2
def baseEnd_439725 : Nat := 200702471820797606769109

theorem tailTrace_439725 : CollatzResearch.WordTrace tailWord_439725 prefixEnd_439725 200702471820797606769109 := by
  unfold tailWord_439725
  simp only [CollatzResearch.WordTrace]
  refine ⟨16038088331958898896168629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10692058887972599264112419 16038088331958898896168629)
  ·
    refine ⟨1503570781121146771515809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16038088331958898896168629 1503570781121146771515809)
    ·
      refine ⟨1127678085840860078636857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1503570781121146771515809 1127678085840860078636857)
      ·
        refine ⟨845758564380645058977643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1127678085840860078636857 845758564380645058977643)
        ·
          refine ⟨1268637846570967588466465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 845758564380645058977643 1268637846570967588466465)
          ·
            refine ⟨951478384928225691349849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1268637846570967588466465 951478384928225691349849)
            ·
              refine ⟨713608788696169268512387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 951478384928225691349849 713608788696169268512387)
              ·
                refine ⟨1070413183044253902768581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 713608788696169268512387 1070413183044253902768581)
                ·
                  refine ⟨200702471820797606769109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1070413183044253902768581 200702471820797606769109)
                  ·
                    rfl

theorem cell20_439725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_439725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_439725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_439725 prefixEnd_439725 := by exact prefixLift 439725
  have htrace : WordTrace (prefixWord ++ tailWord_439725) baseStart_439725 baseEnd_439725 := by
    simpa [prefixWord, tailWord_439725, baseEnd_439725] using wordTrace_append hprefix tailTrace_439725
  have hstable : (prefixWord ++ tailWord_439725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439725).length < 2 ^ (prefixWord ++ tailWord_439725).sum := by decide
  have hdescent : baseEnd_439725 < baseStart_439725 := by decide
  rcases family_descends (prefixWord ++ tailWord_439725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439794 : List Nat := [3, 2, 1, 4, 1, 1, 4, 1, 3]
def baseStart_439794 : Nat := 118140960795 + 439794 * 2 ^ 59
def prefixEnd_439794 : Nat := 4983230072969 + 3 ^ 40 * 439794 * 2
def baseEnd_439794 : Nat := 200733965300940033468827

theorem tailTrace_439794 : CollatzResearch.WordTrace tailWord_439794 prefixEnd_439794 200733965300940033468827 := by
  unfold tailWord_439794
  simp only [CollatzResearch.WordTrace]
  refine ⟨4010151242177230920107609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10693736645805949120286957 4010151242177230920107609)
  ·
    refine ⟨3007613431632923190080707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4010151242177230920107609 3007613431632923190080707)
    ·
      refine ⟨4511420147449384785121061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3007613431632923190080707 4511420147449384785121061)
      ·
        refine ⟨845891277646759647210199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4511420147449384785121061 845891277646759647210199)
        ·
          refine ⟨1268836916470139470815299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 845891277646759647210199 1268836916470139470815299)
          ·
            refine ⟨1903255374705209206222949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1268836916470139470815299 1903255374705209206222949)
            ·
              refine ⟨356860382757226726166803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1903255374705209206222949 356860382757226726166803)
              ·
                refine ⟨535290574135840089250205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 356860382757226726166803 535290574135840089250205)
                ·
                  refine ⟨200733965300940033468827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 535290574135840089250205 200733965300940033468827)
                  ·
                    rfl

theorem cell20_439794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_439794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_439794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_439794 prefixEnd_439794 := by exact prefixLift 439794
  have htrace : WordTrace (prefixWord ++ tailWord_439794) baseStart_439794 baseEnd_439794 := by
    simpa [prefixWord, tailWord_439794, baseEnd_439794] using wordTrace_append hprefix tailTrace_439794
  have hstable : (prefixWord ++ tailWord_439794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439794).length < 2 ^ (prefixWord ++ tailWord_439794).sum := by decide
  have hdescent : baseEnd_439794 < baseStart_439794 := by decide
  rcases family_descends (prefixWord ++ tailWord_439794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439839 : List Nat := [1, 1, 2, 4, 1, 1, 6, 2, 2]
def baseStart_439839 : Nat := 118140960795 + 439839 * 2 ^ 59
def prefixEnd_439839 : Nat := 4983230072969 + 3 ^ 40 * 439839 * 2
def baseEnd_439839 : Nat := 200754504527119876968643

theorem tailTrace_439839 : CollatzResearch.WordTrace tailWord_439839 prefixEnd_439839 200754504527119876968643 := by
  unfold tailWord_439839
  simp only [CollatzResearch.WordTrace]
  refine ⟨16042246253545896365818571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10694830835697264243879047 16042246253545896365818571)
  ·
    refine ⟨24063369380318844548727857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16042246253545896365818571 24063369380318844548727857)
    ·
      refine ⟨18047527035239133411545893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24063369380318844548727857 18047527035239133411545893)
      ·
        refine ⟨3383911319107337514664855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18047527035239133411545893 3383911319107337514664855)
        ·
          refine ⟨5075866978661006271997283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3383911319107337514664855 5075866978661006271997283)
          ·
            refine ⟨7613800467991509407995925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5075866978661006271997283 7613800467991509407995925)
            ·
              refine ⟨356896896937102003499809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7613800467991509407995925 356896896937102003499809)
              ·
                refine ⟨267672672702826502624857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 356896896937102003499809 267672672702826502624857)
                ·
                  refine ⟨200754504527119876968643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 267672672702826502624857 200754504527119876968643)
                  ·
                    rfl

theorem cell20_439839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 2, 2].length) (baseStart_439839 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_439839 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_439839 prefixEnd_439839 := by exact prefixLift 439839
  have htrace : WordTrace (prefixWord ++ tailWord_439839) baseStart_439839 baseEnd_439839 := by
    simpa [prefixWord, tailWord_439839, baseEnd_439839] using wordTrace_append hprefix tailTrace_439839
  have hstable : (prefixWord ++ tailWord_439839).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439839).length < 2 ^ (prefixWord ++ tailWord_439839).sum := by decide
  have hdescent : baseEnd_439839 < baseStart_439839 := by decide
  rcases family_descends (prefixWord ++ tailWord_439839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439857 : List Nat := [1, 2, 2, 3, 1, 1, 1, 2, 7]
def baseStart_439857 : Nat := 118140960795 + 439857 * 2 ^ 59
def prefixEnd_439857 : Nat := 4983230072969 + 3 ^ 40 * 439857 * 2
def baseEnd_439857 : Nat := 200762720217591814368569

theorem tailTrace_439857 : CollatzResearch.WordTrace tailWord_439857 prefixEnd_439857 200762720217591814368569 := by
  unfold tailWord_439857
  simp only [CollatzResearch.WordTrace]
  refine ⟨16042902767480685439973825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10695268511653790293315883 16042902767480685439973825)
  ·
    refine ⟨12032177075610514079980369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16042902767480685439973825 12032177075610514079980369)
    ·
      refine ⟨9024132806707885559985277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12032177075610514079980369 9024132806707885559985277)
      ·
        refine ⟨3384049802515457084994479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9024132806707885559985277 3384049802515457084994479)
        ·
          refine ⟨5076074703773185627491719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3384049802515457084994479 5076074703773185627491719)
          ·
            refine ⟨7614112055659778441237579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5076074703773185627491719 7614112055659778441237579)
            ·
              refine ⟨11421168083489667661856369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7614112055659778441237579 11421168083489667661856369)
              ·
                refine ⟨8565876062617250746392277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11421168083489667661856369 8565876062617250746392277)
                ·
                  refine ⟨200762720217591814368569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8565876062617250746392277 200762720217591814368569)
                  ·
                    rfl

theorem cell20_439857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 7].length) (baseStart_439857 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_439857 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_439857 prefixEnd_439857 := by exact prefixLift 439857
  have htrace : WordTrace (prefixWord ++ tailWord_439857) baseStart_439857 baseEnd_439857 := by
    simpa [prefixWord, tailWord_439857, baseEnd_439857] using wordTrace_append hprefix tailTrace_439857
  have hstable : (prefixWord ++ tailWord_439857).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439857).length < 2 ^ (prefixWord ++ tailWord_439857).sum := by decide
  have hdescent : baseEnd_439857 < baseStart_439857 := by decide
  rcases family_descends (prefixWord ++ tailWord_439857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439922 : List Nat := [3, 2, 1, 2, 3, 3, 2, 4]
def baseStart_439922 : Nat := 118140960795 + 439922 * 2 ^ 59
def prefixEnd_439922 : Nat := 4983230072969 + 3 ^ 40 * 439922 * 2
def baseEnd_439922 : Nat := 66930795996246825733879

theorem tailTrace_439922 : CollatzResearch.WordTrace tailWord_439922 prefixEnd_439922 66930795996246825733879 := by
  unfold tailWord_439922
  simp only [CollatzResearch.WordTrace]
  refine ⟨4011318378061300385272505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10696849008163467694060013 4011318378061300385272505)
  ·
    refine ⟨3008488783545975288954379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4011318378061300385272505 3008488783545975288954379)
    ·
      refine ⟨4512733175318962933431569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3008488783545975288954379 4512733175318962933431569)
      ·
        refine ⟨3384549881489222200073677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4512733175318962933431569 3384549881489222200073677)
        ·
          refine ⟨1269206205558458325027629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3384549881489222200073677 1269206205558458325027629)
          ·
            refine ⟨475952327084421871885361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1269206205558458325027629 475952327084421871885361)
            ·
              refine ⟨356964245313316403914021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 475952327084421871885361 356964245313316403914021)
              ·
                refine ⟨66930795996246825733879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 356964245313316403914021 66930795996246825733879)
                ·
                  rfl

theorem cell20_439922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 4].length) (baseStart_439922 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_439922 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_439922 prefixEnd_439922 := by exact prefixLift 439922
  have htrace : WordTrace (prefixWord ++ tailWord_439922) baseStart_439922 baseEnd_439922 := by
    simpa [prefixWord, tailWord_439922, baseEnd_439922] using wordTrace_append hprefix tailTrace_439922
  have hstable : (prefixWord ++ tailWord_439922).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439922).length < 2 ^ (prefixWord ++ tailWord_439922).sum := by decide
  have hdescent : baseEnd_439922 < baseStart_439922 := by decide
  rcases family_descends (prefixWord ++ tailWord_439922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439950 : List Nat := [4, 1, 1, 3, 1, 2, 2, 1, 5]
def baseStart_439950 : Nat := 118140960795 + 439950 * 2 ^ 59
def prefixEnd_439950 : Nat := 4983230072969 + 3 ^ 40 * 439950 * 2
def baseEnd_439950 : Nat := 200805167951696824268189

theorem tailTrace_439950 : CollatzResearch.WordTrace tailWord_439950 prefixEnd_439950 200805167951696824268189 := by
  unfold tailWord_439950
  simp only [CollatzResearch.WordTrace]
  refine ⟨2005786844517970290388663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10697529837429174882072869 2005786844517970290388663)
  ·
    refine ⟨3008680266776955435582995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2005786844517970290388663 3008680266776955435582995)
    ·
      refine ⟨4513020400165433153374493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3008680266776955435582995 4513020400165433153374493)
      ·
        refine ⟨1692382650062037432515435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4513020400165433153374493 1692382650062037432515435)
        ·
          refine ⟨2538573975093056148773153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1692382650062037432515435 2538573975093056148773153)
          ·
            refine ⟨1903930481319792111579865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2538573975093056148773153 1903930481319792111579865)
            ·
              refine ⟨1427947860989844083684899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1903930481319792111579865 1427947860989844083684899)
              ·
                refine ⟨2141921791484766125527349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1427947860989844083684899 2141921791484766125527349)
                ·
                  refine ⟨200805167951696824268189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2141921791484766125527349 200805167951696824268189)
                  ·
                    rfl

theorem cell20_439950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_439950 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_439950 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_439950 prefixEnd_439950 := by exact prefixLift 439950
  have htrace : WordTrace (prefixWord ++ tailWord_439950) baseStart_439950 baseEnd_439950 := by
    simpa [prefixWord, tailWord_439950, baseEnd_439950] using wordTrace_append hprefix tailTrace_439950
  have hstable : (prefixWord ++ tailWord_439950).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439950).length < 2 ^ (prefixWord ++ tailWord_439950).sum := by decide
  have hdescent : baseEnd_439950 < baseStart_439950 := by decide
  rcases family_descends (prefixWord ++ tailWord_439950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440026 : List Nat := [3, 1, 1, 2, 2, 3, 2, 3, 3]
def baseStart_440026 : Nat := 118140960795 + 440026 * 2 ^ 59
def prefixEnd_440026 : Nat := 4983230072969 + 3 ^ 40 * 440026 * 2
def baseEnd_440026 : Nat := 200839856422578337734545

theorem tailTrace_440026 : CollatzResearch.WordTrace tailWord_440026 prefixEnd_440026 200839856422578337734545 := by
  unfold tailWord_440026
  simp only [CollatzResearch.WordTrace]
  refine ⟨4012266675967106825718983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10699377802578951535250621 4012266675967106825718983)
  ·
    refine ⟨6018400013950660238578475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4012266675967106825718983 6018400013950660238578475)
    ·
      refine ⟨9027600020925990357867713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6018400013950660238578475 9027600020925990357867713)
      ·
        refine ⟨6770700015694492768400785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9027600020925990357867713 6770700015694492768400785)
        ·
          refine ⟨5078025011770869576300589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6770700015694492768400785 5078025011770869576300589)
          ·
            refine ⟨1904259379414076091112721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5078025011770869576300589 1904259379414076091112721)
            ·
              refine ⟨1428194534560557068334541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1904259379414076091112721 1428194534560557068334541)
              ·
                refine ⟨535572950460208900625453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1428194534560557068334541 535572950460208900625453)
                ·
                  refine ⟨200839856422578337734545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 535572950460208900625453 200839856422578337734545)
                  ·
                    rfl

theorem cell20_440026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 3, 3].length) (baseStart_440026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_440026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_440026 prefixEnd_440026 := by exact prefixLift 440026
  have htrace : WordTrace (prefixWord ++ tailWord_440026) baseStart_440026 baseEnd_440026 := by
    simpa [prefixWord, tailWord_440026, baseEnd_440026] using wordTrace_append hprefix tailTrace_440026
  have hstable : (prefixWord ++ tailWord_440026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440026).length < 2 ^ (prefixWord ++ tailWord_440026).sum := by decide
  have hdescent : baseEnd_440026 < baseStart_440026 := by decide
  rcases family_descends (prefixWord ++ tailWord_440026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440029 : List Nat := [1, 4, 3, 3, 1, 1, 1, 2, 4]
def baseStart_440029 : Nat := 118140960795 + 440029 * 2 ^ 59
def prefixEnd_440029 : Nat := 4983230072969 + 3 ^ 40 * 440029 * 2
def baseEnd_440029 : Nat := 200841225704323660634533

theorem tailTrace_440029 : CollatzResearch.WordTrace tailWord_440029 prefixEnd_440029 200841225704323660634533 := by
  unfold tailWord_440029
  simp only [CollatzResearch.WordTrace]
  refine ⟨16049176122857558815235141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10699450748571705876823427 16049176122857558815235141)
  ·
    refine ⟨3009220523035792277856589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16049176122857558815235141 3009220523035792277856589)
    ·
      refine ⟨1128457696138422104196221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3009220523035792277856589 1128457696138422104196221)
      ·
        refine ⟨423171636051908289073583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1128457696138422104196221 423171636051908289073583)
        ·
          refine ⟨634757454077862433610375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423171636051908289073583 634757454077862433610375)
          ·
            refine ⟨952136181116793650415563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 634757454077862433610375 952136181116793650415563)
            ·
              refine ⟨1428204271675190475623345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 952136181116793650415563 1428204271675190475623345)
              ·
                refine ⟨1071153203756392856717509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1428204271675190475623345 1071153203756392856717509)
                ·
                  refine ⟨200841225704323660634533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1071153203756392856717509 200841225704323660634533)
                  ·
                    rfl

theorem cell20_440029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_440029 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_440029 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_440029 prefixEnd_440029 := by exact prefixLift 440029
  have htrace : WordTrace (prefixWord ++ tailWord_440029) baseStart_440029 baseEnd_440029 := by
    simpa [prefixWord, tailWord_440029, baseEnd_440029] using wordTrace_append hprefix tailTrace_440029
  have hstable : (prefixWord ++ tailWord_440029).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440029).length < 2 ^ (prefixWord ++ tailWord_440029).sum := by decide
  have hdescent : baseEnd_440029 < baseStart_440029 := by decide
  rcases family_descends (prefixWord ++ tailWord_440029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440047 : List Nat := [1, 1, 2, 1, 5, 1, 2, 2, 5]
def baseStart_440047 : Nat := 118140960795 + 440047 * 2 ^ 59
def prefixEnd_440047 : Nat := 4983230072969 + 3 ^ 40 * 440047 * 2
def baseEnd_440047 : Nat := 200849441394795598034459

theorem tailTrace_440047 : CollatzResearch.WordTrace tailWord_440047 prefixEnd_440047 200849441394795598034459 := by
  unfold tailWord_440047
  simp only [CollatzResearch.WordTrace]
  refine ⟨16049832636792347889390395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10699888424528231926260263 16049832636792347889390395)
  ·
    refine ⟨24074748955188521834085593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16049832636792347889390395 24074748955188521834085593)
    ·
      refine ⟨18056061716391391375564195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24074748955188521834085593 18056061716391391375564195)
      ·
        refine ⟨27084092574587087063346293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18056061716391391375564195 27084092574587087063346293)
        ·
          refine ⟨2539133678867539412188715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27084092574587087063346293 2539133678867539412188715)
          ·
            refine ⟨3808700518301309118283073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2539133678867539412188715 3808700518301309118283073)
            ·
              refine ⟨2856525388725981838712305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3808700518301309118283073 2856525388725981838712305)
              ·
                refine ⟨2142394041544486379034229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2856525388725981838712305 2142394041544486379034229)
                ·
                  refine ⟨200849441394795598034459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2142394041544486379034229 200849441394795598034459)
                  ·
                    rfl

theorem cell20_440047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 5].length) (baseStart_440047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_440047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_440047 prefixEnd_440047 := by exact prefixLift 440047
  have htrace : WordTrace (prefixWord ++ tailWord_440047) baseStart_440047 baseEnd_440047 := by
    simpa [prefixWord, tailWord_440047, baseEnd_440047] using wordTrace_append hprefix tailTrace_440047
  have hstable : (prefixWord ++ tailWord_440047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440047).length < 2 ^ (prefixWord ++ tailWord_440047).sum := by decide
  have hdescent : baseEnd_440047 < baseStart_440047 := by decide
  rcases family_descends (prefixWord ++ tailWord_440047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440126 : List Nat := [4, 2, 1, 2, 2, 1, 3, 1, 4]
def baseStart_440126 : Nat := 118140960795 + 440126 * 2 ^ 59
def prefixEnd_440126 : Nat := 4983230072969 + 3 ^ 40 * 440126 * 2
def baseEnd_440126 : Nat := 200885499147422434400803

theorem tailTrace_440126 : CollatzResearch.WordTrace tailWord_440126 prefixEnd_440126 200885499147422434400803 := by
  unfold tailWord_440126
  simp only [CollatzResearch.WordTrace]
  refine ⟨2006589250438268047689529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10701809335670762921010821 2006589250438268047689529)
  ·
    refine ⟨1504941937828701035767147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2006589250438268047689529 1504941937828701035767147)
    ·
      refine ⟨2257412906743051553650721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1504941937828701035767147 2257412906743051553650721)
      ·
        refine ⟨1693059680057288665238041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2257412906743051553650721 1693059680057288665238041)
        ·
          refine ⟨1269794760042966498928531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1693059680057288665238041 1269794760042966498928531)
          ·
            refine ⟨1904692140064449748392797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1269794760042966498928531 1904692140064449748392797)
            ·
              refine ⟨714259552524168655647299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1904692140064449748392797 714259552524168655647299)
              ·
                refine ⟨1071389328786252983470949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 714259552524168655647299 1071389328786252983470949)
                ·
                  refine ⟨200885499147422434400803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1071389328786252983470949 200885499147422434400803)
                  ·
                    rfl

theorem cell20_440126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_440126 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_440126 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_440126 prefixEnd_440126 := by exact prefixLift 440126
  have htrace : WordTrace (prefixWord ++ tailWord_440126) baseStart_440126 baseEnd_440126 := by
    simpa [prefixWord, tailWord_440126, baseEnd_440126] using wordTrace_append hprefix tailTrace_440126
  have hstable : (prefixWord ++ tailWord_440126).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440126).length < 2 ^ (prefixWord ++ tailWord_440126).sum := by decide
  have hdescent : baseEnd_440126 < baseStart_440126 := by decide
  rcases family_descends (prefixWord ++ tailWord_440126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440202 : List Nat := [3, 1, 2, 4, 2, 1, 1, 2, 4]
def baseStart_440202 : Nat := 118140960795 + 440202 * 2 ^ 59
def prefixEnd_440202 : Nat := 4983230072969 + 3 ^ 40 * 440202 * 2
def baseEnd_440202 : Nat := 200920187618303947867159

theorem tailTrace_440202 : CollatzResearch.WordTrace tailWord_440202 prefixEnd_440202 200920187618303947867159 := by
  unfold tailWord_440202
  simp only [CollatzResearch.WordTrace]
  refine ⟨4013871487807702340320715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10703657300820539574188573 4013871487807702340320715)
  ·
    refine ⟨6020807231711553510481073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4013871487807702340320715 6020807231711553510481073)
    ·
      refine ⟨4515605423783665132860805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6020807231711553510481073 4515605423783665132860805)
      ·
        refine ⟨846676016959437212411401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4515605423783665132860805 846676016959437212411401)
        ·
          refine ⟨635007012719577909308551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 846676016959437212411401 635007012719577909308551)
          ·
            refine ⟨952510519079366863962827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 635007012719577909308551 952510519079366863962827)
            ·
              refine ⟨1428765778619050295944241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 952510519079366863962827 1428765778619050295944241)
              ·
                refine ⟨1071574333964287721958181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1428765778619050295944241 1071574333964287721958181)
                ·
                  refine ⟨200920187618303947867159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1071574333964287721958181 200920187618303947867159)
                  ·
                    rfl

theorem cell20_440202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 4].length) (baseStart_440202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_440202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_440202 prefixEnd_440202 := by exact prefixLift 440202
  have htrace : WordTrace (prefixWord ++ tailWord_440202) baseStart_440202 baseEnd_440202 := by
    simpa [prefixWord, tailWord_440202, baseEnd_440202] using wordTrace_append hprefix tailTrace_440202
  have hstable : (prefixWord ++ tailWord_440202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440202).length < 2 ^ (prefixWord ++ tailWord_440202).sum := by decide
  have hdescent : baseEnd_440202 < baseStart_440202 := by decide
  rcases family_descends (prefixWord ++ tailWord_440202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440268 : List Nat := [2, 2, 1, 4, 1, 3, 1, 6]
def baseStart_440268 : Nat := 118140960795 + 440268 * 2 ^ 59
def prefixEnd_440268 : Nat := 4983230072969 + 3 ^ 40 * 440268 * 2
def baseEnd_440268 : Nat := 66983437272233683888963

theorem tailTrace_440268 : CollatzResearch.WordTrace tailWord_440268 prefixEnd_440268 66983437272233683888963 := by
  unfold tailWord_440268
  simp only [CollatzResearch.WordTrace]
  refine ⟨8028946584495851316592729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10705262112661135088790305 8028946584495851316592729)
  ·
    refine ⟨6021709938371888487444547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8028946584495851316592729 6021709938371888487444547)
    ·
      refine ⟨9032564907557832731166821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6021709938371888487444547 9032564907557832731166821)
      ·
        refine ⟨1693605920167093637093779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9032564907557832731166821 1693605920167093637093779)
        ·
          refine ⟨2540408880250640455640669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1693605920167093637093779 2540408880250640455640669)
          ·
            refine ⟨952653330093990170865251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2540408880250640455640669 952653330093990170865251)
            ·
              refine ⟨1428979995140985256297877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 952653330093990170865251 1428979995140985256297877)
              ·
                refine ⟨66983437272233683888963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1428979995140985256297877 66983437272233683888963)
                ·
                  rfl

theorem cell20_440268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 6].length) (baseStart_440268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_440268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_440268 prefixEnd_440268 := by exact prefixLift 440268
  have htrace : WordTrace (prefixWord ++ tailWord_440268) baseStart_440268 baseEnd_440268 := by
    simpa [prefixWord, tailWord_440268, baseEnd_440268] using wordTrace_append hprefix tailTrace_440268
  have hstable : (prefixWord ++ tailWord_440268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440268).length < 2 ^ (prefixWord ++ tailWord_440268).sum := by decide
  have hdescent : baseEnd_440268 < baseStart_440268 := by decide
  rcases family_descends (prefixWord ++ tailWord_440268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440274 : List Nat := [3, 2, 2, 3, 2, 2, 1, 3, 2]
def baseStart_440274 : Nat := 118140960795 + 440274 * 2 ^ 59
def prefixEnd_440274 : Nat := 4983230072969 + 3 ^ 40 * 440274 * 2
def baseEnd_440274 : Nat := 200953050380191697466865

theorem tailTrace_440274 : CollatzResearch.WordTrace tailWord_440274 prefixEnd_440274 200953050380191697466865 := by
  unfold tailWord_440274
  simp only [CollatzResearch.WordTrace]
  refine ⟨4014528001742491414475969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10705408004646643771935917 4014528001742491414475969)
  ·
    refine ⟨3010896001306868560856977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4014528001742491414475969 3010896001306868560856977)
    ·
      refine ⟨2258172000980151420642733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3010896001306868560856977 2258172000980151420642733)
      ·
        refine ⟨846814500367556782741025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2258172000980151420642733 846814500367556782741025)
        ·
          refine ⟨635110875275667587055769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 846814500367556782741025 635110875275667587055769)
          ·
            refine ⟨476333156456750690291827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 635110875275667587055769 476333156456750690291827)
            ·
              refine ⟨714499734685126035437741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 476333156456750690291827 714499734685126035437741)
              ·
                refine ⟨267937400506922263289153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 714499734685126035437741 267937400506922263289153)
                ·
                  refine ⟨200953050380191697466865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 267937400506922263289153 200953050380191697466865)
                  ·
                    rfl

theorem cell20_440274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 3, 2].length) (baseStart_440274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_440274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_440274 prefixEnd_440274 := by exact prefixLift 440274
  have htrace : WordTrace (prefixWord ++ tailWord_440274) baseStart_440274 baseEnd_440274 := by
    simpa [prefixWord, tailWord_440274, baseEnd_440274] using wordTrace_append hprefix tailTrace_440274
  have hstable : (prefixWord ++ tailWord_440274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440274).length < 2 ^ (prefixWord ++ tailWord_440274).sum := by decide
  have hdescent : baseEnd_440274 < baseStart_440274 := by decide
  rcases family_descends (prefixWord ++ tailWord_440274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440285 : List Nat := [1, 4, 3, 1, 3, 2, 6]
def baseStart_440285 : Nat := 118140960795 + 440285 * 2 ^ 59
def prefixEnd_440285 : Nat := 4983230072969 + 3 ^ 40 * 440285 * 2
def baseEnd_440285 : Nat := 22328674564436060900017

theorem tailTrace_440285 : CollatzResearch.WordTrace tailWord_440285 prefixEnd_440285 22328674564436060900017 := by
  unfold tailWord_440285
  simp only [CollatzResearch.WordTrace]
  refine ⟨16058513209930114536554309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10705675473286743024369539 16058513209930114536554309)
  ·
    refine ⟨3010971226861896475603933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16058513209930114536554309 3010971226861896475603933)
    ·
      refine ⟨1129114210073211178351475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3010971226861896475603933 1129114210073211178351475)
      ·
        refine ⟨1693671315109816767527213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1129114210073211178351475 1693671315109816767527213)
        ·
          refine ⟨635126743166181287822705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1693671315109816767527213 635126743166181287822705)
          ·
            refine ⟨476345057374635965867029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 635126743166181287822705 476345057374635965867029)
            ·
              refine ⟨22328674564436060900017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 476345057374635965867029 22328674564436060900017)
              ·
                rfl

theorem cell20_440285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 6].length) (baseStart_440285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_440285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_440285 prefixEnd_440285 := by exact prefixLift 440285
  have htrace : WordTrace (prefixWord ++ tailWord_440285) baseStart_440285 baseEnd_440285 := by
    simpa [prefixWord, tailWord_440285, baseEnd_440285] using wordTrace_append hprefix tailTrace_440285
  have hstable : (prefixWord ++ tailWord_440285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440285).length < 2 ^ (prefixWord ++ tailWord_440285).sum := by decide
  have hdescent : baseEnd_440285 < baseStart_440285 := by decide
  rcases family_descends (prefixWord ++ tailWord_440285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440289 : List Nat := [1, 2, 3, 1, 2, 1, 10]
def baseStart_440289 : Nat := 118140960795 + 440289 * 2 ^ 59
def prefixEnd_440289 : Nat := 4983230072969 + 3 ^ 40 * 440289 * 2
def baseEnd_440289 : Nat := 22328877420990923551867

theorem tailTrace_440289 : CollatzResearch.WordTrace tailWord_440289 prefixEnd_440289 22328877420990923551867 := by
  unfold tailWord_440289
  simp only [CollatzResearch.WordTrace]
  refine ⟨16058659101915623219699921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10705772734610415479799947 16058659101915623219699921)
  ·
    refine ⟨12043994326436717414774941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16058659101915623219699921 12043994326436717414774941)
    ·
      refine ⟨4516497872413769030540603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12043994326436717414774941 4516497872413769030540603)
      ·
        refine ⟨6774746808620653545810905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4516497872413769030540603 6774746808620653545810905)
        ·
          refine ⟨5081060106465490159358179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6774746808620653545810905 5081060106465490159358179)
          ·
            refine ⟨7621590159698235239037269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5081060106465490159358179 7621590159698235239037269)
            ·
              refine ⟨22328877420990923551867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7621590159698235239037269 22328877420990923551867)
              ·
                rfl

theorem cell20_440289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 10].length) (baseStart_440289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_440289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_440289 prefixEnd_440289 := by exact prefixLift 440289
  have htrace : WordTrace (prefixWord ++ tailWord_440289) baseStart_440289 baseEnd_440289 := by
    simpa [prefixWord, tailWord_440289, baseEnd_440289] using wordTrace_append hprefix tailTrace_440289
  have hstable : (prefixWord ++ tailWord_440289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440289).length < 2 ^ (prefixWord ++ tailWord_440289).sum := by decide
  have hdescent : baseEnd_440289 < baseStart_440289 := by decide
  rcases family_descends (prefixWord ++ tailWord_440289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440295 : List Nat := [1, 1, 5, 2, 4, 1, 1, 1, 4]
def baseStart_440295 : Nat := 118140960795 + 440295 * 2 ^ 59
def prefixEnd_440295 : Nat := 4983230072969 + 3 ^ 40 * 440295 * 2
def baseEnd_440295 : Nat := 200962635352408957766779

theorem tailTrace_440295 : CollatzResearch.WordTrace tailWord_440295 prefixEnd_440295 200962635352408957766779 := by
  unfold tailWord_440295
  simp only [CollatzResearch.WordTrace]
  refine ⟨16058877939893886244418339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10705918626595924162945559 16058877939893886244418339)
  ·
    refine ⟨24088316909840829366627509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16058877939893886244418339 24088316909840829366627509)
    ·
      refine ⟨2258279710297577753121329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24088316909840829366627509 2258279710297577753121329)
      ·
        refine ⟨1693709782723183314840997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2258279710297577753121329 1693709782723183314840997)
        ·
          refine ⟨317570584260596871532687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1693709782723183314840997 317570584260596871532687)
          ·
            refine ⟨476355876390895307299031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317570584260596871532687 476355876390895307299031)
            ·
              refine ⟨714533814586342960948547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 476355876390895307299031 714533814586342960948547)
              ·
                refine ⟨1071800721879514441422821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 714533814586342960948547 1071800721879514441422821)
                ·
                  refine ⟨200962635352408957766779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1071800721879514441422821 200962635352408957766779)
                  ·
                    rfl

theorem cell20_440295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 4].length) (baseStart_440295 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_440295 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_440295 prefixEnd_440295 := by exact prefixLift 440295
  have htrace : WordTrace (prefixWord ++ tailWord_440295) baseStart_440295 baseEnd_440295 := by
    simpa [prefixWord, tailWord_440295, baseEnd_440295] using wordTrace_append hprefix tailTrace_440295
  have hstable : (prefixWord ++ tailWord_440295).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440295).length < 2 ^ (prefixWord ++ tailWord_440295).sum := by decide
  have hdescent : baseEnd_440295 < baseStart_440295 := by decide
  rcases family_descends (prefixWord ++ tailWord_440295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440299 : List Nat := [1, 1, 1, 1, 2, 3, 1, 8, 2]
def baseStart_440299 : Nat := 118140960795 + 440299 * 2 ^ 59
def prefixEnd_440299 : Nat := 4983230072969 + 3 ^ 40 * 440299 * 2
def baseEnd_440299 : Nat := 200964461061402721633429

theorem tailTrace_440299 : CollatzResearch.WordTrace tailWord_440299 prefixEnd_440299 200964461061402721633429 := by
  unfold tailWord_440299
  simp only [CollatzResearch.WordTrace]
  refine ⟨16059023831879394927563951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10706015887919596618375967 16059023831879394927563951)
  ·
    refine ⟨24088535747819092391345927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16059023831879394927563951 24088535747819092391345927)
    ·
      refine ⟨36132803621728638587018891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24088535747819092391345927 36132803621728638587018891)
      ·
        refine ⟨54199205432592957880528337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36132803621728638587018891 54199205432592957880528337)
        ·
          refine ⟨40649404074444718410396253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54199205432592957880528337 40649404074444718410396253)
          ·
            refine ⟨15243526527916769403898595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40649404074444718410396253 15243526527916769403898595)
            ·
              refine ⟨22865289791875154105847893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15243526527916769403898595 22865289791875154105847893)
              ·
                refine ⟨267952614748536962177905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 22865289791875154105847893 267952614748536962177905)
                ·
                  refine ⟨200964461061402721633429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 267952614748536962177905 200964461061402721633429)
                  ·
                    rfl

theorem cell20_440299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 8, 2].length) (baseStart_440299 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_440299 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_440299 prefixEnd_440299 := by exact prefixLift 440299
  have htrace : WordTrace (prefixWord ++ tailWord_440299) baseStart_440299 baseEnd_440299 := by
    simpa [prefixWord, tailWord_440299, baseEnd_440299] using wordTrace_append hprefix tailTrace_440299
  have hstable : (prefixWord ++ tailWord_440299).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440299).length < 2 ^ (prefixWord ++ tailWord_440299).sum := by decide
  have hdescent : baseEnd_440299 < baseStart_440299 := by decide
  rcases family_descends (prefixWord ++ tailWord_440299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440340 : List Nat := [2, 4, 3, 2, 2, 7]
def baseStart_440340 : Nat := 118140960795 + 440340 * 2 ^ 59
def prefixEnd_440340 : Nat := 4983230072969 + 3 ^ 40 * 440340 * 2
def baseEnd_440340 : Nat := 7443821280688474120985

theorem tailTrace_440340 : CollatzResearch.WordTrace tailWord_440340 prefixEnd_440340 7443821280688474120985 := by
  unfold tailWord_440340
  simp only [CollatzResearch.WordTrace]
  refine ⟨8030259612365429464903237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10707012816487239286537649 8030259612365429464903237)
  ·
    refine ⟨1505673677318518024669357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8030259612365429464903237 1505673677318518024669357)
    ·
      refine ⟨564627628994444259251009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1505673677318518024669357 564627628994444259251009)
      ·
        refine ⟨423470721745833194438257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 564627628994444259251009 423470721745833194438257)
        ·
          refine ⟨317603041309374895828693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 423470721745833194438257 317603041309374895828693)
          ·
            refine ⟨7443821280688474120985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 317603041309374895828693 7443821280688474120985)
            ·
              rfl

theorem cell20_440340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 7].length) (baseStart_440340 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_440340 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_440340 prefixEnd_440340 := by exact prefixLift 440340
  have htrace : WordTrace (prefixWord ++ tailWord_440340) baseStart_440340 baseEnd_440340 := by
    simpa [prefixWord, tailWord_440340, baseEnd_440340] using wordTrace_append hprefix tailTrace_440340
  have hstable : (prefixWord ++ tailWord_440340).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440340).length < 2 ^ (prefixWord ++ tailWord_440340).sum := by decide
  have hdescent : baseEnd_440340 < baseStart_440340 := by decide
  rcases family_descends (prefixWord ++ tailWord_440340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440354 : List Nat := [3, 3, 1, 1, 1, 2, 3, 4, 2]
def baseStart_440354 : Nat := 118140960795 + 440354 * 2 ^ 59
def prefixEnd_440354 : Nat := 4983230072969 + 3 ^ 40 * 440354 * 2
def baseEnd_440354 : Nat := 200989564560066974799871

theorem tailTrace_440354 : CollatzResearch.WordTrace tailWord_440354 prefixEnd_440354 200989564560066974799871 := by
  unfold tailWord_440354
  simp only [CollatzResearch.WordTrace]
  refine ⟨4015257461670034830204029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10707353231120092880544077 4015257461670034830204029)
  ·
    refine ⟨1505721548126263061326511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4015257461670034830204029 1505721548126263061326511)
    ·
      refine ⟨2258582322189394591989767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1505721548126263061326511 2258582322189394591989767)
      ·
        refine ⟨3387873483284091887984651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2258582322189394591989767 3387873483284091887984651)
        ·
          refine ⟨5081810224926137831976977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3387873483284091887984651 5081810224926137831976977)
          ·
            refine ⟨3811357668694603373982733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5081810224926137831976977 3811357668694603373982733)
            ·
              refine ⟨1429259125760476265243525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3811357668694603373982733 1429259125760476265243525)
              ·
                refine ⟨267986086080089299733161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1429259125760476265243525 267986086080089299733161)
                ·
                  refine ⟨200989564560066974799871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 267986086080089299733161 200989564560066974799871)
                  ·
                    rfl

theorem cell20_440354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_440354 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_440354 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_440354 prefixEnd_440354 := by exact prefixLift 440354
  have htrace : WordTrace (prefixWord ++ tailWord_440354) baseStart_440354 baseEnd_440354 := by
    simpa [prefixWord, tailWord_440354, baseEnd_440354] using wordTrace_append hprefix tailTrace_440354
  have hstable : (prefixWord ++ tailWord_440354).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440354).length < 2 ^ (prefixWord ++ tailWord_440354).sum := by decide
  have hdescent : baseEnd_440354 < baseStart_440354 := by decide
  rcases family_descends (prefixWord ++ tailWord_440354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440402 : List Nat := [3, 2, 2, 1, 5, 1, 1, 2, 3]
def baseStart_440402 : Nat := 118140960795 + 440402 * 2 ^ 59
def prefixEnd_440402 : Nat := 4983230072969 + 3 ^ 40 * 440402 * 2
def baseEnd_440402 : Nat := 201011473067992141199675

theorem tailTrace_440402 : CollatzResearch.WordTrace tailWord_440402 prefixEnd_440402 201011473067992141199675 := by
  unfold tailWord_440402
  simp only [CollatzResearch.WordTrace]
  refine ⟨4015695137626560879640865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10708520367004162345708973 4015695137626560879640865)
  ·
    refine ⟨3011771353219920659730649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4015695137626560879640865 3011771353219920659730649)
    ·
      refine ⟨2258828514914940494797987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3011771353219920659730649 2258828514914940494797987)
      ·
        refine ⟨3388242772372410742196981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2258828514914940494797987 3388242772372410742196981)
        ·
          refine ⟨317647759909913507080967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3388242772372410742196981 317647759909913507080967)
          ·
            refine ⟨476471639864870260621451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317647759909913507080967 476471639864870260621451)
            ·
              refine ⟨714707459797305390932177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 476471639864870260621451 714707459797305390932177)
              ·
                refine ⟨536030594847979043199133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 714707459797305390932177 536030594847979043199133)
                ·
                  refine ⟨201011473067992141199675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 536030594847979043199133 201011473067992141199675)
                  ·
                    rfl

theorem cell20_440402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 2, 3].length) (baseStart_440402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_440402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_440402 prefixEnd_440402 := by exact prefixLift 440402
  have htrace : WordTrace (prefixWord ++ tailWord_440402) baseStart_440402 baseEnd_440402 := by
    simpa [prefixWord, tailWord_440402, baseEnd_440402] using wordTrace_append hprefix tailTrace_440402
  have hstable : (prefixWord ++ tailWord_440402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440402).length < 2 ^ (prefixWord ++ tailWord_440402).sum := by decide
  have hdescent : baseEnd_440402 < baseStart_440402 := by decide
  rcases family_descends (prefixWord ++ tailWord_440402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440458 : List Nat := [3, 1, 2, 3, 1, 4, 6]
def baseStart_440458 : Nat := 118140960795 + 440458 * 2 ^ 59
def prefixEnd_440458 : Nat := 4983230072969 + 3 ^ 40 * 440458 * 2
def baseEnd_440458 : Nat := 22337448110433870592531

theorem tailTrace_440458 : CollatzResearch.WordTrace tailWord_440458 prefixEnd_440458 22337448110433870592531 := by
  unfold tailWord_440458
  simp only [CollatzResearch.WordTrace]
  refine ⟨4016205759575841270650507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10709882025535576721734685 4016205759575841270650507)
  ·
    refine ⟨6024308639363761905975761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4016205759575841270650507 6024308639363761905975761)
    ·
      refine ⟨4518231479522821429481821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6024308639363761905975761 4518231479522821429481821)
      ·
        refine ⟨1694336804821058036055683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4518231479522821429481821 1694336804821058036055683)
        ·
          refine ⟨2541505207231587054083525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1694336804821058036055683 2541505207231587054083525)
          ·
            refine ⟨476532226355922572640661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2541505207231587054083525 476532226355922572640661)
            ·
              refine ⟨22337448110433870592531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 476532226355922572640661 22337448110433870592531)
              ·
                rfl

theorem cell20_440458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 6].length) (baseStart_440458 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_440458 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_440458 prefixEnd_440458 := by exact prefixLift 440458
  have htrace : WordTrace (prefixWord ++ tailWord_440458) baseStart_440458 baseEnd_440458 := by
    simpa [prefixWord, tailWord_440458, baseEnd_440458] using wordTrace_append hprefix tailTrace_440458
  have hstable : (prefixWord ++ tailWord_440458).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440458).length < 2 ^ (prefixWord ++ tailWord_440458).sum := by decide
  have hdescent : baseEnd_440458 < baseStart_440458 := by decide
  rcases family_descends (prefixWord ++ tailWord_440458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440470 : List Nat := [5, 3, 2, 1, 2, 1, 2, 1, 3]
def baseStart_440470 : Nat := 118140960795 + 440470 * 2 ^ 59
def prefixEnd_440470 : Nat := 4983230072969 + 3 ^ 40 * 440470 * 2
def baseEnd_440470 : Nat := 201042510120886126932731

theorem tailTrace_440470 : CollatzResearch.WordTrace tailWord_440470 prefixEnd_440470 201042510120886126932731 := by
  unfold tailWord_440470
  simp only [CollatzResearch.WordTrace]
  refine ⟨1004078794641243195752429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10710173809506594088025909 1004078794641243195752429)
  ·
    refine ⟨376529547990466198407161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1004078794641243195752429 376529547990466198407161)
    ·
      refine ⟨282397160992849648805371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376529547990466198407161 282397160992849648805371)
      ·
        refine ⟨423595741489274473208057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282397160992849648805371 423595741489274473208057)
        ·
          refine ⟨317696806116955854906043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 423595741489274473208057 317696806116955854906043)
          ·
            refine ⟨476545209175433782359065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317696806116955854906043 476545209175433782359065)
            ·
              refine ⟨357408906881575336769299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 476545209175433782359065 357408906881575336769299)
              ·
                refine ⟨536113360322363005153949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 357408906881575336769299 536113360322363005153949)
                ·
                  refine ⟨201042510120886126932731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 536113360322363005153949 201042510120886126932731)
                  ·
                    rfl

theorem cell20_440470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_440470 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_440470 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_440470 prefixEnd_440470 := by exact prefixLift 440470
  have htrace : WordTrace (prefixWord ++ tailWord_440470) baseStart_440470 baseEnd_440470 := by
    simpa [prefixWord, tailWord_440470, baseEnd_440470] using wordTrace_append hprefix tailTrace_440470
  have hstable : (prefixWord ++ tailWord_440470).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440470).length < 2 ^ (prefixWord ++ tailWord_440470).sum := by decide
  have hdescent : baseEnd_440470 < baseStart_440470 := by decide
  rcases family_descends (prefixWord ++ tailWord_440470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440513 : List Nat := [1, 2, 6, 1, 3, 7]
def baseStart_440513 : Nat := 118140960795 + 440513 * 2 ^ 59
def prefixEnd_440513 : Nat := 4983230072969 + 3 ^ 40 * 440513 * 2
def baseEnd_440513 : Nat := 7446745796021077351823

theorem tailTrace_440513 : CollatzResearch.WordTrace tailWord_440513 prefixEnd_440513 7446745796021077351823 := by
  unfold tailWord_440513
  simp only [CollatzResearch.WordTrace]
  refine ⟨16066829053104109475854193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10711219368736072983902795 16066829053104109475854193)
  ·
    refine ⟨12050121789828082106890645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16066829053104109475854193 12050121789828082106890645)
    ·
      refine ⟨564849458898191348760499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12050121789828082106890645 564849458898191348760499)
      ·
        refine ⟨847274188347287023140749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 564849458898191348760499 847274188347287023140749)
        ·
          refine ⟨317727820630232633677781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 847274188347287023140749 317727820630232633677781)
          ·
            refine ⟨7446745796021077351823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 317727820630232633677781 7446745796021077351823)
            ·
              rfl

theorem cell20_440513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 7].length) (baseStart_440513 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_440513 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_440513 prefixEnd_440513 := by exact prefixLift 440513
  have htrace : WordTrace (prefixWord ++ tailWord_440513) baseStart_440513 baseEnd_440513 := by
    simpa [prefixWord, tailWord_440513, baseEnd_440513] using wordTrace_append hprefix tailTrace_440513
  have hstable : (prefixWord ++ tailWord_440513).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440513).length < 2 ^ (prefixWord ++ tailWord_440513).sum := by decide
  have hdescent : baseEnd_440513 < baseStart_440513 := by decide
  rcases family_descends (prefixWord ++ tailWord_440513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440527 : List Nat := [1, 1, 2, 1, 1, 3, 5, 4, 2]
def baseStart_440527 : Nat := 118140960795 + 440527 * 2 ^ 59
def prefixEnd_440527 : Nat := 4983230072969 + 3 ^ 40 * 440527 * 2
def baseEnd_440527 : Nat := 201068526474047262032497

theorem tailTrace_440527 : CollatzResearch.WordTrace tailWord_440527 prefixEnd_440527 201068526474047262032497 := by
  unfold tailWord_440527
  simp only [CollatzResearch.WordTrace]
  refine ⟨16067339675053389866863835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10711559783368926577909223 16067339675053389866863835)
  ·
    refine ⟨24101009512580084800295753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16067339675053389866863835 24101009512580084800295753)
    ·
      refine ⟨18075757134435063600221815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24101009512580084800295753 18075757134435063600221815)
      ·
        refine ⟨27113635701652595400332723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18075757134435063600221815 27113635701652595400332723)
        ·
          refine ⟨40670453552478893100499085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27113635701652595400332723 40670453552478893100499085)
          ·
            refine ⟨15251420082179584912687157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40670453552478893100499085 15251420082179584912687157)
            ·
              refine ⟨1429820632704336085564421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15251420082179584912687157 1429820632704336085564421)
              ·
                refine ⟨268091368632063016043329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1429820632704336085564421 268091368632063016043329)
                ·
                  refine ⟨201068526474047262032497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 268091368632063016043329 201068526474047262032497)
                  ·
                    rfl

theorem cell20_440527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 4, 2].length) (baseStart_440527 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_440527 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_440527 prefixEnd_440527 := by exact prefixLift 440527
  have htrace : WordTrace (prefixWord ++ tailWord_440527) baseStart_440527 baseEnd_440527 := by
    simpa [prefixWord, tailWord_440527, baseEnd_440527] using wordTrace_append hprefix tailTrace_440527
  have hstable : (prefixWord ++ tailWord_440527).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440527).length < 2 ^ (prefixWord ++ tailWord_440527).sum := by decide
  have hdescent : baseEnd_440527 < baseStart_440527 := by decide
  rcases family_descends (prefixWord ++ tailWord_440527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440551 : List Nat := [1, 1, 5, 3, 1, 2, 3, 4]
def baseStart_440551 : Nat := 118140960795 + 440551 * 2 ^ 59
def prefixEnd_440551 : Nat := 4983230072969 + 3 ^ 40 * 440551 * 2
def baseEnd_440551 : Nat := 67026493576003281744133

theorem tailTrace_440551 : CollatzResearch.WordTrace tailWord_440551 prefixEnd_440551 67026493576003281744133 := by
  unfold tailWord_440551
  simp only [CollatzResearch.WordTrace]
  refine ⟨16068215026966441965737507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10712143351310961310491671 16068215026966441965737507)
  ·
    refine ⟨24102322540449662948606261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16068215026966441965737507 24102322540449662948606261)
    ·
      refine ⟨2259592738167155901431837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24102322540449662948606261 2259592738167155901431837)
      ·
        refine ⟨847347276812683463036939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2259592738167155901431837 847347276812683463036939)
        ·
          refine ⟨1271020915219025194555409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 847347276812683463036939 1271020915219025194555409)
          ·
            refine ⟨953265686414268895916557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1271020915219025194555409 953265686414268895916557)
            ·
              refine ⟨357474632405350835968709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 953265686414268895916557 357474632405350835968709)
              ·
                refine ⟨67026493576003281744133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 357474632405350835968709 67026493576003281744133)
                ·
                  rfl

theorem cell20_440551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 4].length) (baseStart_440551 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_440551 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_440551 prefixEnd_440551 := by exact prefixLift 440551
  have htrace : WordTrace (prefixWord ++ tailWord_440551) baseStart_440551 baseEnd_440551 := by
    simpa [prefixWord, tailWord_440551, baseEnd_440551] using wordTrace_append hprefix tailTrace_440551
  have hstable : (prefixWord ++ tailWord_440551).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440551).length < 2 ^ (prefixWord ++ tailWord_440551).sum := by decide
  have hdescent : baseEnd_440551 < baseStart_440551 := by decide
  rcases family_descends (prefixWord ++ tailWord_440551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440586 : List Nat := [3, 1, 2, 2, 1, 1, 3, 3, 4]
def baseStart_440586 : Nat := 118140960795 + 440586 * 2 ^ 59
def prefixEnd_440586 : Nat := 4983230072969 + 3 ^ 40 * 440586 * 2
def baseEnd_440586 : Nat := 201095455681705279065589

theorem tailTrace_440586 : CollatzResearch.WordTrace tailWord_440586 prefixEnd_440586 201095455681705279065589 := by
  unfold tailWord_440586
  simp only [CollatzResearch.WordTrace]
  refine ⟨4017372895459910735815403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10712994387893095295507741 4017372895459910735815403)
  ·
    refine ⟨6026059343189866103723105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4017372895459910735815403 6026059343189866103723105)
    ·
      refine ⟨4519544507392399577792329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6026059343189866103723105 4519544507392399577792329)
      ·
        refine ⟨3389658380544299683344247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4519544507392399577792329 3389658380544299683344247)
        ·
          refine ⟨5084487570816449525016371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3389658380544299683344247 5084487570816449525016371)
          ·
            refine ⟨7626731356224674287524557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5084487570816449525016371 7626731356224674287524557)
            ·
              refine ⟨2860024258584252857821709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7626731356224674287524557 2860024258584252857821709)
              ·
                refine ⟨1072509096969094821683141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2860024258584252857821709 1072509096969094821683141)
                ·
                  refine ⟨201095455681705279065589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1072509096969094821683141 201095455681705279065589)
                  ·
                    rfl

theorem cell20_440586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_440586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_440586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_440586 prefixEnd_440586 := by exact prefixLift 440586
  have htrace : WordTrace (prefixWord ++ tailWord_440586) baseStart_440586 baseEnd_440586 := by
    simpa [prefixWord, tailWord_440586, baseEnd_440586] using wordTrace_append hprefix tailTrace_440586
  have hstable : (prefixWord ++ tailWord_440586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440586).length < 2 ^ (prefixWord ++ tailWord_440586).sum := by decide
  have hdescent : baseEnd_440586 < baseStart_440586 := by decide
  rcases family_descends (prefixWord ++ tailWord_440586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440606 : List Nat := [4, 3, 2, 1, 1, 1, 4, 4]
def baseStart_440606 : Nat := 118140960795 + 440606 * 2 ^ 59
def prefixEnd_440606 : Nat := 4983230072969 + 3 ^ 40 * 440606 * 2
def baseEnd_440606 : Nat := 67034861408891366132947

theorem tailTrace_440606 : CollatzResearch.WordTrace tailWord_440606 prefixEnd_440606 67034861408891366132947 := by
  unfold tailWord_440606
  simp only [CollatzResearch.WordTrace]
  refine ⟨2008777630220898294873709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10713480694511457572659781 2008777630220898294873709)
  ·
    refine ⟨753291611332836860577641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2008777630220898294873709 753291611332836860577641)
    ·
      refine ⟨564968708499627645433231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 753291611332836860577641 564968708499627645433231)
      ·
        refine ⟨847453062749441468149847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 564968708499627645433231 847453062749441468149847)
        ·
          refine ⟨1271179594124162202224771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 847453062749441468149847 1271179594124162202224771)
          ·
            refine ⟨1906769391186243303337157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1271179594124162202224771 1906769391186243303337157)
            ·
              refine ⟨357519260847420619375717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1906769391186243303337157 357519260847420619375717)
              ·
                refine ⟨67034861408891366132947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 357519260847420619375717 67034861408891366132947)
                ·
                  rfl

theorem cell20_440606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_440606 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_440606 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_440606 prefixEnd_440606 := by exact prefixLift 440606
  have htrace : WordTrace (prefixWord ++ tailWord_440606) baseStart_440606 baseEnd_440606 := by
    simpa [prefixWord, tailWord_440606, baseEnd_440606] using wordTrace_append hprefix tailTrace_440606
  have hstable : (prefixWord ++ tailWord_440606).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440606).length < 2 ^ (prefixWord ++ tailWord_440606).sum := by decide
  have hdescent : baseEnd_440606 < baseStart_440606 := by decide
  rcases family_descends (prefixWord ++ tailWord_440606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440610 : List Nat := [3, 3, 1, 1, 3, 2, 1, 6]
def baseStart_440610 : Nat := 118140960795 + 440610 * 2 ^ 59
def prefixEnd_440610 : Nat := 4983230072969 + 3 ^ 40 * 440610 * 2
def baseEnd_440610 : Nat := 67035469978555954088497

theorem tailTrace_440610 : CollatzResearch.WordTrace tailWord_440610 prefixEnd_440610 67035469978555954088497 := by
  unfold tailWord_440610
  simp only [CollatzResearch.WordTrace]
  refine ⟨4017591733438173760533821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10713577955835130028090189 4017591733438173760533821)
  ·
    refine ⟨1506596900039315160200183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4017591733438173760533821 1506596900039315160200183)
    ·
      refine ⟨2259895350058972740300275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1506596900039315160200183 2259895350058972740300275)
      ·
        refine ⟨3389843025088459110450413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2259895350058972740300275 3389843025088459110450413)
        ·
          refine ⟨1271191134408172166418905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3389843025088459110450413 1271191134408172166418905)
          ·
            refine ⟨953393350806129124814179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1271191134408172166418905 953393350806129124814179)
            ·
              refine ⟨1430090026209193687221269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 953393350806129124814179 1430090026209193687221269)
              ·
                refine ⟨67035469978555954088497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1430090026209193687221269 67035469978555954088497)
                ·
                  rfl

theorem cell20_440610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 6].length) (baseStart_440610 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_440610 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_440610 prefixEnd_440610 := by exact prefixLift 440610
  have htrace : WordTrace (prefixWord ++ tailWord_440610) baseStart_440610 baseEnd_440610 := by
    simpa [prefixWord, tailWord_440610, baseEnd_440610] using wordTrace_append hprefix tailTrace_440610
  have hstable : (prefixWord ++ tailWord_440610).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440610).length < 2 ^ (prefixWord ++ tailWord_440610).sum := by decide
  have hdescent : baseEnd_440610 < baseStart_440610 := by decide
  rcases family_descends (prefixWord ++ tailWord_440610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440616 : List Nat := [2, 1, 5, 1, 4, 1, 1, 3, 2]
def baseStart_440616 : Nat := 118140960795 + 440616 * 2 ^ 59
def prefixEnd_440616 : Nat := 4983230072969 + 3 ^ 40 * 440616 * 2
def baseEnd_440616 : Nat := 201109148499158508065467

theorem tailTrace_440616 : CollatzResearch.WordTrace tailWord_440616 prefixEnd_440616 201109148499158508065467 := by
  unfold tailWord_440616
  simp only [CollatzResearch.WordTrace]
  refine ⟨8035292885865479033426851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10713723847820638711235801 8035292885865479033426851)
  ·
    refine ⟨12052939328798218550140277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8035292885865479033426851 12052939328798218550140277)
    ·
      refine ⟨1129963062074832989075651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12052939328798218550140277 1129963062074832989075651)
      ·
        refine ⟨1694944593112249483613477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1129963062074832989075651 1694944593112249483613477)
        ·
          refine ⟨317802111208546778177527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1694944593112249483613477 317802111208546778177527)
          ·
            refine ⟨476703166812820167266291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317802111208546778177527 476703166812820167266291)
            ·
              refine ⟨715054750219230250899437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 476703166812820167266291 715054750219230250899437)
              ·
                refine ⟨268145531332211344087289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 715054750219230250899437 268145531332211344087289)
                ·
                  refine ⟨201109148499158508065467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 268145531332211344087289 201109148499158508065467)
                  ·
                    rfl

theorem cell20_440616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 3, 2].length) (baseStart_440616 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_440616 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_440616 prefixEnd_440616 := by exact prefixLift 440616
  have htrace : WordTrace (prefixWord ++ tailWord_440616) baseStart_440616 baseEnd_440616 := by
    simpa [prefixWord, tailWord_440616, baseEnd_440616] using wordTrace_append hprefix tailTrace_440616
  have hstable : (prefixWord ++ tailWord_440616).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440616).length < 2 ^ (prefixWord ++ tailWord_440616).sum := by decide
  have hdescent : baseEnd_440616 < baseStart_440616 := by decide
  rcases family_descends (prefixWord ++ tailWord_440616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440683 : List Nat := [1, 1, 1, 1, 2, 2, 2, 4, 6]
def baseStart_440683 : Nat := 118140960795 + 440683 * 2 ^ 59
def prefixEnd_440683 : Nat := 4983230072969 + 3 ^ 40 * 440683 * 2
def baseEnd_440683 : Nat := 201139729124804052831859

theorem tailTrace_440683 : CollatzResearch.WordTrace tailWord_440683 prefixEnd_440683 201139729124804052831859 := by
  unfold tailWord_440683
  simp only [CollatzResearch.WordTrace]
  refine ⟨16073029462488228509542703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10715352974992152339695135 16073029462488228509542703)
  ·
    refine ⟨24109544193732342764314055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16073029462488228509542703 24109544193732342764314055)
    ·
      refine ⟨36164316290598514146471083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24109544193732342764314055 36164316290598514146471083)
      ·
        refine ⟨54246474435897771219706625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36164316290598514146471083 54246474435897771219706625)
        ·
          refine ⟨40684855826923328414779969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54246474435897771219706625 40684855826923328414779969)
          ·
            refine ⟨30513641870192496311084977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40684855826923328414779969 30513641870192496311084977)
            ·
              refine ⟨22885231402644372233313733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30513641870192496311084977 22885231402644372233313733)
              ·
                refine ⟨4290980887995819793746325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22885231402644372233313733 4290980887995819793746325)
                ·
                  refine ⟨201139729124804052831859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4290980887995819793746325 201139729124804052831859)
                  ·
                    rfl

theorem cell20_440683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 6].length) (baseStart_440683 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_440683 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_440683 prefixEnd_440683 := by exact prefixLift 440683
  have htrace : WordTrace (prefixWord ++ tailWord_440683) baseStart_440683 baseEnd_440683 := by
    simpa [prefixWord, tailWord_440683, baseEnd_440683] using wordTrace_append hprefix tailTrace_440683
  have hstable : (prefixWord ++ tailWord_440683).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440683).length < 2 ^ (prefixWord ++ tailWord_440683).sum := by decide
  have hdescent : baseEnd_440683 < baseStart_440683 := by decide
  rcases family_descends (prefixWord ++ tailWord_440683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440738 : List Nat := [3, 3, 1, 2, 1, 1, 1, 2, 6]
def baseStart_440738 : Nat := 118140960795 + 440738 * 2 ^ 59
def prefixEnd_440738 : Nat := 4983230072969 + 3 ^ 40 * 440738 * 2
def baseEnd_440738 : Nat := 201164832623468305998301

theorem tailTrace_440738 : CollatzResearch.WordTrace tailWord_440738 prefixEnd_440738 201164832623468305998301 := by
  unfold tailWord_440738
  simp only [CollatzResearch.WordTrace]
  refine ⟨4018758869322243225698717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10716690318192648601863245 4018758869322243225698717)
  ·
    refine ⟨1507034575995841209637019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4018758869322243225698717 1507034575995841209637019)
    ·
      refine ⟨2260551863993761814455529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1507034575995841209637019 2260551863993761814455529)
      ·
        refine ⟨1695413897995321360841647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2260551863993761814455529 1695413897995321360841647)
        ·
          refine ⟨2543120846992982041262471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1695413897995321360841647 2543120846992982041262471)
          ·
            refine ⟨3814681270489473061893707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2543120846992982041262471 3814681270489473061893707)
            ·
              refine ⟨5722021905734209592840561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3814681270489473061893707 5722021905734209592840561)
              ·
                refine ⟨4291516429300657194630421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5722021905734209592840561 4291516429300657194630421)
                ·
                  refine ⟨201164832623468305998301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4291516429300657194630421 201164832623468305998301)
                  ·
                    rfl

theorem cell20_440738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_440738 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_440738 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_440738 prefixEnd_440738 := by exact prefixLift 440738
  have htrace : WordTrace (prefixWord ++ tailWord_440738) baseStart_440738 baseEnd_440738 := by
    simpa [prefixWord, tailWord_440738, baseEnd_440738] using wordTrace_append hprefix tailTrace_440738
  have hstable : (prefixWord ++ tailWord_440738).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440738).length < 2 ^ (prefixWord ++ tailWord_440738).sum := by decide
  have hdescent : baseEnd_440738 < baseStart_440738 := by decide
  rcases family_descends (prefixWord ++ tailWord_440738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440776 : List Nat := [2, 1, 3, 1, 3, 2, 2, 2, 4]
def baseStart_440776 : Nat := 118140960795 + 440776 * 2 ^ 59
def prefixEnd_440776 : Nat := 4983230072969 + 3 ^ 40 * 440776 * 2
def baseEnd_440776 : Nat := 201182176858909062731479

theorem tailTrace_440776 : CollatzResearch.WordTrace tailWord_440776 prefixEnd_440776 201182176858909062731479 := by
  unfold tailWord_440776
  simp only [CollatzResearch.WordTrace]
  refine ⟨8038210725575652696339091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10717614300767536928452121 8038210725575652696339091)
  ·
    refine ⟨12057316088363479044508637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8038210725575652696339091 12057316088363479044508637)
    ·
      refine ⟨4521493533136304641690739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12057316088363479044508637 4521493533136304641690739)
      ·
        refine ⟨6782240299704456962536109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4521493533136304641690739 6782240299704456962536109)
        ·
          refine ⟨2543340112389171360951041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6782240299704456962536109 2543340112389171360951041)
          ·
            refine ⟨1907505084291878520713281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2543340112389171360951041 1907505084291878520713281)
            ·
              refine ⟨1430628813218908890534961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1907505084291878520713281 1430628813218908890534961)
              ·
                refine ⟨1072971609914181667901221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1430628813218908890534961 1072971609914181667901221)
                ·
                  refine ⟨201182176858909062731479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1072971609914181667901221 201182176858909062731479)
                  ·
                    rfl

theorem cell20_440776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 4].length) (baseStart_440776 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_440776 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_440776 prefixEnd_440776 := by exact prefixLift 440776
  have htrace : WordTrace (prefixWord ++ tailWord_440776) baseStart_440776 baseEnd_440776 := by
    simpa [prefixWord, tailWord_440776, baseEnd_440776] using wordTrace_append hprefix tailTrace_440776
  have hstable : (prefixWord ++ tailWord_440776).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440776).length < 2 ^ (prefixWord ++ tailWord_440776).sum := by decide
  have hdescent : baseEnd_440776 < baseStart_440776 := by decide
  rcases family_descends (prefixWord ++ tailWord_440776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440807 : List Nat := [1, 1, 5, 2, 1, 1, 2, 4, 3]
def baseStart_440807 : Nat := 118140960795 + 440807 * 2 ^ 59
def prefixEnd_440807 : Nat := 4983230072969 + 3 ^ 40 * 440807 * 2
def baseEnd_440807 : Nat := 201196326103610732698019

theorem tailTrace_440807 : CollatzResearch.WordTrace tailWord_440807 prefixEnd_440807 201196326103610732698019 := by
  unfold tailWord_440807
  simp only [CollatzResearch.WordTrace]
  refine ⟨16077552114038997687056675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10718368076025998458037783 16077552114038997687056675)
  ·
    refine ⟨24116328171058496530585013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16077552114038997687056675 24116328171058496530585013)
    ·
      refine ⟨2260905766036734049742345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24116328171058496530585013 2260905766036734049742345)
      ·
        refine ⟨1695679324527550537306759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2260905766036734049742345 1695679324527550537306759)
        ·
          refine ⟨2543518986791325805960139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1695679324527550537306759 2543518986791325805960139)
          ·
            refine ⟨3815278480186988708940209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2543518986791325805960139 3815278480186988708940209)
            ·
              refine ⟨2861458860140241531705157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3815278480186988708940209 2861458860140241531705157)
              ·
                refine ⟨536523536276295287194717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2861458860140241531705157 536523536276295287194717)
                ·
                  refine ⟨201196326103610732698019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 536523536276295287194717 201196326103610732698019)
                  ·
                    rfl

theorem cell20_440807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 4, 3].length) (baseStart_440807 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_440807 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_440807 prefixEnd_440807 := by exact prefixLift 440807
  have htrace : WordTrace (prefixWord ++ tailWord_440807) baseStart_440807 baseEnd_440807 := by
    simpa [prefixWord, tailWord_440807, baseEnd_440807] using wordTrace_append hprefix tailTrace_440807
  have hstable : (prefixWord ++ tailWord_440807).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440807).length < 2 ^ (prefixWord ++ tailWord_440807).sum := by decide
  have hdescent : baseEnd_440807 < baseStart_440807 := by decide
  rcases family_descends (prefixWord ++ tailWord_440807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440835 : List Nat := [1, 1, 1, 3, 2, 1, 4, 1, 6]
def baseStart_440835 : Nat := 118140960795 + 440835 * 2 ^ 59
def prefixEnd_440835 : Nat := 4983230072969 + 3 ^ 40 * 440835 * 2
def baseEnd_440835 : Nat := 201209106066567079764571

theorem tailTrace_440835 : CollatzResearch.WordTrace tailWord_440835 prefixEnd_440835 201209106066567079764571 := by
  unfold tailWord_440835
  simp only [CollatzResearch.WordTrace]
  refine ⟨16078573357937558469075959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10719048905291705646050639 16078573357937558469075959)
  ·
    refine ⟨24117860036906337703613939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16078573357937558469075959 24117860036906337703613939)
    ·
      refine ⟨36176790055359506555420909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24117860036906337703613939 36176790055359506555420909)
      ·
        refine ⟨13566296270759814958282841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36176790055359506555420909 13566296270759814958282841)
        ·
          refine ⟨10174722203069861218712131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13566296270759814958282841 10174722203069861218712131)
          ·
            refine ⟨15262083304604791828068197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10174722203069861218712131 15262083304604791828068197)
            ·
              refine ⟨2861640619613398467762787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15262083304604791828068197 2861640619613398467762787)
              ·
                refine ⟨4292460929420097701644181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2861640619613398467762787 4292460929420097701644181)
                ·
                  refine ⟨201209106066567079764571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4292460929420097701644181 201209106066567079764571)
                  ·
                    rfl

theorem cell20_440835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 6].length) (baseStart_440835 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_440835 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_440835 prefixEnd_440835 := by exact prefixLift 440835
  have htrace : WordTrace (prefixWord ++ tailWord_440835) baseStart_440835 baseEnd_440835 := by
    simpa [prefixWord, tailWord_440835, baseEnd_440835] using wordTrace_append hprefix tailTrace_440835
  have hstable : (prefixWord ++ tailWord_440835).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440835).length < 2 ^ (prefixWord ++ tailWord_440835).sum := by decide
  have hdescent : baseEnd_440835 < baseStart_440835 := by decide
  rcases family_descends (prefixWord ++ tailWord_440835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440890 : List Nat := [3, 1, 1, 1, 3, 4, 1, 2, 4]
def baseStart_440890 : Nat := 118140960795 + 440890 * 2 ^ 59
def prefixEnd_440890 : Nat := 4983230072969 + 3 ^ 40 * 440890 * 2
def baseEnd_440890 : Nat := 201234209565231332931013

theorem tailTrace_440890 : CollatzResearch.WordTrace tailWord_440890 prefixEnd_440890 201234209565231332931013 := by
  unfold tailWord_440890
  simp only [CollatzResearch.WordTrace]
  refine ⟨4020144843184575715582031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10720386248492201908218749 4020144843184575715582031)
  ·
    refine ⟨6030217264776863573373047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4020144843184575715582031 6030217264776863573373047)
    ·
      refine ⟨9045325897165295360059571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6030217264776863573373047 9045325897165295360059571)
      ·
        refine ⟨13567988845747943040089357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9045325897165295360059571 13567988845747943040089357)
        ·
          refine ⟨5087995817155478640033509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13567988845747943040089357 5087995817155478640033509)
          ·
            refine ⟨953999215716652245006283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5087995817155478640033509 953999215716652245006283)
            ·
              refine ⟨1430998823574978367509425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 953999215716652245006283 1430998823574978367509425)
              ·
                refine ⟨1073249117681233775632069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1430998823574978367509425 1073249117681233775632069)
                ·
                  refine ⟨201234209565231332931013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1073249117681233775632069 201234209565231332931013)
                  ·
                    rfl

theorem cell20_440890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_440890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_440890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_440890 prefixEnd_440890 := by exact prefixLift 440890
  have htrace : WordTrace (prefixWord ++ tailWord_440890) baseStart_440890 baseEnd_440890 := by
    simpa [prefixWord, tailWord_440890, baseEnd_440890] using wordTrace_append hprefix tailTrace_440890
  have hstable : (prefixWord ++ tailWord_440890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440890).length < 2 ^ (prefixWord ++ tailWord_440890).sum := by decide
  have hdescent : baseEnd_440890 < baseStart_440890 := by decide
  rcases family_descends (prefixWord ++ tailWord_440890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440938 : List Nat := [3, 1, 3, 2, 1, 1, 5, 1, 3]
def baseStart_440938 : Nat := 118140960795 + 440938 * 2 ^ 59
def prefixEnd_440938 : Nat := 4983230072969 + 3 ^ 40 * 440938 * 2
def baseEnd_440938 : Nat := 201256118073156499330817

theorem tailTrace_440938 : CollatzResearch.WordTrace tailWord_440938 prefixEnd_440938 201256118073156499330817 := by
  unfold tailWord_440938
  simp only [CollatzResearch.WordTrace]
  refine ⟨4020582519141101765018867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10721553384376271373383645 4020582519141101765018867)
  ·
    refine ⟨6030873778711652647528301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4020582519141101765018867 6030873778711652647528301)
    ·
      refine ⟨2261577667016869742823113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6030873778711652647528301 2261577667016869742823113)
      ·
        refine ⟨1696183250262652307117335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2261577667016869742823113 1696183250262652307117335)
        ·
          refine ⟨2544274875393978460676003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1696183250262652307117335 2544274875393978460676003)
          ·
            refine ⟨3816412313090967691014005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2544274875393978460676003 3816412313090967691014005)
            ·
              refine ⟨357788654352278221032563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3816412313090967691014005 357788654352278221032563)
              ·
                refine ⟨536682981528417331548845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 357788654352278221032563 536682981528417331548845)
                ·
                  refine ⟨201256118073156499330817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 536682981528417331548845 201256118073156499330817)
                  ·
                    rfl

theorem cell20_440938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 1, 3].length) (baseStart_440938 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_440938 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_440938 prefixEnd_440938 := by exact prefixLift 440938
  have htrace : WordTrace (prefixWord ++ tailWord_440938) baseStart_440938 baseEnd_440938 := by
    simpa [prefixWord, tailWord_440938, baseEnd_440938] using wordTrace_append hprefix tailTrace_440938
  have hstable : (prefixWord ++ tailWord_440938).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440938).length < 2 ^ (prefixWord ++ tailWord_440938).sum := by decide
  have hdescent : baseEnd_440938 < baseStart_440938 := by decide
  rcases family_descends (prefixWord ++ tailWord_440938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440990 : List Nat := [4, 3, 1, 1, 1, 1, 4, 5]
def baseStart_440990 : Nat := 118140960795 + 440990 * 2 ^ 59
def prefixEnd_440990 : Nat := 4983230072969 + 3 ^ 40 * 440990 * 2
def baseEnd_440990 : Nat := 67093284096691809865757

theorem tailTrace_440990 : CollatzResearch.WordTrace tailWord_440990 prefixEnd_440990 67093284096691809865757 := by
  unfold tailWord_440990
  simp only [CollatzResearch.WordTrace]
  refine ⟨2010528334047002492621053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10722817781584013293978949 2010528334047002492621053)
  ·
    refine ⟨753948125267625934732895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2010528334047002492621053 753948125267625934732895)
    ·
      refine ⟨1130922187901438902099343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 753948125267625934732895 1130922187901438902099343)
      ·
        refine ⟨1696383281852158353149015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1130922187901438902099343 1696383281852158353149015)
        ·
          refine ⟨2544574922778237529723523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1696383281852158353149015 2544574922778237529723523)
          ·
            refine ⟨3816862384167356294585285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2544574922778237529723523 3816862384167356294585285)
            ·
              refine ⟨715661697031379305234741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3816862384167356294585285 715661697031379305234741)
              ·
                refine ⟨67093284096691809865757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 715661697031379305234741 67093284096691809865757)
                ·
                  rfl

theorem cell20_440990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_440990 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_440990 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_440990 prefixEnd_440990 := by exact prefixLift 440990
  have htrace : WordTrace (prefixWord ++ tailWord_440990) baseStart_440990 baseEnd_440990 := by
    simpa [prefixWord, tailWord_440990, baseEnd_440990] using wordTrace_append hprefix tailTrace_440990
  have hstable : (prefixWord ++ tailWord_440990).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440990).length < 2 ^ (prefixWord ++ tailWord_440990).sum := by decide
  have hdescent : baseEnd_440990 < baseStart_440990 := by decide
  rcases family_descends (prefixWord ++ tailWord_440990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440993 : List Nat := [1, 2, 3, 3, 3, 2, 2, 1, 3]
def baseStart_440993 : Nat := 118140960795 + 440993 * 2 ^ 59
def prefixEnd_440993 : Nat := 4983230072969 + 3 ^ 40 * 440993 * 2
def baseEnd_440993 : Nat := 201281221571820752497259

theorem tailTrace_440993 : CollatzResearch.WordTrace tailWord_440993 prefixEnd_440993 201281221571820752497259 := by
  unfold tailWord_440993
  simp only [CollatzResearch.WordTrace]
  refine ⟨16084336091365151453327633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10722890727576767635551755 16084336091365151453327633)
  ·
    refine ⟨12063252068523863589995725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16084336091365151453327633 12063252068523863589995725)
    ·
      refine ⟨4523719525696448846248397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12063252068523863589995725 4523719525696448846248397)
      ·
        refine ⟨1696394822136168317343149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4523719525696448846248397 1696394822136168317343149)
        ·
          refine ⟨636148058301063119003681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1696394822136168317343149 636148058301063119003681)
          ·
            refine ⟨477111043725797339252761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 636148058301063119003681 477111043725797339252761)
            ·
              refine ⟨357833282794348004439571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 477111043725797339252761 357833282794348004439571)
              ·
                refine ⟨536749924191522006659357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 357833282794348004439571 536749924191522006659357)
                ·
                  refine ⟨201281221571820752497259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 536749924191522006659357 201281221571820752497259)
                  ·
                    rfl

theorem cell20_440993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 1, 3].length) (baseStart_440993 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_440993 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_440993 prefixEnd_440993 := by exact prefixLift 440993
  have htrace : WordTrace (prefixWord ++ tailWord_440993) baseStart_440993 baseEnd_440993 := by
    simpa [prefixWord, tailWord_440993, baseEnd_440993] using wordTrace_append hprefix tailTrace_440993
  have hstable : (prefixWord ++ tailWord_440993).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440993).length < 2 ^ (prefixWord ++ tailWord_440993).sum := by decide
  have hdescent : baseEnd_440993 < baseStart_440993 := by decide
  rcases family_descends (prefixWord ++ tailWord_440993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441030 : List Nat := [6, 1, 2, 1, 3, 1, 2, 2, 2]
def baseStart_441030 : Nat := 118140960795 + 441030 * 2 ^ 59
def prefixEnd_441030 : Nat := 4983230072969 + 3 ^ 40 * 441030 * 2
def baseEnd_441030 : Nat := 201298109380013068263775

theorem tailTrace_441030 : CollatzResearch.WordTrace tailWord_441030 prefixEnd_441030 201298109380013068263775 := by
  unfold tailWord_441030
  simp only [CollatzResearch.WordTrace]
  refine ⟨502677674757222086638267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10723790394820737848283029 502677674757222086638267)
  ·
    refine ⟨754016512135833129957401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 502677674757222086638267 754016512135833129957401)
    ·
      refine ⟨565512384101874847468051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 754016512135833129957401 565512384101874847468051)
      ·
        refine ⟨848268576152812271202077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 565512384101874847468051 848268576152812271202077)
        ·
          refine ⟨318100716057304601700779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 848268576152812271202077 318100716057304601700779)
          ·
            refine ⟨477151074085956902551169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318100716057304601700779 477151074085956902551169)
            ·
              refine ⟨357863305564467676913377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 477151074085956902551169 357863305564467676913377)
              ·
                refine ⟨268397479173350757685033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 357863305564467676913377 268397479173350757685033)
                ·
                  refine ⟨201298109380013068263775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 268397479173350757685033 201298109380013068263775)
                  ·
                    rfl

theorem cell20_441030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_441030 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_441030 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_441030 prefixEnd_441030 := by exact prefixLift 441030
  have htrace : WordTrace (prefixWord ++ tailWord_441030) baseStart_441030 baseEnd_441030 := by
    simpa [prefixWord, tailWord_441030, baseEnd_441030] using wordTrace_append hprefix tailTrace_441030
  have hstable : (prefixWord ++ tailWord_441030).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441030).length < 2 ^ (prefixWord ++ tailWord_441030).sum := by decide
  have hdescent : baseEnd_441030 < baseStart_441030 := by decide
  rcases family_descends (prefixWord ++ tailWord_441030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441032 : List Nat := [2, 1, 3, 1, 2, 11]
def baseStart_441032 : Nat := 118140960795 + 441032 * 2 ^ 59
def prefixEnd_441032 : Nat := 4983230072969 + 3 ^ 40 * 441032 * 2
def baseEnd_441032 : Nat := 7455519342018887044337

theorem tailTrace_441032 : CollatzResearch.WordTrace tailWord_441032 prefixEnd_441032 7455519342018887044337 := by
  unfold tailWord_441032
  simp only [CollatzResearch.WordTrace]
  refine ⟨8042879269111930556998675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10723839025482574075998233 8042879269111930556998675)
  ·
    refine ⟨12064318903667895835498013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8042879269111930556998675 12064318903667895835498013)
    ·
      refine ⟨4524119588875460938311755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12064318903667895835498013 4524119588875460938311755)
      ·
        refine ⟨6786179383313191407467633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4524119588875460938311755 6786179383313191407467633)
        ·
          refine ⟨5089634537484893555600725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6786179383313191407467633 5089634537484893555600725)
          ·
            refine ⟨7455519342018887044337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5089634537484893555600725 7455519342018887044337)
            ·
              rfl

theorem cell20_441032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 11].length) (baseStart_441032 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_441032 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_441032 prefixEnd_441032 := by exact prefixLift 441032
  have htrace : WordTrace (prefixWord ++ tailWord_441032) baseStart_441032 baseEnd_441032 := by
    simpa [prefixWord, tailWord_441032, baseEnd_441032] using wordTrace_append hprefix tailTrace_441032
  have hstable : (prefixWord ++ tailWord_441032).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441032).length < 2 ^ (prefixWord ++ tailWord_441032).sum := by decide
  have hdescent : baseEnd_441032 < baseStart_441032 := by decide
  rcases family_descends (prefixWord ++ tailWord_441032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441038 : List Nat := [4, 1, 1, 1, 3, 2, 4, 2, 2]
def baseStart_441038 : Nat := 118140960795 + 441038 * 2 ^ 59
def prefixEnd_441038 : Nat := 4983230072969 + 3 ^ 40 * 441038 * 2
def baseEnd_441038 : Nat := 201301760798000595997075

theorem tailTrace_441038 : CollatzResearch.WordTrace tailWord_441038 prefixEnd_441038 201301760798000595997075 := by
  unfold tailWord_441038
  simp only [CollatzResearch.WordTrace]
  refine ⟨2010747172025265517339471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10723984917468082759143845 2010747172025265517339471)
  ·
    refine ⟨3016120758037898276009207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2010747172025265517339471 3016120758037898276009207)
    ·
      refine ⟨4524181137056847414013811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3016120758037898276009207 4524181137056847414013811)
      ·
        refine ⟨6786271705585271121020717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4524181137056847414013811 6786271705585271121020717)
        ·
          refine ⟨2544851889594476670382769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6786271705585271121020717 2544851889594476670382769)
          ·
            refine ⟨1908638917195857502787077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2544851889594476670382769 1908638917195857502787077)
            ·
              refine ⟨357869796974223281772577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1908638917195857502787077 357869796974223281772577)
              ·
                refine ⟨268402347730667461329433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 357869796974223281772577 268402347730667461329433)
                ·
                  refine ⟨201301760798000595997075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 268402347730667461329433 201301760798000595997075)
                  ·
                    rfl

theorem cell20_441038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 2, 2].length) (baseStart_441038 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_441038 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_441038 prefixEnd_441038 := by exact prefixLift 441038
  have htrace : WordTrace (prefixWord ++ tailWord_441038) baseStart_441038 baseEnd_441038 := by
    simpa [prefixWord, tailWord_441038, baseEnd_441038] using wordTrace_append hprefix tailTrace_441038
  have hstable : (prefixWord ++ tailWord_441038).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441038).length < 2 ^ (prefixWord ++ tailWord_441038).sum := by decide
  have hdescent : baseEnd_441038 < baseStart_441038 := by decide
  rcases family_descends (prefixWord ++ tailWord_441038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441045 : List Nat := [1, 3, 2, 5, 1, 2, 1, 5]
def baseStart_441045 : Nat := 118140960795 + 441045 * 2 ^ 59
def prefixEnd_441045 : Nat := 4983230072969 + 3 ^ 40 * 441045 * 2
def baseEnd_441045 : Nat := 67101651929579894254571

theorem tailTrace_441045 : CollatzResearch.WordTrace tailWord_441045 prefixEnd_441045 67101651929579894254571 := by
  unfold tailWord_441045
  simp only [CollatzResearch.WordTrace]
  refine ⟨16086232687176764334220589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10724155124784509556147059 16086232687176764334220589)
  ·
    refine ⟨6032337257691286625332721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16086232687176764334220589 6032337257691286625332721)
    ·
      refine ⟨4524252943268464968999541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6032337257691286625332721 4524252943268464968999541)
      ·
        refine ⟨424148713431418590843707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4524252943268464968999541 424148713431418590843707)
        ·
          refine ⟨636223070147127886265561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424148713431418590843707 636223070147127886265561)
          ·
            refine ⟨477167302610345914699171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 636223070147127886265561 477167302610345914699171)
            ·
              refine ⟨715750953915518872048757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 477167302610345914699171 715750953915518872048757)
              ·
                refine ⟨67101651929579894254571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 715750953915518872048757 67101651929579894254571)
                ·
                  rfl

theorem cell20_441045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 5].length) (baseStart_441045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_441045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_441045 prefixEnd_441045 := by exact prefixLift 441045
  have htrace : WordTrace (prefixWord ++ tailWord_441045) baseStart_441045 baseEnd_441045 := by
    simpa [prefixWord, tailWord_441045, baseEnd_441045] using wordTrace_append hprefix tailTrace_441045
  have hstable : (prefixWord ++ tailWord_441045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441045).length < 2 ^ (prefixWord ++ tailWord_441045).sum := by decide
  have hdescent : baseEnd_441045 < baseStart_441045 := by decide
  rcases family_descends (prefixWord ++ tailWord_441045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441052 : List Nat := [2, 2, 5, 1, 1, 1, 2, 3, 3]
def baseStart_441052 : Nat := 118140960795 + 441052 * 2 ^ 59
def prefixEnd_441052 : Nat := 4983230072969 + 3 ^ 40 * 441052 * 2
def baseEnd_441052 : Nat := 201308150779478769530351

theorem tailTrace_441052 : CollatzResearch.WordTrace tailWord_441052 prefixEnd_441052 201308150779478769530351 := by
  unfold tailWord_441052
  simp only [CollatzResearch.WordTrace]
  refine ⟨8043243999075702264862705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10724325332100936353150273 8043243999075702264862705)
  ·
    refine ⟨6032432999306776698647029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8043243999075702264862705 6032432999306776698647029)
    ·
      refine ⟨565540593685010315498159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6032432999306776698647029 565540593685010315498159)
      ·
        refine ⟨848310890527515473247239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 565540593685010315498159 848310890527515473247239)
        ·
          refine ⟨1272466335791273209870859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 848310890527515473247239 1272466335791273209870859)
          ·
            refine ⟨1908699503686909814806289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1272466335791273209870859 1908699503686909814806289)
            ·
              refine ⟨1431524627765182361104717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1908699503686909814806289 1431524627765182361104717)
              ·
                refine ⟨536821735411943385414269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1431524627765182361104717 536821735411943385414269)
                ·
                  refine ⟨201308150779478769530351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 536821735411943385414269 201308150779478769530351)
                  ·
                    rfl

theorem cell20_441052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 3, 3].length) (baseStart_441052 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_441052 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_441052 prefixEnd_441052 := by exact prefixLift 441052
  have htrace : WordTrace (prefixWord ++ tailWord_441052) baseStart_441052 baseEnd_441052 := by
    simpa [prefixWord, tailWord_441052, baseEnd_441052] using wordTrace_append hprefix tailTrace_441052
  have hstable : (prefixWord ++ tailWord_441052).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441052).length < 2 ^ (prefixWord ++ tailWord_441052).sum := by decide
  have hdescent : baseEnd_441052 < baseStart_441052 := by decide
  rcases family_descends (prefixWord ++ tailWord_441052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441090 : List Nat := [3, 4, 1, 1, 1, 2, 3, 2, 3]
def baseStart_441090 : Nat := 118140960795 + 441090 * 2 ^ 59
def prefixEnd_441090 : Nat := 4983230072969 + 3 ^ 40 * 441090 * 2
def baseEnd_441090 : Nat := 201325495014919526263529

theorem tailTrace_441090 : CollatzResearch.WordTrace tailWord_441090 prefixEnd_441090 201325495014919526263529 := by
  unfold tailWord_441090
  simp only [CollatzResearch.WordTrace]
  refine ⟨4021968493003434254902181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10725249314675824679739149 4021968493003434254902181)
  ·
    refine ⟨754119092438143922794159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4021968493003434254902181 754119092438143922794159)
    ·
      refine ⟨1131178638657215884191239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 754119092438143922794159 1131178638657215884191239)
      ·
        refine ⟨1696767957985823826286859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1131178638657215884191239 1696767957985823826286859)
        ·
          refine ⟨2545151936978735739430289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1696767957985823826286859 2545151936978735739430289)
          ·
            refine ⟨1908863952734051804572717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2545151936978735739430289 1908863952734051804572717)
            ·
              refine ⟨715823982275269426714769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1908863952734051804572717 715823982275269426714769)
              ·
                refine ⟨536867986706452070036077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 715823982275269426714769 536867986706452070036077)
                ·
                  refine ⟨201325495014919526263529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 536867986706452070036077 201325495014919526263529)
                  ·
                    rfl

theorem cell20_441090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_441090 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_441090 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_441090 prefixEnd_441090 := by exact prefixLift 441090
  have htrace : WordTrace (prefixWord ++ tailWord_441090) baseStart_441090 baseEnd_441090 := by
    simpa [prefixWord, tailWord_441090, baseEnd_441090] using wordTrace_append hprefix tailTrace_441090
  have hstable : (prefixWord ++ tailWord_441090).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441090).length < 2 ^ (prefixWord ++ tailWord_441090).sum := by decide
  have hdescent : baseEnd_441090 < baseStart_441090 := by decide
  rcases family_descends (prefixWord ++ tailWord_441090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441115 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 9]
def baseStart_441115 : Nat := 118140960795 + 441115 * 2 ^ 59
def prefixEnd_441115 : Nat := 4983230072969 + 3 ^ 40 * 441115 * 2
def baseEnd_441115 : Nat := 201336905696130550430093

theorem tailTrace_441115 : CollatzResearch.WordTrace tailWord_441115 prefixEnd_441115 201336905696130550430093 := by
  unfold tailWord_441115
  simp only [CollatzResearch.WordTrace]
  refine ⟨16088785796923166289268799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10725857197948777526179199 16088785796923166289268799)
  ·
    refine ⟨24133178695384749433903199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16088785796923166289268799 24133178695384749433903199)
    ·
      refine ⟨36199768043077124150854799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24133178695384749433903199 36199768043077124150854799)
      ·
        refine ⟨54299652064615686226282199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36199768043077124150854799 54299652064615686226282199)
        ·
          refine ⟨81449478096923529339423299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54299652064615686226282199 81449478096923529339423299)
          ·
            refine ⟨122174217145385294009134949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81449478096923529339423299 122174217145385294009134949)
            ·
              refine ⟨22907665714759742626712803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122174217145385294009134949 22907665714759742626712803)
              ·
                refine ⟨34361498572139613940069205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22907665714759742626712803 34361498572139613940069205)
                ·
                  refine ⟨201336905696130550430093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 34361498572139613940069205 201336905696130550430093)
                  ·
                    rfl

theorem cell20_441115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 9].length) (baseStart_441115 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_441115 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_441115 prefixEnd_441115 := by exact prefixLift 441115
  have htrace : WordTrace (prefixWord ++ tailWord_441115) baseStart_441115 baseEnd_441115 := by
    simpa [prefixWord, tailWord_441115, baseEnd_441115] using wordTrace_append hprefix tailTrace_441115
  have hstable : (prefixWord ++ tailWord_441115).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441115).length < 2 ^ (prefixWord ++ tailWord_441115).sum := by decide
  have hdescent : baseEnd_441115 < baseStart_441115 := by decide
  rcases family_descends (prefixWord ++ tailWord_441115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441184 : List Nat := [2, 1, 1, 3, 3, 1, 1, 8]
def baseStart_441184 : Nat := 118140960795 + 441184 * 2 ^ 59
def prefixEnd_441184 : Nat := 4983230072969 + 3 ^ 40 * 441184 * 2
def baseEnd_441184 : Nat := 67122799725424325709937

theorem tailTrace_441184 : CollatzResearch.WordTrace tailWord_441184 prefixEnd_441184 67122799725424325709937 := by
  unfold tailWord_441184
  simp only [CollatzResearch.WordTrace]
  refine ⟨8045651216836595536765303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10727534955782127382353737 8045651216836595536765303)
  ·
    refine ⟨12068476825254893305147955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8045651216836595536765303 12068476825254893305147955)
    ·
      refine ⟨18102715237882339957721933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12068476825254893305147955 18102715237882339957721933)
      ·
        refine ⟨6788518214205877484145725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18102715237882339957721933 6788518214205877484145725)
        ·
          refine ⟨2545694330327204056554647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6788518214205877484145725 2545694330327204056554647)
          ·
            refine ⟨3818541495490806084831971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2545694330327204056554647 3818541495490806084831971)
            ·
              refine ⟨5727812243236209127247957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3818541495490806084831971 5727812243236209127247957)
              ·
                refine ⟨67122799725424325709937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5727812243236209127247957 67122799725424325709937)
                ·
                  rfl

theorem cell20_441184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 8].length) (baseStart_441184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_441184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_441184 prefixEnd_441184 := by exact prefixLift 441184
  have htrace : WordTrace (prefixWord ++ tailWord_441184) baseStart_441184 baseEnd_441184 := by
    simpa [prefixWord, tailWord_441184, baseEnd_441184] using wordTrace_append hprefix tailTrace_441184
  have hstable : (prefixWord ++ tailWord_441184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441184).length < 2 ^ (prefixWord ++ tailWord_441184).sum := by decide
  have hdescent : baseEnd_441184 < baseStart_441184 := by decide
  rcases family_descends (prefixWord ++ tailWord_441184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441211 : List Nat := [1, 1, 1, 1, 1, 5, 6, 2, 2]
def baseStart_441211 : Nat := 118140960795 + 441211 * 2 ^ 59
def prefixEnd_441211 : Nat := 4983230072969 + 3 ^ 40 * 441211 * 2
def baseEnd_441211 : Nat := 201380722711980883229701

theorem tailTrace_441211 : CollatzResearch.WordTrace tailWord_441211 prefixEnd_441211 201380722711980883229701 := by
  unfold tailWord_441211
  simp only [CollatzResearch.WordTrace]
  refine ⟨16092287204575374684763487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10728191469716916456508991 16092287204575374684763487)
  ·
    refine ⟨24138430806863062027145231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16092287204575374684763487 24138430806863062027145231)
    ·
      refine ⟨36207646210294593040717847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24138430806863062027145231 36207646210294593040717847)
      ·
        refine ⟨54311469315441889561076771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36207646210294593040717847 54311469315441889561076771)
        ·
          refine ⟨81467203973162834341615157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54311469315441889561076771 81467203973162834341615157)
          ·
            refine ⟨7637550372484015719526421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81467203973162834341615157 7637550372484015719526421)
            ·
              refine ⟨358010173710188236852801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7637550372484015719526421 358010173710188236852801)
              ·
                refine ⟨268507630282641177639601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 358010173710188236852801 268507630282641177639601)
                ·
                  refine ⟨201380722711980883229701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 268507630282641177639601 201380722711980883229701)
                  ·
                    rfl

theorem cell20_441211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 2, 2].length) (baseStart_441211 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_441211 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_441211 prefixEnd_441211 := by exact prefixLift 441211
  have htrace : WordTrace (prefixWord ++ tailWord_441211) baseStart_441211 baseEnd_441211 := by
    simpa [prefixWord, tailWord_441211, baseEnd_441211] using wordTrace_append hprefix tailTrace_441211
  have hstable : (prefixWord ++ tailWord_441211).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441211).length < 2 ^ (prefixWord ++ tailWord_441211).sum := by decide
  have hdescent : baseEnd_441211 < baseStart_441211 := by decide
  rcases family_descends (prefixWord ++ tailWord_441211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441214 : List Nat := [4, 2, 3, 1, 3, 1, 1, 5]
def baseStart_441214 : Nat := 118140960795 + 441214 * 2 ^ 59
def prefixEnd_441214 : Nat := 4983230072969 + 3 ^ 40 * 441214 * 2
def baseEnd_441214 : Nat := 67127363997908735376563

theorem tailTrace_441214 : CollatzResearch.WordTrace tailWord_441214 prefixEnd_441214 67127363997908735376563 := by
  unfold tailWord_441214
  simp only [CollatzResearch.WordTrace]
  refine ⟨2011549577945563274640337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10728264415709670798081797 2011549577945563274640337)
  ·
    refine ⟨1508662183459172455980253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2011549577945563274640337 1508662183459172455980253)
    ·
      refine ⟨565748318797189670992595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1508662183459172455980253 565748318797189670992595)
      ·
        refine ⟨848622478195784506488893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 565748318797189670992595 848622478195784506488893)
        ·
          refine ⟨318233429323419189933335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 848622478195784506488893 318233429323419189933335)
          ·
            refine ⟨477350143985128784900003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318233429323419189933335 477350143985128784900003)
            ·
              refine ⟨716025215977693177350005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 477350143985128784900003 716025215977693177350005)
              ·
                refine ⟨67127363997908735376563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 716025215977693177350005 67127363997908735376563)
                ·
                  rfl

theorem cell20_441214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_441214 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_441214 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_441214 prefixEnd_441214 := by exact prefixLift 441214
  have htrace : WordTrace (prefixWord ++ tailWord_441214) baseStart_441214 baseEnd_441214 := by
    simpa [prefixWord, tailWord_441214, baseEnd_441214] using wordTrace_append hprefix tailTrace_441214
  have hstable : (prefixWord ++ tailWord_441214).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441214).length < 2 ^ (prefixWord ++ tailWord_441214).sum := by decide
  have hdescent : baseEnd_441214 < baseStart_441214 := by decide
  rcases family_descends (prefixWord ++ tailWord_441214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441239 : List Nat := [1, 1, 3, 3, 1, 2, 5, 4]
def baseStart_441239 : Nat := 118140960795 + 441239 * 2 ^ 59
def prefixEnd_441239 : Nat := 4983230072969 + 3 ^ 40 * 441239 * 2
def baseEnd_441239 : Nat := 67131167558312410098751

theorem tailTrace_441239 : CollatzResearch.WordTrace tailWord_441239 prefixEnd_441239 67131167558312410098751 := by
  unfold tailWord_441239
  simp only [CollatzResearch.WordTrace]
  refine ⟨16093308448473935466782771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10728872298982623644521847 16093308448473935466782771)
  ·
    refine ⟨24139962672710903200174157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16093308448473935466782771 24139962672710903200174157)
    ·
      refine ⟨9052486002266588700065309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24139962672710903200174157 9052486002266588700065309)
      ·
        refine ⟨3394682250849970762524491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9052486002266588700065309 3394682250849970762524491)
        ·
          refine ⟨5092023376274956143786737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3394682250849970762524491 5092023376274956143786737)
          ·
            refine ⟨3819017532206217107840053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5092023376274956143786737 3819017532206217107840053)
            ·
              refine ⟨358032893644332853860005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3819017532206217107840053 358032893644332853860005)
              ·
                refine ⟨67131167558312410098751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 358032893644332853860005 67131167558312410098751)
                ·
                  rfl

theorem cell20_441239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 4].length) (baseStart_441239 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_441239 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_441239 prefixEnd_441239 := by exact prefixLift 441239
  have htrace : WordTrace (prefixWord ++ tailWord_441239) baseStart_441239 baseEnd_441239 := by
    simpa [prefixWord, tailWord_441239, baseEnd_441239] using wordTrace_append hprefix tailTrace_441239
  have hstable : (prefixWord ++ tailWord_441239).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441239).length < 2 ^ (prefixWord ++ tailWord_441239).sum := by decide
  have hdescent : baseEnd_441239 < baseStart_441239 := by decide
  rcases family_descends (prefixWord ++ tailWord_441239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441249 : List Nat := [1, 2, 3, 4, 1, 1, 1, 5, 2]
def baseStart_441249 : Nat := 118140960795 + 441249 * 2 ^ 59
def prefixEnd_441249 : Nat := 4983230072969 + 3 ^ 40 * 441249 * 2
def baseEnd_441249 : Nat := 201398066947421639962879

theorem tailTrace_441249 : CollatzResearch.WordTrace tailWord_441249 prefixEnd_441249 201398066947421639962879 := by
  unfold tailWord_441249
  simp only [CollatzResearch.WordTrace]
  refine ⟨16093673178437707174646801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10729115452291804783097867 16093673178437707174646801)
  ·
    refine ⟨12070254883828280380985101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16093673178437707174646801 12070254883828280380985101)
    ·
      refine ⟨4526345581435605142869413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12070254883828280380985101 4526345581435605142869413)
      ·
        refine ⟨848689796519175964288015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4526345581435605142869413 848689796519175964288015)
        ·
          refine ⟨1273034694778763946432023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 848689796519175964288015 1273034694778763946432023)
          ·
            refine ⟨1909552042168145919648035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1273034694778763946432023 1909552042168145919648035)
            ·
              refine ⟨2864328063252218879472053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1909552042168145919648035 2864328063252218879472053)
              ·
                refine ⟨268530755929895519950505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2864328063252218879472053 268530755929895519950505)
                ·
                  refine ⟨201398066947421639962879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 268530755929895519950505 201398066947421639962879)
                  ·
                    rfl

theorem cell20_441249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5, 2].length) (baseStart_441249 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_441249 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_441249 prefixEnd_441249 := by exact prefixLift 441249
  have htrace : WordTrace (prefixWord ++ tailWord_441249) baseStart_441249 baseEnd_441249 := by
    simpa [prefixWord, tailWord_441249, baseEnd_441249] using wordTrace_append hprefix tailTrace_441249
  have hstable : (prefixWord ++ tailWord_441249).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441249).length < 2 ^ (prefixWord ++ tailWord_441249).sum := by decide
  have hdescent : baseEnd_441249 < baseStart_441249 := by decide
  rcases family_descends (prefixWord ++ tailWord_441249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441286 : List Nat := [6, 1, 3, 1, 1, 2, 2, 4]
def baseStart_441286 : Nat := 118140960795 + 441286 * 2 ^ 59
def prefixEnd_441286 : Nat := 4983230072969 + 3 ^ 40 * 441286 * 2
def baseEnd_441286 : Nat := 67138318251871318576465

theorem tailTrace_441286 : CollatzResearch.WordTrace tailWord_441286 prefixEnd_441286 67138318251871318576465 := by
  unfold tailWord_441286
  simp only [CollatzResearch.WordTrace]
  refine ⟨502969458728239452929491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10730015119535774995829141 502969458728239452929491)
  ·
    refine ⟨754454188092359179394237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 502969458728239452929491 754454188092359179394237)
    ·
      refine ⟨282920320534634692272839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 754454188092359179394237 282920320534634692272839)
      ·
        refine ⟨424380480801952038409259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282920320534634692272839 424380480801952038409259)
        ·
          refine ⟨636570721202928057613889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424380480801952038409259 636570721202928057613889)
          ·
            refine ⟨477428040902196043210417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 636570721202928057613889 477428040902196043210417)
            ·
              refine ⟨358071030676647032407813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 477428040902196043210417 358071030676647032407813)
              ·
                refine ⟨67138318251871318576465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 358071030676647032407813 67138318251871318576465)
                ·
                  rfl

theorem cell20_441286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_441286 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_441286 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_441286 prefixEnd_441286 := by exact prefixLift 441286
  have htrace : WordTrace (prefixWord ++ tailWord_441286) baseStart_441286 baseEnd_441286 := by
    simpa [prefixWord, tailWord_441286, baseEnd_441286] using wordTrace_append hprefix tailTrace_441286
  have hstable : (prefixWord ++ tailWord_441286).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441286).length < 2 ^ (prefixWord ++ tailWord_441286).sum := by decide
  have hdescent : baseEnd_441286 < baseStart_441286 := by decide
  rcases family_descends (prefixWord ++ tailWord_441286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441291 : List Nat := [1, 1, 1, 1, 3, 5, 2, 2, 4]
def baseStart_441291 : Nat := 118140960795 + 441291 * 2 ^ 59
def prefixEnd_441291 : Nat := 4983230072969 + 3 ^ 40 * 441291 * 2
def baseEnd_441291 : Nat := 201417236891856160562707

theorem tailTrace_441291 : CollatzResearch.WordTrace tailWord_441291 prefixEnd_441291 201417236891856160562707 := by
  unfold tailWord_441291
  simp only [CollatzResearch.WordTrace]
  refine ⟨16095205044285548347675727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10730136696190365565117151 16095205044285548347675727)
  ·
    refine ⟨24142807566428322521513591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16095205044285548347675727 24142807566428322521513591)
    ·
      refine ⟨36214211349642483782270387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24142807566428322521513591 36214211349642483782270387)
      ·
        refine ⟨54321317024463725673405581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36214211349642483782270387 54321317024463725673405581)
        ·
          refine ⟨20370493884173897127527093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54321317024463725673405581 20370493884173897127527093)
          ·
            refine ⟨1909733801641302855705665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20370493884173897127527093 1909733801641302855705665)
            ·
              refine ⟨1432300351230977141779249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1909733801641302855705665 1432300351230977141779249)
              ·
                refine ⟨1074225263423232856334437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1432300351230977141779249 1074225263423232856334437)
                ·
                  refine ⟨201417236891856160562707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1074225263423232856334437 201417236891856160562707)
                  ·
                    rfl

theorem cell20_441291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 4].length) (baseStart_441291 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_441291 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_441291 prefixEnd_441291 := by exact prefixLift 441291
  have htrace : WordTrace (prefixWord ++ tailWord_441291) baseStart_441291 baseEnd_441291 := by
    simpa [prefixWord, tailWord_441291, baseEnd_441291] using wordTrace_append hprefix tailTrace_441291
  have hstable : (prefixWord ++ tailWord_441291).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441291).length < 2 ^ (prefixWord ++ tailWord_441291).sum := by decide
  have hdescent : baseEnd_441291 < baseStart_441291 := by decide
  rcases family_descends (prefixWord ++ tailWord_441291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441294 : List Nat := [4, 1, 1, 1, 2, 5, 2, 4]
def baseStart_441294 : Nat := 118140960795 + 441294 * 2 ^ 59
def prefixEnd_441294 : Nat := 4983230072969 + 3 ^ 40 * 441294 * 2
def baseEnd_441294 : Nat := 67139535391200494487565

theorem tailTrace_441294 : CollatzResearch.WordTrace tailWord_441294 prefixEnd_441294 67139535391200494487565 := by
  unfold tailWord_441294
  simp only [CollatzResearch.WordTrace]
  refine ⟨2011914307909334982504367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10730209642183119906689957 2011914307909334982504367)
  ·
    refine ⟨3017871461864002473756551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2011914307909334982504367 3017871461864002473756551)
    ·
      refine ⟨4526807192796003710634827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3017871461864002473756551 4526807192796003710634827)
      ·
        refine ⟨6790210789194005565952241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4526807192796003710634827 6790210789194005565952241)
        ·
          refine ⟨5092658091895504174464181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6790210789194005565952241 5092658091895504174464181)
          ·
            refine ⟨477436696115203516356017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5092658091895504174464181 477436696115203516356017)
            ·
              refine ⟨358077522086402637267013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 477436696115203516356017 358077522086402637267013)
              ·
                refine ⟨67139535391200494487565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 358077522086402637267013 67139535391200494487565)
                ·
                  rfl

theorem cell20_441294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_441294 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_441294 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_441294 prefixEnd_441294 := by exact prefixLift 441294
  have htrace : WordTrace (prefixWord ++ tailWord_441294) baseStart_441294 baseEnd_441294 := by
    simpa [prefixWord, tailWord_441294, baseEnd_441294] using wordTrace_append hprefix tailTrace_441294
  have hstable : (prefixWord ++ tailWord_441294).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441294).length < 2 ^ (prefixWord ++ tailWord_441294).sum := by decide
  have hdescent : baseEnd_441294 < baseStart_441294 := by decide
  rcases family_descends (prefixWord ++ tailWord_441294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441322 : List Nat := [3, 1, 3, 1, 2, 2, 2, 1, 5]
def baseStart_441322 : Nat := 118140960795 + 441322 * 2 ^ 59
def prefixEnd_441322 : Nat := 4983230072969 + 3 ^ 40 * 441322 * 2
def baseEnd_441322 : Nat := 201431386136557830529247

theorem tailTrace_441322 : CollatzResearch.WordTrace tailWord_441322 prefixEnd_441322 201431386136557830529247 := by
  unfold tailWord_441322
  simp only [CollatzResearch.WordTrace]
  refine ⟨4024083926793310160513555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10730890471448827094702813 4024083926793310160513555)
  ·
    refine ⟨6036125890189965240770333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4024083926793310160513555 6036125890189965240770333)
    ·
      refine ⟨2263547208821236965288875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6036125890189965240770333 2263547208821236965288875)
      ·
        refine ⟨3395320813231855447933313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2263547208821236965288875 3395320813231855447933313)
        ·
          refine ⟨2546490609923891585949985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3395320813231855447933313 2546490609923891585949985)
          ·
            refine ⟨1909867957442918689462489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2546490609923891585949985 1909867957442918689462489)
            ·
              refine ⟨1432400968082189017096867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1909867957442918689462489 1432400968082189017096867)
              ·
                refine ⟨2148601452123283525645301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1432400968082189017096867 2148601452123283525645301)
                ·
                  refine ⟨201431386136557830529247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2148601452123283525645301 201431386136557830529247)
                  ·
                    rfl

theorem cell20_441322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_441322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_441322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_441322 prefixEnd_441322 := by exact prefixLift 441322
  have htrace : WordTrace (prefixWord ++ tailWord_441322) baseStart_441322 baseEnd_441322 := by
    simpa [prefixWord, tailWord_441322, baseEnd_441322] using wordTrace_append hprefix tailTrace_441322
  have hstable : (prefixWord ++ tailWord_441322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441322).length < 2 ^ (prefixWord ++ tailWord_441322).sum := by decide
  have hdescent : baseEnd_441322 < baseStart_441322 := by decide
  rcases family_descends (prefixWord ++ tailWord_441322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441374 : List Nat := [4, 3, 13]
def baseStart_441374 : Nat := 118140960795 + 441374 * 2 ^ 59
def prefixEnd_441374 : Nat := 4983230072969 + 3 ^ 40 * 441374 * 2
def baseEnd_441374 : Nat := 276344472364165652669

theorem tailTrace_441374 : CollatzResearch.WordTrace tailWord_441374 prefixEnd_441374 276344472364165652669 := by
  unfold tailWord_441374
  simp only [CollatzResearch.WordTrace]
  refine ⟨2012279037873106690368397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10732154868656569015298117 2012279037873106690368397)
  ·
    refine ⟨754604639202415008888149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2012279037873106690368397 754604639202415008888149)
    ·
      refine ⟨276344472364165652669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 13 754604639202415008888149 276344472364165652669)
      ·
        rfl

theorem cell20_441374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 13].length) (baseStart_441374 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_441374 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_441374 prefixEnd_441374 := by exact prefixLift 441374
  have htrace : WordTrace (prefixWord ++ tailWord_441374) baseStart_441374 baseEnd_441374 := by
    simpa [prefixWord, tailWord_441374, baseEnd_441374] using wordTrace_append hprefix tailTrace_441374
  have hstable : (prefixWord ++ tailWord_441374).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441374).length < 2 ^ (prefixWord ++ tailWord_441374).sum := by decide
  have hdescent : baseEnd_441374 < baseStart_441374 := by decide
  rcases family_descends (prefixWord ++ tailWord_441374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441376 : List Nat := [2, 1, 1, 7, 2, 1, 2, 2, 2]
def baseStart_441376 : Nat := 118140960795 + 441376 * 2 ^ 59
def prefixEnd_441376 : Nat := 4983230072969 + 3 ^ 40 * 441376 * 2
def baseEnd_441376 : Nat := 201456033207973642729027

theorem tailTrace_441376 : CollatzResearch.WordTrace tailWord_441376 prefixEnd_441376 201456033207973642729027 := by
  unfold tailWord_441376
  simp only [CollatzResearch.WordTrace]
  refine ⟨8049152624488803932259991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10732203499318405243013321 8049152624488803932259991)
  ·
    refine ⟨12073728936733205898389987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8049152624488803932259991 12073728936733205898389987)
    ·
      refine ⟨18110593405099808847584981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12073728936733205898389987 18110593405099808847584981)
      ·
        refine ⟨424467032932026769865273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 18110593405099808847584981 424467032932026769865273)
        ·
          refine ⟨318350274699020077398955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 424467032932026769865273 318350274699020077398955)
          ·
            refine ⟨477525412048530116098433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318350274699020077398955 477525412048530116098433)
            ·
              refine ⟨358144059036397587073825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 477525412048530116098433 358144059036397587073825)
              ·
                refine ⟨268608044277298190305369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 358144059036397587073825 268608044277298190305369)
                ·
                  refine ⟨201456033207973642729027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 268608044277298190305369 201456033207973642729027)
                  ·
                    rfl

theorem cell20_441376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 2, 2].length) (baseStart_441376 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_441376 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_441376 prefixEnd_441376 := by exact prefixLift 441376
  have htrace : WordTrace (prefixWord ++ tailWord_441376) baseStart_441376 baseEnd_441376 := by
    simpa [prefixWord, tailWord_441376, baseEnd_441376] using wordTrace_append hprefix tailTrace_441376
  have hstable : (prefixWord ++ tailWord_441376).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441376).length < 2 ^ (prefixWord ++ tailWord_441376).sum := by decide
  have hdescent : baseEnd_441376 < baseStart_441376 := by decide
  rcases family_descends (prefixWord ++ tailWord_441376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441377 : List Nat := [1, 2, 3, 2, 3, 2, 2, 2, 3]
def baseStart_441377 : Nat := 118140960795 + 441377 * 2 ^ 59
def prefixEnd_441377 : Nat := 4983230072969 + 3 ^ 40 * 441377 * 2
def baseEnd_441377 : Nat := 201456489635222083695689

theorem tailTrace_441377 : CollatzResearch.WordTrace tailWord_441377 prefixEnd_441377 201456489635222083695689 := by
  unfold tailWord_441377
  simp only [CollatzResearch.WordTrace]
  refine ⟨16098341721973985035306385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10732227814649323356870923 16098341721973985035306385)
  ·
    refine ⟨12073756291480488776479789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16098341721973985035306385 12073756291480488776479789)
    ·
      refine ⟨4527658609305183291179921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12073756291480488776479789 4527658609305183291179921)
      ·
        refine ⟨3395743956978887468384941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4527658609305183291179921 3395743956978887468384941)
        ·
          refine ⟨1273403983867082800644353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3395743956978887468384941 1273403983867082800644353)
          ·
            refine ⟨955052987900312100483265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1273403983867082800644353 955052987900312100483265)
            ·
              refine ⟨716289740925234075362449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 955052987900312100483265 716289740925234075362449)
              ·
                refine ⟨537217305693925556521837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 716289740925234075362449 537217305693925556521837)
                ·
                  refine ⟨201456489635222083695689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 537217305693925556521837 201456489635222083695689)
                  ·
                    rfl

theorem cell20_441377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 2, 3].length) (baseStart_441377 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_441377 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_441377 prefixEnd_441377 := by exact prefixLift 441377
  have htrace : WordTrace (prefixWord ++ tailWord_441377) baseStart_441377 baseEnd_441377 := by
    simpa [prefixWord, tailWord_441377, baseEnd_441377] using wordTrace_append hprefix tailTrace_441377
  have hstable : (prefixWord ++ tailWord_441377).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441377).length < 2 ^ (prefixWord ++ tailWord_441377).sum := by decide
  have hdescent : baseEnd_441377 < baseStart_441377 := by decide
  rcases family_descends (prefixWord ++ tailWord_441377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441380 : List Nat := [2, 3, 1, 4, 1, 1, 4, 2, 2]
def baseStart_441380 : Nat := 118140960795 + 441380 * 2 ^ 59
def prefixEnd_441380 : Nat := 4983230072969 + 3 ^ 40 * 441380 * 2
def baseEnd_441380 : Nat := 201457858916967406595677

theorem tailTrace_441380 : CollatzResearch.WordTrace tailWord_441380 prefixEnd_441380 201457858916967406595677 := by
  unfold tailWord_441380
  simp only [CollatzResearch.WordTrace]
  refine ⟨8049225570481558273832797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10732300760642077698443729 8049225570481558273832797)
  ·
    refine ⟨3018459588930584352687299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8049225570481558273832797 3018459588930584352687299)
    ·
      refine ⟨4527689383395876529030949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3018459588930584352687299 4527689383395876529030949)
      ·
        refine ⟨848941759386726849193303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4527689383395876529030949 848941759386726849193303)
        ·
          refine ⟨1273412639080090273789955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 848941759386726849193303 1273412639080090273789955)
          ·
            refine ⟨1910118958620135410684933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1273412639080090273789955 1910118958620135410684933)
            ·
              refine ⟨358147304741275389503425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1910118958620135410684933 358147304741275389503425)
              ·
                refine ⟨268610478555956542127569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 358147304741275389503425 268610478555956542127569)
                ·
                  refine ⟨201457858916967406595677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 268610478555956542127569 201457858916967406595677)
                  ·
                    rfl

theorem cell20_441380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 2, 2].length) (baseStart_441380 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_441380 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_441380 prefixEnd_441380 := by exact prefixLift 441380
  have htrace : WordTrace (prefixWord ++ tailWord_441380) baseStart_441380 baseEnd_441380 := by
    simpa [prefixWord, tailWord_441380, baseEnd_441380] using wordTrace_append hprefix tailTrace_441380
  have hstable : (prefixWord ++ tailWord_441380).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441380).length < 2 ^ (prefixWord ++ tailWord_441380).sum := by decide
  have hdescent : baseEnd_441380 < baseStart_441380 := by decide
  rcases family_descends (prefixWord ++ tailWord_441380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441405 : List Nat := [1, 4, 1, 3, 1, 2, 1, 1, 6]
def baseStart_441405 : Nat := 118140960795 + 441405 * 2 ^ 59
def prefixEnd_441405 : Nat := 4983230072969 + 3 ^ 40 * 441405 * 2
def baseEnd_441405 : Nat := 201469269598178430762241

theorem tailTrace_441405 : CollatzResearch.WordTrace tailWord_441405 prefixEnd_441405 201469269598178430762241 := by
  unfold tailWord_441405
  simp only [CollatzResearch.WordTrace]
  refine ⟨16099362965872545817325669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10732908643915030544883779 16099362965872545817325669)
  ·
    refine ⟨3018630556101102340748563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16099362965872545817325669 3018630556101102340748563)
    ·
      refine ⟨4527945834151653511122845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3018630556101102340748563 4527945834151653511122845)
      ·
        refine ⟨1697979687806870066671067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4527945834151653511122845 1697979687806870066671067)
        ·
          refine ⟨2546969531710305100006601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1697979687806870066671067 2546969531710305100006601)
          ·
            refine ⟨1910227148782728825004951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2546969531710305100006601 1910227148782728825004951)
            ·
              refine ⟨2865340723174093237507427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1910227148782728825004951 2865340723174093237507427)
              ·
                refine ⟨4298011084761139856261141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2865340723174093237507427 4298011084761139856261141)
                ·
                  refine ⟨201469269598178430762241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4298011084761139856261141 201469269598178430762241)
                  ·
                    rfl

theorem cell20_441405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_441405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_441405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_441405 prefixEnd_441405 := by exact prefixLift 441405
  have htrace : WordTrace (prefixWord ++ tailWord_441405) baseStart_441405 baseEnd_441405 := by
    simpa [prefixWord, tailWord_441405, baseEnd_441405] using wordTrace_append hprefix tailTrace_441405
  have hstable : (prefixWord ++ tailWord_441405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441405).length < 2 ^ (prefixWord ++ tailWord_441405).sum := by decide
  have hdescent : baseEnd_441405 < baseStart_441405 := by decide
  rcases family_descends (prefixWord ++ tailWord_441405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441436 : List Nat := [2, 2, 4, 1, 1, 1, 3, 1, 5]
def baseStart_441436 : Nat := 118140960795 + 441436 * 2 ^ 59
def prefixEnd_441436 : Nat := 4983230072969 + 3 ^ 40 * 441436 * 2
def baseEnd_441436 : Nat := 201483418842880100728781

theorem tailTrace_441436 : CollatzResearch.WordTrace tailWord_441436 prefixEnd_441436 201483418842880100728781 := by
  unfold tailWord_441436
  simp only [CollatzResearch.WordTrace]
  refine ⟨8050246814380119055852081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10733662419173492074469441 8050246814380119055852081)
  ·
    refine ⟨6037685110785089291889061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8050246814380119055852081 6037685110785089291889061)
    ·
      refine ⟨1132065958272204242229199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6037685110785089291889061 1132065958272204242229199)
      ·
        refine ⟨1698098937408306363343799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1132065958272204242229199 1698098937408306363343799)
        ·
          refine ⟨2547148406112459545015699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1698098937408306363343799 2547148406112459545015699)
          ·
            refine ⟨3820722609168689317523549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2547148406112459545015699 3820722609168689317523549)
            ·
              refine ⟨1432770978438258494071331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3820722609168689317523549 1432770978438258494071331)
              ·
                refine ⟨2149156467657387741106997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1432770978438258494071331 2149156467657387741106997)
                ·
                  refine ⟨201483418842880100728781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2149156467657387741106997 201483418842880100728781)
                  ·
                    rfl

theorem cell20_441436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_441436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_441436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_441436 prefixEnd_441436 := by exact prefixLift 441436
  have htrace : WordTrace (prefixWord ++ tailWord_441436) baseStart_441436 baseEnd_441436 := by
    simpa [prefixWord, tailWord_441436, baseEnd_441436] using wordTrace_append hprefix tailTrace_441436
  have hstable : (prefixWord ++ tailWord_441436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441436).length < 2 ^ (prefixWord ++ tailWord_441436).sum := by decide
  have hdescent : baseEnd_441436 < baseStart_441436 := by decide
  rcases family_descends (prefixWord ++ tailWord_441436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441498 : List Nat := [3, 1, 1, 5, 1, 1, 3, 1, 4]
def baseStart_441498 : Nat := 118140960795 + 441498 * 2 ^ 59
def prefixEnd_441498 : Nat := 4983230072969 + 3 ^ 40 * 441498 * 2
def baseEnd_441498 : Nat := 201511717332283440661861

theorem tailTrace_441498 : CollatzResearch.WordTrace tailWord_441498 prefixEnd_441498 201511717332283440661861 := by
  unfold tailWord_441498
  simp only [CollatzResearch.WordTrace]
  refine ⟨4025688738633905675115287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10735169969690415133640765 4025688738633905675115287)
  ·
    refine ⟨6038533107950858512672931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4025688738633905675115287 6038533107950858512672931)
    ·
      refine ⟨9057799661926287769009397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6038533107950858512672931 9057799661926287769009397)
      ·
        refine ⟨849168718305589478344631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9057799661926287769009397 849168718305589478344631)
        ·
          refine ⟨1273753077458384217516947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 849168718305589478344631 1273753077458384217516947)
          ·
            refine ⟨1910629616187576326275421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1273753077458384217516947 1910629616187576326275421)
            ·
              refine ⟨716486106070341122353283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1910629616187576326275421 716486106070341122353283)
              ·
                refine ⟨1074729159105511683529925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 716486106070341122353283 1074729159105511683529925)
                ·
                  refine ⟨201511717332283440661861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1074729159105511683529925 201511717332283440661861)
                  ·
                    rfl

theorem cell20_441498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_441498 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_441498 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_441498 prefixEnd_441498 := by exact prefixLift 441498
  have htrace : WordTrace (prefixWord ++ tailWord_441498) baseStart_441498 baseEnd_441498 := by
    simpa [prefixWord, tailWord_441498, baseEnd_441498] using wordTrace_append hprefix tailTrace_441498
  have hstable : (prefixWord ++ tailWord_441498).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441498).length < 2 ^ (prefixWord ++ tailWord_441498).sum := by decide
  have hdescent : baseEnd_441498 < baseStart_441498 := by decide
  rcases family_descends (prefixWord ++ tailWord_441498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441508 : List Nat := [2, 3, 1, 2, 3, 3, 2, 1, 3]
def baseStart_441508 : Nat := 118140960795 + 441508 * 2 ^ 59
def prefixEnd_441508 : Nat := 4983230072969 + 3 ^ 40 * 441508 * 2
def baseEnd_441508 : Nat := 201516281604767850328487

theorem tailTrace_441508 : CollatzResearch.WordTrace tailWord_441508 prefixEnd_441508 201516281604767850328487 := by
  unfold tailWord_441508
  simp only [CollatzResearch.WordTrace]
  refine ⟨8051559842249697204162589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10735413122999596272216785 8051559842249697204162589)
  ·
    refine ⟨3019334940843636451560971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8051559842249697204162589 3019334940843636451560971)
    ·
      refine ⟨4529002411265454677341457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3019334940843636451560971 4529002411265454677341457)
      ·
        refine ⟨3396751808449091008006093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4529002411265454677341457 3396751808449091008006093)
        ·
          refine ⟨1273781928168409128002285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3396751808449091008006093 1273781928168409128002285)
          ·
            refine ⟨477668223063153423000857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1273781928168409128002285 477668223063153423000857)
            ·
              refine ⟨358251167297365067250643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 477668223063153423000857 358251167297365067250643)
              ·
                refine ⟨537376750946047600875965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 358251167297365067250643 537376750946047600875965)
                ·
                  refine ⟨201516281604767850328487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 537376750946047600875965 201516281604767850328487)
                  ·
                    rfl

theorem cell20_441508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_441508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_441508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_441508 prefixEnd_441508 := by exact prefixLift 441508
  have htrace : WordTrace (prefixWord ++ tailWord_441508) baseStart_441508 baseEnd_441508 := by
    simpa [prefixWord, tailWord_441508, baseEnd_441508] using wordTrace_append hprefix tailTrace_441508
  have hstable : (prefixWord ++ tailWord_441508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441508).length < 2 ^ (prefixWord ++ tailWord_441508).sum := by decide
  have hdescent : baseEnd_441508 < baseStart_441508 := by decide
  rcases family_descends (prefixWord ++ tailWord_441508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441533 : List Nat := [1, 4, 1, 2, 1, 1, 2, 1, 7]
def baseStart_441533 : Nat := 118140960795 + 441533 * 2 ^ 59
def prefixEnd_441533 : Nat := 4983230072969 + 3 ^ 40 * 441533 * 2
def baseEnd_441533 : Nat := 201527692285978874495051

theorem tailTrace_441533 : CollatzResearch.WordTrace tailWord_441533 prefixEnd_441533 201527692285978874495051 := by
  unfold tailWord_441533
  simp only [CollatzResearch.WordTrace]
  refine ⟨16104031509408823677985253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10736021006272549118656835 16104031509408823677985253)
  ·
    refine ⟨3019505908014154439622235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16104031509408823677985253 3019505908014154439622235)
    ·
      refine ⟨4529258862021231659433353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3019505908014154439622235 4529258862021231659433353)
      ·
        refine ⟨3396944146515923744575015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4529258862021231659433353 3396944146515923744575015)
        ·
          refine ⟨5095416219773885616862523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3396944146515923744575015 5095416219773885616862523)
          ·
            refine ⟨7643124329660828425293785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5095416219773885616862523 7643124329660828425293785)
            ·
              refine ⟨5732343247245621318970339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7643124329660828425293785 5732343247245621318970339)
              ·
                refine ⟨8598514870868431978455509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5732343247245621318970339 8598514870868431978455509)
                ·
                  refine ⟨201527692285978874495051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8598514870868431978455509 201527692285978874495051)
                  ·
                    rfl

theorem cell20_441533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_441533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_441533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_441533 prefixEnd_441533 := by exact prefixLift 441533
  have htrace : WordTrace (prefixWord ++ tailWord_441533) baseStart_441533 baseEnd_441533 := by
    simpa [prefixWord, tailWord_441533, baseEnd_441533] using wordTrace_append hprefix tailTrace_441533
  have hstable : (prefixWord ++ tailWord_441533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441533).length < 2 ^ (prefixWord ++ tailWord_441533).sum := by decide
  have hdescent : baseEnd_441533 < baseStart_441533 := by decide
  rcases family_descends (prefixWord ++ tailWord_441533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441542 : List Nat := [6, 1, 2, 2, 1, 1, 2, 2, 3]
def baseStart_441542 : Nat := 118140960795 + 441542 * 2 ^ 59
def prefixEnd_441542 : Nat := 4983230072969 + 3 ^ 40 * 441542 * 2
def baseEnd_441542 : Nat := 201531800131214843195015

theorem tailTrace_441542 : CollatzResearch.WordTrace tailWord_441542 prefixEnd_441542 201531800131214843195015 := by
  unfold tailWord_441542
  simp only [CollatzResearch.WordTrace]
  refine ⟨503261242699256819220715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10736239844250812143375253 503261242699256819220715)
  ·
    refine ⟨754891864048885228831073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 503261242699256819220715 754891864048885228831073)
    ·
      refine ⟨566168898036663921623305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 754891864048885228831073 566168898036663921623305)
      ·
        refine ⟨424626673527497941217479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 566168898036663921623305 424626673527497941217479)
        ·
          refine ⟨636940010291246911826219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424626673527497941217479 636940010291246911826219)
          ·
            refine ⟨955410015436870367739329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 636940010291246911826219 955410015436870367739329)
            ·
              refine ⟨716557511577652775804497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 955410015436870367739329 716557511577652775804497)
              ·
                refine ⟨537418133683239581853373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 716557511577652775804497 537418133683239581853373)
                ·
                  refine ⟨201531800131214843195015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 537418133683239581853373 201531800131214843195015)
                  ·
                    rfl

theorem cell20_441542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_441542 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_441542 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_441542 prefixEnd_441542 := by exact prefixLift 441542
  have htrace : WordTrace (prefixWord ++ tailWord_441542) baseStart_441542 baseEnd_441542 := by
    simpa [prefixWord, tailWord_441542, baseEnd_441542] using wordTrace_append hprefix tailTrace_441542
  have hstable : (prefixWord ++ tailWord_441542).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441542).length < 2 ^ (prefixWord ++ tailWord_441542).sum := by decide
  have hdescent : baseEnd_441542 < baseStart_441542 := by decide
  rcases family_descends (prefixWord ++ tailWord_441542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441549 : List Nat := [1, 6, 2, 2, 1, 1, 1, 4, 2]
def baseStart_441549 : Nat := 118140960795 + 441549 * 2 ^ 59
def prefixEnd_441549 : Nat := 4983230072969 + 3 ^ 40 * 441549 * 2
def baseEnd_441549 : Nat := 201534995121953929961653

theorem tailTrace_441549 : CollatzResearch.WordTrace tailWord_441549 prefixEnd_441549 201534995121953929961653 := by
  unfold tailWord_441549
  simp only [CollatzResearch.WordTrace]
  refine ⟨16104615077350858410567701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10736410051567238940378467 16104615077350858410567701)
  ·
    refine ⟨754903831750821487995361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16104615077350858410567701 754903831750821487995361)
    ·
      refine ⟨566177873813116115996521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 754903831750821487995361 566177873813116115996521)
      ·
        refine ⟨424633405359837086997391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 566177873813116115996521 424633405359837086997391)
        ·
          refine ⟨636950108039755630496087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424633405359837086997391 636950108039755630496087)
          ·
            refine ⟨955425162059633445744131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 636950108039755630496087 955425162059633445744131)
            ·
              refine ⟨1433137743089450168616197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 955425162059633445744131 1433137743089450168616197)
              ·
                refine ⟨268713326829271906615537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1433137743089450168616197 268713326829271906615537)
                ·
                  refine ⟨201534995121953929961653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 268713326829271906615537 201534995121953929961653)
                  ·
                    rfl

theorem cell20_441549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_441549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_441549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_441549 prefixEnd_441549 := by exact prefixLift 441549
  have htrace : WordTrace (prefixWord ++ tailWord_441549) baseStart_441549 baseEnd_441549 := by
    simpa [prefixWord, tailWord_441549, baseEnd_441549] using wordTrace_append hprefix tailTrace_441549
  have hstable : (prefixWord ++ tailWord_441549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441549).length < 2 ^ (prefixWord ++ tailWord_441549).sum := by decide
  have hdescent : baseEnd_441549 < baseStart_441549 := by decide
  rcases family_descends (prefixWord ++ tailWord_441549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441560 : List Nat := [2, 1, 2, 2, 6, 1, 1, 5]
def baseStart_441560 : Nat := 118140960795 + 441560 * 2 ^ 59
def prefixEnd_441560 : Nat := 4983230072969 + 3 ^ 40 * 441560 * 2
def baseEnd_441560 : Nat := 67180005273895593531647

theorem tailTrace_441560 : CollatzResearch.WordTrace tailWord_441560 prefixEnd_441560 67180005273895593531647 := by
  unfold tailWord_441560
  simp only [CollatzResearch.WordTrace]
  refine ⟨8052508140155503644609067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10736677520207338192812089 8052508140155503644609067)
  ·
    refine ⟨12078762210233255466913601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8052508140155503644609067 12078762210233255466913601)
    ·
      refine ⟨9059071657674941600185201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12078762210233255466913601 9059071657674941600185201)
      ·
        refine ⟨6794303743256206200138901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9059071657674941600185201 6794303743256206200138901)
        ·
          refine ⟨318482987965134665631511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6794303743256206200138901 318482987965134665631511)
          ·
            refine ⟨477724481947701998447267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318482987965134665631511 477724481947701998447267)
            ·
              refine ⟨716586722921552997670901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 477724481947701998447267 716586722921552997670901)
              ·
                refine ⟨67180005273895593531647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 716586722921552997670901 67180005273895593531647)
                ·
                  rfl

theorem cell20_441560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 5].length) (baseStart_441560 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_441560 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_441560 prefixEnd_441560 := by exact prefixLift 441560
  have htrace : WordTrace (prefixWord ++ tailWord_441560) baseStart_441560 baseEnd_441560 := by
    simpa [prefixWord, tailWord_441560, baseEnd_441560] using wordTrace_append hprefix tailTrace_441560
  have hstable : (prefixWord ++ tailWord_441560).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441560).length < 2 ^ (prefixWord ++ tailWord_441560).sum := by decide
  have hdescent : baseEnd_441560 < baseStart_441560 := by decide
  rcases family_descends (prefixWord ++ tailWord_441560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441609 : List Nat := [1, 2, 1, 1, 3, 3, 3, 1, 5]
def baseStart_441609 : Nat := 118140960795 + 441609 * 2 ^ 59
def prefixEnd_441609 : Nat := 4983230072969 + 3 ^ 40 * 441609 * 2
def baseEnd_441609 : Nat := 201562380756860387961407

theorem tailTrace_441609 : CollatzResearch.WordTrace tailWord_441609 prefixEnd_441609 201562380756860387961407 := by
  unfold tailWord_441609
  simp only [CollatzResearch.WordTrace]
  refine ⟨16106803457133488657751881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10737868971422325771834587 16106803457133488657751881)
  ·
    refine ⟨12080102592850116493313911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16106803457133488657751881 12080102592850116493313911)
    ·
      refine ⟨18120153889275174739970867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12080102592850116493313911 18120153889275174739970867)
      ·
        refine ⟨27180230833912762109956301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18120153889275174739970867 27180230833912762109956301)
        ·
          refine ⟨10192586562717285791233613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27180230833912762109956301 10192586562717285791233613)
          ·
            refine ⟨3822219961018982171712605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10192586562717285791233613 3822219961018982171712605)
            ·
              refine ⟨1433332485382118314392227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3822219961018982171712605 1433332485382118314392227)
              ·
                refine ⟨2149998728073177471588341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1433332485382118314392227 2149998728073177471588341)
                ·
                  refine ⟨201562380756860387961407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2149998728073177471588341 201562380756860387961407)
                  ·
                    rfl

theorem cell20_441609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 5].length) (baseStart_441609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_441609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_441609 prefixEnd_441609 := by exact prefixLift 441609
  have htrace : WordTrace (prefixWord ++ tailWord_441609) baseStart_441609 baseEnd_441609 := by
    simpa [prefixWord, tailWord_441609, baseEnd_441609] using wordTrace_append hprefix tailTrace_441609
  have hstable : (prefixWord ++ tailWord_441609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441609).length < 2 ^ (prefixWord ++ tailWord_441609).sum := by decide
  have hdescent : baseEnd_441609 < baseStart_441609 := by decide
  rcases family_descends (prefixWord ++ tailWord_441609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441612 : List Nat := [2, 2, 1, 2, 2, 3, 2, 4, 2]
def baseStart_441612 : Nat := 118140960795 + 441612 * 2 ^ 59
def prefixEnd_441612 : Nat := 4983230072969 + 3 ^ 40 * 441612 * 2
def baseEnd_441612 : Nat := 201563750038605710861395

theorem tailTrace_441612 : CollatzResearch.WordTrace tailWord_441612 prefixEnd_441612 201563750038605710861395 := by
  unfold tailWord_441612
  simp only [CollatzResearch.WordTrace]
  refine ⟨8053456438061310085055545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10737941917415080113407393 8053456438061310085055545)
  ·
    refine ⟨6040092328545982563791659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8053456438061310085055545 6040092328545982563791659)
    ·
      refine ⟨9060138492818973845687489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6040092328545982563791659 9060138492818973845687489)
      ·
        refine ⟨6795103869614230384265617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9060138492818973845687489 6795103869614230384265617)
        ·
          refine ⟨5096327902210672788199213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6795103869614230384265617 5096327902210672788199213)
          ·
            refine ⟨1911122963329002295574705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5096327902210672788199213 1911122963329002295574705)
            ·
              refine ⟨1433342222496751721681029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1911122963329002295574705 1433342222496751721681029)
              ·
                refine ⟨268751666718140947815193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1433342222496751721681029 268751666718140947815193)
                ·
                  refine ⟨201563750038605710861395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 268751666718140947815193 201563750038605710861395)
                  ·
                    rfl

theorem cell20_441612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 4, 2].length) (baseStart_441612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_441612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_441612 prefixEnd_441612 := by exact prefixLift 441612
  have htrace : WordTrace (prefixWord ++ tailWord_441612) baseStart_441612 baseEnd_441612 := by
    simpa [prefixWord, tailWord_441612, baseEnd_441612] using wordTrace_append hprefix tailTrace_441612
  have hstable : (prefixWord ++ tailWord_441612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441612).length < 2 ^ (prefixWord ++ tailWord_441612).sum := by decide
  have hdescent : baseEnd_441612 < baseStart_441612 := by decide
  rcases family_descends (prefixWord ++ tailWord_441612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441657 : List Nat := [1, 2, 1, 6, 2, 2, 6]
def baseStart_441657 : Nat := 118140960795 + 441657 * 2 ^ 59
def prefixEnd_441657 : Nat := 4983230072969 + 3 ^ 40 * 441657 * 2
def baseEnd_441657 : Nat := 22398254362753950484579

theorem tailTrace_441657 : CollatzResearch.WordTrace tailWord_441657 prefixEnd_441657 22398254362753950484579 := by
  unfold tailWord_441657
  simp only [CollatzResearch.WordTrace]
  refine ⟨16108554160959592855499225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10739036107306395236999483 16108554160959592855499225)
  ·
    refine ⟨12081415620719694641624419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16108554160959592855499225 12081415620719694641624419)
    ·
      refine ⟨18122123431079541962436629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12081415620719694641624419 18122123431079541962436629)
      ·
        refine ⟨849474535831853529489217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18122123431079541962436629 849474535831853529489217)
        ·
          refine ⟨637105901873890147116913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 849474535831853529489217 637105901873890147116913)
          ·
            refine ⟨477829426405417610337685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 637105901873890147116913 477829426405417610337685)
            ·
              refine ⟨22398254362753950484579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 477829426405417610337685 22398254362753950484579)
              ·
                rfl

theorem cell20_441657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 6].length) (baseStart_441657 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_441657 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_441657 prefixEnd_441657 := by exact prefixLift 441657
  have htrace : WordTrace (prefixWord ++ tailWord_441657) baseStart_441657 baseEnd_441657 := by
    simpa [prefixWord, tailWord_441657, baseEnd_441657] using wordTrace_append hprefix tailTrace_441657
  have hstable : (prefixWord ++ tailWord_441657).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441657).length < 2 ^ (prefixWord ++ tailWord_441657).sum := by decide
  have hdescent : baseEnd_441657 < baseStart_441657 := by decide
  rcases family_descends (prefixWord ++ tailWord_441657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441671 : List Nat := [1, 1, 4, 1, 2, 3, 3, 1, 4]
def baseStart_441671 : Nat := 118140960795 + 441671 * 2 ^ 59
def prefixEnd_441671 : Nat := 4983230072969 + 3 ^ 40 * 441671 * 2
def baseEnd_441671 : Nat := 201590679246263727894487

theorem tailTrace_441671 : CollatzResearch.WordTrace tailWord_441671 prefixEnd_441671 201590679246263727894487 := by
  unfold tailWord_441671
  simp only [CollatzResearch.WordTrace]
  refine ⟨16109064782908873246508867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10739376521939248831005911 16109064782908873246508867)
  ·
    refine ⟨24163597174363309869763301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16109064782908873246508867 24163597174363309869763301)
    ·
      refine ⟨4530674470193120600580619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24163597174363309869763301 4530674470193120600580619)
      ·
        refine ⟨6796011705289680900870929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4530674470193120600580619 6796011705289680900870929)
        ·
          refine ⟨5097008778967260675653197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6796011705289680900870929 5097008778967260675653197)
          ·
            refine ⟨1911378292112722753369949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5097008778967260675653197 1911378292112722753369949)
            ·
              refine ⟨716766859542271032513731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1911378292112722753369949 716766859542271032513731)
              ·
                refine ⟨1075150289313406548770597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 716766859542271032513731 1075150289313406548770597)
                ·
                  refine ⟨201590679246263727894487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1075150289313406548770597 201590679246263727894487)
                  ·
                    rfl

theorem cell20_441671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 4].length) (baseStart_441671 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_441671 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_441671 prefixEnd_441671 := by exact prefixLift 441671
  have htrace : WordTrace (prefixWord ++ tailWord_441671) baseStart_441671 baseEnd_441671 := by
    simpa [prefixWord, tailWord_441671, baseEnd_441671] using wordTrace_append hprefix tailTrace_441671
  have hstable : (prefixWord ++ tailWord_441671).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441671).length < 2 ^ (prefixWord ++ tailWord_441671).sum := by decide
  have hdescent : baseEnd_441671 < baseStart_441671 := by decide
  rcases family_descends (prefixWord ++ tailWord_441671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441678 : List Nat := [4, 1, 1, 1, 1, 1, 6, 5]
def baseStart_441678 : Nat := 118140960795 + 441678 * 2 ^ 59
def prefixEnd_441678 : Nat := 4983230072969 + 3 ^ 40 * 441678 * 2
def baseEnd_441678 : Nat := 67197958079000938220375

theorem tailTrace_441678 : CollatzResearch.WordTrace tailWord_441678 prefixEnd_441678 67197958079000938220375 := by
  unfold tailWord_441678
  simp only [CollatzResearch.WordTrace]
  refine ⟨2013665011735439180251711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10739546729255675628009125 2013665011735439180251711)
  ·
    refine ⟨3020497517603158770377567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2013665011735439180251711 3020497517603158770377567)
    ·
      refine ⟨4530746276404738155566351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3020497517603158770377567 4530746276404738155566351)
      ·
        refine ⟨6796119414607107233349527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4530746276404738155566351 6796119414607107233349527)
        ·
          refine ⟨10194179121910660850024291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6796119414607107233349527 10194179121910660850024291)
          ·
            refine ⟨15291268682865991275036437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10194179121910660850024291 15291268682865991275036437)
            ·
              refine ⟨716778219509343341017333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15291268682865991275036437 716778219509343341017333)
              ·
                refine ⟨67197958079000938220375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 716778219509343341017333 67197958079000938220375)
                ·
                  rfl

theorem cell20_441678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_441678 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_441678 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_441678 prefixEnd_441678 := by exact prefixLift 441678
  have htrace : WordTrace (prefixWord ++ tailWord_441678) baseStart_441678 baseEnd_441678 := by
    simpa [prefixWord, tailWord_441678, baseEnd_441678] using wordTrace_append hprefix tailTrace_441678
  have hstable : (prefixWord ++ tailWord_441678).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441678).length < 2 ^ (prefixWord ++ tailWord_441678).sum := by decide
  have hdescent : baseEnd_441678 < baseStart_441678 := by decide
  rcases family_descends (prefixWord ++ tailWord_441678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441889 : List Nat := [1, 2, 3, 2, 2, 10]
def baseStart_441889 : Nat := 118140960795 + 441889 * 2 ^ 59
def prefixEnd_441889 : Nat := 4983230072969 + 3 ^ 40 * 441889 * 2
def baseEnd_441889 : Nat := 7470006680978661430627

theorem tailTrace_441889 : CollatzResearch.WordTrace tailWord_441889 prefixEnd_441889 7470006680978661430627 := by
  unfold tailWord_441889
  simp only [CollatzResearch.WordTrace]
  refine ⟨16117015896119096477944721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10744677264079397651963147 16117015896119096477944721)
  ·
    refine ⟨12087761922089322358458541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16117015896119096477944721 12087761922089322358458541)
    ·
      refine ⟨4532910720783495884421953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12087761922089322358458541 4532910720783495884421953)
      ·
        refine ⟨3399683040587621913316465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4532910720783495884421953 3399683040587621913316465)
        ·
          refine ⟨2549762280440716434987349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3399683040587621913316465 2549762280440716434987349)
          ·
            refine ⟨7470006680978661430627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2549762280440716434987349 7470006680978661430627)
            ·
              rfl

theorem cell20_441889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 10].length) (baseStart_441889 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_441889 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_441889 prefixEnd_441889 := by exact prefixLift 441889
  have htrace : WordTrace (prefixWord ++ tailWord_441889) baseStart_441889 baseEnd_441889 := by
    simpa [prefixWord, tailWord_441889, baseEnd_441889] using wordTrace_append hprefix tailTrace_441889
  have hstable : (prefixWord ++ tailWord_441889).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441889).length < 2 ^ (prefixWord ++ tailWord_441889).sum := by decide
  have hdescent : baseEnd_441889 < baseStart_441889 := by decide
  rcases family_descends (prefixWord ++ tailWord_441889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441988 : List Nat := [2, 3, 2, 1, 5, 1, 1, 3, 2]
def baseStart_441988 : Nat := 118140960795 + 441988 * 2 ^ 59
def prefixEnd_441988 : Nat := 4983230072969 + 3 ^ 40 * 441988 * 2
def baseEnd_441988 : Nat := 201735366684019514326525

theorem tailTrace_441988 : CollatzResearch.WordTrace tailWord_441988 prefixEnd_441988 201735366684019514326525 := by
  unfold tailWord_441988
  simp only [CollatzResearch.WordTrace]
  refine ⟨8060313361380218192899309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10747084481840290923865745 8060313361380218192899309)
  ·
    refine ⟨3022617510517581822337241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8060313361380218192899309 3022617510517581822337241)
    ·
      refine ⟨2266963132888186366752931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3022617510517581822337241 2266963132888186366752931)
      ·
        refine ⟨3400444699332279550129397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2266963132888186366752931 3400444699332279550129397)
        ·
          refine ⟨318791690562401207824631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3400444699332279550129397 318791690562401207824631)
          ·
            refine ⟨478187535843601811736947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318791690562401207824631 478187535843601811736947)
            ·
              refine ⟨717281303765402717605421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 478187535843601811736947 717281303765402717605421)
              ·
                refine ⟨268980488912026019102033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 717281303765402717605421 268980488912026019102033)
                ·
                  refine ⟨201735366684019514326525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 268980488912026019102033 201735366684019514326525)
                  ·
                    rfl

theorem cell20_441988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 3, 2].length) (baseStart_441988 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_441988 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_441988 prefixEnd_441988 := by exact prefixLift 441988
  have htrace : WordTrace (prefixWord ++ tailWord_441988) baseStart_441988 baseEnd_441988 := by
    simpa [prefixWord, tailWord_441988, baseEnd_441988] using wordTrace_append hprefix tailTrace_441988
  have hstable : (prefixWord ++ tailWord_441988).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441988).length < 2 ^ (prefixWord ++ tailWord_441988).sum := by decide
  have hdescent : baseEnd_441988 < baseStart_441988 := by decide
  rcases family_descends (prefixWord ++ tailWord_441988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442020 : List Nat := [2, 3, 1, 2, 2, 3, 2, 5]
def baseStart_442020 : Nat := 118140960795 + 442020 * 2 ^ 59
def prefixEnd_442020 : Nat := 4983230072969 + 3 ^ 40 * 442020 * 2
def baseEnd_442020 : Nat := 67249990785323208419909

theorem tailTrace_442020 : CollatzResearch.WordTrace tailWord_442020 prefixEnd_442020 67249990785323208419909 := by
  unfold tailWord_442020
  simp only [CollatzResearch.WordTrace]
  refine ⟨8060896929322252925481757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10747862572429670567309009 8060896929322252925481757)
  ·
    refine ⟨3022836348495844847055659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8060896929322252925481757 3022836348495844847055659)
    ·
      refine ⟨4534254522743767270583489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3022836348495844847055659 4534254522743767270583489)
      ·
        refine ⟨3400690892057825452937617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4534254522743767270583489 3400690892057825452937617)
        ·
          refine ⟨2550518169043369089703213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3400690892057825452937617 2550518169043369089703213)
          ·
            refine ⟨956444313391263408638705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2550518169043369089703213 956444313391263408638705)
            ·
              refine ⟨717333235043447556479029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 956444313391263408638705 717333235043447556479029)
              ·
                refine ⟨67249990785323208419909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 717333235043447556479029 67249990785323208419909)
                ·
                  rfl

theorem cell20_442020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 5].length) (baseStart_442020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_442020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_442020 prefixEnd_442020 := by exact prefixLift 442020
  have htrace : WordTrace (prefixWord ++ tailWord_442020) baseStart_442020 baseEnd_442020 := by
    simpa [prefixWord, tailWord_442020, baseEnd_442020] using wordTrace_append hprefix tailTrace_442020
  have hstable : (prefixWord ++ tailWord_442020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442020).length < 2 ^ (prefixWord ++ tailWord_442020).sum := by decide
  have hdescent : baseEnd_442020 < baseStart_442020 := by decide
  rcases family_descends (prefixWord ++ tailWord_442020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442034 : List Nat := [3, 2, 1, 1, 1, 2, 2, 4, 4]
def baseStart_442034 : Nat := 118140960795 + 442034 * 2 ^ 59
def prefixEnd_442034 : Nat := 4983230072969 + 3 ^ 40 * 442034 * 2
def baseEnd_442034 : Nat := 201756362337447798793003

theorem tailTrace_442034 : CollatzResearch.WordTrace tailWord_442034 prefixEnd_442034 201756362337447798793003 := by
  unfold tailWord_442034
  simp only [CollatzResearch.WordTrace]
  refine ⟨4030576120148446560493289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10748202987062524161315437 4030576120148446560493289)
  ·
    refine ⟨3022932090111334920369967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4030576120148446560493289 3022932090111334920369967)
    ·
      refine ⟨4534398135167002380554951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3022932090111334920369967 4534398135167002380554951)
      ·
        refine ⟨6801597202750503570832427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4534398135167002380554951 6801597202750503570832427)
        ·
          refine ⟨10202395804125755356248641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6801597202750503570832427 10202395804125755356248641)
          ·
            refine ⟨7651796853094316517186481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10202395804125755356248641 7651796853094316517186481)
            ·
              refine ⟨5738847639820737387889861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7651796853094316517186481 5738847639820737387889861)
              ·
                refine ⟨1076033932466388260229349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5738847639820737387889861 1076033932466388260229349)
                ·
                  refine ⟨201756362337447798793003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1076033932466388260229349 201756362337447798793003)
                  ·
                    rfl

theorem cell20_442034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_442034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_442034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_442034 prefixEnd_442034 := by exact prefixLift 442034
  have htrace : WordTrace (prefixWord ++ tailWord_442034) baseStart_442034 baseEnd_442034 := by
    simpa [prefixWord, tailWord_442034, baseEnd_442034] using wordTrace_append hprefix tailTrace_442034
  have hstable : (prefixWord ++ tailWord_442034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442034).length < 2 ^ (prefixWord ++ tailWord_442034).sum := by decide
  have hdescent : baseEnd_442034 < baseStart_442034 := by decide
  rcases family_descends (prefixWord ++ tailWord_442034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442041 : List Nat := [1, 2, 1, 4, 1, 1, 4, 6]
def baseStart_442041 : Nat := 118140960795 + 442041 * 2 ^ 59
def prefixEnd_442041 : Nat := 4983230072969 + 3 ^ 40 * 442041 * 2
def baseEnd_442041 : Nat := 67253185776062295186547

theorem tailTrace_442041 : CollatzResearch.WordTrace tailWord_442041 prefixEnd_442041 67253185776062295186547 := by
  unfold tailWord_442041
  simp only [CollatzResearch.WordTrace]
  refine ⟨16122559791568426437477977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10748373194378950958318651 16122559791568426437477977)
  ·
    refine ⟨12091919843676319828108483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16122559791568426437477977 12091919843676319828108483)
    ·
      refine ⟨18137879765514479742162725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12091919843676319828108483 18137879765514479742162725)
      ·
        refine ⟨3400852456033964951655511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18137879765514479742162725 3400852456033964951655511)
        ·
          refine ⟨5101278684050947427483267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3400852456033964951655511 5101278684050947427483267)
          ·
            refine ⟨7651918026076421141224901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5101278684050947427483267 7651918026076421141224901)
            ·
              refine ⟨1434734629889328963979669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7651918026076421141224901 1434734629889328963979669)
              ·
                refine ⟨67253185776062295186547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1434734629889328963979669 67253185776062295186547)
                ·
                  rfl

theorem cell20_442041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 6].length) (baseStart_442041 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_442041 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_442041 prefixEnd_442041 := by exact prefixLift 442041
  have htrace : WordTrace (prefixWord ++ tailWord_442041) baseStart_442041 baseEnd_442041 := by
    simpa [prefixWord, tailWord_442041, baseEnd_442041] using wordTrace_append hprefix tailTrace_442041
  have hstable : (prefixWord ++ tailWord_442041).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442041).length < 2 ^ (prefixWord ++ tailWord_442041).sum := by decide
  have hdescent : baseEnd_442041 < baseStart_442041 := by decide
  rcases family_descends (prefixWord ++ tailWord_442041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442058 : List Nat := [3, 1, 2, 1, 6, 7]
def baseStart_442058 : Nat := 118140960795 + 442058 * 2 ^ 59
def prefixEnd_442058 : Nat := 4983230072969 + 3 ^ 40 * 442058 * 2
def baseEnd_442058 : Nat := 7472863577459643777515

theorem tailTrace_442058 : CollatzResearch.WordTrace tailWord_442058 prefixEnd_442058 7472863577459643777515 := by
  unfold tailWord_442058
  simp only [CollatzResearch.WordTrace]
  refine ⟨4030794958126709585211707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10748786555004558893897885 4030794958126709585211707)
  ·
    refine ⟨6046192437190064377817561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4030794958126709585211707 6046192437190064377817561)
    ·
      refine ⟨4534644327892548283363171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6046192437190064377817561 4534644327892548283363171)
      ·
        refine ⟨6801966491838822425044757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4534644327892548283363171 6801966491838822425044757)
        ·
          refine ⟨318842179304944801173973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6801966491838822425044757 318842179304944801173973)
          ·
            refine ⟨7472863577459643777515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 318842179304944801173973 7472863577459643777515)
            ·
              rfl

theorem cell20_442058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 7].length) (baseStart_442058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_442058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_442058 prefixEnd_442058 := by exact prefixLift 442058
  have htrace : WordTrace (prefixWord ++ tailWord_442058) baseStart_442058 baseEnd_442058 := by
    simpa [prefixWord, tailWord_442058, baseEnd_442058] using wordTrace_append hprefix tailTrace_442058
  have hstable : (prefixWord ++ tailWord_442058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442058).length < 2 ^ (prefixWord ++ tailWord_442058).sum := by decide
  have hdescent : baseEnd_442058 < baseStart_442058 := by decide
  rcases family_descends (prefixWord ++ tailWord_442058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442061 : List Nat := [1, 6, 2, 1, 1, 1, 1, 4, 3]
def baseStart_442061 : Nat := 118140960795 + 442061 * 2 ^ 59
def prefixEnd_442061 : Nat := 4983230072969 + 3 ^ 40 * 442061 * 2
def baseEnd_442061 : Nat := 201768685873155704892893

theorem tailTrace_442061 : CollatzResearch.WordTrace tailWord_442061 prefixEnd_442061 201768685873155704892893 := by
  unfold tailWord_442061
  simp only [CollatzResearch.WordTrace]
  refine ⟨16123289251495969853206037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10748859500997313235470691 16123289251495969853206037)
  ·
    refine ⟨755779183663873586869033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16123289251495969853206037 755779183663873586869033)
    ·
      refine ⟨566834387747905190151775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 755779183663873586869033 566834387747905190151775)
      ·
        refine ⟨850251581621857785227663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 566834387747905190151775 850251581621857785227663)
        ·
          refine ⟨1275377372432786677841495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 850251581621857785227663 1275377372432786677841495)
          ·
            refine ⟨1913066058649180016762243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1275377372432786677841495 1913066058649180016762243)
            ·
              refine ⟨2869599087973770025143365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1913066058649180016762243 2869599087973770025143365)
              ·
                refine ⟨538049828995081879714381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2869599087973770025143365 538049828995081879714381)
                ·
                  refine ⟨201768685873155704892893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 538049828995081879714381 201768685873155704892893)
                  ·
                    rfl

theorem cell20_442061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_442061 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_442061 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_442061 prefixEnd_442061 := by exact prefixLift 442061
  have htrace : WordTrace (prefixWord ++ tailWord_442061) baseStart_442061 baseEnd_442061 := by
    simpa [prefixWord, tailWord_442061, baseEnd_442061] using wordTrace_append hprefix tailTrace_442061
  have hstable : (prefixWord ++ tailWord_442061).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442061).length < 2 ^ (prefixWord ++ tailWord_442061).sum := by decide
  have hdescent : baseEnd_442061 < baseStart_442061 := by decide
  rcases family_descends (prefixWord ++ tailWord_442061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442065 : List Nat := [1, 2, 2, 1, 2, 4, 1, 4, 3]
def baseStart_442065 : Nat := 118140960795 + 442065 * 2 ^ 59
def prefixEnd_442065 : Nat := 4983230072969 + 3 ^ 40 * 442065 * 2
def baseEnd_442065 : Nat := 201770511582149468759543

theorem tailTrace_442065 : CollatzResearch.WordTrace tailWord_442065 prefixEnd_442065 201770511582149468759543 := by
  unfold tailWord_442065
  simp only [CollatzResearch.WordTrace]
  refine ⟨16123435143481478536351649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10748956762320985690901099 16123435143481478536351649)
  ·
    refine ⟨12092576357611108902263737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16123435143481478536351649 12092576357611108902263737)
    ·
      refine ⟨9069432268208331676697803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12092576357611108902263737 9069432268208331676697803)
      ·
        refine ⟨13604148402312497515046705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9069432268208331676697803 13604148402312497515046705)
        ·
          refine ⟨10203111301734373136285029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13604148402312497515046705 10203111301734373136285029)
          ·
            refine ⟨1913083369075194963053443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10203111301734373136285029 1913083369075194963053443)
            ·
              refine ⟨2869625053612792444580165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1913083369075194963053443 2869625053612792444580165)
              ·
                refine ⟨538054697552398583358781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2869625053612792444580165 538054697552398583358781)
                ·
                  refine ⟨201770511582149468759543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 538054697552398583358781 201770511582149468759543)
                  ·
                    rfl

theorem cell20_442065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 4, 3].length) (baseStart_442065 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_442065 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_442065 prefixEnd_442065 := by exact prefixLift 442065
  have htrace : WordTrace (prefixWord ++ tailWord_442065) baseStart_442065 baseEnd_442065 := by
    simpa [prefixWord, tailWord_442065, baseEnd_442065] using wordTrace_append hprefix tailTrace_442065
  have hstable : (prefixWord ++ tailWord_442065).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442065).length < 2 ^ (prefixWord ++ tailWord_442065).sum := by decide
  have hdescent : baseEnd_442065 < baseStart_442065 := by decide
  rcases family_descends (prefixWord ++ tailWord_442065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442072 : List Nat := [2, 1, 2, 2, 3, 1, 2, 3, 4]
def baseStart_442072 : Nat := 118140960795 + 442072 * 2 ^ 59
def prefixEnd_442072 : Nat := 4983230072969 + 3 ^ 40 * 442072 * 2
def baseEnd_442072 : Nat := 201773706572888555526181

theorem tailTrace_442072 : CollatzResearch.WordTrace tailWord_442072 prefixEnd_442072 201773706572888555526181 := by
  unfold tailWord_442072
  simp only [CollatzResearch.WordTrace]
  refine ⟨8061845227228059365928235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10749126969637412487904313 8061845227228059365928235)
  ·
    refine ⟨12092767840842089048892353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8061845227228059365928235 12092767840842089048892353)
    ·
      refine ⟨9069575880631566786669265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12092767840842089048892353 9069575880631566786669265)
      ·
        refine ⟨6802181910473675090001949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9069575880631566786669265 6802181910473675090001949)
        ·
          refine ⟨2550818216427628158750731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6802181910473675090001949 2550818216427628158750731)
          ·
            refine ⟨3826227324641442238126097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2550818216427628158750731 3826227324641442238126097)
            ·
              refine ⟨2869670493481081678594573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3826227324641442238126097 2869670493481081678594573)
              ·
                refine ⟨1076126435055405629472965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2869670493481081678594573 1076126435055405629472965)
                ·
                  refine ⟨201773706572888555526181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1076126435055405629472965 201773706572888555526181)
                  ·
                    rfl

theorem cell20_442072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 4].length) (baseStart_442072 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_442072 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_442072 prefixEnd_442072 := by exact prefixLift 442072
  have htrace : WordTrace (prefixWord ++ tailWord_442072) baseStart_442072 baseEnd_442072 := by
    simpa [prefixWord, tailWord_442072, baseEnd_442072] using wordTrace_append hprefix tailTrace_442072
  have hstable : (prefixWord ++ tailWord_442072).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442072).length < 2 ^ (prefixWord ++ tailWord_442072).sum := by decide
  have hdescent : baseEnd_442072 < baseStart_442072 := by decide
  rcases family_descends (prefixWord ++ tailWord_442072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442189 : List Nat := [1, 6, 1, 2, 1, 2, 2, 5]
def baseStart_442189 : Nat := 118140960795 + 442189 * 2 ^ 59
def prefixEnd_442189 : Nat := 4983230072969 + 3 ^ 40 * 442189 * 2
def baseEnd_442189 : Nat := 67275702853652049541901

theorem tailTrace_442189 : CollatzResearch.WordTrace tailWord_442189 prefixEnd_442189 67275702853652049541901 := by
  unfold tailWord_442189
  simp only [CollatzResearch.WordTrace]
  refine ⟨16127957795032247713865621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10751971863354831809243747 16127957795032247713865621)
  ·
    refine ⟨755998021642136611587451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16127957795032247713865621 755998021642136611587451)
    ·
      refine ⟨1133997032463204917381177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 755998021642136611587451 1133997032463204917381177)
      ·
        refine ⟨850497774347403688035883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1133997032463204917381177 850497774347403688035883)
        ·
          refine ⟨1275746661521105532053825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 850497774347403688035883 1275746661521105532053825)
          ·
            refine ⟨956809996140829149040369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1275746661521105532053825 956809996140829149040369)
            ·
              refine ⟨717607497105621861780277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 956809996140829149040369 717607497105621861780277)
              ·
                refine ⟨67275702853652049541901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 717607497105621861780277 67275702853652049541901)
                ·
                  rfl

theorem cell20_442189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 5].length) (baseStart_442189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_442189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_442189 prefixEnd_442189 := by exact prefixLift 442189
  have htrace : WordTrace (prefixWord ++ tailWord_442189) baseStart_442189 baseEnd_442189 := by
    simpa [prefixWord, tailWord_442189, baseEnd_442189] using wordTrace_append hprefix tailTrace_442189
  have hstable : (prefixWord ++ tailWord_442189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442189).length < 2 ^ (prefixWord ++ tailWord_442189).sum := by decide
  have hdescent : baseEnd_442189 < baseStart_442189 := by decide
  rcases family_descends (prefixWord ++ tailWord_442189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442193 : List Nat := [1, 2, 2, 1, 5, 1, 1, 7]
def baseStart_442193 : Nat := 118140960795 + 442193 * 2 ^ 59
def prefixEnd_442193 : Nat := 4983230072969 + 3 ^ 40 * 442193 * 2
def baseEnd_442193 : Nat := 67276311423316637497451

theorem tailTrace_442193 : CollatzResearch.WordTrace tailWord_442193 prefixEnd_442193 67276311423316637497451 := by
  unfold tailWord_442193
  simp only [CollatzResearch.WordTrace]
  refine ⟨16128103687017756397011233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10752069124678504264674155 16128103687017756397011233)
  ·
    refine ⟨12096077765263317297758425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16128103687017756397011233 12096077765263317297758425)
    ·
      refine ⟨9072058323947487973318819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12096077765263317297758425 9072058323947487973318819)
      ·
        refine ⟨13608087485921231959978229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9072058323947487973318819 13608087485921231959978229)
        ·
          refine ⟨1275758201805115496247959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13608087485921231959978229 1275758201805115496247959)
          ·
            refine ⟨1913637302707673244371939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1275758201805115496247959 1913637302707673244371939)
            ·
              refine ⟨2870455954061509866557909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1913637302707673244371939 2870455954061509866557909)
              ·
                refine ⟨67276311423316637497451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2870455954061509866557909 67276311423316637497451)
                ·
                  rfl

theorem cell20_442193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 7].length) (baseStart_442193 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_442193 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_442193 prefixEnd_442193 := by exact prefixLift 442193
  have htrace : WordTrace (prefixWord ++ tailWord_442193) baseStart_442193 baseEnd_442193 := by
    simpa [prefixWord, tailWord_442193, baseEnd_442193] using wordTrace_append hprefix tailTrace_442193
  have hstable : (prefixWord ++ tailWord_442193).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442193).length < 2 ^ (prefixWord ++ tailWord_442193).sum := by decide
  have hdescent : baseEnd_442193 < baseStart_442193 := by decide
  rcases family_descends (prefixWord ++ tailWord_442193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442196 : List Nat := [2, 4, 1, 1, 3, 2, 1, 3, 3]
def baseStart_442196 : Nat := 118140960795 + 442196 * 2 ^ 59
def prefixEnd_442196 : Nat := 4983230072969 + 3 ^ 40 * 442196 * 2
def baseEnd_442196 : Nat := 201830303551695235392341

theorem tailTrace_442196 : CollatzResearch.WordTrace tailWord_442196 prefixEnd_442196 201830303551695235392341 := by
  unfold tailWord_442196
  simp only [CollatzResearch.WordTrace]
  refine ⟨8064106553003443954685221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10752142070671258606246961 8064106553003443954685221)
  ·
    refine ⟨1512019978688145741503479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8064106553003443954685221 1512019978688145741503479)
    ·
      refine ⟨2268029968032218612255219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1512019978688145741503479 2268029968032218612255219)
      ·
        refine ⟨3402044952048327918382829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2268029968032218612255219 3402044952048327918382829)
        ·
          refine ⟨1275766857018122969393561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3402044952048327918382829 1275766857018122969393561)
          ·
            refine ⟨956825142763592227045171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1275766857018122969393561 956825142763592227045171)
            ·
              refine ⟨1435237714145388340567757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 956825142763592227045171 1435237714145388340567757)
              ·
                refine ⟨538214142804520627712909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1435237714145388340567757 538214142804520627712909)
                ·
                  refine ⟨201830303551695235392341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 538214142804520627712909 201830303551695235392341)
                  ·
                    rfl

theorem cell20_442196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_442196 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_442196 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_442196 prefixEnd_442196 := by exact prefixLift 442196
  have htrace : WordTrace (prefixWord ++ tailWord_442196) baseStart_442196 baseEnd_442196 := by
    simpa [prefixWord, tailWord_442196, baseEnd_442196] using wordTrace_append hprefix tailTrace_442196
  have hstable : (prefixWord ++ tailWord_442196).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442196).length < 2 ^ (prefixWord ++ tailWord_442196).sum := by decide
  have hdescent : baseEnd_442196 < baseStart_442196 := by decide
  rcases family_descends (prefixWord ++ tailWord_442196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442210 : List Nat := [3, 3, 2, 1, 2, 1, 2, 6]
def baseStart_442210 : Nat := 118140960795 + 442210 * 2 ^ 59
def prefixEnd_442210 : Nat := 4983230072969 + 3 ^ 40 * 442210 * 2
def baseEnd_442210 : Nat := 67278897844391136308539

theorem tailTrace_442210 : CollatzResearch.WordTrace tailWord_442210 prefixEnd_442210 67278897844391136308539 := by
  unfold tailWord_442210
  simp only [CollatzResearch.WordTrace]
  refine ⟨4032180931989042075095021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10752482485304112200253389 4032180931989042075095021)
  ·
    refine ⟨1512067849495890778160633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4032180931989042075095021 1512067849495890778160633)
    ·
      refine ⟨1134050887121918083620475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1512067849495890778160633 1134050887121918083620475)
      ·
        refine ⟨1701076330682877125430713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1134050887121918083620475 1701076330682877125430713)
        ·
          refine ⟨1275807248012157844073035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1701076330682877125430713 1275807248012157844073035)
          ·
            refine ⟨1913710872018236766109553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1275807248012157844073035 1913710872018236766109553)
            ·
              refine ⟨1435283154013677574582165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1913710872018236766109553 1435283154013677574582165)
              ·
                refine ⟨67278897844391136308539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1435283154013677574582165 67278897844391136308539)
                ·
                  rfl

theorem cell20_442210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 6].length) (baseStart_442210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_442210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_442210 prefixEnd_442210 := by exact prefixLift 442210
  have htrace : WordTrace (prefixWord ++ tailWord_442210) baseStart_442210 baseEnd_442210 := by
    simpa [prefixWord, tailWord_442210, baseEnd_442210] using wordTrace_append hprefix tailTrace_442210
  have hstable : (prefixWord ++ tailWord_442210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442210).length < 2 ^ (prefixWord ++ tailWord_442210).sum := by decide
  have hdescent : baseEnd_442210 < baseStart_442210 := by decide
  rcases family_descends (prefixWord ++ tailWord_442210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442293 : List Nat := [1, 3, 3, 2, 1, 3, 1, 1, 5]
def baseStart_442293 : Nat := 118140960795 + 442293 * 2 ^ 59
def prefixEnd_442293 : Nat := 4983230072969 + 3 ^ 40 * 442293 * 2
def baseEnd_442293 : Nat := 201874576994794009158611

theorem tailTrace_442293 : CollatzResearch.WordTrace tailWord_442293 prefixEnd_442293 201874576994794009158611 := by
  unfold tailWord_442293
  simp only [CollatzResearch.WordTrace]
  refine ⟨16131750986655473475651533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10754500657770315650434355 16131750986655473475651533)
  ·
    refine ⟨6049406619995802553369325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16131750986655473475651533 6049406619995802553369325)
    ·
      refine ⟨2268527482498425957513497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6049406619995802553369325 2268527482498425957513497)
      ·
        refine ⟨1701395611873819468135123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2268527482498425957513497 1701395611873819468135123)
        ·
          refine ⟨2552093417810729202202685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1701395611873819468135123 2552093417810729202202685)
          ·
            refine ⟨957035031679023450826007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2552093417810729202202685 957035031679023450826007)
            ·
              refine ⟨1435552547518535176239011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 957035031679023450826007 1435552547518535176239011)
              ·
                refine ⟨2153328821277802764358517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1435552547518535176239011 2153328821277802764358517)
                ·
                  refine ⟨201874576994794009158611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2153328821277802764358517 201874576994794009158611)
                  ·
                    rfl

theorem cell20_442293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_442293 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_442293 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_442293 prefixEnd_442293 := by exact prefixLift 442293
  have htrace : WordTrace (prefixWord ++ tailWord_442293) baseStart_442293 baseEnd_442293 := by
    simpa [prefixWord, tailWord_442293, baseEnd_442293] using wordTrace_append hprefix tailTrace_442293
  have hstable : (prefixWord ++ tailWord_442293).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442293).length < 2 ^ (prefixWord ++ tailWord_442293).sum := by decide
  have hdescent : baseEnd_442293 < baseStart_442293 := by decide
  rcases family_descends (prefixWord ++ tailWord_442293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442321 : List Nat := [1, 2, 2, 1, 2, 1, 2, 3, 6]
def baseStart_442321 : Nat := 118140960795 + 442321 * 2 ^ 59
def prefixEnd_442321 : Nat := 4983230072969 + 3 ^ 40 * 442321 * 2
def baseEnd_442321 : Nat := 201887356957750356225163

theorem tailTrace_442321 : CollatzResearch.WordTrace tailWord_442321 prefixEnd_442321 201887356957750356225163 := by
  unfold tailWord_442321
  simp only [CollatzResearch.WordTrace]
  refine ⟨16132772230554034257670817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10755181487036022838447211 16132772230554034257670817)
  ·
    refine ⟨12099579172915525693253113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16132772230554034257670817 12099579172915525693253113)
    ·
      refine ⟨9074684379686644269939835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12099579172915525693253113 9074684379686644269939835)
      ·
        refine ⟨13612026569529966404909753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9074684379686644269939835 13612026569529966404909753)
        ·
          refine ⟨10209019927147474803682315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13612026569529966404909753 10209019927147474803682315)
          ·
            refine ⟨15313529890721212205523473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10209019927147474803682315 15313529890721212205523473)
            ·
              refine ⟨11485147418040909154142605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15313529890721212205523473 11485147418040909154142605)
              ·
                refine ⟨4306930281765340932803477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11485147418040909154142605 4306930281765340932803477)
                ·
                  refine ⟨201887356957750356225163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4306930281765340932803477 201887356957750356225163)
                  ·
                    rfl

theorem cell20_442321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 6].length) (baseStart_442321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_442321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_442321 prefixEnd_442321 := by exact prefixLift 442321
  have htrace : WordTrace (prefixWord ++ tailWord_442321) baseStart_442321 baseEnd_442321 := by
    simpa [prefixWord, tailWord_442321, baseEnd_442321] using wordTrace_append hprefix tailTrace_442321
  have hstable : (prefixWord ++ tailWord_442321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442321).length < 2 ^ (prefixWord ++ tailWord_442321).sum := by decide
  have hdescent : baseEnd_442321 < baseStart_442321 := by decide
  rcases family_descends (prefixWord ++ tailWord_442321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442352 : List Nat := [2, 1, 1, 1, 3, 2, 4, 1, 5]
def baseStart_442352 : Nat := 118140960795 + 442352 * 2 ^ 59
def prefixEnd_442352 : Nat := 4983230072969 + 3 ^ 40 * 442352 * 2
def baseEnd_442352 : Nat := 201901506202452026191703

theorem tailTrace_442352 : CollatzResearch.WordTrace tailWord_442352 prefixEnd_442352 201901506202452026191703 := by
  unfold tailWord_442352
  simp only [CollatzResearch.WordTrace]
  refine ⟨8066951446720863276024655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10755935262294484368032873 8066951446720863276024655)
  ·
    refine ⟨12100427170081294914036983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8066951446720863276024655 12100427170081294914036983)
    ·
      refine ⟨18150640755121942371055475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12100427170081294914036983 18150640755121942371055475)
      ·
        refine ⟨27225961132682913556583213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18150640755121942371055475 27225961132682913556583213)
        ·
          refine ⟨10209735424756092583718705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27225961132682913556583213 10209735424756092583718705)
          ·
            refine ⟨7657301568567069437789029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10209735424756092583718705 7657301568567069437789029)
            ·
              refine ⟨1435744044106325519585443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7657301568567069437789029 1435744044106325519585443)
              ·
                refine ⟨2153616066159488279378165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1435744044106325519585443 2153616066159488279378165)
                ·
                  refine ⟨201901506202452026191703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2153616066159488279378165 201901506202452026191703)
                  ·
                    rfl

theorem cell20_442352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 5].length) (baseStart_442352 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_442352 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_442352 prefixEnd_442352 := by exact prefixLift 442352
  have htrace : WordTrace (prefixWord ++ tailWord_442352) baseStart_442352 baseEnd_442352 := by
    simpa [prefixWord, tailWord_442352, baseEnd_442352] using wordTrace_append hprefix tailTrace_442352
  have hstable : (prefixWord ++ tailWord_442352).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442352).length < 2 ^ (prefixWord ++ tailWord_442352).sum := by decide
  have hdescent : baseEnd_442352 < baseStart_442352 := by decide
  rcases family_descends (prefixWord ++ tailWord_442352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442369 : List Nat := [1, 2, 4, 1, 2, 1, 3, 3, 3]
def baseStart_442369 : Nat := 118140960795 + 442369 * 2 ^ 59
def prefixEnd_442369 : Nat := 4983230072969 + 3 ^ 40 * 442369 * 2
def baseEnd_442369 : Nat := 201909265465675522624967

theorem tailTrace_442369 : CollatzResearch.WordTrace tailWord_442369 prefixEnd_442369 201909265465675522624967 := by
  unfold tailWord_442369
  simp only [CollatzResearch.WordTrace]
  refine ⟨16134522934380138455418161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10756348622920092303612107 16134522934380138455418161)
  ·
    refine ⟨12100892200785103841563621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16134522934380138455418161 12100892200785103841563621)
    ·
      refine ⟨2268917287647206970293179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12100892200785103841563621 2268917287647206970293179)
      ·
        refine ⟨3403375931470810455439769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2268917287647206970293179 3403375931470810455439769)
        ·
          refine ⟨2552531948603107841579827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3403375931470810455439769 2552531948603107841579827)
          ·
            refine ⟨3828797922904661762369741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2552531948603107841579827 3828797922904661762369741)
            ·
              refine ⟨1435799221089248160888653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3828797922904661762369741 1435799221089248160888653)
              ·
                refine ⟨538424707908468060333245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1435799221089248160888653 538424707908468060333245)
                ·
                  refine ⟨201909265465675522624967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 538424707908468060333245 201909265465675522624967)
                  ·
                    rfl

theorem cell20_442369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 3, 3].length) (baseStart_442369 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_442369 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_442369 prefixEnd_442369 := by exact prefixLift 442369
  have htrace : WordTrace (prefixWord ++ tailWord_442369) baseStart_442369 baseEnd_442369 := by
    simpa [prefixWord, tailWord_442369, baseEnd_442369] using wordTrace_append hprefix tailTrace_442369
  have hstable : (prefixWord ++ tailWord_442369).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442369).length < 2 ^ (prefixWord ++ tailWord_442369).sum := by decide
  have hdescent : baseEnd_442369 < baseStart_442369 := by decide
  rcases family_descends (prefixWord ++ tailWord_442369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442410 : List Nat := [3, 1, 4, 1, 2, 2, 1, 4, 2]
def baseStart_442410 : Nat := 118140960795 + 442410 * 2 ^ 59
def prefixEnd_442410 : Nat := 4983230072969 + 3 ^ 40 * 442410 * 2
def baseEnd_442410 : Nat := 201927978982861602258133

theorem tailTrace_442410 : CollatzResearch.WordTrace tailWord_442410 prefixEnd_442410 201927978982861602258133 := by
  unfold tailWord_442410
  simp only [CollatzResearch.WordTrace]
  refine ⟨4034004581807900614415171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10757345551487734971773789 4034004581807900614415171)
  ·
    refine ⟨6051006872711850921622757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4034004581807900614415171 6051006872711850921622757)
    ·
      refine ⟨1134563788633472047804267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6051006872711850921622757 1134563788633472047804267)
      ·
        refine ⟨1701845682950208071706401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1134563788633472047804267 1701845682950208071706401)
        ·
          refine ⟨1276384262212656053779801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1701845682950208071706401 1276384262212656053779801)
          ·
            refine ⟨957288196659492040334851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1276384262212656053779801 957288196659492040334851)
            ·
              refine ⟨1435932294989238060502277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 957288196659492040334851 1435932294989238060502277)
              ·
                refine ⟨269237305310482136344177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1435932294989238060502277 269237305310482136344177)
                ·
                  refine ⟨201927978982861602258133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 269237305310482136344177 201927978982861602258133)
                  ·
                    rfl

theorem cell20_442410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 4, 2].length) (baseStart_442410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_442410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_442410 prefixEnd_442410 := by exact prefixLift 442410
  have htrace : WordTrace (prefixWord ++ tailWord_442410) baseStart_442410 baseEnd_442410 := by
    simpa [prefixWord, tailWord_442410, baseEnd_442410] using wordTrace_append hprefix tailTrace_442410
  have hstable : (prefixWord ++ tailWord_442410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442410).length < 2 ^ (prefixWord ++ tailWord_442410).sum := by decide
  have hdescent : baseEnd_442410 < baseStart_442410 := by decide
  rcases family_descends (prefixWord ++ tailWord_442410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442421 : List Nat := [1, 3, 3, 1, 1, 1, 5, 5]
def baseStart_442421 : Nat := 118140960795 + 442421 * 2 ^ 59
def prefixEnd_442421 : Nat := 4983230072969 + 3 ^ 40 * 442421 * 2
def baseEnd_442421 : Nat := 67310999894198150963807

theorem tailTrace_442421 : CollatzResearch.WordTrace tailWord_442421 prefixEnd_442421 67310999894198150963807 := by
  unfold tailWord_442421
  simp only [CollatzResearch.WordTrace]
  refine ⟨16136419530191751336311117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10757613020127834224207411 16136419530191751336311117)
  ·
    refine ⟨6051157323821906751116669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16136419530191751336311117 6051157323821906751116669)
    ·
      refine ⟨2269183996433215031668751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6051157323821906751116669 2269183996433215031668751)
      ·
        refine ⟨3403775994649822547503127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2269183996433215031668751 3403775994649822547503127)
        ·
          refine ⟨5105663991974733821254691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3403775994649822547503127 5105663991974733821254691)
          ·
            refine ⟨7658495987962100731882037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5105663991974733821254691 7658495987962100731882037)
            ·
              refine ⟨717983998871446943613941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7658495987962100731882037 717983998871446943613941)
              ·
                refine ⟨67310999894198150963807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 717983998871446943613941 67310999894198150963807)
                ·
                  rfl

theorem cell20_442421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 5].length) (baseStart_442421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_442421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_442421 prefixEnd_442421 := by exact prefixLift 442421
  have htrace : WordTrace (prefixWord ++ tailWord_442421) baseStart_442421 baseEnd_442421 := by
    simpa [prefixWord, tailWord_442421, baseEnd_442421] using wordTrace_append hprefix tailTrace_442421
  have hstable : (prefixWord ++ tailWord_442421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442421).length < 2 ^ (prefixWord ++ tailWord_442421).sum := by decide
  have hdescent : baseEnd_442421 < baseStart_442421 := by decide
  rcases family_descends (prefixWord ++ tailWord_442421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442445 : List Nat := [1, 6, 1, 1, 1, 1, 2, 2, 5]
def baseStart_442445 : Nat := 118140960795 + 442445 * 2 ^ 59
def prefixEnd_442445 : Nat := 4983230072969 + 3 ^ 40 * 442445 * 2
def baseEnd_442445 : Nat := 201943953936557036091323

theorem tailTrace_442445 : CollatzResearch.WordTrace tailWord_442445 prefixEnd_442445 201943953936557036091323 := by
  unfold tailWord_442445
  simp only [CollatzResearch.WordTrace]
  refine ⟨16137294882104803435184789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10758196588069868956789859 16137294882104803435184789)
  ·
    refine ⟨756435697598662661024287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16137294882104803435184789 756435697598662661024287)
    ·
      refine ⟨1134653546397993991536431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 756435697598662661024287 1134653546397993991536431)
      ·
        refine ⟨1701980319596990987304647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1134653546397993991536431 1701980319596990987304647)
        ·
          refine ⟨2552970479395486480956971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1701980319596990987304647 2552970479395486480956971)
          ·
            refine ⟨3829455719093229721435457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2552970479395486480956971 3829455719093229721435457)
            ·
              refine ⟨2872091789319922291076593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3829455719093229721435457 2872091789319922291076593)
              ·
                refine ⟨2154068841989941718307445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2872091789319922291076593 2154068841989941718307445)
                ·
                  refine ⟨201943953936557036091323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2154068841989941718307445 201943953936557036091323)
                  ·
                    rfl

theorem cell20_442445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_442445 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_442445 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_442445 prefixEnd_442445 := by exact prefixLift 442445
  have htrace : WordTrace (prefixWord ++ tailWord_442445) baseStart_442445 baseEnd_442445 := by
    simpa [prefixWord, tailWord_442445, baseEnd_442445] using wordTrace_append hprefix tailTrace_442445
  have hstable : (prefixWord ++ tailWord_442445).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442445).length < 2 ^ (prefixWord ++ tailWord_442445).sum := by decide
  have hdescent : baseEnd_442445 < baseStart_442445 := by decide
  rcases family_descends (prefixWord ++ tailWord_442445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442469 : List Nat := [1, 3, 1, 3, 2, 2, 2, 4, 2]
def baseStart_442469 : Nat := 118140960795 + 442469 * 2 ^ 59
def prefixEnd_442469 : Nat := 4983230072969 + 3 ^ 40 * 442469 * 2
def baseEnd_442469 : Nat := 201954908190519619291225

theorem tailTrace_442469 : CollatzResearch.WordTrace tailWord_442469 prefixEnd_442469 201954908190519619291225 := by
  unfold tailWord_442469
  simp only [CollatzResearch.WordTrace]
  refine ⟨16138170234017855534058461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10758780156011903689372307 16138170234017855534058461)
  ·
    refine ⟨6051813837756695825271923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16138170234017855534058461 6051813837756695825271923)
    ·
      refine ⟨9077720756635043737907885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6051813837756695825271923 9077720756635043737907885)
      ·
        refine ⟨3404145283738141401715457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9077720756635043737907885 3404145283738141401715457)
        ·
          refine ⟨2553108962803606051286593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3404145283738141401715457 2553108962803606051286593)
          ·
            refine ⟨1914831722102704538464945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2553108962803606051286593 1914831722102704538464945)
            ·
              refine ⟨1436123791577028403848709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1914831722102704538464945 1436123791577028403848709)
              ·
                refine ⟨269273210920692825721633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1436123791577028403848709 269273210920692825721633)
                ·
                  refine ⟨201954908190519619291225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 269273210920692825721633 201954908190519619291225)
                  ·
                    rfl

theorem cell20_442469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 4, 2].length) (baseStart_442469 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_442469 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_442469 prefixEnd_442469 := by exact prefixLift 442469
  have htrace : WordTrace (prefixWord ++ tailWord_442469) baseStart_442469 baseEnd_442469 := by
    simpa [prefixWord, tailWord_442469, baseEnd_442469] using wordTrace_append hprefix tailTrace_442469
  have hstable : (prefixWord ++ tailWord_442469).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442469).length < 2 ^ (prefixWord ++ tailWord_442469).sum := by decide
  have hdescent : baseEnd_442469 < baseStart_442469 := by decide
  rcases family_descends (prefixWord ++ tailWord_442469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442524 : List Nat := [2, 2, 3, 2, 1, 1, 5, 2, 2]
def baseStart_442524 : Nat := 118140960795 + 442524 * 2 ^ 59
def prefixEnd_442524 : Nat := 4983230072969 + 3 ^ 40 * 442524 * 2
def baseEnd_442524 : Nat := 201980011689183872457667

theorem tailTrace_442524 : CollatzResearch.WordTrace tailWord_442524 prefixEnd_442524 201980011689183872457667 := by
  unfold tailWord_442524
  simp only [CollatzResearch.WordTrace]
  refine ⟨8070088124409299963655313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10760117499212399951540417 8070088124409299963655313)
  ·
    refine ⟨6052566093306974972741485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8070088124409299963655313 6052566093306974972741485)
    ·
      refine ⟨2269712284990115614778057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6052566093306974972741485 2269712284990115614778057)
      ·
        refine ⟨1702284213742586711083543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2269712284990115614778057 1702284213742586711083543)
        ·
          refine ⟨2553426320613880066625315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1702284213742586711083543 2553426320613880066625315)
          ·
            refine ⟨3830139480920820099937973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2553426320613880066625315 3830139480920820099937973)
            ·
              refine ⟨359075576336326884369185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3830139480920820099937973 359075576336326884369185)
              ·
                refine ⟨269306682252245163276889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 359075576336326884369185 269306682252245163276889)
                ·
                  refine ⟨201980011689183872457667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 269306682252245163276889 201980011689183872457667)
                  ·
                    rfl

theorem cell20_442524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 2, 2].length) (baseStart_442524 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_442524 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_442524 prefixEnd_442524 := by exact prefixLift 442524
  have htrace : WordTrace (prefixWord ++ tailWord_442524) baseStart_442524 baseEnd_442524 := by
    simpa [prefixWord, tailWord_442524, baseEnd_442524] using wordTrace_append hprefix tailTrace_442524
  have hstable : (prefixWord ++ tailWord_442524).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442524).length < 2 ^ (prefixWord ++ tailWord_442524).sum := by decide
  have hdescent : baseEnd_442524 < baseStart_442524 := by decide
  rcases family_descends (prefixWord ++ tailWord_442524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442528 : List Nat := [2, 1, 1, 4, 2, 2, 3, 1, 4]
def baseStart_442528 : Nat := 118140960795 + 442528 * 2 ^ 59
def prefixEnd_442528 : Nat := 4983230072969 + 3 ^ 40 * 442528 * 2
def baseEnd_442528 : Nat := 201981837398177636324317

theorem tailTrace_442528 : CollatzResearch.WordTrace tailWord_442528 prefixEnd_442528 201981837398177636324317 := by
  unfold tailWord_442528
  simp only [CollatzResearch.WordTrace]
  refine ⟨8070161070402054305228119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10760214760536072406970825 8070161070402054305228119)
  ·
    refine ⟨12105241605603081457842179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8070161070402054305228119 12105241605603081457842179)
    ·
      refine ⟨18157862408404622186763269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12105241605603081457842179 18157862408404622186763269)
      ·
        refine ⟨3404599201575866660018113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18157862408404622186763269 3404599201575866660018113)
        ·
          refine ⟨2553449401181899995013585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3404599201575866660018113 2553449401181899995013585)
          ·
            refine ⟨1915087050886424996260189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2553449401181899995013585 1915087050886424996260189)
            ·
              refine ⟨718157644082409373597571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1915087050886424996260189 718157644082409373597571)
              ·
                refine ⟨1077236466123614060396357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 718157644082409373597571 1077236466123614060396357)
                ·
                  refine ⟨201981837398177636324317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1077236466123614060396357 201981837398177636324317)
                  ·
                    rfl

theorem cell20_442528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 4].length) (baseStart_442528 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_442528 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_442528 prefixEnd_442528 := by exact prefixLift 442528
  have htrace : WordTrace (prefixWord ++ tailWord_442528) baseStart_442528 baseEnd_442528 := by
    simpa [prefixWord, tailWord_442528, baseEnd_442528] using wordTrace_append hprefix tailTrace_442528
  have hstable : (prefixWord ++ tailWord_442528).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442528).length < 2 ^ (prefixWord ++ tailWord_442528).sum := by decide
  have hdescent : baseEnd_442528 < baseStart_442528 := by decide
  rcases family_descends (prefixWord ++ tailWord_442528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442573 : List Nat := [1, 6, 2, 11]
def baseStart_442573 : Nat := 118140960795 + 442573 * 2 ^ 59
def prefixEnd_442573 : Nat := 4983230072969 + 3 ^ 40 * 442573 * 2
def baseEnd_442573 : Nat := 831285500511759176231

theorem tailTrace_442573 : CollatzResearch.WordTrace tailWord_442573 prefixEnd_442573 831285500511759176231 := by
  unfold tailWord_442573
  simp only [CollatzResearch.WordTrace]
  refine ⟨16141963425641081295844373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10761308950427387530562915 16141963425641081295844373)
  ·
    refine ⟨756654535576925685742705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16141963425641081295844373 756654535576925685742705)
    ·
      refine ⟨567490901682694264307029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 756654535576925685742705 567490901682694264307029)
      ·
        refine ⟨831285500511759176231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 567490901682694264307029 831285500511759176231)
        ·
          rfl

theorem cell20_442573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 11].length) (baseStart_442573 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_442573 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_442573 prefixEnd_442573 := by exact prefixLift 442573
  have htrace : WordTrace (prefixWord ++ tailWord_442573) baseStart_442573 baseEnd_442573 := by
    simpa [prefixWord, tailWord_442573, baseEnd_442573] using wordTrace_append hprefix tailTrace_442573
  have hstable : (prefixWord ++ tailWord_442573).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442573).length < 2 ^ (prefixWord ++ tailWord_442573).sum := by decide
  have hdescent : baseEnd_442573 < baseStart_442573 := by decide
  rcases family_descends (prefixWord ++ tailWord_442573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442597 : List Nat := [1, 3, 1, 4, 2, 1, 2, 3, 3]
def baseStart_442597 : Nat := 118140960795 + 442597 * 2 ^ 59
def prefixEnd_442597 : Nat := 4983230072969 + 3 ^ 40 * 442597 * 2
def baseEnd_442597 : Nat := 202013330878320063024035

theorem tailTrace_442597 : CollatzResearch.WordTrace tailWord_442597 prefixEnd_442597 202013330878320063024035 := by
  unfold tailWord_442597
  simp only [CollatzResearch.WordTrace]
  refine ⟨16142838777554133394718045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10761892518369422263145363 16142838777554133394718045)
  ·
    refine ⟨6053564541582800023019267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16142838777554133394718045 6053564541582800023019267)
    ·
      refine ⟨9080346812374200034528901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6053564541582800023019267 9080346812374200034528901)
      ·
        refine ⟨1702565027320162506474169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9080346812374200034528901 1702565027320162506474169)
        ·
          refine ⟨1276923770490121879855627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1702565027320162506474169 1276923770490121879855627)
          ·
            refine ⟨1915385655735182819783441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1276923770490121879855627 1915385655735182819783441)
            ·
              refine ⟨1436539241801387114837581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1915385655735182819783441 1436539241801387114837581)
              ·
                refine ⟨538702215675520168064093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1436539241801387114837581 538702215675520168064093)
                ·
                  refine ⟨202013330878320063024035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 538702215675520168064093 202013330878320063024035)
                  ·
                    rfl

theorem cell20_442597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 3, 3].length) (baseStart_442597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_442597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_442597 prefixEnd_442597 := by exact prefixLift 442597
  have htrace : WordTrace (prefixWord ++ tailWord_442597) baseStart_442597 baseEnd_442597 := by
    simpa [prefixWord, tailWord_442597, baseEnd_442597] using wordTrace_append hprefix tailTrace_442597
  have hstable : (prefixWord ++ tailWord_442597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442597).length < 2 ^ (prefixWord ++ tailWord_442597).sum := by decide
  have hdescent : baseEnd_442597 < baseStart_442597 := by decide
  rcases family_descends (prefixWord ++ tailWord_442597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442611 : List Nat := [1, 1, 1, 2, 2, 4, 5, 4]
def baseStart_442611 : Nat := 118140960795 + 442611 * 2 ^ 59
def prefixEnd_442611 : Nat := 4983230072969 + 3 ^ 40 * 442611 * 2
def baseEnd_442611 : Nat := 67339906953266078852437

theorem tailTrace_442611 : CollatzResearch.WordTrace tailWord_442611 prefixEnd_442611 67339906953266078852437 := by
  unfold tailWord_442611
  simp only [CollatzResearch.WordTrace]
  refine ⟨16143349399503413785727687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10762232933002275857151791 16143349399503413785727687)
  ·
    refine ⟨24215024099255120678591531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16143349399503413785727687 24215024099255120678591531)
    ·
      refine ⟨36322536148882681017887297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24215024099255120678591531 36322536148882681017887297)
      ·
        refine ⟨27241902111662010763415473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36322536148882681017887297 27241902111662010763415473)
        ·
          refine ⟨20431426583746508072561605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27241902111662010763415473 20431426583746508072561605)
          ·
            refine ⟨3830892484452470263605301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20431426583746508072561605 3830892484452470263605301)
            ·
              refine ⟨359146170417419087212997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3830892484452470263605301 359146170417419087212997)
              ·
                refine ⟨67339906953266078852437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 359146170417419087212997 67339906953266078852437)
                ·
                  rfl

theorem cell20_442611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 4].length) (baseStart_442611 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_442611 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_442611 prefixEnd_442611 := by exact prefixLift 442611
  have htrace : WordTrace (prefixWord ++ tailWord_442611) baseStart_442611 baseEnd_442611 := by
    simpa [prefixWord, tailWord_442611, baseEnd_442611] using wordTrace_append hprefix tailTrace_442611
  have hstable : (prefixWord ++ tailWord_442611).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442611).length < 2 ^ (prefixWord ++ tailWord_442611).sum := by decide
  have hdescent : baseEnd_442611 < baseStart_442611 := by decide
  rcases family_descends (prefixWord ++ tailWord_442611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442625 : List Nat := [1, 2, 4, 1, 1, 2, 1, 2, 6]
def baseStart_442625 : Nat := 118140960795 + 442625 * 2 ^ 59
def prefixEnd_442625 : Nat := 4983230072969 + 3 ^ 40 * 442625 * 2
def baseEnd_442625 : Nat := 202026110841276410090587

theorem tailTrace_442625 : CollatzResearch.WordTrace tailWord_442625 prefixEnd_442625 202026110841276410090587 := by
  unfold tailWord_442625
  simp only [CollatzResearch.WordTrace]
  refine ⟨16143860021452694176737329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10762573347635129451158219 16143860021452694176737329)
  ·
    refine ⟨12107895016089520632552997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16143860021452694176737329 12107895016089520632552997)
    ·
      refine ⟨2270230315516785118603687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12107895016089520632552997 2270230315516785118603687)
      ·
        refine ⟨3405345473275177677905531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2270230315516785118603687 3405345473275177677905531)
        ·
          refine ⟨5108018209912766516858297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3405345473275177677905531 5108018209912766516858297)
          ·
            refine ⟨3831013657434574887643723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5108018209912766516858297 3831013657434574887643723)
            ·
              refine ⟨5746520486151862331465585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3831013657434574887643723 5746520486151862331465585)
              ·
                refine ⟨4309890364613896748599189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5746520486151862331465585 4309890364613896748599189)
                ·
                  refine ⟨202026110841276410090587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4309890364613896748599189 202026110841276410090587)
                  ·
                    rfl

theorem cell20_442625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 6].length) (baseStart_442625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_442625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_442625 prefixEnd_442625 := by exact prefixLift 442625
  have htrace : WordTrace (prefixWord ++ tailWord_442625) baseStart_442625 baseEnd_442625 := by
    simpa [prefixWord, tailWord_442625, baseEnd_442625] using wordTrace_append hprefix tailTrace_442625
  have hstable : (prefixWord ++ tailWord_442625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442625).length < 2 ^ (prefixWord ++ tailWord_442625).sum := by decide
  have hdescent : baseEnd_442625 < baseStart_442625 := by decide
  rcases family_descends (prefixWord ++ tailWord_442625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442631 : List Nat := [1, 1, 4, 5, 1, 2, 1, 2, 3]
def baseStart_442631 : Nat := 118140960795 + 442631 * 2 ^ 59
def prefixEnd_442631 : Nat := 4983230072969 + 3 ^ 40 * 442631 * 2
def baseEnd_442631 : Nat := 202028849404767055890563

theorem tailTrace_442631 : CollatzResearch.WordTrace tailWord_442631 prefixEnd_442631 202028849404767055890563 := by
  unfold tailWord_442631
  simp only [CollatzResearch.WordTrace]
  refine ⟨16144078859430957201455747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10762719239620638134303831 16144078859430957201455747)
  ·
    refine ⟨24216118289146435802183621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16144078859430957201455747 24216118289146435802183621)
    ·
      refine ⟨4540522179214956712909429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24216118289146435802183621 4540522179214956712909429)
      ·
        refine ⟨425673954301402191835259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4540522179214956712909429 425673954301402191835259)
        ·
          refine ⟨638510931452103287752889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425673954301402191835259 638510931452103287752889)
          ·
            refine ⟨478883198589077465814667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 638510931452103287752889 478883198589077465814667)
            ·
              refine ⟨718324797883616198722001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 478883198589077465814667 718324797883616198722001)
              ·
                refine ⟨538743598412712149041501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 718324797883616198722001 538743598412712149041501)
                ·
                  refine ⟨202028849404767055890563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 538743598412712149041501 202028849404767055890563)
                  ·
                    rfl

theorem cell20_442631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 2, 3].length) (baseStart_442631 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_442631 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_442631 prefixEnd_442631 := by exact prefixLift 442631
  have htrace : WordTrace (prefixWord ++ tailWord_442631) baseStart_442631 baseEnd_442631 := by
    simpa [prefixWord, tailWord_442631, baseEnd_442631] using wordTrace_append hprefix tailTrace_442631
  have hstable : (prefixWord ++ tailWord_442631).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442631).length < 2 ^ (prefixWord ++ tailWord_442631).sum := by decide
  have hdescent : baseEnd_442631 < baseStart_442631 := by decide
  rcases family_descends (prefixWord ++ tailWord_442631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442666 : List Nat := [3, 1, 4, 2, 2, 1, 1, 6]
def baseStart_442666 : Nat := 118140960795 + 442666 * 2 ^ 59
def prefixEnd_442666 : Nat := 4983230072969 + 3 ^ 40 * 442666 * 2
def baseEnd_442666 : Nat := 67348274786154163241251

theorem tailTrace_442666 : CollatzResearch.WordTrace tailWord_442666 prefixEnd_442666 67348274786154163241251 := by
  unfold tailWord_442666
  simp only [CollatzResearch.WordTrace]
  refine ⟨4036338853576039544744963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10763570276202772119319901 4036338853576039544744963)
  ·
    refine ⟨6054508280364059317117445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4036338853576039544744963 6054508280364059317117445)
    ·
      refine ⟨1135220302568261121959521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6054508280364059317117445 1135220302568261121959521)
      ·
        refine ⟨851415226926195841469641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1135220302568261121959521 851415226926195841469641)
        ·
          refine ⟨638561420194646881102231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 851415226926195841469641 638561420194646881102231)
          ·
            refine ⟨957842130291970321653347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 638561420194646881102231 957842130291970321653347)
            ·
              refine ⟨1436763195437955482480021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 957842130291970321653347 1436763195437955482480021)
              ·
                refine ⟨67348274786154163241251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1436763195437955482480021 67348274786154163241251)
                ·
                  rfl

theorem cell20_442666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 6].length) (baseStart_442666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_442666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_442666 prefixEnd_442666 := by exact prefixLift 442666
  have htrace : WordTrace (prefixWord ++ tailWord_442666) baseStart_442666 baseEnd_442666 := by
    simpa [prefixWord, tailWord_442666, baseEnd_442666] using wordTrace_append hprefix tailTrace_442666
  have hstable : (prefixWord ++ tailWord_442666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442666).length < 2 ^ (prefixWord ++ tailWord_442666).sum := by decide
  have hdescent : baseEnd_442666 < baseStart_442666 := by decide
  rcases family_descends (prefixWord ++ tailWord_442666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442676 : List Nat := [2, 5, 1, 1, 1, 2, 3, 3, 2]
def baseStart_442676 : Nat := 118140960795 + 442676 * 2 ^ 59
def prefixEnd_442676 : Nat := 4983230072969 + 3 ^ 40 * 442676 * 2
def baseEnd_442676 : Nat := 202049388630946899390379

theorem tailTrace_442676 : CollatzResearch.WordTrace tailWord_442676 prefixEnd_442676 202049388630946899390379 := by
  unfold tailWord_442676
  simp only [CollatzResearch.WordTrace]
  refine ⟨8072860072133964943421941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10763813429511953257895921 8072860072133964943421941)
  ·
    refine ⟨756830631762559213445807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8072860072133964943421941 756830631762559213445807)
    ·
      refine ⟨1135245947643838820168711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 756830631762559213445807 1135245947643838820168711)
      ·
        refine ⟨1702868921465758230253067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1135245947643838820168711 1702868921465758230253067)
        ·
          refine ⟨2554303382198637345379601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1702868921465758230253067 2554303382198637345379601)
          ·
            refine ⟨1915727536648978009034701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2554303382198637345379601 1915727536648978009034701)
            ·
              refine ⟨718397826243366753388013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1915727536648978009034701 718397826243366753388013)
              ·
                refine ⟨269399184841262532520505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 718397826243366753388013 269399184841262532520505)
                ·
                  refine ⟨202049388630946899390379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 269399184841262532520505 202049388630946899390379)
                  ·
                    rfl

theorem cell20_442676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_442676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_442676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_442676 prefixEnd_442676 := by exact prefixLift 442676
  have htrace : WordTrace (prefixWord ++ tailWord_442676) baseStart_442676 baseEnd_442676 := by
    simpa [prefixWord, tailWord_442676, baseEnd_442676] using wordTrace_append hprefix tailTrace_442676
  have hstable : (prefixWord ++ tailWord_442676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442676).length < 2 ^ (prefixWord ++ tailWord_442676).sum := by decide
  have hdescent : baseEnd_442676 < baseStart_442676 := by decide
  rcases family_descends (prefixWord ++ tailWord_442676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442742 : List Nat := [5, 1, 1, 4, 1, 8]
def baseStart_442742 : Nat := 118140960795 + 442742 * 2 ^ 59
def prefixEnd_442742 : Nat := 4983230072969 + 3 ^ 40 * 442742 * 2
def baseEnd_442742 : Nat := 7484426401086814932967

theorem tailTrace_442742 : CollatzResearch.WordTrace tailWord_442742 prefixEnd_442742 7484426401086814932967 := by
  unfold tailWord_442742
  simp only [CollatzResearch.WordTrace]
  refine ⟨1009257960126801447421655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10765418241352548772497653 1009257960126801447421655)
  ·
    refine ⟨1513886940190202171132483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1009257960126801447421655 1513886940190202171132483)
    ·
      refine ⟨2270830410285303256698725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1513886940190202171132483 2270830410285303256698725)
      ·
        refine ⟨425780701928494360631011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2270830410285303256698725 425780701928494360631011)
        ·
          refine ⟨638671052892741540946517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425780701928494360631011 638671052892741540946517)
          ·
            refine ⟨7484426401086814932967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 638671052892741540946517 7484426401086814932967)
            ·
              rfl

theorem cell20_442742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 8].length) (baseStart_442742 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_442742 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_442742 prefixEnd_442742 := by exact prefixLift 442742
  have htrace : WordTrace (prefixWord ++ tailWord_442742) baseStart_442742 baseEnd_442742 := by
    simpa [prefixWord, tailWord_442742, baseEnd_442742] using wordTrace_append hprefix tailTrace_442742
  have hstable : (prefixWord ++ tailWord_442742).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442742).length < 2 ^ (prefixWord ++ tailWord_442742).sum := by decide
  have hdescent : baseEnd_442742 < baseStart_442742 := by decide
  rcases family_descends (prefixWord ++ tailWord_442742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442749 : List Nat := [1, 4, 1, 1, 2, 4, 2, 2, 3]
def baseStart_442749 : Nat := 118140960795 + 442749 * 2 ^ 59
def prefixEnd_442749 : Nat := 4983230072969 + 3 ^ 40 * 442749 * 2
def baseEnd_442749 : Nat := 202082707820083089956747

theorem tailTrace_442749 : CollatzResearch.WordTrace tailWord_442749 prefixEnd_442749 202082707820083089956747 := by
  unfold tailWord_442749
  simp only [CollatzResearch.WordTrace]
  refine ⟨16148382673003463354251301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10765588448668975569500867 16148382673003463354251301)
  ·
    refine ⟨3027821751188149378922119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16148382673003463354251301 3027821751188149378922119)
    ·
      refine ⟨4541732626782224068383179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3027821751188149378922119 4541732626782224068383179)
      ·
        refine ⟨6812598940173336102574769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4541732626782224068383179 6812598940173336102574769)
        ·
          refine ⟨5109449205130002076931077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6812598940173336102574769 5109449205130002076931077)
          ·
            refine ⟨958021725961875389424577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5109449205130002076931077 958021725961875389424577)
            ·
              refine ⟨718516294471406542068433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 958021725961875389424577 718516294471406542068433)
              ·
                refine ⟨538887220853554906551325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 718516294471406542068433 538887220853554906551325)
                ·
                  refine ⟨202082707820083089956747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 538887220853554906551325 202082707820083089956747)
                  ·
                    rfl

theorem cell20_442749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_442749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_442749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_442749 prefixEnd_442749 := by exact prefixLift 442749
  have htrace : WordTrace (prefixWord ++ tailWord_442749) baseStart_442749 baseEnd_442749 := by
    simpa [prefixWord, tailWord_442749, baseEnd_442749] using wordTrace_append hprefix tailTrace_442749
  have hstable : (prefixWord ++ tailWord_442749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442749).length < 2 ^ (prefixWord ++ tailWord_442749).sum := by decide
  have hdescent : baseEnd_442749 < baseStart_442749 := by decide
  rcases family_descends (prefixWord ++ tailWord_442749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442763 : List Nat := [1, 1, 1, 1, 4, 6, 1, 5]
def baseStart_442763 : Nat := 118140960795 + 442763 * 2 ^ 59
def prefixEnd_442763 : Nat := 4983230072969 + 3 ^ 40 * 442763 * 2
def baseEnd_442763 : Nat := 67363032600520421163341

theorem tailTrace_442763 : CollatzResearch.WordTrace tailWord_442763 prefixEnd_442763 67363032600520421163341 := by
  unfold tailWord_442763
  simp only [CollatzResearch.WordTrace]
  refine ⟨16148893294952743745260943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10765928863301829163507295 16148893294952743745260943)
  ·
    refine ⟨24223339942429115617891415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16148893294952743745260943 24223339942429115617891415)
    ·
      refine ⟨36335009913643673426837123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24223339942429115617891415 36335009913643673426837123)
      ·
        refine ⟨54502514870465510140255685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36335009913643673426837123 54502514870465510140255685)
        ·
          refine ⟨10219221538212283151297941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54502514870465510140255685 10219221538212283151297941)
          ·
            refine ⟨479026009603700772717091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10219221538212283151297941 479026009603700772717091)
            ·
              refine ⟨718539014405551159075637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 479026009603700772717091 718539014405551159075637)
              ·
                refine ⟨67363032600520421163341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 718539014405551159075637 67363032600520421163341)
                ·
                  rfl

theorem cell20_442763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 5].length) (baseStart_442763 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_442763 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_442763 prefixEnd_442763 := by exact prefixLift 442763
  have htrace : WordTrace (prefixWord ++ tailWord_442763) baseStart_442763 baseEnd_442763 := by
    simpa [prefixWord, tailWord_442763, baseEnd_442763] using wordTrace_append hprefix tailTrace_442763
  have hstable : (prefixWord ++ tailWord_442763).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442763).length < 2 ^ (prefixWord ++ tailWord_442763).sum := by decide
  have hdescent : baseEnd_442763 < baseStart_442763 := by decide
  rcases family_descends (prefixWord ++ tailWord_442763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442777 : List Nat := [1, 2, 1, 2, 1, 4, 3, 2, 4]
def baseStart_442777 : Nat := 118140960795 + 442777 * 2 ^ 59
def prefixEnd_442777 : Nat := 4983230072969 + 3 ^ 40 * 442777 * 2
def baseEnd_442777 : Nat := 202095487783039437023299

theorem tailTrace_442777 : CollatzResearch.WordTrace tailWord_442777 prefixEnd_442777 202095487783039437023299 := by
  unfold tailWord_442777
  simp only [CollatzResearch.WordTrace]
  refine ⟨16149403916902024136270585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10766269277934682757513723 16149403916902024136270585)
  ·
    refine ⟨12112052937676518102202939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16149403916902024136270585 12112052937676518102202939)
    ·
      refine ⟨18168079406514777153304409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12112052937676518102202939 18168079406514777153304409)
      ·
        refine ⟨13626059554886082864978307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18168079406514777153304409 13626059554886082864978307)
        ·
          refine ⟨20439089332329124297467461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13626059554886082864978307 20439089332329124297467461)
          ·
            refine ⟨3832329249811710805775149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20439089332329124297467461 3832329249811710805775149)
            ·
              refine ⟨1437123468679391552165681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3832329249811710805775149 1437123468679391552165681)
              ·
                refine ⟨1077842601509543664124261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1437123468679391552165681 1077842601509543664124261)
                ·
                  refine ⟨202095487783039437023299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1077842601509543664124261 202095487783039437023299)
                  ·
                    rfl

theorem cell20_442777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 4].length) (baseStart_442777 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_442777 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_442777 prefixEnd_442777 := by exact prefixLift 442777
  have htrace : WordTrace (prefixWord ++ tailWord_442777) baseStart_442777 baseEnd_442777 := by
    simpa [prefixWord, tailWord_442777, baseEnd_442777] using wordTrace_append hprefix tailTrace_442777
  have hstable : (prefixWord ++ tailWord_442777).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442777).length < 2 ^ (prefixWord ++ tailWord_442777).sum := by decide
  have hdescent : baseEnd_442777 < baseStart_442777 := by decide
  rcases family_descends (prefixWord ++ tailWord_442777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442866 : List Nat := [3, 2, 1, 4, 3, 1, 1, 1, 4]
def baseStart_442866 : Nat := 118140960795 + 442866 * 2 ^ 59
def prefixEnd_442866 : Nat := 4983230072969 + 3 ^ 40 * 442866 * 2
def baseEnd_442866 : Nat := 202136109808150683056269

theorem tailTrace_442866 : CollatzResearch.WordTrace tailWord_442866 prefixEnd_442866 202136109808150683056269 := by
  unfold tailWord_442866
  simp only [CollatzResearch.WordTrace]
  refine ⟨4038162503394898084065113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10768433342386394890840301 4038162503394898084065113)
  ·
    refine ⟨3028621877546173563048835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4038162503394898084065113 3028621877546173563048835)
    ·
      refine ⟨4542932816319260344573253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3028621877546173563048835 4542932816319260344573253)
      ·
        refine ⟨851799903059861314607485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4542932816319260344573253 851799903059861314607485)
        ·
          refine ⟨319424963647447992977807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 851799903059861314607485 319424963647447992977807)
          ·
            refine ⟨479137445471171989466711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319424963647447992977807 479137445471171989466711)
            ·
              refine ⟨718706168206757984200067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 479137445471171989466711 718706168206757984200067)
              ·
                refine ⟨1078059252310136976300101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 718706168206757984200067 1078059252310136976300101)
                ·
                  refine ⟨202136109808150683056269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1078059252310136976300101 202136109808150683056269)
                  ·
                    rfl

theorem cell20_442866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 4].length) (baseStart_442866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_442866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_442866 prefixEnd_442866 := by exact prefixLift 442866
  have htrace : WordTrace (prefixWord ++ tailWord_442866) baseStart_442866 baseEnd_442866 := by
    simpa [prefixWord, tailWord_442866, baseEnd_442866] using wordTrace_append hprefix tailTrace_442866
  have hstable : (prefixWord ++ tailWord_442866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442866).length < 2 ^ (prefixWord ++ tailWord_442866).sum := by decide
  have hdescent : baseEnd_442866 < baseStart_442866 := by decide
  rcases family_descends (prefixWord ++ tailWord_442866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442867 : List Nat := [1, 1, 1, 2, 2, 2, 3, 3, 5]
def baseStart_442867 : Nat := 118140960795 + 442867 * 2 ^ 59
def prefixEnd_442867 : Nat := 4983230072969 + 3 ^ 40 * 442867 * 2
def baseEnd_442867 : Nat := 202136566235399124022931

theorem tailTrace_442867 : CollatzResearch.WordTrace tailWord_442867 prefixEnd_442867 202136566235399124022931 := by
  unfold tailWord_442867
  simp only [CollatzResearch.WordTrace]
  refine ⟨16152686486575969507046855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10768457657717313004697903 16152686486575969507046855)
  ·
    refine ⟨24229029729863954260570283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16152686486575969507046855 24229029729863954260570283)
    ·
      refine ⟨36343544594795931390855425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24229029729863954260570283 36343544594795931390855425)
      ·
        refine ⟨27257658446096948543141569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36343544594795931390855425 27257658446096948543141569)
        ·
          refine ⟨20443243834572711407356177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27257658446096948543141569 20443243834572711407356177)
          ·
            refine ⟨15332432875929533555517133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20443243834572711407356177 15332432875929533555517133)
            ·
              refine ⟨5749662328473575083318925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15332432875929533555517133 5749662328473575083318925)
              ·
                refine ⟨2156123373177590656244597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5749662328473575083318925 2156123373177590656244597)
                ·
                  refine ⟨202136566235399124022931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2156123373177590656244597 202136566235399124022931)
                  ·
                    rfl

theorem cell20_442867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 5].length) (baseStart_442867 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_442867 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_442867 prefixEnd_442867 := by exact prefixLift 442867
  have htrace : WordTrace (prefixWord ++ tailWord_442867) baseStart_442867 baseEnd_442867 := by
    simpa [prefixWord, tailWord_442867, baseEnd_442867] using wordTrace_append hprefix tailTrace_442867
  have hstable : (prefixWord ++ tailWord_442867).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442867).length < 2 ^ (prefixWord ++ tailWord_442867).sum := by decide
  have hdescent : baseEnd_442867 < baseStart_442867 := by decide
  rcases family_descends (prefixWord ++ tailWord_442867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442977 : List Nat := [1, 2, 3, 1, 1, 6, 1, 2, 3]
def baseStart_442977 : Nat := 118140960795 + 442977 * 2 ^ 59
def prefixEnd_442977 : Nat := 4983230072969 + 3 ^ 40 * 442977 * 2
def baseEnd_442977 : Nat := 202186773232727630355815

theorem tailTrace_442977 : CollatzResearch.WordTrace tailWord_442977 prefixEnd_442977 202186773232727630355815 := by
  unfold tailWord_442977
  simp only [CollatzResearch.WordTrace]
  refine ⟨16156698516177458293551185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10771132344118305529034123 16156698516177458293551185)
  ·
    refine ⟨12117523887133093720163389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16156698516177458293551185 12117523887133093720163389)
    ·
      refine ⟨4544071457674910145061271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12117523887133093720163389 4544071457674910145061271)
      ·
        refine ⟨6816107186512365217591907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4544071457674910145061271 6816107186512365217591907)
        ·
          refine ⟨10224160779768547826387861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6816107186512365217591907 10224160779768547826387861)
          ·
            refine ⟨479257536551650679361931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10224160779768547826387861 479257536551650679361931)
            ·
              refine ⟨718886304827476019042897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 479257536551650679361931 718886304827476019042897)
              ·
                refine ⟨539164728620607014282173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 718886304827476019042897 539164728620607014282173)
                ·
                  refine ⟨202186773232727630355815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 539164728620607014282173 202186773232727630355815)
                  ·
                    rfl

theorem cell20_442977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 2, 3].length) (baseStart_442977 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_442977 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_442977 prefixEnd_442977 := by exact prefixLift 442977
  have htrace : WordTrace (prefixWord ++ tailWord_442977) baseStart_442977 baseEnd_442977 := by
    simpa [prefixWord, tailWord_442977, baseEnd_442977] using wordTrace_append hprefix tailTrace_442977
  have hstable : (prefixWord ++ tailWord_442977).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442977).length < 2 ^ (prefixWord ++ tailWord_442977).sum := by decide
  have hdescent : baseEnd_442977 < baseStart_442977 := by decide
  rcases family_descends (prefixWord ++ tailWord_442977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442994 : List Nat := [3, 2, 1, 2, 4, 1, 3, 1, 3]
def baseStart_442994 : Nat := 118140960795 + 442994 * 2 ^ 59
def prefixEnd_442994 : Nat := 4983230072969 + 3 ^ 40 * 442994 * 2
def baseEnd_442994 : Nat := 202194532495951126789079

theorem tailTrace_442994 : CollatzResearch.WordTrace tailWord_442994 prefixEnd_442994 202194532495951126789079 := by
  unfold tailWord_442994
  simp only [CollatzResearch.WordTrace]
  refine ⟨4039329639278967549230009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10771545704743913464613357 4039329639278967549230009)
  ·
    refine ⟨3029497229459225661922507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4039329639278967549230009 3029497229459225661922507)
    ·
      refine ⟨4544245844188838492883761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3029497229459225661922507 4544245844188838492883761)
      ·
        refine ⟨3408184383141628869662821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4544245844188838492883761 3408184383141628869662821)
        ·
          refine ⟨639034571839055413061779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3408184383141628869662821 639034571839055413061779)
          ·
            refine ⟨958551857758583119592669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 639034571839055413061779 958551857758583119592669)
            ·
              refine ⟨359456946659468669847251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 958551857758583119592669 359456946659468669847251)
              ·
                refine ⟨539185419989203004770877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 359456946659468669847251 539185419989203004770877)
                ·
                  refine ⟨202194532495951126789079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 539185419989203004770877 202194532495951126789079)
                  ·
                    rfl

theorem cell20_442994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_442994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_442994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_442994 prefixEnd_442994 := by exact prefixLift 442994
  have htrace : WordTrace (prefixWord ++ tailWord_442994) baseStart_442994 baseEnd_442994 := by
    simpa [prefixWord, tailWord_442994, baseEnd_442994] using wordTrace_append hprefix tailTrace_442994
  have hstable : (prefixWord ++ tailWord_442994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442994).length < 2 ^ (prefixWord ++ tailWord_442994).sum := by decide
  have hdescent : baseEnd_442994 < baseStart_442994 := by decide
  rcases family_descends (prefixWord ++ tailWord_442994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443018 : List Nat := [3, 1, 2, 3, 3, 2, 1, 3, 2]
def baseStart_443018 : Nat := 118140960795 + 443018 * 2 ^ 59
def prefixEnd_443018 : Nat := 4983230072969 + 3 ^ 40 * 443018 * 2
def baseEnd_443018 : Nat := 202205486749913709988981

theorem tailTrace_443018 : CollatzResearch.WordTrace tailWord_443018 prefixEnd_443018 202205486749913709988981 := by
  unfold tailWord_443018
  simp only [CollatzResearch.WordTrace]
  refine ⟨4039548477257230573948427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10772129272685948197195805 4039548477257230573948427)
  ·
    refine ⟨6059322715885845860922641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4039548477257230573948427 6059322715885845860922641)
    ·
      refine ⟨4544492036914384395691981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6059322715885845860922641 4544492036914384395691981)
      ·
        refine ⟨1704184513842894148384493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4544492036914384395691981 1704184513842894148384493)
        ·
          refine ⟨639069192691085305644185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1704184513842894148384493 639069192691085305644185)
          ·
            refine ⟨479301894518313979233139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 639069192691085305644185 479301894518313979233139)
            ·
              refine ⟨718952841777470968849709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 479301894518313979233139 718952841777470968849709)
              ·
                refine ⟨269607315666551613318641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 718952841777470968849709 269607315666551613318641)
                ·
                  refine ⟨202205486749913709988981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 269607315666551613318641 202205486749913709988981)
                  ·
                    rfl

theorem cell20_443018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 3, 2].length) (baseStart_443018 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_443018 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_443018 prefixEnd_443018 := by exact prefixLift 443018
  have htrace : WordTrace (prefixWord ++ tailWord_443018) baseStart_443018 baseEnd_443018 := by
    simpa [prefixWord, tailWord_443018, baseEnd_443018] using wordTrace_append hprefix tailTrace_443018
  have hstable : (prefixWord ++ tailWord_443018).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443018).length < 2 ^ (prefixWord ++ tailWord_443018).sum := by decide
  have hdescent : baseEnd_443018 < baseStart_443018 := by decide
  rcases family_descends (prefixWord ++ tailWord_443018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443036 : List Nat := [2, 2, 3, 2, 2, 1, 2, 1, 5]
def baseStart_443036 : Nat := 118140960795 + 443036 * 2 ^ 59
def prefixEnd_443036 : Nat := 4983230072969 + 3 ^ 40 * 443036 * 2
def baseEnd_443036 : Nat := 202213702440385647388907

theorem tailTrace_443036 : CollatzResearch.WordTrace tailWord_443036 prefixEnd_443036 202213702440385647388907 := by
  unfold tailWord_443036
  simp only [CollatzResearch.WordTrace]
  refine ⟨8079425211481855684974481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10772566948642474246632641 8079425211481855684974481)
  ·
    refine ⟨6059568908611391763730861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8079425211481855684974481 6059568908611391763730861)
    ·
      refine ⟨2272338340729271911399073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6059568908611391763730861 2272338340729271911399073)
      ·
        refine ⟨1704253755546953933549305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2272338340729271911399073 1704253755546953933549305)
        ·
          refine ⟨1278190316660215450161979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1704253755546953933549305 1278190316660215450161979)
          ·
            refine ⟨1917285474990323175242969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1278190316660215450161979 1917285474990323175242969)
            ·
              refine ⟨1437964106242742381432227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1917285474990323175242969 1437964106242742381432227)
              ·
                refine ⟨2156946159364113572148341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1437964106242742381432227 2156946159364113572148341)
                ·
                  refine ⟨202213702440385647388907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2156946159364113572148341 202213702440385647388907)
                  ·
                    rfl

theorem cell20_443036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_443036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_443036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_443036 prefixEnd_443036 := by exact prefixLift 443036
  have htrace : WordTrace (prefixWord ++ tailWord_443036) baseStart_443036 baseEnd_443036 := by
    simpa [prefixWord, tailWord_443036, baseEnd_443036] using wordTrace_append hprefix tailTrace_443036
  have hstable : (prefixWord ++ tailWord_443036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443036).length < 2 ^ (prefixWord ++ tailWord_443036).sum := by decide
  have hdescent : baseEnd_443036 < baseStart_443036 := by decide
  rcases family_descends (prefixWord ++ tailWord_443036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443053 : List Nat := [1, 5, 2, 1, 1, 3, 1, 3, 3]
def baseStart_443053 : Nat := 118140960795 + 443053 * 2 ^ 59
def prefixEnd_443053 : Nat := 4983230072969 + 3 ^ 40 * 443053 * 2
def baseEnd_443053 : Nat := 202221461703609143822171

theorem tailTrace_443053 : CollatzResearch.WordTrace tailWord_443053 prefixEnd_443053 202221461703609143822171 := by
  unfold tailWord_443053
  simp only [CollatzResearch.WordTrace]
  refine ⟨16159470463902123273317813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10772980309268082182211875 16159470463902123273317813)
  ·
    refine ⟨1514950355990824056873545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16159470463902123273317813 1514950355990824056873545)
    ·
      refine ⟨1136212766993118042655159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1514950355990824056873545 1136212766993118042655159)
      ·
        refine ⟨1704319150489677063982739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1136212766993118042655159 1704319150489677063982739)
        ·
          refine ⟨2556478725734515595974109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1704319150489677063982739 2556478725734515595974109)
          ·
            refine ⟨958679522150443348490291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2556478725734515595974109 958679522150443348490291)
            ·
              refine ⟨1438019283225665022735437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 958679522150443348490291 1438019283225665022735437)
              ·
                refine ⟨539257231209624383525789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1438019283225665022735437 539257231209624383525789)
                ·
                  refine ⟨202221461703609143822171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 539257231209624383525789 202221461703609143822171)
                  ·
                    rfl

theorem cell20_443053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_443053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_443053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_443053 prefixEnd_443053 := by exact prefixLift 443053
  have htrace : WordTrace (prefixWord ++ tailWord_443053) baseStart_443053 baseEnd_443053 := by
    simpa [prefixWord, tailWord_443053, baseEnd_443053] using wordTrace_append hprefix tailTrace_443053
  have hstable : (prefixWord ++ tailWord_443053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443053).length < 2 ^ (prefixWord ++ tailWord_443053).sum := by decide
  have hdescent : baseEnd_443053 < baseStart_443053 := by decide
  rcases family_descends (prefixWord ++ tailWord_443053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443098 : List Nat := [3, 1, 1, 2, 2, 2, 3, 4, 2]
def baseStart_443098 : Nat := 118140960795 + 443098 * 2 ^ 59
def prefixEnd_443098 : Nat := 4983230072969 + 3 ^ 40 * 443098 * 2
def baseEnd_443098 : Nat := 202242000929788987321987

theorem tailTrace_443098 : CollatzResearch.WordTrace tailWord_443098 prefixEnd_443098 202242000929788987321987 := by
  unfold tailWord_443098
  simp only [CollatzResearch.WordTrace]
  refine ⟨4040277937184773989676487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10774074499159397305803965 4040277937184773989676487)
  ·
    refine ⟨6060416905777160984514731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4040277937184773989676487 6060416905777160984514731)
    ·
      refine ⟨9090625358665741476772097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6060416905777160984514731 9090625358665741476772097)
      ·
        refine ⟨6817969018999306107579073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9090625358665741476772097 6817969018999306107579073)
        ·
          refine ⟨5113476764249479580684305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6817969018999306107579073 5113476764249479580684305)
          ·
            refine ⟨3835107573187109685513229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5113476764249479580684305 3835107573187109685513229)
            ·
              refine ⟨1438165339945166132067461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3835107573187109685513229 1438165339945166132067461)
              ·
                refine ⟨269656001239718649762649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1438165339945166132067461 269656001239718649762649)
                ·
                  refine ⟨202242000929788987321987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 269656001239718649762649 202242000929788987321987)
                  ·
                    rfl

theorem cell20_443098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 4, 2].length) (baseStart_443098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_443098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_443098 prefixEnd_443098 := by exact prefixLift 443098
  have htrace : WordTrace (prefixWord ++ tailWord_443098) baseStart_443098 baseEnd_443098 := by
    simpa [prefixWord, tailWord_443098, baseEnd_443098] using wordTrace_append hprefix tailTrace_443098
  have hstable : (prefixWord ++ tailWord_443098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443098).length < 2 ^ (prefixWord ++ tailWord_443098).sum := by decide
  have hdescent : baseEnd_443098 < baseStart_443098 := by decide
  rcases family_descends (prefixWord ++ tailWord_443098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443105 : List Nat := [1, 2, 3, 1, 4, 3, 1, 5]
def baseStart_443105 : Nat := 118140960795 + 443105 * 2 ^ 59
def prefixEnd_443105 : Nat := 4983230072969 + 3 ^ 40 * 443105 * 2
def baseEnd_443105 : Nat := 67415065306842691362875

theorem tailTrace_443105 : CollatzResearch.WordTrace tailWord_443105 prefixEnd_443105 67415065306842691362875 := by
  unfold tailWord_443105
  simp only [CollatzResearch.WordTrace]
  refine ⟨16161367059713736154210769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10774244706475824102807179 16161367059713736154210769)
  ·
    refine ⟨12121025294785302115658077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16161367059713736154210769 12121025294785302115658077)
    ·
      refine ⟨4545384485544488293371779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12121025294785302115658077 4545384485544488293371779)
      ·
        refine ⟨6818076728316732440057669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4545384485544488293371779 6818076728316732440057669)
        ·
          refine ⟨1278389386559387332510813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6818076728316732440057669 1278389386559387332510813)
          ·
            refine ⟨479396019959770249691555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1278389386559387332510813 479396019959770249691555)
            ·
              refine ⟨719094029939655374537333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 479396019959770249691555 719094029939655374537333)
              ·
                refine ⟨67415065306842691362875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 719094029939655374537333 67415065306842691362875)
                ·
                  rfl

theorem cell20_443105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 5].length) (baseStart_443105 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_443105 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_443105 prefixEnd_443105 := by exact prefixLift 443105
  have htrace : WordTrace (prefixWord ++ tailWord_443105) baseStart_443105 baseEnd_443105 := by
    simpa [prefixWord, tailWord_443105, baseEnd_443105] using wordTrace_append hprefix tailTrace_443105
  have hstable : (prefixWord ++ tailWord_443105).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443105).length < 2 ^ (prefixWord ++ tailWord_443105).sum := by decide
  have hdescent : baseEnd_443105 < baseStart_443105 := by decide
  rcases family_descends (prefixWord ++ tailWord_443105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443119 : List Nat := [1, 1, 2, 1, 5, 3, 1, 2, 4]
def baseStart_443119 : Nat := 118140960795 + 443119 * 2 ^ 59
def prefixEnd_443119 : Nat := 4983230072969 + 3 ^ 40 * 443119 * 2
def baseEnd_443119 : Nat := 202251585902006247621901

theorem tailTrace_443119 : CollatzResearch.WordTrace tailWord_443119 prefixEnd_443119 202251585902006247621901 := by
  unfold tailWord_443119
  simp only [CollatzResearch.WordTrace]
  refine ⟨16161877681663016545220411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10774585121108677696813607 16161877681663016545220411)
  ·
    refine ⟨24242816522494524817830617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16161877681663016545220411 24242816522494524817830617)
    ·
      refine ⟨18182112391870893613372963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24242816522494524817830617 18182112391870893613372963)
      ·
        refine ⟨27273168587806340420059445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18182112391870893613372963 27273168587806340420059445)
        ·
          refine ⟨2556859555106844414380573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27273168587806340420059445 2556859555106844414380573)
          ·
            refine ⟨958822333165066655392715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2556859555106844414380573 958822333165066655392715)
            ·
              refine ⟨1438233499747599983089073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 958822333165066655392715 1438233499747599983089073)
              ·
                refine ⟨1078675124810699987316805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1438233499747599983089073 1078675124810699987316805)
                ·
                  refine ⟨202251585902006247621901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1078675124810699987316805 202251585902006247621901)
                  ·
                    rfl

theorem cell20_443119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 4].length) (baseStart_443119 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_443119 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_443119 prefixEnd_443119 := by exact prefixLift 443119
  have htrace : WordTrace (prefixWord ++ tailWord_443119) baseStart_443119 baseEnd_443119 := by
    simpa [prefixWord, tailWord_443119, baseEnd_443119] using wordTrace_append hprefix tailTrace_443119
  have hstable : (prefixWord ++ tailWord_443119).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443119).length < 2 ^ (prefixWord ++ tailWord_443119).sum := by decide
  have hdescent : baseEnd_443119 < baseStart_443119 := by decide
  rcases family_descends (prefixWord ++ tailWord_443119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443133 : List Nat := [1, 4, 1, 1, 1, 1, 4, 2, 5]
def baseStart_443133 : Nat := 118140960795 + 443133 * 2 ^ 59
def prefixEnd_443133 : Nat := 4983230072969 + 3 ^ 40 * 443133 * 2
def baseEnd_443133 : Nat := 202257975883484421155177

theorem tailTrace_443133 : CollatzResearch.WordTrace tailWord_443133 prefixEnd_443133 202257975883484421155177 := by
  unfold tailWord_443133
  simp only [CollatzResearch.WordTrace]
  refine ⟨16162388303612296936230053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10774925535741531290820035 16162388303612296936230053)
  ·
    refine ⟨3030447806927305675543135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16162388303612296936230053 3030447806927305675543135)
    ·
      refine ⟨4545671710390958513314703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3030447806927305675543135 4545671710390958513314703)
      ·
        refine ⟨6818507565586437769972055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4545671710390958513314703 6818507565586437769972055)
        ·
          refine ⟨10227761348379656654958083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6818507565586437769972055 10227761348379656654958083)
          ·
            refine ⟨15341642022569484982437125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10227761348379656654958083 15341642022569484982437125)
            ·
              refine ⟨2876557879231778434206961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15341642022569484982437125 2876557879231778434206961)
              ·
                refine ⟨2157418409423833825655221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2876557879231778434206961 2157418409423833825655221)
                ·
                  refine ⟨202257975883484421155177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2157418409423833825655221 202257975883484421155177)
                  ·
                    rfl

theorem cell20_443133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_443133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_443133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_443133 prefixEnd_443133 := by exact prefixLift 443133
  have htrace : WordTrace (prefixWord ++ tailWord_443133) baseStart_443133 baseEnd_443133 := by
    simpa [prefixWord, tailWord_443133, baseEnd_443133] using wordTrace_append hprefix tailTrace_443133
  have hstable : (prefixWord ++ tailWord_443133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443133).length < 2 ^ (prefixWord ++ tailWord_443133).sum := by decide
  have hdescent : baseEnd_443133 < baseStart_443133 := by decide
  rcases family_descends (prefixWord ++ tailWord_443133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443157 : List Nat := [1, 3, 2, 1, 2, 2, 4, 1, 4]
def baseStart_443157 : Nat := 118140960795 + 443157 * 2 ^ 59
def prefixEnd_443157 : Nat := 4983230072969 + 3 ^ 40 * 443157 * 2
def baseEnd_443157 : Nat := 202268930137447004355079

theorem tailTrace_443157 : CollatzResearch.WordTrace tailWord_443157 prefixEnd_443157 202268930137447004355079 := by
  unfold tailWord_443157
  simp only [CollatzResearch.WordTrace]
  refine ⟨16163263655525349035103725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10775509103683566023402483 16163263655525349035103725)
  ·
    refine ⟨6061223870822005888163897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16163263655525349035103725 6061223870822005888163897)
    ·
      refine ⟨4545917903116504416122923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6061223870822005888163897 4545917903116504416122923)
      ·
        refine ⟨6818876854674756624184385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4545917903116504416122923 6818876854674756624184385)
        ·
          refine ⟨5114157641006067468138289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6818876854674756624184385 5114157641006067468138289)
          ·
            refine ⟨3835618230754550601103717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5114157641006067468138289 3835618230754550601103717)
            ·
              refine ⟨719178418266478237706947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3835618230754550601103717 719178418266478237706947)
              ·
                refine ⟨1078767627399717356560421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 719178418266478237706947 1078767627399717356560421)
                ·
                  refine ⟨202268930137447004355079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1078767627399717356560421 202268930137447004355079)
                  ·
                    rfl

theorem cell20_443157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_443157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_443157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_443157 prefixEnd_443157 := by exact prefixLift 443157
  have htrace : WordTrace (prefixWord ++ tailWord_443157) baseStart_443157 baseEnd_443157 := by
    simpa [prefixWord, tailWord_443157, baseEnd_443157] using wordTrace_append hprefix tailTrace_443157
  have hstable : (prefixWord ++ tailWord_443157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443157).length < 2 ^ (prefixWord ++ tailWord_443157).sum := by decide
  have hdescent : baseEnd_443157 < baseStart_443157 := by decide
  rcases family_descends (prefixWord ++ tailWord_443157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443167 : List Nat := [1, 1, 2, 4, 2, 3, 3, 1, 3]
def baseStart_443167 : Nat := 118140960795 + 443167 * 2 ^ 59
def prefixEnd_443167 : Nat := 4983230072969 + 3 ^ 40 * 443167 * 2
def baseEnd_443167 : Nat := 202273494409931414021705

theorem tailTrace_443167 : CollatzResearch.WordTrace tailWord_443167 prefixEnd_443167 202273494409931414021705 := by
  unfold tailWord_443167
  simp only [CollatzResearch.WordTrace]
  refine ⟨16163628385489120742967755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10775752256992747161978503 16163628385489120742967755)
  ·
    refine ⟨24245442578233681114451633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16163628385489120742967755 24245442578233681114451633)
    ·
      refine ⟨18184081933675260835838725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24245442578233681114451633 18184081933675260835838725)
      ·
        refine ⟨3409515362564111406719761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18184081933675260835838725 3409515362564111406719761)
        ·
          refine ⟨2557136521923083555039821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3409515362564111406719761 2557136521923083555039821)
          ·
            refine ⟨958926195721156333139933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2557136521923083555039821 958926195721156333139933)
            ·
              refine ⟨359597323395433624927475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 958926195721156333139933 359597323395433624927475)
              ·
                refine ⟨539395985093150437391213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 359597323395433624927475 539395985093150437391213)
                ·
                  refine ⟨202273494409931414021705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 539395985093150437391213 202273494409931414021705)
                  ·
                    rfl

theorem cell20_443167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 1, 3].length) (baseStart_443167 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_443167 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_443167 prefixEnd_443167 := by exact prefixLift 443167
  have htrace : WordTrace (prefixWord ++ tailWord_443167) baseStart_443167 baseEnd_443167 := by
    simpa [prefixWord, tailWord_443167, baseEnd_443167] using wordTrace_append hprefix tailTrace_443167
  have hstable : (prefixWord ++ tailWord_443167).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443167).length < 2 ^ (prefixWord ++ tailWord_443167).sum := by decide
  have hdescent : baseEnd_443167 < baseStart_443167 := by decide
  rcases family_descends (prefixWord ++ tailWord_443167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443198 : List Nat := [4, 2, 1, 2, 4, 1, 6]
def baseStart_443198 : Nat := 118140960795 + 443198 * 2 ^ 59
def prefixEnd_443198 : Nat := 4983230072969 + 3 ^ 40 * 443198 * 2
def baseEnd_443198 : Nat := 22476404850514787109805

theorem tailTrace_443198 : CollatzResearch.WordTrace tailWord_443198 prefixEnd_443198 22476404850514787109805 := by
  unfold tailWord_443198
  simp only [CollatzResearch.WordTrace]
  refine ⟨2020594881047101629668281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10776506032251208691564165 2020594881047101629668281)
  ·
    refine ⟨1515446160785326222251211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2020594881047101629668281 1515446160785326222251211)
    ·
      refine ⟨2273169241177989333376817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1515446160785326222251211 2273169241177989333376817)
      ·
        refine ⟨1704876930883492000032613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2273169241177989333376817 1704876930883492000032613)
        ·
          refine ⟨319664424540654750006115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1704876930883492000032613 319664424540654750006115)
          ·
            refine ⟨479496636810982125009173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319664424540654750006115 479496636810982125009173)
            ·
              refine ⟨22476404850514787109805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 479496636810982125009173 22476404850514787109805)
              ·
                rfl

theorem cell20_443198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 6].length) (baseStart_443198 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_443198 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_443198 prefixEnd_443198 := by exact prefixLift 443198
  have htrace : WordTrace (prefixWord ++ tailWord_443198) baseStart_443198 baseEnd_443198 := by
    simpa [prefixWord, tailWord_443198, baseEnd_443198] using wordTrace_append hprefix tailTrace_443198
  have hstable : (prefixWord ++ tailWord_443198).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443198).length < 2 ^ (prefixWord ++ tailWord_443198).sum := by decide
  have hdescent : baseEnd_443198 < baseStart_443198 := by decide
  rcases family_descends (prefixWord ++ tailWord_443198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443209 : List Nat := [1, 2, 1, 1, 2, 5, 2, 1, 5]
def baseStart_443209 : Nat := 118140960795 + 443209 * 2 ^ 59
def prefixEnd_443209 : Nat := 4983230072969 + 3 ^ 40 * 443209 * 2
def baseEnd_443209 : Nat := 202292664354365934621533

theorem tailTrace_443209 : CollatzResearch.WordTrace tailWord_443209 prefixEnd_443209 202292664354365934621533 := by
  unfold tailWord_443209
  simp only [CollatzResearch.WordTrace]
  refine ⟨16165160251336961915996681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10776773500891307943997787 16165160251336961915996681)
  ·
    refine ⟨12123870188502721436997511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16165160251336961915996681 12123870188502721436997511)
    ·
      refine ⟨18185805282754082155496267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12123870188502721436997511 18185805282754082155496267)
      ·
        refine ⟨27278707924131123233244401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18185805282754082155496267 27278707924131123233244401)
        ·
          refine ⟨20459030943098342424933301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27278707924131123233244401 20459030943098342424933301)
          ·
            refine ⟨1918034150915469602337497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20459030943098342424933301 1918034150915469602337497)
            ·
              refine ⟨1438525613186602201753123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1918034150915469602337497 1438525613186602201753123)
              ·
                refine ⟨2157788419779903302629685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1438525613186602201753123 2157788419779903302629685)
                ·
                  refine ⟨202292664354365934621533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2157788419779903302629685 202292664354365934621533)
                  ·
                    rfl

theorem cell20_443209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 5].length) (baseStart_443209 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_443209 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_443209 prefixEnd_443209 := by exact prefixLift 443209
  have htrace : WordTrace (prefixWord ++ tailWord_443209) baseStart_443209 baseEnd_443209 := by
    simpa [prefixWord, tailWord_443209, baseEnd_443209] using wordTrace_append hprefix tailTrace_443209
  have hstable : (prefixWord ++ tailWord_443209).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443209).length < 2 ^ (prefixWord ++ tailWord_443209).sum := by decide
  have hdescent : baseEnd_443209 < baseStart_443209 := by decide
  rcases family_descends (prefixWord ++ tailWord_443209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443212 : List Nat := [2, 2, 1, 3, 3, 3, 1, 1, 4]
def baseStart_443212 : Nat := 118140960795 + 443212 * 2 ^ 59
def prefixEnd_443212 : Nat := 4983230072969 + 3 ^ 40 * 443212 * 2
def baseEnd_443212 : Nat := 202294033636111257521521

theorem tailTrace_443212 : CollatzResearch.WordTrace tailWord_443212 prefixEnd_443212 202294033636111257521521 := by
  unfold tailWord_443212
  simp only [CollatzResearch.WordTrace]
  refine ⟨8082634835163046714177945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10776846446884062285570593 8082634835163046714177945)
  ·
    refine ⟨6061976126372285035633459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8082634835163046714177945 6061976126372285035633459)
    ·
      refine ⟨9092964189558427553450189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6061976126372285035633459 9092964189558427553450189)
      ·
        refine ⟨3409861571084410332543821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9092964189558427553450189 3409861571084410332543821)
        ·
          refine ⟨1278698089156653874703933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3409861571084410332543821 1278698089156653874703933)
          ·
            refine ⟨479511783433745203013975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1278698089156653874703933 479511783433745203013975)
            ·
              refine ⟨719267675150617804520963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 479511783433745203013975 719267675150617804520963)
              ·
                refine ⟨1078901512725926706781445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 719267675150617804520963 1078901512725926706781445)
                ·
                  refine ⟨202294033636111257521521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1078901512725926706781445 202294033636111257521521)
                  ·
                    rfl

theorem cell20_443212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 4].length) (baseStart_443212 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_443212 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_443212 prefixEnd_443212 := by exact prefixLift 443212
  have htrace : WordTrace (prefixWord ++ tailWord_443212) baseStart_443212 baseEnd_443212 := by
    simpa [prefixWord, tailWord_443212, baseEnd_443212] using wordTrace_append hprefix tailTrace_443212
  have hstable : (prefixWord ++ tailWord_443212).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443212).length < 2 ^ (prefixWord ++ tailWord_443212).sum := by decide
  have hdescent : baseEnd_443212 < baseStart_443212 := by decide
  rcases family_descends (prefixWord ++ tailWord_443212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443226 : List Nat := [3, 1, 1, 2, 1, 5, 1, 3, 3]
def baseStart_443226 : Nat := 118140960795 + 443226 * 2 ^ 59
def prefixEnd_443226 : Nat := 4983230072969 + 3 ^ 40 * 443226 * 2
def baseEnd_443226 : Nat := 202300423617589431054797

theorem tailTrace_443226 : CollatzResearch.WordTrace tailWord_443226 prefixEnd_443226 202300423617589431054797 := by
  unfold tailWord_443226
  simp only [CollatzResearch.WordTrace]
  refine ⟨4041445073068843454841383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10777186861516915879577021 4041445073068843454841383)
  ·
    refine ⟨6062167609603265182262075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4041445073068843454841383 6062167609603265182262075)
    ·
      refine ⟨9093251414404897773393113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6062167609603265182262075 9093251414404897773393113)
      ·
        refine ⟨6819938560803673330044835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9093251414404897773393113 6819938560803673330044835)
        ·
          refine ⟨10229907841205509995067253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6819938560803673330044835 10229907841205509995067253)
          ·
            refine ⟨959053860113016562037555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10229907841205509995067253 959053860113016562037555)
            ·
              refine ⟨1438580790169524843056333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 959053860113016562037555 1438580790169524843056333)
              ·
                refine ⟨539467796313571816146125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1438580790169524843056333 539467796313571816146125)
                ·
                  refine ⟨202300423617589431054797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 539467796313571816146125 202300423617589431054797)
                  ·
                    rfl

theorem cell20_443226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 3, 3].length) (baseStart_443226 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_443226 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_443226 prefixEnd_443226 := by exact prefixLift 443226
  have htrace : WordTrace (prefixWord ++ tailWord_443226) baseStart_443226 baseEnd_443226 := by
    simpa [prefixWord, tailWord_443226, baseEnd_443226] using wordTrace_append hprefix tailTrace_443226
  have hstable : (prefixWord ++ tailWord_443226).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443226).length < 2 ^ (prefixWord ++ tailWord_443226).sum := by decide
  have hdescent : baseEnd_443226 < baseStart_443226 := by decide
  rcases family_descends (prefixWord ++ tailWord_443226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443240 : List Nat := [2, 1, 4, 2, 1, 2, 2, 6]
def baseStart_443240 : Nat := 118140960795 + 443240 * 2 ^ 59
def prefixEnd_443240 : Nat := 4983230072969 + 3 ^ 40 * 443240 * 2
def baseEnd_443240 : Nat := 67435604533022534862691

theorem tailTrace_443240 : CollatzResearch.WordTrace tailWord_443240 prefixEnd_443240 67435604533022534862691 := by
  unfold tailWord_443240
  simp only [CollatzResearch.WordTrace]
  refine ⟨8083145457112327105187587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10777527276149769473583449 8083145457112327105187587)
  ·
    refine ⟨12124718185668490657781381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8083145457112327105187587 12124718185668490657781381)
    ·
      refine ⟨2273384659812841998334009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12124718185668490657781381 2273384659812841998334009)
      ·
        refine ⟨1705038494859631498750507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2273384659812841998334009 1705038494859631498750507)
        ·
          refine ⟨2557557742289447248125761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1705038494859631498750507 2557557742289447248125761)
          ·
            refine ⟨1918168306717085436094321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2557557742289447248125761 1918168306717085436094321)
            ·
              refine ⟨1438626230037814077070741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1918168306717085436094321 1438626230037814077070741)
              ·
                refine ⟨67435604533022534862691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1438626230037814077070741 67435604533022534862691)
                ·
                  rfl

theorem cell20_443240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 6].length) (baseStart_443240 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_443240 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_443240 prefixEnd_443240 := by exact prefixLift 443240
  have htrace : WordTrace (prefixWord ++ tailWord_443240) baseStart_443240 baseEnd_443240 := by
    simpa [prefixWord, tailWord_443240, baseEnd_443240] using wordTrace_append hprefix tailTrace_443240
  have hstable : (prefixWord ++ tailWord_443240).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443240).length < 2 ^ (prefixWord ++ tailWord_443240).sum := by decide
  have hdescent : baseEnd_443240 < baseStart_443240 := by decide
  rcases family_descends (prefixWord ++ tailWord_443240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443295 : List Nat := [1, 1, 2, 5, 2, 2, 3, 4]
def baseStart_443295 : Nat := 118140960795 + 443295 * 2 ^ 59
def prefixEnd_443295 : Nat := 4983230072969 + 3 ^ 40 * 443295 * 2
def baseEnd_443295 : Nat := 67443972365910619251505

theorem tailTrace_443295 : CollatzResearch.WordTrace tailWord_443295 prefixEnd_443295 67443972365910619251505 := by
  unfold tailWord_443295
  simp only [CollatzResearch.WordTrace]
  refine ⟨16168296929025398603627339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10778864619350265735751559 16168296929025398603627339)
  ·
    refine ⟨24252445393538097905441009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16168296929025398603627339 24252445393538097905441009)
    ·
      refine ⟨18189334045153573429080757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24252445393538097905441009 18189334045153573429080757)
      ·
        refine ⟨1705250066733147508976321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18189334045153573429080757 1705250066733147508976321)
        ·
          refine ⟨1278937550049860631732241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1705250066733147508976321 1278937550049860631732241)
          ·
            refine ⟨959203162537395473799181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1278937550049860631732241 959203162537395473799181)
            ·
              refine ⟨359701185951523302674693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 959203162537395473799181 359701185951523302674693)
              ·
                refine ⟨67443972365910619251505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 359701185951523302674693 67443972365910619251505)
                ·
                  rfl

theorem cell20_443295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 4].length) (baseStart_443295 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_443295 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_443295 prefixEnd_443295 := by exact prefixLift 443295
  have htrace : WordTrace (prefixWord ++ tailWord_443295) baseStart_443295 baseEnd_443295 := by
    simpa [prefixWord, tailWord_443295, baseEnd_443295] using wordTrace_append hprefix tailTrace_443295
  have hstable : (prefixWord ++ tailWord_443295).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443295).length < 2 ^ (prefixWord ++ tailWord_443295).sum := by decide
  have hdescent : baseEnd_443295 < baseStart_443295 := by decide
  rcases family_descends (prefixWord ++ tailWord_443295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443299 : List Nat := [1, 1, 1, 4, 1, 2, 2, 8]
def baseStart_443299 : Nat := 118140960795 + 443299 * 2 ^ 59
def prefixEnd_443299 : Nat := 4983230072969 + 3 ^ 40 * 443299 * 2
def baseEnd_443299 : Nat := 67444580935575207207055

theorem tailTrace_443299 : CollatzResearch.WordTrace tailWord_443299 prefixEnd_443299 67444580935575207207055 := by
  unfold tailWord_443299
  simp only [CollatzResearch.WordTrace]
  refine ⟨16168442821010907286772951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10778961880673938191181967 16168442821010907286772951)
  ·
    refine ⟨24252664231516360930159427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16168442821010907286772951 24252664231516360930159427)
    ·
      refine ⟨36378996347274541395239141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24252664231516360930159427 36378996347274541395239141)
      ·
        refine ⟨6821061815113976511607339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36378996347274541395239141 6821061815113976511607339)
        ·
          refine ⟨10231592722670964767411009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6821061815113976511607339 10231592722670964767411009)
          ·
            refine ⟨7673694542003223575558257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10231592722670964767411009 7673694542003223575558257)
            ·
              refine ⟨5755270906502417681668693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7673694542003223575558257 5755270906502417681668693)
              ·
                refine ⟨67444580935575207207055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5755270906502417681668693 67444580935575207207055)
                ·
                  rfl

theorem cell20_443299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 8].length) (baseStart_443299 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_443299 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_443299 prefixEnd_443299 := by exact prefixLift 443299
  have htrace : WordTrace (prefixWord ++ tailWord_443299) baseStart_443299 baseEnd_443299 := by
    simpa [prefixWord, tailWord_443299, baseEnd_443299] using wordTrace_append hprefix tailTrace_443299
  have hstable : (prefixWord ++ tailWord_443299).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443299).length < 2 ^ (prefixWord ++ tailWord_443299).sum := by decide
  have hdescent : baseEnd_443299 < baseStart_443299 := by decide
  rcases family_descends (prefixWord ++ tailWord_443299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443326 : List Nat := [4, 2, 1, 1, 1, 2, 1, 6, 2]
def baseStart_443326 : Nat := 118140960795 + 443326 * 2 ^ 59
def prefixEnd_443326 : Nat := 4983230072969 + 3 ^ 40 * 443326 * 2
def baseEnd_443326 : Nat := 202346066342433527721055

theorem tailTrace_443326 : CollatzResearch.WordTrace tailWord_443326 prefixEnd_443326 202346066342433527721055 := by
  unfold tailWord_443326
  simp only [CollatzResearch.WordTrace]
  refine ⟨2021178448989136362250729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10779618394608727265337221 2021178448989136362250729)
  ·
    refine ⟨1515883836741852271688047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2021178448989136362250729 1515883836741852271688047)
    ·
      refine ⟨2273825755112778407532071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1515883836741852271688047 2273825755112778407532071)
      ·
        refine ⟨3410738632669167611298107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2273825755112778407532071 3410738632669167611298107)
        ·
          refine ⟨5116107949003751416947161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3410738632669167611298107 5116107949003751416947161)
          ·
            refine ⟨3837080961752813562710371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5116107949003751416947161 3837080961752813562710371)
            ·
              refine ⟨5755621442629220344065557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3837080961752813562710371 5755621442629220344065557)
              ·
                refine ⟨269794755123244703628073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5755621442629220344065557 269794755123244703628073)
                ·
                  refine ⟨202346066342433527721055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 269794755123244703628073 202346066342433527721055)
                  ·
                    rfl

theorem cell20_443326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_443326 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_443326 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_443326 prefixEnd_443326 := by exact prefixLift 443326
  have htrace : WordTrace (prefixWord ++ tailWord_443326) baseStart_443326 baseEnd_443326 := by
    simpa [prefixWord, tailWord_443326, baseEnd_443326] using wordTrace_append hprefix tailTrace_443326
  have hstable : (prefixWord ++ tailWord_443326).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443326).length < 2 ^ (prefixWord ++ tailWord_443326).sum := by decide
  have hdescent : baseEnd_443326 < baseStart_443326 := by decide
  rcases family_descends (prefixWord ++ tailWord_443326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443350 : List Nat := [5, 2, 1, 1, 2, 1, 4, 4]
def baseStart_443350 : Nat := 118140960795 + 443350 * 2 ^ 59
def prefixEnd_443350 : Nat := 4983230072969 + 3 ^ 40 * 443350 * 2
def baseEnd_443350 : Nat := 67452340198798703640319

theorem tailTrace_443350 : CollatzResearch.WordTrace tailWord_443350 prefixEnd_443350 67452340198798703640319 := by
  unfold tailWord_443350
  simp only [CollatzResearch.WordTrace]
  refine ⟨1010643933989133937304969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10780201962550761997919669 1010643933989133937304969)
  ·
    refine ⟨757982950491850452978727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1010643933989133937304969 757982950491850452978727)
    ·
      refine ⟨1136974425737775679468091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 757982950491850452978727 1136974425737775679468091)
      ·
        refine ⟨1705461638606663519202137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1136974425737775679468091 1705461638606663519202137)
        ·
          refine ⟨1279096228954997639401603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1705461638606663519202137 1279096228954997639401603)
          ·
            refine ⟨1918644343432496459102405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1279096228954997639401603 1918644343432496459102405)
            ·
              refine ⟨359745814393593086081701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1918644343432496459102405 359745814393593086081701)
              ·
                refine ⟨67452340198798703640319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 359745814393593086081701 67452340198798703640319)
                ·
                  rfl

theorem cell20_443350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_443350 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_443350 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_443350 prefixEnd_443350 := by exact prefixLift 443350
  have htrace : WordTrace (prefixWord ++ tailWord_443350) baseStart_443350 baseEnd_443350 := by
    simpa [prefixWord, tailWord_443350, baseEnd_443350] using wordTrace_append hprefix tailTrace_443350
  have hstable : (prefixWord ++ tailWord_443350).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443350).length < 2 ^ (prefixWord ++ tailWord_443350).sum := by decide
  have hdescent : baseEnd_443350 < baseStart_443350 := by decide
  rcases family_descends (prefixWord ++ tailWord_443350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443354 : List Nat := [3, 1, 1, 2, 4, 2, 1, 6]
def baseStart_443354 : Nat := 118140960795 + 443354 * 2 ^ 59
def prefixEnd_443354 : Nat := 4983230072969 + 3 ^ 40 * 443354 * 2
def baseEnd_443354 : Nat := 67452948768463291595869

theorem tailTrace_443354 : CollatzResearch.WordTrace tailWord_443354 prefixEnd_443354 67452948768463291595869 := by
  unfold tailWord_443354
  simp only [CollatzResearch.WordTrace]
  refine ⟨4042612208952912920006279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10780299223874434453350077 4042612208952912920006279)
  ·
    refine ⟨6063918313429369380009419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4042612208952912920006279 6063918313429369380009419)
    ·
      refine ⟨9095877470144054070014129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6063918313429369380009419 9095877470144054070014129)
      ·
        refine ⟨6821908102608040552510597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9095877470144054070014129 6821908102608040552510597)
        ·
          refine ⟨1279107769239007603595737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6821908102608040552510597 1279107769239007603595737)
          ·
            refine ⟨959330826929255702696803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1279107769239007603595737 959330826929255702696803)
            ·
              refine ⟨1438996240393883554045205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 959330826929255702696803 1438996240393883554045205)
              ·
                refine ⟨67452948768463291595869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1438996240393883554045205 67452948768463291595869)
                ·
                  rfl

theorem cell20_443354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 6].length) (baseStart_443354 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_443354 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_443354 prefixEnd_443354 := by exact prefixLift 443354
  have htrace : WordTrace (prefixWord ++ tailWord_443354) baseStart_443354 baseEnd_443354 := by
    simpa [prefixWord, tailWord_443354, baseEnd_443354] using wordTrace_append hprefix tailTrace_443354
  have hstable : (prefixWord ++ tailWord_443354).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443354).length < 2 ^ (prefixWord ++ tailWord_443354).sum := by decide
  have hdescent : baseEnd_443354 < baseStart_443354 := by decide
  rcases family_descends (prefixWord ++ tailWord_443354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443368 : List Nat := [2, 1, 4, 1, 1, 1, 2, 2, 6]
def baseStart_443368 : Nat := 118140960795 + 443368 * 2 ^ 59
def prefixEnd_443368 : Nat := 4983230072969 + 3 ^ 40 * 443368 * 2
def baseEnd_443368 : Nat := 202365236286868048320883

theorem tailTrace_443368 : CollatzResearch.WordTrace tailWord_443368 prefixEnd_443368 202365236286868048320883 := by
  unfold tailWord_443368
  simp only [CollatzResearch.WordTrace]
  refine ⟨8085479728880466035517379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10780639638507288047356505 8085479728880466035517379)
  ·
    refine ⟨12128219593320699053276069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8085479728880466035517379 12128219593320699053276069)
    ·
      refine ⟨2274041173747631072489263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12128219593320699053276069 2274041173747631072489263)
      ·
        refine ⟨3411061760621446608733895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2274041173747631072489263 3411061760621446608733895)
        ·
          refine ⟨5116592640932169913100843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3411061760621446608733895 5116592640932169913100843)
          ·
            refine ⟨7674888961398254869651265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5116592640932169913100843 7674888961398254869651265)
            ·
              refine ⟨5756166721048691152238449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7674888961398254869651265 5756166721048691152238449)
              ·
                refine ⟨4317125040786518364178837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5756166721048691152238449 4317125040786518364178837)
                ·
                  refine ⟨202365236286868048320883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4317125040786518364178837 202365236286868048320883)
                  ·
                    rfl

theorem cell20_443368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 6].length) (baseStart_443368 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_443368 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_443368 prefixEnd_443368 := by exact prefixLift 443368
  have htrace : WordTrace (prefixWord ++ tailWord_443368) baseStart_443368 baseEnd_443368 := by
    simpa [prefixWord, tailWord_443368, baseEnd_443368] using wordTrace_append hprefix tailTrace_443368
  have hstable : (prefixWord ++ tailWord_443368).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443368).length < 2 ^ (prefixWord ++ tailWord_443368).sum := by decide
  have hdescent : baseEnd_443368 < baseStart_443368 := by decide
  rcases family_descends (prefixWord ++ tailWord_443368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443375 : List Nat := [1, 1, 2, 1, 4, 3, 8]
def baseStart_443375 : Nat := 118140960795 + 443375 * 2 ^ 59
def prefixEnd_443375 : Nat := 4983230072969 + 3 ^ 40 * 443375 * 2
def baseEnd_443375 : Nat := 22485381253067459454169

theorem tailTrace_443375 : CollatzResearch.WordTrace tailWord_443375 prefixEnd_443375 22485381253067459454169 := by
  unfold tailWord_443375
  simp only [CollatzResearch.WordTrace]
  refine ⟨16171214768735572266539579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10780809845823714844359719 16171214768735572266539579)
  ·
    refine ⟨24256822153103358399809369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16171214768735572266539579 24256822153103358399809369)
    ·
      refine ⟨18192616614827518799857027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24256822153103358399809369 18192616614827518799857027)
      ·
        refine ⟨27288924922241278199785541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18192616614827518799857027 27288924922241278199785541)
        ·
          refine ⟨5116673422920239662459789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27288924922241278199785541 5116673422920239662459789)
          ·
            refine ⟨1918752533595089873422421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5116673422920239662459789 1918752533595089873422421)
            ·
              refine ⟨22485381253067459454169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1918752533595089873422421 22485381253067459454169)
              ·
                rfl

theorem cell20_443375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 8].length) (baseStart_443375 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_443375 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_443375 prefixEnd_443375 := by exact prefixLift 443375
  have htrace : WordTrace (prefixWord ++ tailWord_443375) baseStart_443375 baseEnd_443375 := by
    simpa [prefixWord, tailWord_443375, baseEnd_443375] using wordTrace_append hprefix tailTrace_443375
  have hstable : (prefixWord ++ tailWord_443375).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443375).length < 2 ^ (prefixWord ++ tailWord_443375).sum := by decide
  have hdescent : baseEnd_443375 < baseStart_443375 := by decide
  rcases family_descends (prefixWord ++ tailWord_443375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443485 : List Nat := [1, 4, 4, 1, 2, 1, 7]
def baseStart_443485 : Nat := 118140960795 + 443485 * 2 ^ 59
def prefixEnd_443485 : Nat := 4983230072969 + 3 ^ 40 * 443485 * 2
def baseEnd_443485 : Nat := 22490959808326182380045

theorem tailTrace_443485 : CollatzResearch.WordTrace tailWord_443485 prefixEnd_443485 22490959808326182380045 := by
  unfold tailWord_443485
  simp only [CollatzResearch.WordTrace]
  refine ⟨16175226798337061053043909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10783484532224707368695939 16175226798337061053043909)
  ·
    refine ⟨3032855024688198947445733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16175226798337061053043909 3032855024688198947445733)
    ·
      refine ⟨568660317129037302646075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3032855024688198947445733 568660317129037302646075)
      ·
        refine ⟨852990475693555953969113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 568660317129037302646075 852990475693555953969113)
        ·
          refine ⟨639742856770166965476835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 852990475693555953969113 639742856770166965476835)
          ·
            refine ⟨959614285155250448215253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 639742856770166965476835 959614285155250448215253)
            ·
              refine ⟨22490959808326182380045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 959614285155250448215253 22490959808326182380045)
              ·
                rfl

theorem cell20_443485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 7].length) (baseStart_443485 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_443485 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_443485 prefixEnd_443485 := by exact prefixLift 443485
  have htrace : WordTrace (prefixWord ++ tailWord_443485) baseStart_443485 baseEnd_443485 := by
    simpa [prefixWord, tailWord_443485, baseEnd_443485] using wordTrace_append hprefix tailTrace_443485
  have hstable : (prefixWord ++ tailWord_443485).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443485).length < 2 ^ (prefixWord ++ tailWord_443485).sum := by decide
  have hdescent : baseEnd_443485 < baseStart_443485 := by decide
  rcases family_descends (prefixWord ++ tailWord_443485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443520 : List Nat := [2, 1, 1, 2, 1, 3, 4, 2, 4]
def baseStart_443520 : Nat := 118140960795 + 443520 * 2 ^ 59
def prefixEnd_443520 : Nat := 4983230072969 + 3 ^ 40 * 443520 * 2
def baseEnd_443520 : Nat := 202434613228631075253595

theorem tailTrace_443520 : CollatzResearch.WordTrace tailWord_443520 prefixEnd_443520 202434613228631075253595 := by
  unfold tailWord_443520
  simp only [CollatzResearch.WordTrace]
  refine ⟨8088251676605131015284007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10784335568806841353712009 8088251676605131015284007)
  ·
    refine ⟨12132377514907696522926011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8088251676605131015284007 12132377514907696522926011)
    ·
      refine ⟨18198566272361544784389017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12132377514907696522926011 18198566272361544784389017)
      ·
        refine ⟨13648924704271158588291763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18198566272361544784389017 13648924704271158588291763)
        ·
          refine ⟨20473387056406737882437645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13648924704271158588291763 20473387056406737882437645)
          ·
            refine ⟨7677520146152526705914117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20473387056406737882437645 7677520146152526705914117)
            ·
              refine ⟨1439535027403598757358897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7677520146152526705914117 1439535027403598757358897)
              ·
                refine ⟨1079651270552699068019173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1439535027403598757358897 1079651270552699068019173)
                ·
                  refine ⟨202434613228631075253595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1079651270552699068019173 202434613228631075253595)
                  ·
                    rfl

theorem cell20_443520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 4].length) (baseStart_443520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_443520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_443520 prefixEnd_443520 := by exact prefixLift 443520
  have htrace : WordTrace (prefixWord ++ tailWord_443520) baseStart_443520 baseEnd_443520 := by
    simpa [prefixWord, tailWord_443520, baseEnd_443520] using wordTrace_append hprefix tailTrace_443520
  have hstable : (prefixWord ++ tailWord_443520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443520).length < 2 ^ (prefixWord ++ tailWord_443520).sum := by decide
  have hdescent : baseEnd_443520 < baseStart_443520 := by decide
  rcases family_descends (prefixWord ++ tailWord_443520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443544 : List Nat := [2, 1, 2, 4, 2, 3, 6]
def baseStart_443544 : Nat := 118140960795 + 443544 * 2 ^ 59
def prefixEnd_443544 : Nat := 4983230072969 + 3 ^ 40 * 443544 * 2
def baseEnd_443544 : Nat := 22493951942510406494833

theorem tailTrace_443544 : CollatzResearch.WordTrace tailWord_443544 prefixEnd_443544 22493951942510406494833 := by
  unfold tailWord_443544
  simp only [CollatzResearch.WordTrace]
  refine ⟨8088689352561657064720843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10784919136748876086294457 8088689352561657064720843)
  ·
    refine ⟨12133034028842485597081265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8088689352561657064720843 12133034028842485597081265)
    ·
      refine ⟨9099775521631864197810949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12133034028842485597081265 9099775521631864197810949)
      ·
        refine ⟨1706207910305974537089553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9099775521631864197810949 1706207910305974537089553)
        ·
          refine ⟨1279655932729480902817165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1706207910305974537089553 1279655932729480902817165)
          ·
            refine ⟨479870974773555338556437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1279655932729480902817165 479870974773555338556437)
            ·
              refine ⟨22493951942510406494833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 479870974773555338556437 22493951942510406494833)
              ·
                rfl

theorem cell20_443544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 6].length) (baseStart_443544 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_443544 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_443544 prefixEnd_443544 := by exact prefixLift 443544
  have htrace : WordTrace (prefixWord ++ tailWord_443544) baseStart_443544 baseEnd_443544 := by
    simpa [prefixWord, tailWord_443544, baseEnd_443544] using wordTrace_append hprefix tailTrace_443544
  have hstable : (prefixWord ++ tailWord_443544).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443544).length < 2 ^ (prefixWord ++ tailWord_443544).sum := by decide
  have hdescent : baseEnd_443544 < baseStart_443544 := by decide
  rcases family_descends (prefixWord ++ tailWord_443544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443550 : List Nat := [4, 3, 1, 1, 2, 2, 3, 2, 2]
def baseStart_443550 : Nat := 118140960795 + 443550 * 2 ^ 59
def prefixEnd_443550 : Nat := 4983230072969 + 3 ^ 40 * 443550 * 2
def baseEnd_443550 : Nat := 202448306046084304253473

theorem tailTrace_443550 : CollatzResearch.WordTrace tailWord_443550 prefixEnd_443550 202448306046084304253473 := by
  unfold tailWord_443550
  simp only [CollatzResearch.WordTrace]
  refine ⟨2022199692887697144270013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10785065028734384769440069 2022199692887697144270013)
  ·
    refine ⟨758324884832886429101255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2022199692887697144270013 758324884832886429101255)
    ·
      refine ⟨1137487327249329643651883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 758324884832886429101255 1137487327249329643651883)
      ·
        refine ⟨1706230990873994465477825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1137487327249329643651883 1706230990873994465477825)
        ·
          refine ⟨1279673243155495849108369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1706230990873994465477825 1279673243155495849108369)
          ·
            refine ⟨959754932366621886831277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1279673243155495849108369 959754932366621886831277)
            ·
              refine ⟨359908099637483207561729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 959754932366621886831277 359908099637483207561729)
              ·
                refine ⟨269931074728112405671297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 359908099637483207561729 269931074728112405671297)
                ·
                  refine ⟨202448306046084304253473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 269931074728112405671297 202448306046084304253473)
                  ·
                    rfl

theorem cell20_443550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_443550 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_443550 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_443550 prefixEnd_443550 := by exact prefixLift 443550
  have htrace : WordTrace (prefixWord ++ tailWord_443550) baseStart_443550 baseEnd_443550 := by
    simpa [prefixWord, tailWord_443550, baseEnd_443550] using wordTrace_append hprefix tailTrace_443550
  have hstable : (prefixWord ++ tailWord_443550).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443550).length < 2 ^ (prefixWord ++ tailWord_443550).sum := by decide
  have hdescent : baseEnd_443550 < baseStart_443550 := by decide
  rcases family_descends (prefixWord ++ tailWord_443550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443582 : List Nat := [4, 2, 1, 1, 3, 1, 2, 6]
def baseStart_443582 : Nat := 118140960795 + 443582 * 2 ^ 59
def prefixEnd_443582 : Nat := 4983230072969 + 3 ^ 40 * 443582 * 2
def baseEnd_443582 : Nat := 67487637239344805062225

theorem tailTrace_443582 : CollatzResearch.WordTrace tailWord_443582 prefixEnd_443582 67487637239344805062225 := by
  unfold tailWord_443582
  simp only [CollatzResearch.WordTrace]
  refine ⟨2022345584873205827415625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10785843119323764412883333 2022345584873205827415625)
  ·
    refine ⟨1516759188654904370561719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2022345584873205827415625 1516759188654904370561719)
    ·
      refine ⟨2275138782982356555842579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1516759188654904370561719 2275138782982356555842579)
      ·
        refine ⟨3412708174473534833763869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2275138782982356555842579 3412708174473534833763869)
        ·
          refine ⟨1279765565427575562661451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3412708174473534833763869 1279765565427575562661451)
          ·
            refine ⟨1919648348141363343992177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1279765565427575562661451 1919648348141363343992177)
            ·
              refine ⟨1439736261106022507994133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1919648348141363343992177 1439736261106022507994133)
              ·
                refine ⟨67487637239344805062225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1439736261106022507994133 67487637239344805062225)
                ·
                  rfl

theorem cell20_443582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_443582 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_443582 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_443582 prefixEnd_443582 := by exact prefixLift 443582
  have htrace : WordTrace (prefixWord ++ tailWord_443582) baseStart_443582 baseEnd_443582 := by
    simpa [prefixWord, tailWord_443582, baseEnd_443582] using wordTrace_append hprefix tailTrace_443582
  have hstable : (prefixWord ++ tailWord_443582).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443582).length < 2 ^ (prefixWord ++ tailWord_443582).sum := by decide
  have hdescent : baseEnd_443582 < baseStart_443582 := by decide
  rcases family_descends (prefixWord ++ tailWord_443582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443627 : List Nat := [1, 1, 1, 1, 2, 6, 2, 3, 3]
def baseStart_443627 : Nat := 118140960795 + 443627 * 2 ^ 59
def prefixEnd_443627 : Nat := 4983230072969 + 3 ^ 40 * 443627 * 2
def baseEnd_443627 : Nat := 202483450944214258686491

theorem tailTrace_443627 : CollatzResearch.WordTrace tailWord_443627 prefixEnd_443627 202483450944214258686491 := by
  unfold tailWord_443627
  simp only [CollatzResearch.WordTrace]
  refine ⟨16180405963822619304713135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10786937309215079536475423 16180405963822619304713135)
  ·
    refine ⟨24270608945733928957069703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16180405963822619304713135 24270608945733928957069703)
    ·
      refine ⟨36405913418600893435604555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24270608945733928957069703 36405913418600893435604555)
      ·
        refine ⟨54608870127901340153406833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36405913418600893435604555 54608870127901340153406833)
        ·
          refine ⟨40956652595926005115055125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54608870127901340153406833 40956652595926005115055125)
          ·
            refine ⟨1919843090434031489768209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 40956652595926005115055125 1919843090434031489768209)
            ·
              refine ⟨1439882317825523617326157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1919843090434031489768209 1439882317825523617326157)
              ·
                refine ⟨539955869184571356497309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1439882317825523617326157 539955869184571356497309)
                ·
                  refine ⟨202483450944214258686491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 539955869184571356497309 202483450944214258686491)
                  ·
                    rfl

theorem cell20_443627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 3, 3].length) (baseStart_443627 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_443627 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_443627 prefixEnd_443627 := by exact prefixLift 443627
  have htrace : WordTrace (prefixWord ++ tailWord_443627) baseStart_443627 baseEnd_443627 := by
    simpa [prefixWord, tailWord_443627, baseEnd_443627] using wordTrace_append hprefix tailTrace_443627
  have hstable : (prefixWord ++ tailWord_443627).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443627).length < 2 ^ (prefixWord ++ tailWord_443627).sum := by decide
  have hdescent : baseEnd_443627 < baseStart_443627 := by decide
  rcases family_descends (prefixWord ++ tailWord_443627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443648 : List Nat := [2, 1, 1, 2, 1, 1, 3, 4, 5]
def baseStart_443648 : Nat := 118140960795 + 443648 * 2 ^ 59
def prefixEnd_443648 : Nat := 4983230072969 + 3 ^ 40 * 443648 * 2
def baseEnd_443648 : Nat := 202493035916431518986405

theorem tailTrace_443648 : CollatzResearch.WordTrace tailWord_443648 prefixEnd_443648 202493035916431518986405 := by
  unfold tailWord_443648
  simp only [CollatzResearch.WordTrace]
  refine ⟨8090585948373269945613799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10787447931164359927485065 8090585948373269945613799)
  ·
    refine ⟨12135878922559904918420699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8090585948373269945613799 12135878922559904918420699)
    ·
      refine ⟨18203818383839857377631049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12135878922559904918420699 18203818383839857377631049)
      ·
        refine ⟨13652863787879893033223287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18203818383839857377631049 13652863787879893033223287)
        ·
          refine ⟨20479295681819839549834931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13652863787879893033223287 20479295681819839549834931)
          ·
            refine ⟨30718943522729759324752397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20479295681819839549834931 30718943522729759324752397)
            ·
              refine ⟨11519603821023659746782149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30718943522729759324752397 11519603821023659746782149)
              ·
                refine ⟨2159925716441936202521653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11519603821023659746782149 2159925716441936202521653)
                ·
                  refine ⟨202493035916431518986405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2159925716441936202521653 202493035916431518986405)
                  ·
                    rfl

theorem cell20_443648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 5].length) (baseStart_443648 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_443648 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_443648 prefixEnd_443648 := by exact prefixLift 443648
  have htrace : WordTrace (prefixWord ++ tailWord_443648) baseStart_443648 baseEnd_443648 := by
    simpa [prefixWord, tailWord_443648, baseEnd_443648] using wordTrace_append hprefix tailTrace_443648
  have hstable : (prefixWord ++ tailWord_443648).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443648).length < 2 ^ (prefixWord ++ tailWord_443648).sum := by decide
  have hdescent : baseEnd_443648 < baseStart_443648 := by decide
  rcases family_descends (prefixWord ++ tailWord_443648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443651 : List Nat := [1, 1, 1, 3, 2, 4, 1, 5, 2]
def baseStart_443651 : Nat := 118140960795 + 443651 * 2 ^ 59
def prefixEnd_443651 : Nat := 4983230072969 + 3 ^ 40 * 443651 * 2
def baseEnd_443651 : Nat := 202494405198176841886393

theorem tailTrace_443651 : CollatzResearch.WordTrace tailWord_443651 prefixEnd_443651 202494405198176841886393 := by
  unfold tailWord_443651
  simp only [CollatzResearch.WordTrace]
  refine ⟨16181281315735671403586807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10787520877157114269057871 16181281315735671403586807)
  ·
    refine ⟨24271921973603507105380211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16181281315735671403586807 24271921973603507105380211)
    ·
      refine ⟨36407882960405260658070317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24271921973603507105380211 36407882960405260658070317)
      ·
        refine ⟨13652956110151972746776369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36407882960405260658070317 13652956110151972746776369)
        ·
          refine ⟨10239717082613979560082277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13652956110151972746776369 10239717082613979560082277)
          ·
            refine ⟨1919946952990121167515427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10239717082613979560082277 1919946952990121167515427)
            ·
              refine ⟨2879920429485181751273141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1919946952990121167515427 2879920429485181751273141)
              ·
                refine ⟨269992540264235789181857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2879920429485181751273141 269992540264235789181857)
                ·
                  refine ⟨202494405198176841886393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 269992540264235789181857 202494405198176841886393)
                  ·
                    rfl

theorem cell20_443651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 5, 2].length) (baseStart_443651 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_443651 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_443651 prefixEnd_443651 := by exact prefixLift 443651
  have htrace : WordTrace (prefixWord ++ tailWord_443651) baseStart_443651 baseEnd_443651 := by
    simpa [prefixWord, tailWord_443651, baseEnd_443651] using wordTrace_append hprefix tailTrace_443651
  have hstable : (prefixWord ++ tailWord_443651).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443651).length < 2 ^ (prefixWord ++ tailWord_443651).sum := by decide
  have hdescent : baseEnd_443651 < baseStart_443651 := by decide
  rcases family_descends (prefixWord ++ tailWord_443651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443672 : List Nat := [2, 1, 2, 3, 1, 3, 1, 3, 4]
def baseStart_443672 : Nat := 118140960795 + 443672 * 2 ^ 59
def prefixEnd_443672 : Nat := 4983230072969 + 3 ^ 40 * 443672 * 2
def baseEnd_443672 : Nat := 202503990170394102186307

theorem tailTrace_443672 : CollatzResearch.WordTrace tailWord_443672 prefixEnd_443672 202503990170394102186307 := by
  unfold tailWord_443672
  simp only [CollatzResearch.WordTrace]
  refine ⟨8091023624329795995050635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10788031499106394660067513 8091023624329795995050635)
  ·
    refine ⟨12136535436494693992575953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8091023624329795995050635 12136535436494693992575953)
    ·
      refine ⟨9102401577371020494431965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12136535436494693992575953 9102401577371020494431965)
      ·
        refine ⟨3413400591514132685411987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9102401577371020494431965 3413400591514132685411987)
        ·
          refine ⟨5120100887271199028117981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3413400591514132685411987 5120100887271199028117981)
          ·
            refine ⟨1920037832726699635544243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5120100887271199028117981 1920037832726699635544243)
            ·
              refine ⟨2880056749090049453316365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1920037832726699635544243 2880056749090049453316365)
              ·
                refine ⟨1080021280908768544993637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2880056749090049453316365 1080021280908768544993637)
                ·
                  refine ⟨202503990170394102186307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1080021280908768544993637 202503990170394102186307)
                  ·
                    rfl

theorem cell20_443672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 4].length) (baseStart_443672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_443672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_443672 prefixEnd_443672 := by exact prefixLift 443672
  have htrace : WordTrace (prefixWord ++ tailWord_443672) baseStart_443672 baseEnd_443672 := by
    simpa [prefixWord, tailWord_443672, baseEnd_443672] using wordTrace_append hprefix tailTrace_443672
  have hstable : (prefixWord ++ tailWord_443672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443672).length < 2 ^ (prefixWord ++ tailWord_443672).sum := by decide
  have hdescent : baseEnd_443672 < baseStart_443672 := by decide
  rcases family_descends (prefixWord ++ tailWord_443672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443774 : List Nat := [4, 2, 3, 2, 2, 1, 2, 2, 2]
def baseStart_443774 : Nat := 118140960795 + 443774 * 2 ^ 59
def prefixEnd_443774 : Nat := 4983230072969 + 3 ^ 40 * 443774 * 2
def baseEnd_443774 : Nat := 202550545749735080785891

theorem tailTrace_443774 : CollatzResearch.WordTrace tailWord_443774 prefixEnd_443774 202550545749735080785891 := by
  unfold tailWord_443774
  simp only [CollatzResearch.WordTrace]
  refine ⟨2023220936786257926289297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10790511662860042273542917 2023220936786257926289297)
  ·
    refine ⟨1517415702589693444716973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2023220936786257926289297 1517415702589693444716973)
    ·
      refine ⟨569030888471135041768865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1517415702589693444716973 569030888471135041768865)
      ·
        refine ⟨426773166353351281326649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 569030888471135041768865 426773166353351281326649)
        ·
          refine ⟨320079874765013460994987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 426773166353351281326649 320079874765013460994987)
          ·
            refine ⟨480119812147520191492481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320079874765013460994987 480119812147520191492481)
            ·
              refine ⟨360089859110640143619361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 480119812147520191492481 360089859110640143619361)
              ·
                refine ⟨270067394332980107714521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 360089859110640143619361 270067394332980107714521)
                ·
                  refine ⟨202550545749735080785891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 270067394332980107714521 202550545749735080785891)
                  ·
                    rfl

theorem cell20_443774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_443774 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_443774 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_443774 prefixEnd_443774 := by exact prefixLift 443774
  have htrace : WordTrace (prefixWord ++ tailWord_443774) baseStart_443774 baseEnd_443774 := by
    simpa [prefixWord, tailWord_443774, baseEnd_443774] using wordTrace_append hprefix tailTrace_443774
  have hstable : (prefixWord ++ tailWord_443774).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443774).length < 2 ^ (prefixWord ++ tailWord_443774).sum := by decide
  have hdescent : baseEnd_443774 < baseStart_443774 := by decide
  rcases family_descends (prefixWord ++ tailWord_443774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443778 : List Nat := [3, 4, 2, 1, 1, 1, 4, 2, 2]
def baseStart_443778 : Nat := 118140960795 + 443778 * 2 ^ 59
def prefixEnd_443778 : Nat := 4983230072969 + 3 ^ 40 * 443778 * 2
def baseEnd_443778 : Nat := 202552371458728844652541

theorem tailTrace_443778 : CollatzResearch.WordTrace tailWord_443778 prefixEnd_443778 202552371458728844652541 := by
  unfold tailWord_443778
  simp only [CollatzResearch.WordTrace]
  refine ⟨4046478346568893023364997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10790608924183714728973325 4046478346568893023364997)
  ·
    refine ⟨758714689981667441880937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4046478346568893023364997 758714689981667441880937)
    ·
      refine ⟨569036017486250581410703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 758714689981667441880937 569036017486250581410703)
      ·
        refine ⟨853554026229375872116055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 569036017486250581410703 853554026229375872116055)
        ·
          refine ⟨1280331039344063808174083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 853554026229375872116055 1280331039344063808174083)
          ·
            refine ⟨1920496559016095712261125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1280331039344063808174083 1920496559016095712261125)
            ·
              refine ⟨360093104815517946048961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1920496559016095712261125 360093104815517946048961)
              ·
                refine ⟨270069828611638459536721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 360093104815517946048961 270069828611638459536721)
                ·
                  refine ⟨202552371458728844652541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 270069828611638459536721 202552371458728844652541)
                  ·
                    rfl

theorem cell20_443778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_443778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_443778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_443778 prefixEnd_443778 := by exact prefixLift 443778
  have htrace : WordTrace (prefixWord ++ tailWord_443778) baseStart_443778 baseEnd_443778 := by
    simpa [prefixWord, tailWord_443778, baseEnd_443778] using wordTrace_append hprefix tailTrace_443778
  have hstable : (prefixWord ++ tailWord_443778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443778).length < 2 ^ (prefixWord ++ tailWord_443778).sum := by decide
  have hdescent : baseEnd_443778 < baseStart_443778 := by decide
  rcases family_descends (prefixWord ++ tailWord_443778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443779 : List Nat := [1, 1, 1, 3, 5, 1, 1, 4, 3]
def baseStart_443779 : Nat := 118140960795 + 443779 * 2 ^ 59
def prefixEnd_443779 : Nat := 4983230072969 + 3 ^ 40 * 443779 * 2
def baseEnd_443779 : Nat := 202552827885977285619203

theorem tailTrace_443779 : CollatzResearch.WordTrace tailWord_443779 prefixEnd_443779 202552827885977285619203 := by
  unfold tailWord_443779
  simp only [CollatzResearch.WordTrace]
  refine ⟨16185949859271949264246391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10790633239514632842830927 16185949859271949264246391)
  ·
    refine ⟨24278924788907923896369587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16185949859271949264246391 24278924788907923896369587)
    ·
      refine ⟨36418387183361885844554381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24278924788907923896369587 36418387183361885844554381)
      ·
        refine ⟨13656895193760707191707893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36418387183361885844554381 13656895193760707191707893)
        ·
          refine ⟨1280333924415066299222615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13656895193760707191707893 1280333924415066299222615)
          ·
            refine ⟨1920500886622599448833923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1280333924415066299222615 1920500886622599448833923)
            ·
              refine ⟨2880751329933899173250885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1920500886622599448833923 2880751329933899173250885)
              ·
                refine ⟨540140874362606094984541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2880751329933899173250885 540140874362606094984541)
                ·
                  refine ⟨202552827885977285619203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 540140874362606094984541 202552827885977285619203)
                  ·
                    rfl

theorem cell20_443779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 4, 3].length) (baseStart_443779 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_443779 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_443779 prefixEnd_443779 := by exact prefixLift 443779
  have htrace : WordTrace (prefixWord ++ tailWord_443779) baseStart_443779 baseEnd_443779 := by
    simpa [prefixWord, tailWord_443779, baseEnd_443779] using wordTrace_append hprefix tailTrace_443779
  have hstable : (prefixWord ++ tailWord_443779).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443779).length < 2 ^ (prefixWord ++ tailWord_443779).sum := by decide
  have hdescent : baseEnd_443779 < baseStart_443779 := by decide
  rcases family_descends (prefixWord ++ tailWord_443779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443796 : List Nat := [2, 4, 2, 1, 2, 1, 2, 3, 3]
def baseStart_443796 : Nat := 118140960795 + 443796 * 2 ^ 59
def prefixEnd_443796 : Nat := 4983230072969 + 3 ^ 40 * 443796 * 2
def baseEnd_443796 : Nat := 202560587149200782052467

theorem tailTrace_443796 : CollatzResearch.WordTrace tailWord_443796 prefixEnd_443796 202560587149200782052467 := by
  unfold tailWord_443796
  simp only [CollatzResearch.WordTrace]
  refine ⟨8093284950105180583807621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10791046600140240778410161 8093284950105180583807621)
  ·
    refine ⟨1517490928144721359463929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8093284950105180583807621 1517490928144721359463929)
    ·
      refine ⟨1138118196108541019597947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1517490928144721359463929 1138118196108541019597947)
      ·
        refine ⟨1707177294162811529396921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1138118196108541019597947 1707177294162811529396921)
        ·
          refine ⟨1280382970622108647047691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1707177294162811529396921 1280382970622108647047691)
          ·
            refine ⟨1920574455933162970571537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1280382970622108647047691 1920574455933162970571537)
            ·
              refine ⟨1440430841949872227928653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1920574455933162970571537 1440430841949872227928653)
              ·
                refine ⟨540161565731202085473245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1440430841949872227928653 540161565731202085473245)
                ·
                  refine ⟨202560587149200782052467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 540161565731202085473245 202560587149200782052467)
                  ·
                    rfl

theorem cell20_443796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_443796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_443796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_443796 prefixEnd_443796 := by exact prefixLift 443796
  have htrace : WordTrace (prefixWord ++ tailWord_443796) baseStart_443796 baseEnd_443796 := by
    simpa [prefixWord, tailWord_443796, baseEnd_443796] using wordTrace_append hprefix tailTrace_443796
  have hstable : (prefixWord ++ tailWord_443796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443796).length < 2 ^ (prefixWord ++ tailWord_443796).sum := by decide
  have hdescent : baseEnd_443796 < baseStart_443796 := by decide
  rcases family_descends (prefixWord ++ tailWord_443796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443806 : List Nat := [4, 3, 1, 2, 2, 1, 3, 4]
def baseStart_443806 : Nat := 118140960795 + 443806 * 2 ^ 59
def prefixEnd_443806 : Nat := 4983230072969 + 3 ^ 40 * 443806 * 2
def baseEnd_443806 : Nat := 67521717140561730573031

theorem tailTrace_443806 : CollatzResearch.WordTrace tailWord_443806 prefixEnd_443806 67521717140561730573031 := by
  unfold tailWord_443806
  simp only [CollatzResearch.WordTrace]
  refine ⟨2023366828771766609434909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10791289753449421916986181 2023366828771766609434909)
  ·
    refine ⟨758762560789412478538091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2023366828771766609434909 758762560789412478538091)
    ·
      refine ⟨1138143841184118717807137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 758762560789412478538091 1138143841184118717807137)
      ·
        refine ⟨853607880888089038355353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1138143841184118717807137 853607880888089038355353)
        ·
          refine ⟨640205910666066778766515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 853607880888089038355353 640205910666066778766515)
          ·
            refine ⟨960308865999100168149773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640205910666066778766515 960308865999100168149773)
            ·
              refine ⟨360115824749662563056165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 960308865999100168149773 360115824749662563056165)
              ·
                refine ⟨67521717140561730573031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 360115824749662563056165 67521717140561730573031)
                ·
                  rfl

theorem cell20_443806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_443806 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_443806 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_443806 prefixEnd_443806 := by exact prefixLift 443806
  have htrace : WordTrace (prefixWord ++ tailWord_443806) baseStart_443806 baseEnd_443806 := by
    simpa [prefixWord, tailWord_443806, baseEnd_443806] using wordTrace_append hprefix tailTrace_443806
  have hstable : (prefixWord ++ tailWord_443806).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443806).length < 2 ^ (prefixWord ++ tailWord_443806).sum := by decide
  have hdescent : baseEnd_443806 < baseStart_443806 := by decide
  rcases family_descends (prefixWord ++ tailWord_443806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443896 : List Nat := [2, 1, 2, 1, 1, 6, 3, 2, 2]
def baseStart_443896 : Nat := 118140960795 + 443896 * 2 ^ 59
def prefixEnd_443896 : Nat := 4983230072969 + 3 ^ 40 * 443896 * 2
def baseEnd_443896 : Nat := 202606229874044878718725

theorem tailTrace_443896 : CollatzResearch.WordTrace tailWord_443896 prefixEnd_443896 202606229874044878718725 := by
  unfold tailWord_443896
  simp only [CollatzResearch.WordTrace]
  refine ⟨8095108599924039123127771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10793478133232052164170361 8095108599924039123127771)
  ·
    refine ⟨12142662899886058684691657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8095108599924039123127771 12142662899886058684691657)
    ·
      refine ⟨9106997174914544013518743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12142662899886058684691657 9106997174914544013518743)
      ·
        refine ⟨13660495762371816020278115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9106997174914544013518743 13660495762371816020278115)
        ·
          refine ⟨20490743643557724030417173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13660495762371816020278115 20490743643557724030417173)
          ·
            refine ⟨960503608291768313925805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20490743643557724030417173 960503608291768313925805)
            ·
              refine ⟨360188853109413117722177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 960503608291768313925805 360188853109413117722177)
              ·
                refine ⟨270141639832059838291633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 360188853109413117722177 270141639832059838291633)
                ·
                  refine ⟨202606229874044878718725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 270141639832059838291633 202606229874044878718725)
                  ·
                    rfl

theorem cell20_443896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 2, 2].length) (baseStart_443896 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_443896 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_443896 prefixEnd_443896 := by exact prefixLift 443896
  have htrace : WordTrace (prefixWord ++ tailWord_443896) baseStart_443896 baseEnd_443896 := by
    simpa [prefixWord, tailWord_443896, baseEnd_443896] using wordTrace_append hprefix tailTrace_443896
  have hstable : (prefixWord ++ tailWord_443896).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443896).length < 2 ^ (prefixWord ++ tailWord_443896).sum := by decide
  have hdescent : baseEnd_443896 < baseStart_443896 := by decide
  rcases family_descends (prefixWord ++ tailWord_443896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443900 : List Nat := [2, 2, 2, 1, 2, 1, 5, 1, 4]
def baseStart_443900 : Nat := 118140960795 + 443900 * 2 ^ 59
def prefixEnd_443900 : Nat := 4983230072969 + 3 ^ 40 * 443900 * 2
def baseEnd_443900 : Nat := 202608055583038642585375

theorem tailTrace_443900 : CollatzResearch.WordTrace tailWord_443900 prefixEnd_443900 202608055583038642585375 := by
  unfold tailWord_443900
  simp only [CollatzResearch.WordTrace]
  refine ⟨8095181545916793464700577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10793575394555724619600769 8095181545916793464700577)
  ·
    refine ⟨6071386159437595098525433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8095181545916793464700577 6071386159437595098525433)
    ·
      refine ⟨4553539619578196323894075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6071386159437595098525433 4553539619578196323894075)
      ·
        refine ⟨6830309429367294485841113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4553539619578196323894075 6830309429367294485841113)
        ·
          refine ⟨5122732072025470864380835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6830309429367294485841113 5122732072025470864380835)
          ·
            refine ⟨7684098108038206296571253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5122732072025470864380835 7684098108038206296571253)
            ·
              refine ⟨720384197628581840303555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7684098108038206296571253 720384197628581840303555)
              ·
                refine ⟨1080576296442872760455333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 720384197628581840303555 1080576296442872760455333)
                ·
                  refine ⟨202608055583038642585375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1080576296442872760455333 202608055583038642585375)
                  ·
                    rfl

theorem cell20_443900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_443900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_443900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_443900 prefixEnd_443900 := by exact prefixLift 443900
  have htrace : WordTrace (prefixWord ++ tailWord_443900) baseStart_443900 baseEnd_443900 := by
    simpa [prefixWord, tailWord_443900, baseEnd_443900] using wordTrace_append hprefix tailTrace_443900
  have hstable : (prefixWord ++ tailWord_443900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443900).length < 2 ^ (prefixWord ++ tailWord_443900).sum := by decide
  have hdescent : baseEnd_443900 < baseStart_443900 := by decide
  rcases family_descends (prefixWord ++ tailWord_443900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443906 : List Nat := [3, 4, 1, 2, 1, 3, 2, 1, 3]
def baseStart_443906 : Nat := 118140960795 + 443906 * 2 ^ 59
def prefixEnd_443906 : Nat := 4983230072969 + 3 ^ 40 * 443906 * 2
def baseEnd_443906 : Nat := 202610794146529288385351

theorem tailTrace_443906 : CollatzResearch.WordTrace tailWord_443906 prefixEnd_443906 202610794146529288385351 := by
  unfold tailWord_443906
  simp only [CollatzResearch.WordTrace]
  refine ⟨4047645482452962488529893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10793721286541233302746381 4047645482452962488529893)
  ·
    refine ⟨758933527959930466599355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4047645482452962488529893 758933527959930466599355)
    ·
      refine ⟨1138400291939895699899033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 758933527959930466599355 1138400291939895699899033)
      ·
        refine ⟨853800218954921774924275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1138400291939895699899033 853800218954921774924275)
        ·
          refine ⟨1280700328432382662386413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 853800218954921774924275 1280700328432382662386413)
          ·
            refine ⟨480262623162143498394905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1280700328432382662386413 480262623162143498394905)
            ·
              refine ⟨360196967371607623796179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 480262623162143498394905 360196967371607623796179)
              ·
                refine ⟨540295451057411435694269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 360196967371607623796179 540295451057411435694269)
                ·
                  refine ⟨202610794146529288385351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 540295451057411435694269 202610794146529288385351)
                  ·
                    rfl

theorem cell20_443906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_443906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_443906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_443906 prefixEnd_443906 := by exact prefixLift 443906
  have htrace : WordTrace (prefixWord ++ tailWord_443906) baseStart_443906 baseEnd_443906 := by
    simpa [prefixWord, tailWord_443906, baseEnd_443906] using wordTrace_append hprefix tailTrace_443906
  have hstable : (prefixWord ++ tailWord_443906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443906).length < 2 ^ (prefixWord ++ tailWord_443906).sum := by decide
  have hdescent : baseEnd_443906 < baseStart_443906 := by decide
  rcases family_descends (prefixWord ++ tailWord_443906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443921 : List Nat := [1, 2, 2, 1, 1, 2, 4, 1, 6]
def baseStart_443921 : Nat := 118140960795 + 443921 * 2 ^ 59
def prefixEnd_443921 : Nat := 4983230072969 + 3 ^ 40 * 443921 * 2
def baseEnd_443921 : Nat := 202617640555255902885289

theorem tailTrace_443921 : CollatzResearch.WordTrace tailWord_443921 prefixEnd_443921 202617640555255902885289 := by
  unfold tailWord_443921
  simp only [CollatzResearch.WordTrace]
  refine ⟨16191129024757507515915617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10794086016505005010610411 16191129024757507515915617)
  ·
    refine ⟨12143346768568130636936713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16191129024757507515915617 12143346768568130636936713)
    ·
      refine ⟨9107510076426097977702535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12143346768568130636936713 9107510076426097977702535)
      ·
        refine ⟨13661265114639146966553803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9107510076426097977702535 13661265114639146966553803)
        ·
          refine ⟨20491897671958720449830705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13661265114639146966553803 20491897671958720449830705)
          ·
            refine ⟨15368923253969040337373029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20491897671958720449830705 15368923253969040337373029)
            ·
              refine ⟨2881673110119195063257443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15368923253969040337373029 2881673110119195063257443)
              ·
                refine ⟨4322509665178792594886165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2881673110119195063257443 4322509665178792594886165)
                ·
                  refine ⟨202617640555255902885289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4322509665178792594886165 202617640555255902885289)
                  ·
                    rfl

theorem cell20_443921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 6].length) (baseStart_443921 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_443921 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_443921 prefixEnd_443921 := by exact prefixLift 443921
  have htrace : WordTrace (prefixWord ++ tailWord_443921) baseStart_443921 baseEnd_443921 := by
    simpa [prefixWord, tailWord_443921, baseEnd_443921] using wordTrace_append hprefix tailTrace_443921
  have hstable : (prefixWord ++ tailWord_443921).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443921).length < 2 ^ (prefixWord ++ tailWord_443921).sum := by decide
  have hdescent : baseEnd_443921 < baseStart_443921 := by decide
  rcases family_descends (prefixWord ++ tailWord_443921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443955 : List Nat := [1, 1, 1, 2, 4, 4, 1, 4, 2]
def baseStart_443955 : Nat := 118140960795 + 443955 * 2 ^ 59
def prefixEnd_443955 : Nat := 4983230072969 + 3 ^ 40 * 443955 * 2
def baseEnd_443955 : Nat := 202633159081702895751817

theorem tailTrace_443955 : CollatzResearch.WordTrace tailWord_443955 prefixEnd_443955 202633159081702895751817 := by
  unfold tailWord_443955
  simp only [CollatzResearch.WordTrace]
  refine ⟨16192369106634331322653319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10794912737756220881768879 16192369106634331322653319)
  ·
    refine ⟨24288553659951496983979979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16192369106634331322653319 24288553659951496983979979)
    ·
      refine ⟨36432830489927245475969969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24288553659951496983979979 36432830489927245475969969)
      ·
        refine ⟨27324622867445434106977477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36432830489927245475969969 27324622867445434106977477)
        ·
          refine ⟨5123366787646018895058277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27324622867445434106977477 5123366787646018895058277)
          ·
            refine ⟨960631272683628542823427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5123366787646018895058277 960631272683628542823427)
            ·
              refine ⟨1440946909025442814235141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 960631272683628542823427 1440946909025442814235141)
              ·
                refine ⟨270177545442270527669089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1440946909025442814235141 270177545442270527669089)
                ·
                  refine ⟨202633159081702895751817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 270177545442270527669089 202633159081702895751817)
                  ·
                    rfl

theorem cell20_443955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 4, 2].length) (baseStart_443955 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_443955 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_443955 prefixEnd_443955 := by exact prefixLift 443955
  have htrace : WordTrace (prefixWord ++ tailWord_443955) baseStart_443955 baseEnd_443955 := by
    simpa [prefixWord, tailWord_443955, baseEnd_443955] using wordTrace_append hprefix tailTrace_443955
  have hstable : (prefixWord ++ tailWord_443955).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443955).length < 2 ^ (prefixWord ++ tailWord_443955).sum := by decide
  have hdescent : baseEnd_443955 < baseStart_443955 := by decide
  rcases family_descends (prefixWord ++ tailWord_443955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443958 : List Nat := [5, 1, 2, 1, 4, 1, 1, 5]
def baseStart_443958 : Nat := 118140960795 + 443958 * 2 ^ 59
def prefixEnd_443958 : Nat := 4983230072969 + 3 ^ 40 * 443958 * 2
def baseEnd_443958 : Nat := 67544842787816072883935

theorem tailTrace_443958 : CollatzResearch.WordTrace tailWord_443958 prefixEnd_443958 67544842787816072883935 := by
  unfold tailWord_443958
  simp only [CollatzResearch.WordTrace]
  refine ⟨1012029907851466427188283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10794985683748975223341685 1012029907851466427188283)
  ·
    refine ⟨1518044861777199640782425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1012029907851466427188283 1518044861777199640782425)
    ·
      refine ⟨1138533646332899730586819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1518044861777199640782425 1138533646332899730586819)
      ·
        refine ⟨1707800469499349595880229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1138533646332899730586819 1707800469499349595880229)
        ·
          refine ⟨320212588031128049227543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1707800469499349595880229 320212588031128049227543)
          ·
            refine ⟨480318882046692073841315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320212588031128049227543 480318882046692073841315)
            ·
              refine ⟨720478323070038110761973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 480318882046692073841315 720478323070038110761973)
              ·
                refine ⟨67544842787816072883935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 720478323070038110761973 67544842787816072883935)
                ·
                  rfl

theorem cell20_443958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_443958 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_443958 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_443958 prefixEnd_443958 := by exact prefixLift 443958
  have htrace : WordTrace (prefixWord ++ tailWord_443958) baseStart_443958 baseEnd_443958 := by
    simpa [prefixWord, tailWord_443958, baseEnd_443958] using wordTrace_append hprefix tailTrace_443958
  have hstable : (prefixWord ++ tailWord_443958).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443958).length < 2 ^ (prefixWord ++ tailWord_443958).sum := by decide
  have hdescent : baseEnd_443958 < baseStart_443958 := by decide
  rcases family_descends (prefixWord ++ tailWord_443958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443969 : List Nat := [1, 2, 5, 1, 1, 1, 1, 5, 3]
def baseStart_443969 : Nat := 118140960795 + 443969 * 2 ^ 59
def prefixEnd_443969 : Nat := 4983230072969 + 3 ^ 40 * 443969 * 2
def baseEnd_443969 : Nat := 202639549063181069285093

theorem tailTrace_443969 : CollatzResearch.WordTrace tailWord_443969 prefixEnd_443969 202639549063181069285093 := by
  unfold tailWord_443969
  simp only [CollatzResearch.WordTrace]
  refine ⟨16192879728583611713662961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10795253152389074475775307 16192879728583611713662961)
  ·
    refine ⟨12144659796437708785247221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16192879728583611713662961 12144659796437708785247221)
    ·
      refine ⟨1138561855916035198616927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12144659796437708785247221 1138561855916035198616927)
      ·
        refine ⟨1707842783874052797925391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1138561855916035198616927 1707842783874052797925391)
        ·
          refine ⟨2561764175811079196888087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1707842783874052797925391 2561764175811079196888087)
          ·
            refine ⟨3842646263716618795332131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2561764175811079196888087 3842646263716618795332131)
            ·
              refine ⟨5763969395574928192998197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3842646263716618795332131 5763969395574928192998197)
              ·
                refine ⟨540372130835149518093581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5763969395574928192998197 540372130835149518093581)
                ·
                  refine ⟨202639549063181069285093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 540372130835149518093581 202639549063181069285093)
                  ·
                    rfl

theorem cell20_443969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 5, 3].length) (baseStart_443969 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_443969 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_443969 prefixEnd_443969 := by exact prefixLift 443969
  have htrace : WordTrace (prefixWord ++ tailWord_443969) baseStart_443969 baseEnd_443969 := by
    simpa [prefixWord, tailWord_443969, baseEnd_443969] using wordTrace_append hprefix tailTrace_443969
  have hstable : (prefixWord ++ tailWord_443969).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443969).length < 2 ^ (prefixWord ++ tailWord_443969).sum := by decide
  have hdescent : baseEnd_443969 < baseStart_443969 := by decide
  rcases family_descends (prefixWord ++ tailWord_443969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444007 : List Nat := [1, 1, 5, 1, 1, 1, 5, 2, 3]
def baseStart_444007 : Nat := 118140960795 + 444007 * 2 ^ 59
def prefixEnd_444007 : Nat := 4983230072969 + 3 ^ 40 * 444007 * 2
def baseEnd_444007 : Nat := 202656893298621826018271

theorem tailTrace_444007 : CollatzResearch.WordTrace tailWord_444007 prefixEnd_444007 202656893298621826018271 := by
  unfold tailWord_444007
  simp only [CollatzResearch.WordTrace]
  refine ⟨16194265702445944203546275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10796177134963962802364183 16194265702445944203546275)
  ·
    refine ⟨24291398553668916305319413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16194265702445944203546275 24291398553668916305319413)
    ·
      refine ⟨2277318614406460903623695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24291398553668916305319413 2277318614406460903623695)
      ·
        refine ⟨3415977921609691355435543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2277318614406460903623695 3415977921609691355435543)
        ·
          refine ⟨5123966882414537033153315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3415977921609691355435543 5123966882414537033153315)
          ·
            refine ⟨7685950323621805549729973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5123966882414537033153315 7685950323621805549729973)
            ·
              refine ⟨720557842839544270287185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7685950323621805549729973 720557842839544270287185)
              ·
                refine ⟨540418382129658202715389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 720557842839544270287185 540418382129658202715389)
                ·
                  refine ⟨202656893298621826018271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 540418382129658202715389 202656893298621826018271)
                  ·
                    rfl

theorem cell20_444007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 2, 3].length) (baseStart_444007 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_444007 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_444007 prefixEnd_444007 := by exact prefixLift 444007
  have htrace : WordTrace (prefixWord ++ tailWord_444007) baseStart_444007 baseEnd_444007 := by
    simpa [prefixWord, tailWord_444007, baseEnd_444007] using wordTrace_append hprefix tailTrace_444007
  have hstable : (prefixWord ++ tailWord_444007).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444007).length < 2 ^ (prefixWord ++ tailWord_444007).sum := by decide
  have hdescent : baseEnd_444007 < baseStart_444007 := by decide
  rcases family_descends (prefixWord ++ tailWord_444007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444072 : List Nat := [2, 1, 7, 1, 1, 1, 2, 5]
def baseStart_444072 : Nat := 118140960795 + 444072 * 2 ^ 59
def prefixEnd_444072 : Nat := 4983230072969 + 3 ^ 40 * 444072 * 2
def baseEnd_444072 : Nat := 67562187023256829617113

theorem tailTrace_444072 : CollatzResearch.WordTrace tailWord_444072 prefixEnd_444072 67562187023256829617113 := by
  unfold tailWord_444072
  simp only [CollatzResearch.WordTrace]
  refine ⟨8098318223605230152331235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10797757631473640203108313 8098318223605230152331235)
  ·
    refine ⟨12147477335407845228496853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8098318223605230152331235 12147477335407845228496853)
    ·
      refine ⟨284706500048621372542895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 12147477335407845228496853 284706500048621372542895)
      ·
        refine ⟨427059750072932058814343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284706500048621372542895 427059750072932058814343)
        ·
          refine ⟨640589625109398088221515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427059750072932058814343 640589625109398088221515)
          ·
            refine ⟨960884437664097132332273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640589625109398088221515 960884437664097132332273)
            ·
              refine ⟨720663328248072849249205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 960884437664097132332273 720663328248072849249205)
              ·
                refine ⟨67562187023256829617113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 720663328248072849249205 67562187023256829617113)
                ·
                  rfl

theorem cell20_444072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 5].length) (baseStart_444072 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_444072 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_444072 prefixEnd_444072 := by exact prefixLift 444072
  have htrace : WordTrace (prefixWord ++ tailWord_444072) baseStart_444072 baseEnd_444072 := by
    simpa [prefixWord, tailWord_444072, baseEnd_444072] using wordTrace_append hprefix tailTrace_444072
  have hstable : (prefixWord ++ tailWord_444072).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444072).length < 2 ^ (prefixWord ++ tailWord_444072).sum := by decide
  have hdescent : baseEnd_444072 < baseStart_444072 := by decide
  rcases family_descends (prefixWord ++ tailWord_444072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444080 : List Nat := [2, 1, 1, 1, 2, 1, 5, 7]
def baseStart_444080 : Nat := 118140960795 + 444080 * 2 ^ 59
def prefixEnd_444080 : Nat := 4983230072969 + 3 ^ 40 * 444080 * 2
def baseEnd_444080 : Nat := 67563404162586005528213

theorem tailTrace_444080 : CollatzResearch.WordTrace tailWord_444080 prefixEnd_444080 67563404162586005528213 := by
  unfold tailWord_444080
  simp only [CollatzResearch.WordTrace]
  refine ⟨8098464115590738835476847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10797952154120985113969129 8098464115590738835476847)
  ·
    refine ⟨12147696173386108253215271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8098464115590738835476847 12147696173386108253215271)
    ·
      refine ⟨18221544260079162379822907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12147696173386108253215271 18221544260079162379822907)
      ·
        refine ⟨27332316390118743569734361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18221544260079162379822907 27332316390118743569734361)
        ·
          refine ⟨20499237292589057677300771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27332316390118743569734361 20499237292589057677300771)
          ·
            refine ⟨30748855938883586515951157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20499237292589057677300771 30748855938883586515951157)
            ·
              refine ⟨2882705244270336235870421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30748855938883586515951157 2882705244270336235870421)
              ·
                refine ⟨67563404162586005528213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2882705244270336235870421 67563404162586005528213)
                ·
                  rfl

theorem cell20_444080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 7].length) (baseStart_444080 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_444080 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_444080 prefixEnd_444080 := by exact prefixLift 444080
  have htrace : WordTrace (prefixWord ++ tailWord_444080) baseStart_444080 baseEnd_444080 := by
    simpa [prefixWord, tailWord_444080, baseEnd_444080] using wordTrace_append hprefix tailTrace_444080
  have hstable : (prefixWord ++ tailWord_444080).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444080).length < 2 ^ (prefixWord ++ tailWord_444080).sum := by decide
  have hdescent : baseEnd_444080 < baseStart_444080 := by decide
  rcases family_descends (prefixWord ++ tailWord_444080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444121 : List Nat := [1, 2, 1, 2, 3, 4, 2, 2, 3]
def baseStart_444121 : Nat := 118140960795 + 444121 * 2 ^ 59
def prefixEnd_444121 : Nat := 4983230072969 + 3 ^ 40 * 444121 * 2
def baseEnd_444121 : Nat := 202708926004944096217805

theorem tailTrace_444121 : CollatzResearch.WordTrace tailWord_444121 prefixEnd_444121 202708926004944096217805 := by
  unfold tailWord_444121
  simp only [CollatzResearch.WordTrace]
  refine ⟨16198423624032941673196217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10798949082688627782130811 16198423624032941673196217)
  ·
    refine ⟨12148817718024706254897163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16198423624032941673196217 12148817718024706254897163)
    ·
      refine ⟨18223226577037059382345745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12148817718024706254897163 18223226577037059382345745)
      ·
        refine ⟨13667419932777794536759309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18223226577037059382345745 13667419932777794536759309)
        ·
          refine ⟨5125282474791672951284741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13667419932777794536759309 5125282474791672951284741)
          ·
            refine ⟨960990464023438678365889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5125282474791672951284741 960990464023438678365889)
            ·
              refine ⟨720742848017579008774417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 960990464023438678365889 720742848017579008774417)
              ·
                refine ⟨540557136013184256580813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 720742848017579008774417 540557136013184256580813)
                ·
                  refine ⟨202708926004944096217805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 540557136013184256580813 202708926004944096217805)
                  ·
                    rfl

theorem cell20_444121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 2, 3].length) (baseStart_444121 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_444121 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_444121 prefixEnd_444121 := by exact prefixLift 444121
  have htrace : WordTrace (prefixWord ++ tailWord_444121) baseStart_444121 baseEnd_444121 := by
    simpa [prefixWord, tailWord_444121, baseEnd_444121] using wordTrace_append hprefix tailTrace_444121
  have hstable : (prefixWord ++ tailWord_444121).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444121).length < 2 ^ (prefixWord ++ tailWord_444121).sum := by decide
  have hdescent : baseEnd_444121 < baseStart_444121 := by decide
  rcases family_descends (prefixWord ++ tailWord_444121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444131 : List Nat := [1, 1, 1, 7, 3, 1, 1, 5]
def baseStart_444131 : Nat := 118140960795 + 444131 * 2 ^ 59
def prefixEnd_444131 : Nat := 4983230072969 + 3 ^ 40 * 444131 * 2
def baseEnd_444131 : Nat := 67571163425809501961477

theorem tailTrace_444131 : CollatzResearch.WordTrace tailWord_444131 prefixEnd_444131 67571163425809501961477 := by
  unfold tailWord_444131
  simp only [CollatzResearch.WordTrace]
  refine ⟨16198788353996713381060247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10799192235997808920706831 16198788353996713381060247)
  ·
    refine ⟨24298182530995070071590371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16198788353996713381060247 24298182530995070071590371)
    ·
      refine ⟨36447273796492605107385557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24298182530995070071590371 36447273796492605107385557)
      ·
        refine ⟨854232979605295432204349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 36447273796492605107385557 854232979605295432204349)
        ·
          refine ⟨320337367351985787076631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 854232979605295432204349 320337367351985787076631)
          ·
            refine ⟨480506051027978680614947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320337367351985787076631 480506051027978680614947)
            ·
              refine ⟨720759076541968020922421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 480506051027978680614947 720759076541968020922421)
              ·
                refine ⟨67571163425809501961477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 720759076541968020922421 67571163425809501961477)
                ·
                  rfl

theorem cell20_444131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 5].length) (baseStart_444131 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_444131 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_444131 prefixEnd_444131 := by exact prefixLift 444131
  have htrace : WordTrace (prefixWord ++ tailWord_444131) baseStart_444131 baseEnd_444131 := by
    simpa [prefixWord, tailWord_444131, baseEnd_444131] using wordTrace_append hprefix tailTrace_444131
  have hstable : (prefixWord ++ tailWord_444131).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444131).length < 2 ^ (prefixWord ++ tailWord_444131).sum := by decide
  have hdescent : baseEnd_444131 < baseStart_444131 := by decide
  rcases family_descends (prefixWord ++ tailWord_444131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444148 : List Nat := [2, 6, 1, 1, 1, 2, 3, 4]
def baseStart_444148 : Nat := 118140960795 + 444148 * 2 ^ 59
def prefixEnd_444148 : Nat := 4983230072969 + 3 ^ 40 * 444148 * 2
def baseEnd_444148 : Nat := 67573749846884000772565

theorem tailTrace_444148 : CollatzResearch.WordTrace tailWord_444148 prefixEnd_444148 67573749846884000772565 := by
  unfold tailWord_444148
  simp only [CollatzResearch.WordTrace]
  refine ⟨8099704197467562642214549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10799605596623416856286065 8099704197467562642214549)
  ·
    refine ⟨379673634256291998853807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8099704197467562642214549 379673634256291998853807)
    ·
      refine ⟨569510451384437998280711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379673634256291998853807 569510451384437998280711)
      ·
        refine ⟨854265677076656997421067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 569510451384437998280711 854265677076656997421067)
        ·
          refine ⟨1281398515614985496131601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 854265677076656997421067 1281398515614985496131601)
          ·
            refine ⟨961048886711239122098701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1281398515614985496131601 961048886711239122098701)
            ·
              refine ⟨360393332516714670787013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 961048886711239122098701 360393332516714670787013)
              ·
                refine ⟨67573749846884000772565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 360393332516714670787013 67573749846884000772565)
                ·
                  rfl

theorem cell20_444148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 4].length) (baseStart_444148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_444148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_444148 prefixEnd_444148 := by exact prefixLift 444148
  have htrace : WordTrace (prefixWord ++ tailWord_444148) baseStart_444148 baseEnd_444148 := by
    simpa [prefixWord, tailWord_444148, baseEnd_444148] using wordTrace_append hprefix tailTrace_444148
  have hstable : (prefixWord ++ tailWord_444148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444148).length < 2 ^ (prefixWord ++ tailWord_444148).sum := by decide
  have hdescent : baseEnd_444148 < baseStart_444148 := by decide
  rcases family_descends (prefixWord ++ tailWord_444148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444162 : List Nat := [3, 4, 1, 1, 1, 1, 4, 3, 2]
def baseStart_444162 : Nat := 118140960795 + 444162 * 2 ^ 59
def prefixEnd_444162 : Nat := 4983230072969 + 3 ^ 40 * 444162 * 2
def baseEnd_444162 : Nat := 202727639522130175850971

theorem tailTrace_444162 : CollatzResearch.WordTrace tailWord_444162 prefixEnd_444162 202727639522130175850971 := by
  unfold tailWord_444162
  simp only [CollatzResearch.WordTrace]
  refine ⟨4049979754221101418859685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10799946011256270450292493 4049979754221101418859685)
  ·
    refine ⟨759371203916456516036191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4049979754221101418859685 759371203916456516036191)
    ·
      refine ⟨1139056805874684774054287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 759371203916456516036191 1139056805874684774054287)
      ·
        refine ⟨1708585208812027161081431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1139056805874684774054287 1708585208812027161081431)
        ·
          refine ⟨2562877813218040741622147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1708585208812027161081431 2562877813218040741622147)
          ·
            refine ⟨3844316719827061112433221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2562877813218040741622147 3844316719827061112433221)
            ·
              refine ⟨720809384967573958581229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3844316719827061112433221 720809384967573958581229)
              ·
                refine ⟨270303519362840234467961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 720809384967573958581229 270303519362840234467961)
                ·
                  refine ⟨202727639522130175850971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 270303519362840234467961 202727639522130175850971)
                  ·
                    rfl

theorem cell20_444162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_444162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_444162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_444162 prefixEnd_444162 := by exact prefixLift 444162
  have htrace : WordTrace (prefixWord ++ tailWord_444162) baseStart_444162 baseEnd_444162 := by
    simpa [prefixWord, tailWord_444162, baseEnd_444162] using wordTrace_append hprefix tailTrace_444162
  have hstable : (prefixWord ++ tailWord_444162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444162).length < 2 ^ (prefixWord ++ tailWord_444162).sum := by decide
  have hdescent : baseEnd_444162 < baseStart_444162 := by decide
  rcases family_descends (prefixWord ++ tailWord_444162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444183 : List Nat := [1, 1, 3, 4, 2, 1, 2, 4, 2]
def baseStart_444183 : Nat := 118140960795 + 444183 * 2 ^ 59
def prefixEnd_444183 : Nat := 4983230072969 + 3 ^ 40 * 444183 * 2
def baseEnd_444183 : Nat := 202737224494347436150885

theorem tailTrace_444183 : CollatzResearch.WordTrace tailWord_444183 prefixEnd_444183 202737224494347436150885 := by
  unfold tailWord_444183
  simp only [CollatzResearch.WordTrace]
  refine ⟨16200684949808326261953203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10800456633205550841302135 16200684949808326261953203)
  ·
    refine ⟨24301027424712489392929805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16200684949808326261953203 24301027424712489392929805)
    ·
      refine ⟨9112885284267183522348677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24301027424712489392929805 9112885284267183522348677)
      ·
        refine ⟨1708665990800096910440377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9112885284267183522348677 1708665990800096910440377)
        ·
          refine ⟨1281499493100072682830283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1708665990800096910440377 1281499493100072682830283)
          ·
            refine ⟨1922249239650109024245425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1281499493100072682830283 1922249239650109024245425)
            ·
              refine ⟨1441686929737581768184069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1922249239650109024245425 1441686929737581768184069)
              ·
                refine ⟨270316299325796581534513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1441686929737581768184069 270316299325796581534513)
                ·
                  refine ⟨202737224494347436150885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 270316299325796581534513 202737224494347436150885)
                  ·
                    rfl

theorem cell20_444183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 4, 2].length) (baseStart_444183 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_444183 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_444183 prefixEnd_444183 := by exact prefixLift 444183
  have htrace : WordTrace (prefixWord ++ tailWord_444183) baseStart_444183 baseEnd_444183 := by
    simpa [prefixWord, tailWord_444183, baseEnd_444183] using wordTrace_append hprefix tailTrace_444183
  have hstable : (prefixWord ++ tailWord_444183).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444183).length < 2 ^ (prefixWord ++ tailWord_444183).sum := by decide
  have hdescent : baseEnd_444183 < baseStart_444183 := by decide
  rcases family_descends (prefixWord ++ tailWord_444183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444201 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 9]
def baseStart_444201 : Nat := 118140960795 + 444201 * 2 ^ 59
def prefixEnd_444201 : Nat := 4983230072969 + 3 ^ 40 * 444201 * 2
def baseEnd_444201 : Nat := 202745440184819373550811

theorem tailTrace_444201 : CollatzResearch.WordTrace tailWord_444201 prefixEnd_444201 202745440184819373550811 := by
  unfold tailWord_444201
  simp only [CollatzResearch.WordTrace]
  refine ⟨16201341463743115336108457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10800894309162076890738971 16201341463743115336108457)
  ·
    refine ⟨12151006097807336502081343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16201341463743115336108457 12151006097807336502081343)
    ·
      refine ⟨18226509146711004753122015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12151006097807336502081343 18226509146711004753122015)
      ·
        refine ⟨27339763720066507129683023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18226509146711004753122015 27339763720066507129683023)
        ·
          refine ⟨41009645580099760694524535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27339763720066507129683023 41009645580099760694524535)
          ·
            refine ⟨61514468370149641041786803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41009645580099760694524535 61514468370149641041786803)
            ·
              refine ⟨92271702555224461562680205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61514468370149641041786803 92271702555224461562680205)
              ·
                refine ⟨34601888458209173086005077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92271702555224461562680205 34601888458209173086005077)
                ·
                  refine ⟨202745440184819373550811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 34601888458209173086005077 202745440184819373550811)
                  ·
                    rfl

theorem cell20_444201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 9].length) (baseStart_444201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_444201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_444201 prefixEnd_444201 := by exact prefixLift 444201
  have htrace : WordTrace (prefixWord ++ tailWord_444201) baseStart_444201 baseEnd_444201 := by
    simpa [prefixWord, tailWord_444201, baseEnd_444201] using wordTrace_append hprefix tailTrace_444201
  have hstable : (prefixWord ++ tailWord_444201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444201).length < 2 ^ (prefixWord ++ tailWord_444201).sum := by decide
  have hdescent : baseEnd_444201 < baseStart_444201 := by decide
  rcases family_descends (prefixWord ++ tailWord_444201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444211 : List Nat := [1, 1, 1, 2, 7, 1, 1, 6]
def baseStart_444211 : Nat := 118140960795 + 444211 * 2 ^ 59
def prefixEnd_444211 : Nat := 4983230072969 + 3 ^ 40 * 444211 * 2
def baseEnd_444211 : Nat := 67583334819101261072479

theorem tailTrace_444211 : CollatzResearch.WordTrace tailWord_444211 prefixEnd_444211 67583334819101261072479 := by
  unfold tailWord_444211
  simp only [CollatzResearch.WordTrace]
  refine ⟨16201706193706887043972487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10801137462471258029314991 16201706193706887043972487)
  ·
    refine ⟨24302559290560330565958731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16201706193706887043972487 24302559290560330565958731)
    ·
      refine ⟨36453838935840495848938097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24302559290560330565958731 36453838935840495848938097)
      ·
        refine ⟨27340379201880371886703573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36453838935840495848938097 27340379201880371886703573)
        ·
          refine ⟨640790137544071216094615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 27340379201880371886703573 640790137544071216094615)
          ·
            refine ⟨961185206316106824141923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640790137544071216094615 961185206316106824141923)
            ·
              refine ⟨1441777809474160236212885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 961185206316106824141923 1441777809474160236212885)
              ·
                refine ⟨67583334819101261072479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1441777809474160236212885 67583334819101261072479)
                ·
                  rfl

theorem cell20_444211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 6].length) (baseStart_444211 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_444211 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_444211 prefixEnd_444211 := by exact prefixLift 444211
  have htrace : WordTrace (prefixWord ++ tailWord_444211) baseStart_444211 baseEnd_444211 := by
    simpa [prefixWord, tailWord_444211, baseEnd_444211] using wordTrace_append hprefix tailTrace_444211
  have hstable : (prefixWord ++ tailWord_444211).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444211).length < 2 ^ (prefixWord ++ tailWord_444211).sum := by decide
  have hdescent : baseEnd_444211 < baseStart_444211 := by decide
  rcases family_descends (prefixWord ++ tailWord_444211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444217 : List Nat := [1, 2, 1, 7, 1, 2, 1, 3, 2]
def baseStart_444217 : Nat := 118140960795 + 444217 * 2 ^ 59
def prefixEnd_444217 : Nat := 4983230072969 + 3 ^ 40 * 444217 * 2
def baseEnd_444217 : Nat := 202752743020794429017413

theorem tailTrace_444217 : CollatzResearch.WordTrace tailWord_444217 prefixEnd_444217 202752743020794429017413 := by
  unfold tailWord_444217
  simp only [CollatzResearch.WordTrace]
  refine ⟨16201925031685150068690905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10801283354456766712460603 16201925031685150068690905)
  ·
    refine ⟨12151443773763862551518179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16201925031685150068690905 12151443773763862551518179)
    ·
      refine ⟨18227165660645793827277269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12151443773763862551518179 18227165660645793827277269)
      ·
        refine ⟨427199195171385792826811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 18227165660645793827277269 427199195171385792826811)
        ·
          refine ⟨640798792757078689240217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427199195171385792826811 640798792757078689240217)
          ·
            refine ⟨480599094567809016930163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 640798792757078689240217 480599094567809016930163)
            ·
              refine ⟨720898641851713525395245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 480599094567809016930163 720898641851713525395245)
              ·
                refine ⟨270336990694392572023217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 720898641851713525395245 270336990694392572023217)
                ·
                  refine ⟨202752743020794429017413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 270336990694392572023217 202752743020794429017413)
                  ·
                    rfl

theorem cell20_444217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 3, 2].length) (baseStart_444217 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_444217 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_444217 prefixEnd_444217 := by exact prefixLift 444217
  have htrace : WordTrace (prefixWord ++ tailWord_444217) baseStart_444217 baseEnd_444217 := by
    simpa [prefixWord, tailWord_444217, baseEnd_444217] using wordTrace_append hprefix tailTrace_444217
  have hstable : (prefixWord ++ tailWord_444217).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444217).length < 2 ^ (prefixWord ++ tailWord_444217).sum := by decide
  have hdescent : baseEnd_444217 < baseStart_444217 := by decide
  rcases family_descends (prefixWord ++ tailWord_444217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444218 : List Nat := [3, 1, 1, 1, 5, 1, 1, 2, 5]
def baseStart_444218 : Nat := 118140960795 + 444218 * 2 ^ 59
def prefixEnd_444218 : Nat := 4983230072969 + 3 ^ 40 * 444218 * 2
def baseEnd_444218 : Nat := 202753199448042869984075

theorem tailTrace_444218 : CollatzResearch.WordTrace tailWord_444218 prefixEnd_444218 202753199448042869984075 := by
  unfold tailWord_444218
  simp only [CollatzResearch.WordTrace]
  refine ⟨4050490376170381809869327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10801307669787684826318205 4050490376170381809869327)
  ·
    refine ⟨6075735564255572714803991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4050490376170381809869327 6075735564255572714803991)
    ·
      refine ⟨9113603346383359072205987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6075735564255572714803991 9113603346383359072205987)
      ·
        refine ⟨13670405019575038608308981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9113603346383359072205987 13670405019575038608308981)
        ·
          refine ⟨1281600470585159869528967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13670405019575038608308981 1281600470585159869528967)
          ·
            refine ⟨1922400705877739804293451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1281600470585159869528967 1922400705877739804293451)
            ·
              refine ⟨2883601058816609706440177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1922400705877739804293451 2883601058816609706440177)
              ·
                refine ⟨2162700794112457279830133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2883601058816609706440177 2162700794112457279830133)
                ·
                  refine ⟨202753199448042869984075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2162700794112457279830133 202753199448042869984075)
                  ·
                    rfl

theorem cell20_444218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_444218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_444218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_444218 prefixEnd_444218 := by exact prefixLift 444218
  have htrace : WordTrace (prefixWord ++ tailWord_444218) baseStart_444218 baseEnd_444218 := by
    simpa [prefixWord, tailWord_444218, baseEnd_444218] using wordTrace_append hprefix tailTrace_444218
  have hstable : (prefixWord ++ tailWord_444218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444218).length < 2 ^ (prefixWord ++ tailWord_444218).sum := by decide
  have hdescent : baseEnd_444218 < baseStart_444218 := by decide
  rcases family_descends (prefixWord ++ tailWord_444218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444232 : List Nat := [2, 1, 3, 1, 1, 4, 8]
def baseStart_444232 : Nat := 118140960795 + 444232 * 2 ^ 59
def prefixEnd_444232 : Nat := 4983230072969 + 3 ^ 40 * 444232 * 2
def baseEnd_444232 : Nat := 22528843269946782613039

theorem tailTrace_444232 : CollatzResearch.WordTrace tailWord_444232 prefixEnd_444232 22528843269946782613039 := by
  unfold tailWord_444232
  simp only [CollatzResearch.WordTrace]
  refine ⟨8101236063315403815243475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10801648084420538420324633 8101236063315403815243475)
  ·
    refine ⟨12151854094973105722865213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8101236063315403815243475 12151854094973105722865213)
    ·
      refine ⟨4556945285614914646074455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12151854094973105722865213 4556945285614914646074455)
      ·
        refine ⟨6835417928422371969111683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4556945285614914646074455 6835417928422371969111683)
        ·
          refine ⟨10253126892633557953667525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6835417928422371969111683 10253126892633557953667525)
          ·
            refine ⟨1922461292368792116312661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10253126892633557953667525 1922461292368792116312661)
            ·
              refine ⟨22528843269946782613039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1922461292368792116312661 22528843269946782613039)
              ·
                rfl

theorem cell20_444232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 8].length) (baseStart_444232 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_444232 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_444232 prefixEnd_444232 := by exact prefixLift 444232
  have htrace : WordTrace (prefixWord ++ tailWord_444232) baseStart_444232 baseEnd_444232 := by
    simpa [prefixWord, tailWord_444232, baseEnd_444232] using wordTrace_append hprefix tailTrace_444232
  have hstable : (prefixWord ++ tailWord_444232).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444232).length < 2 ^ (prefixWord ++ tailWord_444232).sum := by decide
  have hdescent : baseEnd_444232 < baseStart_444232 := by decide
  rcases family_descends (prefixWord ++ tailWord_444232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444242 : List Nat := [3, 2, 2, 1, 1, 3, 3, 1, 4]
def baseStart_444242 : Nat := 118140960795 + 444242 * 2 ^ 59
def prefixEnd_444242 : Nat := 4983230072969 + 3 ^ 40 * 444242 * 2
def baseEnd_444242 : Nat := 202764153702005453183977

theorem tailTrace_444242 : CollatzResearch.WordTrace tailWord_444242 prefixEnd_444242 202764153702005453183977 := by
  unfold tailWord_444242
  simp only [CollatzResearch.WordTrace]
  refine ⟨4050709214148644834587745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10801891237729719558900653 4050709214148644834587745)
  ·
    refine ⟨3038031910611483625940809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4050709214148644834587745 3038031910611483625940809)
    ·
      refine ⟨2278523932958612719455607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3038031910611483625940809 2278523932958612719455607)
      ·
        refine ⟨3417785899437919079183411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2278523932958612719455607 3417785899437919079183411)
        ·
          refine ⟨5126678849156878618775117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3417785899437919079183411 5126678849156878618775117)
          ·
            refine ⟨1922504568433829482040669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5126678849156878618775117 1922504568433829482040669)
            ·
              refine ⟨720939213162686055765251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1922504568433829482040669 720939213162686055765251)
              ·
                refine ⟨1081408819744029083647877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 720939213162686055765251 1081408819744029083647877)
                ·
                  refine ⟨202764153702005453183977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1081408819744029083647877 202764153702005453183977)
                  ·
                    rfl

theorem cell20_444242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_444242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_444242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_444242 prefixEnd_444242 := by exact prefixLift 444242
  have htrace : WordTrace (prefixWord ++ tailWord_444242) baseStart_444242 baseEnd_444242 := by
    simpa [prefixWord, tailWord_444242, baseEnd_444242] using wordTrace_append hprefix tailTrace_444242
  have hstable : (prefixWord ++ tailWord_444242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444242).length < 2 ^ (prefixWord ++ tailWord_444242).sum := by decide
  have hdescent : baseEnd_444242 < baseStart_444242 := by decide
  rcases family_descends (prefixWord ++ tailWord_444242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444252 : List Nat := [2, 2, 4, 2, 2, 1, 1, 3, 3]
def baseStart_444252 : Nat := 118140960795 + 444252 * 2 ^ 59
def prefixEnd_444252 : Nat := 4983230072969 + 3 ^ 40 * 444252 * 2
def baseEnd_444252 : Nat := 202768717974489862850603

theorem tailTrace_444252 : CollatzResearch.WordTrace tailWord_444252 prefixEnd_444252 202768717974489862850603 := by
  unfold tailWord_444252
  simp only [CollatzResearch.WordTrace]
  refine ⟨8101600793279175523107505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10802134391038900697476673 8101600793279175523107505)
  ·
    refine ⟨6076200594959381642330629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8101600793279175523107505 6076200594959381642330629)
    ·
      refine ⟨1139287611554884057936993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6076200594959381642330629 1139287611554884057936993)
      ·
        refine ⟨854465708666163043452745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1139287611554884057936993 854465708666163043452745)
        ·
          refine ⟨640849281499622282589559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 854465708666163043452745 640849281499622282589559)
          ·
            refine ⟨961273922249433423884339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640849281499622282589559 961273922249433423884339)
            ·
              refine ⟨1441910883374150135826509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 961273922249433423884339 1441910883374150135826509)
              ·
                refine ⟨540716581265306300934941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1441910883374150135826509 540716581265306300934941)
                ·
                  refine ⟨202768717974489862850603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 540716581265306300934941 202768717974489862850603)
                  ·
                    rfl

theorem cell20_444252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 3, 3].length) (baseStart_444252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_444252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_444252 prefixEnd_444252 := by exact prefixLift 444252
  have htrace : WordTrace (prefixWord ++ tailWord_444252) baseStart_444252 baseEnd_444252 := by
    simpa [prefixWord, tailWord_444252, baseEnd_444252] using wordTrace_append hprefix tailTrace_444252
  have hstable : (prefixWord ++ tailWord_444252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444252).length < 2 ^ (prefixWord ++ tailWord_444252).sum := by decide
  have hdescent : baseEnd_444252 < baseStart_444252 := by decide
  rcases family_descends (prefixWord ++ tailWord_444252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444263 : List Nat := [1, 1, 5, 1, 2, 1, 2, 1, 6]
def baseStart_444263 : Nat := 118140960795 + 444263 * 2 ^ 59
def prefixEnd_444263 : Nat := 4983230072969 + 3 ^ 40 * 444263 * 2
def baseEnd_444263 : Nat := 202773738674222713483891

theorem tailTrace_444263 : CollatzResearch.WordTrace tailWord_444263 prefixEnd_444263 202773738674222713483891 := by
  unfold tailWord_444263
  simp only [CollatzResearch.WordTrace]
  refine ⟨16203602789518499924865443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10802401859678999949910295 16203602789518499924865443)
  ·
    refine ⟨24305404184277749887298165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16203602789518499924865443 24305404184277749887298165)
    ·
      refine ⟨2278631642276039051934203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24305404184277749887298165 2278631642276039051934203)
      ·
        refine ⟨3417947463414058577901305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2278631642276039051934203 3417947463414058577901305)
        ·
          refine ⟨2563460597560543933425979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3417947463414058577901305 2563460597560543933425979)
          ·
            refine ⟨3845190896340815900138969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2563460597560543933425979 3845190896340815900138969)
            ·
              refine ⟨2883893172255611925104227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3845190896340815900138969 2883893172255611925104227)
              ·
                refine ⟨4325839758383417887656341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2883893172255611925104227 4325839758383417887656341)
                ·
                  refine ⟨202773738674222713483891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4325839758383417887656341 202773738674222713483891)
                  ·
                    rfl

theorem cell20_444263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 6].length) (baseStart_444263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_444263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_444263 prefixEnd_444263 := by exact prefixLift 444263
  have htrace : WordTrace (prefixWord ++ tailWord_444263) baseStart_444263 baseEnd_444263 := by
    simpa [prefixWord, tailWord_444263, baseEnd_444263] using wordTrace_append hprefix tailTrace_444263
  have hstable : (prefixWord ++ tailWord_444263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444263).length < 2 ^ (prefixWord ++ tailWord_444263).sum := by decide
  have hdescent : baseEnd_444263 < baseStart_444263 := by decide
  rcases family_descends (prefixWord ++ tailWord_444263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444349 : List Nat := [1, 4, 1, 2, 3, 1, 3, 2, 3]
def baseStart_444349 : Nat := 118140960795 + 444349 * 2 ^ 59
def prefixEnd_444349 : Nat := 4983230072969 + 3 ^ 40 * 444349 * 2
def baseEnd_444349 : Nat := 202812991417588636616873

theorem tailTrace_444349 : CollatzResearch.WordTrace tailWord_444349 prefixEnd_444349 202812991417588636616873 := by
  unfold tailWord_444349
  simp only [CollatzResearch.WordTrace]
  refine ⟨16206739467206936612496101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10804492978137957741664067 16206739467206936612496101)
  ·
    refine ⟨3038763650101300614843019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16206739467206936612496101 3038763650101300614843019)
    ·
      refine ⟨4558145475151950922264529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3038763650101300614843019 4558145475151950922264529)
      ·
        refine ⟨3418609106363963191698397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4558145475151950922264529 3418609106363963191698397)
        ·
          refine ⟨1281978414886486196886899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3418609106363963191698397 1281978414886486196886899)
          ·
            refine ⟨1922967622329729295330349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1281978414886486196886899 1922967622329729295330349)
            ·
              refine ⟨721112858373648485748881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1922967622329729295330349 721112858373648485748881)
              ·
                refine ⟨540834643780236364311661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 721112858373648485748881 540834643780236364311661)
                ·
                  refine ⟨202812991417588636616873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 540834643780236364311661 202812991417588636616873)
                  ·
                    rfl

theorem cell20_444349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_444349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_444349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_444349 prefixEnd_444349 := by exact prefixLift 444349
  have htrace : WordTrace (prefixWord ++ tailWord_444349) baseStart_444349 baseEnd_444349 := by
    simpa [prefixWord, tailWord_444349, baseEnd_444349] using wordTrace_append hprefix tailTrace_444349
  have hstable : (prefixWord ++ tailWord_444349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444349).length < 2 ^ (prefixWord ++ tailWord_444349).sum := by decide
  have hdescent : baseEnd_444349 < baseStart_444349 := by decide
  rcases family_descends (prefixWord ++ tailWord_444349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444386 : List Nat := [3, 3, 3, 1, 3, 1, 1, 3, 2]
def baseStart_444386 : Nat := 118140960795 + 444386 * 2 ^ 59
def prefixEnd_444386 : Nat := 4983230072969 + 3 ^ 40 * 444386 * 2
def baseEnd_444386 : Nat := 202829879225780952383389

theorem tailTrace_444386 : CollatzResearch.WordTrace tailWord_444386 prefixEnd_444386 202829879225780952383389 := by
  unfold tailWord_444386
  simp only [CollatzResearch.WordTrace]
  refine ⟨4052022242018222982898253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10805392645381927954395341 4052022242018222982898253)
  ·
    refine ⟨1519508340756833618586845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4052022242018222982898253 1519508340756833618586845)
    ·
      refine ⟨569815627783812606970067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1519508340756833618586845 569815627783812606970067)
      ·
        refine ⟨854723441675718910455101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 569815627783812606970067 854723441675718910455101)
        ·
          refine ⟨320521290628394591420663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 854723441675718910455101 320521290628394591420663)
          ·
            refine ⟨480781935942591887130995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320521290628394591420663 480781935942591887130995)
            ·
              refine ⟨721172903913887830696493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 480781935942591887130995 721172903913887830696493)
              ·
                refine ⟨270439838967707936511185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 721172903913887830696493 270439838967707936511185)
                ·
                  refine ⟨202829879225780952383389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 270439838967707936511185 202829879225780952383389)
                  ·
                    rfl

theorem cell20_444386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_444386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_444386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_444386 prefixEnd_444386 := by exact prefixLift 444386
  have htrace : WordTrace (prefixWord ++ tailWord_444386) baseStart_444386 baseEnd_444386 := by
    simpa [prefixWord, tailWord_444386, baseEnd_444386] using wordTrace_append hprefix tailTrace_444386
  have hstable : (prefixWord ++ tailWord_444386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444386).length < 2 ^ (prefixWord ++ tailWord_444386).sum := by decide
  have hdescent : baseEnd_444386 < baseStart_444386 := by decide
  rcases family_descends (prefixWord ++ tailWord_444386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444397 : List Nat := [1, 5, 1, 4, 2, 1, 6]
def baseStart_444397 : Nat := 118140960795 + 444397 * 2 ^ 59
def prefixEnd_444397 : Nat := 4983230072969 + 3 ^ 40 * 444397 * 2
def baseEnd_444397 : Nat := 22537211102834867001853

theorem tailTrace_444397 : CollatzResearch.WordTrace tailWord_444397 prefixEnd_444397 22537211102834867001853 := by
  unfold tailWord_444397
  simp only [CollatzResearch.WordTrace]
  refine ⟨16208490171033040810243445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10805660114022027206828963 16208490171033040810243445)
  ·
    refine ⟨1519545953534347575960323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16208490171033040810243445 1519545953534347575960323)
    ·
      refine ⟨2279318930301521363940485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1519545953534347575960323 2279318930301521363940485)
      ·
        refine ⟨427372299431535255738841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2279318930301521363940485 427372299431535255738841)
        ·
          refine ⟨320529224573651441804131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 427372299431535255738841 320529224573651441804131)
          ·
            refine ⟨480793836860477162706197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320529224573651441804131 480793836860477162706197)
            ·
              refine ⟨22537211102834867001853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 480793836860477162706197 22537211102834867001853)
              ·
                rfl

theorem cell20_444397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 6].length) (baseStart_444397 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_444397 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_444397 prefixEnd_444397 := by exact prefixLift 444397
  have htrace : WordTrace (prefixWord ++ tailWord_444397) baseStart_444397 baseEnd_444397 := by
    simpa [prefixWord, tailWord_444397, baseEnd_444397] using wordTrace_append hprefix tailTrace_444397
  have hstable : (prefixWord ++ tailWord_444397).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444397).length < 2 ^ (prefixWord ++ tailWord_444397).sum := by decide
  have hdescent : baseEnd_444397 < baseStart_444397 := by decide
  rcases family_descends (prefixWord ++ tailWord_444397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444401 : List Nat := [1, 2, 2, 2, 5, 2, 6]
def baseStart_444401 : Nat := 118140960795 + 444401 * 2 ^ 59
def prefixEnd_444401 : Nat := 4983230072969 + 3 ^ 40 * 444401 * 2
def baseEnd_444401 : Nat := 22537413959389729653703

theorem tailTrace_444401 : CollatzResearch.WordTrace tailWord_444401 prefixEnd_444401 22537413959389729653703 := by
  unfold tailWord_444401
  simp only [CollatzResearch.WordTrace]
  refine ⟨16208636063018549493389057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10805757375345699662259371 16208636063018549493389057)
  ·
    refine ⟨12156477047263912120041793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16208636063018549493389057 12156477047263912120041793)
    ·
      refine ⟨9117357785447934090031345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12156477047263912120041793 9117357785447934090031345)
      ·
        refine ⟨6838018339085950567523509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9117357785447934090031345 6838018339085950567523509)
        ·
          refine ⟨641064219289307865705329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6838018339085950567523509 641064219289307865705329)
          ·
            refine ⟨480798164466980899278997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 641064219289307865705329 480798164466980899278997)
            ·
              refine ⟨22537413959389729653703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 480798164466980899278997 22537413959389729653703)
              ·
                rfl

theorem cell20_444401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 6].length) (baseStart_444401 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_444401 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_444401 prefixEnd_444401 := by exact prefixLift 444401
  have htrace : WordTrace (prefixWord ++ tailWord_444401) baseStart_444401 baseEnd_444401 := by
    simpa [prefixWord, tailWord_444401, baseEnd_444401] using wordTrace_append hprefix tailTrace_444401
  have hstable : (prefixWord ++ tailWord_444401).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444401).length < 2 ^ (prefixWord ++ tailWord_444401).sum := by decide
  have hdescent : baseEnd_444401 < baseStart_444401 := by decide
  rcases family_descends (prefixWord ++ tailWord_444401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444456 : List Nat := [2, 1, 5, 3, 2, 7]
def baseStart_444456 : Nat := 118140960795 + 444456 * 2 ^ 59
def prefixEnd_444456 : Nat := 4983230072969 + 3 ^ 40 * 444456 * 2
def baseEnd_444456 : Nat := 7513401079006363705547

theorem tailTrace_444456 : CollatzResearch.WordTrace tailWord_444456 prefixEnd_444456 7513401079006363705547 := by
  unfold tailWord_444456
  simp only [CollatzResearch.WordTrace]
  refine ⟨8105321038909646943320611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10807094718546195924427481 8105321038909646943320611)
  ·
    refine ⟨12157981558364470414980917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8105321038909646943320611 12157981558364470414980917)
    ·
      refine ⟨1139810771096669101404461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12157981558364470414980917 1139810771096669101404461)
      ·
        refine ⟨427429039161250913026673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1139810771096669101404461 427429039161250913026673)
        ·
          refine ⟨320571779370938184770005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 427429039161250913026673 320571779370938184770005)
          ·
            refine ⟨7513401079006363705547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 320571779370938184770005 7513401079006363705547)
            ·
              rfl

theorem cell20_444456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 7].length) (baseStart_444456 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_444456 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_444456 prefixEnd_444456 := by exact prefixLift 444456
  have htrace : WordTrace (prefixWord ++ tailWord_444456) baseStart_444456 baseEnd_444456 := by
    simpa [prefixWord, tailWord_444456, baseEnd_444456] using wordTrace_append hprefix tailTrace_444456
  have hstable : (prefixWord ++ tailWord_444456).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444456).length < 2 ^ (prefixWord ++ tailWord_444456).sum := by decide
  have hdescent : baseEnd_444456 < baseStart_444456 := by decide
  rcases family_descends (prefixWord ++ tailWord_444456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444466 : List Nat := [3, 2, 1, 1, 2, 5, 2, 2, 2]
def baseStart_444466 : Nat := 118140960795 + 444466 * 2 ^ 59
def prefixEnd_444466 : Nat := 4983230072969 + 3 ^ 40 * 444466 * 2
def baseEnd_444466 : Nat := 202866393405656229716395

theorem tailTrace_444466 : CollatzResearch.WordTrace tailWord_444466 prefixEnd_444466 202866393405656229716395 := by
  unfold tailWord_444466
  simp only [CollatzResearch.WordTrace]
  refine ⟨4052751701945766398626313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10807337871855377063003501 4052751701945766398626313)
  ·
    refine ⟨3039563776459324798969735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4052751701945766398626313 3039563776459324798969735)
    ·
      refine ⟨4559345664688987198454603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3039563776459324798969735 4559345664688987198454603)
      ·
        refine ⟨6839018497033480797681905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4559345664688987198454603 6839018497033480797681905)
        ·
          refine ⟨5129263872775110598261429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6839018497033480797681905 5129263872775110598261429)
          ·
            refine ⟨480868488072666618587009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5129263872775110598261429 480868488072666618587009)
            ·
              refine ⟨360651366054499963940257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 480868488072666618587009 360651366054499963940257)
              ·
                refine ⟨270488524540874972955193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 360651366054499963940257 270488524540874972955193)
                ·
                  refine ⟨202866393405656229716395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 270488524540874972955193 202866393405656229716395)
                  ·
                    rfl

theorem cell20_444466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 2, 2].length) (baseStart_444466 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_444466 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_444466 prefixEnd_444466 := by exact prefixLift 444466
  have htrace : WordTrace (prefixWord ++ tailWord_444466) baseStart_444466 baseEnd_444466 := by
    simpa [prefixWord, tailWord_444466, baseEnd_444466] using wordTrace_append hprefix tailTrace_444466
  have hstable : (prefixWord ++ tailWord_444466).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444466).length < 2 ^ (prefixWord ++ tailWord_444466).sum := by decide
  have hdescent : baseEnd_444466 < baseStart_444466 := by decide
  rcases family_descends (prefixWord ++ tailWord_444466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444467 : List Nat := [1, 1, 1, 2, 4, 1, 2, 3, 5]
def baseStart_444467 : Nat := 118140960795 + 444467 * 2 ^ 59
def prefixEnd_444467 : Nat := 4983230072969 + 3 ^ 40 * 444467 * 2
def baseEnd_444467 : Nat := 202866849832904670683057

theorem tailTrace_444467 : CollatzResearch.WordTrace tailWord_444467 prefixEnd_444467 202866849832904670683057 := by
  unfold tailWord_444467
  simp only [CollatzResearch.WordTrace]
  refine ⟨16211043280779442765291655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10807362187186295176861103 16211043280779442765291655)
  ·
    refine ⟨24316564921169164147937483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16211043280779442765291655 24316564921169164147937483)
    ·
      refine ⟨36474847381753746221906225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24316564921169164147937483 36474847381753746221906225)
      ·
        refine ⟨27356135536315309666429669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36474847381753746221906225 27356135536315309666429669)
        ·
          refine ⟨5129275413059120562455563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27356135536315309666429669 5129275413059120562455563)
          ·
            refine ⟨7693913119588680843683345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5129275413059120562455563 7693913119588680843683345)
            ·
              refine ⟨5770434839691510632762509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7693913119588680843683345 5770434839691510632762509)
              ·
                refine ⟨2163913064884316487285941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5770434839691510632762509 2163913064884316487285941)
                ·
                  refine ⟨202866849832904670683057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2163913064884316487285941 202866849832904670683057)
                  ·
                    rfl

theorem cell20_444467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 5].length) (baseStart_444467 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_444467 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_444467 prefixEnd_444467 := by exact prefixLift 444467
  have htrace : WordTrace (prefixWord ++ tailWord_444467) baseStart_444467 baseEnd_444467 := by
    simpa [prefixWord, tailWord_444467, baseEnd_444467] using wordTrace_append hprefix tailTrace_444467
  have hstable : (prefixWord ++ tailWord_444467).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444467).length < 2 ^ (prefixWord ++ tailWord_444467).sum := by decide
  have hdescent : baseEnd_444467 < baseStart_444467 := by decide
  rcases family_descends (prefixWord ++ tailWord_444467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444470 : List Nat := [5, 1, 2, 1, 1, 1, 2, 3, 4]
def baseStart_444470 : Nat := 118140960795 + 444470 * 2 ^ 59
def prefixEnd_444470 : Nat := 4983230072969 + 3 ^ 40 * 444470 * 2
def baseEnd_444470 : Nat := 202868219114649993583045

theorem tailTrace_444470 : CollatzResearch.WordTrace tailWord_444470 prefixEnd_444470 202868219114649993583045 := by
  unfold tailWord_444470
  simp only [CollatzResearch.WordTrace]
  refine ⟨1013197043735535892353179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10807435133179049518433909 1013197043735535892353179)
  ·
    refine ⟨1519795565603303838529769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1013197043735535892353179 1519795565603303838529769)
    ·
      refine ⟨1139846674202477878897327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1519795565603303838529769 1139846674202477878897327)
      ·
        refine ⟨1709770011303716818345991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1139846674202477878897327 1709770011303716818345991)
        ·
          refine ⟨2564655016955575227518987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1709770011303716818345991 2564655016955575227518987)
          ·
            refine ⟨3846982525433362841278481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2564655016955575227518987 3846982525433362841278481)
            ·
              refine ⟨2885236894075022130958861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3846982525433362841278481 2885236894075022130958861)
              ·
                refine ⟨1081963835278133299109573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2885236894075022130958861 1081963835278133299109573)
                ·
                  refine ⟨202868219114649993583045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1081963835278133299109573 202868219114649993583045)
                  ·
                    rfl

theorem cell20_444470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_444470 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_444470 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_444470 prefixEnd_444470 := by exact prefixLift 444470
  have htrace : WordTrace (prefixWord ++ tailWord_444470) baseStart_444470 baseEnd_444470 := by
    simpa [prefixWord, tailWord_444470, baseEnd_444470] using wordTrace_append hprefix tailTrace_444470
  have hstable : (prefixWord ++ tailWord_444470).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444470).length < 2 ^ (prefixWord ++ tailWord_444470).sum := by decide
  have hdescent : baseEnd_444470 < baseStart_444470 := by decide
  rcases family_descends (prefixWord ++ tailWord_444470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444505 : List Nat := [1, 2, 1, 2, 2, 1, 4, 2, 5]
def baseStart_444505 : Nat := 118140960795 + 444505 * 2 ^ 59
def prefixEnd_444505 : Nat := 4983230072969 + 3 ^ 40 * 444505 * 2
def baseEnd_444505 : Nat := 202884194068345427416235

theorem tailTrace_444505 : CollatzResearch.WordTrace tailWord_444505 prefixEnd_444505 202884194068345427416235 := by
  unfold tailWord_444505
  simp only [CollatzResearch.WordTrace]
  refine ⟨16212429254641775255174969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10808286169761183503449979 16212429254641775255174969)
  ·
    refine ⟨12159321940981331441381227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16212429254641775255174969 12159321940981331441381227)
    ·
      refine ⟨18238982911471997162071841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12159321940981331441381227 18238982911471997162071841)
      ·
        refine ⟨13679237183603997871553881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18238982911471997162071841 13679237183603997871553881)
        ·
          refine ⟨10259427887702998403665411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13679237183603997871553881 10259427887702998403665411)
          ·
            refine ⟨15389141831554497605498117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10259427887702998403665411 15389141831554497605498117)
            ·
              refine ⟨2885464093416468301030897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15389141831554497605498117 2885464093416468301030897)
              ·
                refine ⟨2164098070062351225773173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2885464093416468301030897 2164098070062351225773173)
                ·
                  refine ⟨202884194068345427416235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2164098070062351225773173 202884194068345427416235)
                  ·
                    rfl

theorem cell20_444505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 5].length) (baseStart_444505 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_444505 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_444505 prefixEnd_444505 := by exact prefixLift 444505
  have htrace : WordTrace (prefixWord ++ tailWord_444505) baseStart_444505 baseEnd_444505 := by
    simpa [prefixWord, tailWord_444505, baseEnd_444505] using wordTrace_append hprefix tailTrace_444505
  have hstable : (prefixWord ++ tailWord_444505).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444505).length < 2 ^ (prefixWord ++ tailWord_444505).sum := by decide
  have hdescent : baseEnd_444505 < baseStart_444505 := by decide
  rcases family_descends (prefixWord ++ tailWord_444505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444529 : List Nat := [1, 2, 2, 2, 1, 1, 6, 1, 4]
def baseStart_444529 : Nat := 118140960795 + 444529 * 2 ^ 59
def prefixEnd_444529 : Nat := 4983230072969 + 3 ^ 40 * 444529 * 2
def baseEnd_444529 : Nat := 202895148322308010616137

theorem tailTrace_444529 : CollatzResearch.WordTrace tailWord_444529 prefixEnd_444529 202895148322308010616137 := by
  unfold tailWord_444529
  simp only [CollatzResearch.WordTrace]
  refine ⟨16213304606554827354048641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10808869737703218236032427 16213304606554827354048641)
  ·
    refine ⟨12159978454916120515536481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16213304606554827354048641 12159978454916120515536481)
    ·
      refine ⟨9119983841187090386652361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12159978454916120515536481 9119983841187090386652361)
      ·
        refine ⟨6839987880890317789989271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9119983841187090386652361 6839987880890317789989271)
        ·
          refine ⟨10259981821335476684983907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6839987880890317789989271 10259981821335476684983907)
          ·
            refine ⟨15389972732003215027475861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10259981821335476684983907 15389972732003215027475861)
            ·
              refine ⟨721404971812650704412931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15389972732003215027475861 721404971812650704412931)
              ·
                refine ⟨1082107457718976056619397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 721404971812650704412931 1082107457718976056619397)
                ·
                  refine ⟨202895148322308010616137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1082107457718976056619397 202895148322308010616137)
                  ·
                    rfl

theorem cell20_444529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 4].length) (baseStart_444529 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_444529 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_444529 prefixEnd_444529 := by exact prefixLift 444529
  have htrace : WordTrace (prefixWord ++ tailWord_444529) baseStart_444529 baseEnd_444529 := by
    simpa [prefixWord, tailWord_444529, baseEnd_444529] using wordTrace_append hprefix tailTrace_444529
  have hstable : (prefixWord ++ tailWord_444529).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444529).length < 2 ^ (prefixWord ++ tailWord_444529).sum := by decide
  have hdescent : baseEnd_444529 < baseStart_444529 := by decide
  rcases family_descends (prefixWord ++ tailWord_444529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444570 : List Nat := [3, 1, 1, 5, 3, 1, 6]
def baseStart_444570 : Nat := 118140960795 + 444570 * 2 ^ 59
def prefixEnd_444570 : Nat := 4983230072969 + 3 ^ 40 * 444570 * 2
def baseEnd_444570 : Nat := 22545984648832676694367

theorem tailTrace_444570 : CollatzResearch.WordTrace tailWord_444570 prefixEnd_444570 22545984648832676694367 := by
  unfold tailWord_444570
  simp only [CollatzResearch.WordTrace]
  refine ⟨4053699999851572839072791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10809866666270860904194109 4053699999851572839072791)
  ·
    refine ⟨6080549999777359258609187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4053699999851572839072791 6080549999777359258609187)
    ·
      refine ⟨9120824999666038887913781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6080549999777359258609187 9120824999666038887913781)
      ·
        refine ⟨855077343718691145741917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9120824999666038887913781 855077343718691145741917)
        ·
          refine ⟨320654003894509179653219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 855077343718691145741917 320654003894509179653219)
          ·
            refine ⟨480981005841763769479829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320654003894509179653219 480981005841763769479829)
            ·
              refine ⟨22545984648832676694367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 480981005841763769479829 22545984648832676694367)
              ·
                rfl

theorem cell20_444570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 6].length) (baseStart_444570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_444570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_444570 prefixEnd_444570 := by exact prefixLift 444570
  have htrace : WordTrace (prefixWord ++ tailWord_444570) baseStart_444570 baseEnd_444570 := by
    simpa [prefixWord, tailWord_444570, baseEnd_444570] using wordTrace_append hprefix tailTrace_444570
  have hstable : (prefixWord ++ tailWord_444570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444570).length < 2 ^ (prefixWord ++ tailWord_444570).sum := by decide
  have hdescent : baseEnd_444570 < baseStart_444570 := by decide
  rcases family_descends (prefixWord ++ tailWord_444570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444580 : List Nat := [2, 3, 1, 2, 4, 1, 3, 2, 2]
def baseStart_444580 : Nat := 118140960795 + 444580 * 2 ^ 59
def prefixEnd_444580 : Nat := 4983230072969 + 3 ^ 40 * 444580 * 2
def baseEnd_444580 : Nat := 202918426111978499915929

theorem tailTrace_444580 : CollatzResearch.WordTrace tailWord_444580 prefixEnd_444580 202918426111978499915929 := by
  unfold tailWord_444580
  simp only [CollatzResearch.WordTrace]
  refine ⟨8107582364685031532077597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10810109819580042042770129 8107582364685031532077597)
  ·
    refine ⟨3040343386756886824529099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8107582364685031532077597 3040343386756886824529099)
    ·
      refine ⟨4560515080135330236793649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3040343386756886824529099 4560515080135330236793649)
      ·
        refine ⟨3420386310101497677595237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4560515080135330236793649 3420386310101497677595237)
        ·
          refine ⟨641322433144030814549107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3420386310101497677595237 641322433144030814549107)
          ·
            refine ⟨961983649716046221823661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 641322433144030814549107 961983649716046221823661)
            ·
              refine ⟨360743868643517333183873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 961983649716046221823661 360743868643517333183873)
              ·
                refine ⟨270557901482637999887905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 360743868643517333183873 270557901482637999887905)
                ·
                  refine ⟨202918426111978499915929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 270557901482637999887905 202918426111978499915929)
                  ·
                    rfl

theorem cell20_444580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 2, 2].length) (baseStart_444580 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_444580 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_444580 prefixEnd_444580 := by exact prefixLift 444580
  have htrace : WordTrace (prefixWord ++ tailWord_444580) baseStart_444580 baseEnd_444580 := by
    simpa [prefixWord, tailWord_444580, baseEnd_444580] using wordTrace_append hprefix tailTrace_444580
  have hstable : (prefixWord ++ tailWord_444580).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444580).length < 2 ^ (prefixWord ++ tailWord_444580).sum := by decide
  have hdescent : baseEnd_444580 < baseStart_444580 := by decide
  rcases family_descends (prefixWord ++ tailWord_444580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444581 : List Nat := [1, 3, 1, 2, 1, 3, 1, 3, 5]
def baseStart_444581 : Nat := 118140960795 + 444581 * 2 ^ 59
def prefixEnd_444581 : Nat := 4983230072969 + 3 ^ 40 * 444581 * 2
def baseEnd_444581 : Nat := 202918882539226940882591

theorem tailTrace_444581 : CollatzResearch.WordTrace tailWord_444581 prefixEnd_444581 202918882539226940882591 := by
  unfold tailWord_444581
  simp only [CollatzResearch.WordTrace]
  refine ⟨16215201202366440234941597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10810134134910960156627731 16215201202366440234941597)
  ·
    refine ⟨6080700450887415088103099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16215201202366440234941597 6080700450887415088103099)
    ·
      refine ⟨9121050676331122632154649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6080700450887415088103099 9121050676331122632154649)
      ·
        refine ⟨6840788007248341974115987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9121050676331122632154649 6840788007248341974115987)
        ·
          refine ⟨10261182010872512961173981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6840788007248341974115987 10261182010872512961173981)
          ·
            refine ⟨3847943254077192360440243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10261182010872512961173981 3847943254077192360440243)
            ·
              refine ⟨5771914881115788540660365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3847943254077192360440243 5771914881115788540660365)
              ·
                refine ⟨2164468080418420702747637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5771914881115788540660365 2164468080418420702747637)
                ·
                  refine ⟨202918882539226940882591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2164468080418420702747637 202918882539226940882591)
                  ·
                    rfl

theorem cell20_444581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_444581 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_444581 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_444581 prefixEnd_444581 := by exact prefixLift 444581
  have htrace : WordTrace (prefixWord ++ tailWord_444581) baseStart_444581 baseEnd_444581 := by
    simpa [prefixWord, tailWord_444581, baseEnd_444581] using wordTrace_append hprefix tailTrace_444581
  have hstable : (prefixWord ++ tailWord_444581).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444581).length < 2 ^ (prefixWord ++ tailWord_444581).sum := by decide
  have hdescent : baseEnd_444581 < baseStart_444581 := by decide
  rcases family_descends (prefixWord ++ tailWord_444581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444590 : List Nat := [4, 1, 4, 2, 1, 2, 2, 1, 3]
def baseStart_444590 : Nat := 118140960795 + 444590 * 2 ^ 59
def prefixEnd_444590 : Nat := 4983230072969 + 3 ^ 40 * 444590 * 2
def baseEnd_444590 : Nat := 202922990384462909582555

theorem tailTrace_444590 : CollatzResearch.WordTrace tailWord_444590 prefixEnd_444590 202922990384462909582555 := by
  unfold tailWord_444590
  simp only [CollatzResearch.WordTrace]
  refine ⟨2026941182416729346502403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10810352972889223181346149 2026941182416729346502403)
  ·
    refine ⟨3040411773625094019753605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2026941182416729346502403 3040411773625094019753605)
    ·
      refine ⟨570077207554705128703801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3040411773625094019753605 570077207554705128703801)
      ·
        refine ⟨427557905666028846527851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 570077207554705128703801 427557905666028846527851)
        ·
          refine ⟨641336858499043269791777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427557905666028846527851 641336858499043269791777)
          ·
            refine ⟨481002643874282452343833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 641336858499043269791777 481002643874282452343833)
            ·
              refine ⟨360751982905711839257875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 481002643874282452343833 360751982905711839257875)
              ·
                refine ⟨541127974358567758886813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 360751982905711839257875 541127974358567758886813)
                ·
                  refine ⟨202922990384462909582555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 541127974358567758886813 202922990384462909582555)
                  ·
                    rfl

theorem cell20_444590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_444590 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_444590 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_444590 prefixEnd_444590 := by exact prefixLift 444590
  have htrace : WordTrace (prefixWord ++ tailWord_444590) baseStart_444590 baseEnd_444590 := by
    simpa [prefixWord, tailWord_444590, baseEnd_444590] using wordTrace_append hprefix tailTrace_444590
  have hstable : (prefixWord ++ tailWord_444590).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444590).length < 2 ^ (prefixWord ++ tailWord_444590).sum := by decide
  have hdescent : baseEnd_444590 < baseStart_444590 := by decide
  rcases family_descends (prefixWord ++ tailWord_444590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
