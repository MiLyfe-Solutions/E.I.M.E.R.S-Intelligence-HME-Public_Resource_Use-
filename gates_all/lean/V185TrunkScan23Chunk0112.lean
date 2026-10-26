import V185TrunkScan23Chunk0111

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_662919 : List Nat := [1, 1, 4, 2, 2, 2, 2, 1, 3, 2, 3]
def baseStart_662919 : Nat := 118140960795 + 662919 * 2 ^ 59
def prefixEnd_662919 : Nat := 4983230072969 + 3 ^ 40 * 662919 * 2
def baseEnd_662919 : Nat := 340396081997997060063797

theorem tailTrace_662919 : CollatzResearch.WordTrace tailWord_662919 prefixEnd_662919 340396081997997060063797 := by
  unfold tailWord_662919
  simp only [CollatzResearch.WordTrace]
  refine ⟨24178642285365155396599811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16119094856910103597733207 24178642285365155396599811)
  ·
    refine ⟨36267963428047733094899717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24178642285365155396599811 36267963428047733094899717)
    ·
      refine ⟨6800243142758949955293697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36267963428047733094899717 6800243142758949955293697)
      ·
        refine ⟨5100182357069212466470273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6800243142758949955293697 5100182357069212466470273)
        ·
          refine ⟨3825136767801909349852705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5100182357069212466470273 3825136767801909349852705)
          ·
            refine ⟨2868852575851432012389529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3825136767801909349852705 2868852575851432012389529)
            ·
              refine ⟨2151639431888574009292147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2868852575851432012389529 2151639431888574009292147)
              ·
                refine ⟨3227459147832861013938221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2151639431888574009292147 3227459147832861013938221)
                ·
                  refine ⟨1210297180437322880226833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3227459147832861013938221 1210297180437322880226833)
                  ·
                    refine ⟨907722885327992160170125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1210297180437322880226833 907722885327992160170125)
                    ·
                      refine ⟨340396081997997060063797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 907722885327992160170125 340396081997997060063797)
                      ·
                        rfl

theorem cell23_662919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_662919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_662919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_662919 prefixEnd_662919 := by exact prefixLift 662919
  have htrace : WordTrace (prefixWord ++ tailWord_662919) baseStart_662919 baseEnd_662919 := by
    simpa [prefixWord, tailWord_662919, baseEnd_662919] using wordTrace_append hprefix tailTrace_662919
  have hstable : (prefixWord ++ tailWord_662919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662919).length < 2 ^ (prefixWord ++ tailWord_662919).sum := by decide
  have hdescent : baseEnd_662919 < baseStart_662919 := by decide
  rcases family_descends (prefixWord ++ tailWord_662919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662930 : List Nat := [3, 2, 3, 3, 1, 2, 2, 1, 1, 5]
def baseStart_662930 : Nat := 118140960795 + 662930 * 2 ^ 59
def prefixEnd_662930 : Nat := 4983230072969 + 3 ^ 40 * 662930 * 2
def baseEnd_662930 : Nat := 113467243428398839008749

theorem tailTrace_662930 : CollatzResearch.WordTrace tailWord_662930 prefixEnd_662930 113467243428398839008749 := by
  unfold tailWord_662930
  simp only [CollatzResearch.WordTrace]
  refine ⟨6044760872081326068812561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16119362325550202850166829 6044760872081326068812561)
  ·
    refine ⟨4533570654060994551609421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6044760872081326068812561 4533570654060994551609421)
    ·
      refine ⟨1700088995272872956853533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4533570654060994551609421 1700088995272872956853533)
      ·
        refine ⟨637533373227327358820075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1700088995272872956853533 637533373227327358820075)
        ·
          refine ⟨956300059840991038230113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 637533373227327358820075 956300059840991038230113)
          ·
            refine ⟨717225044880743278672585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 956300059840991038230113 717225044880743278672585)
            ·
              refine ⟨537918783660557459004439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 717225044880743278672585 537918783660557459004439)
              ·
                refine ⟨806878175490836188506659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 537918783660557459004439 806878175490836188506659)
                ·
                  refine ⟨1210317263236254282759989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 806878175490836188506659 1210317263236254282759989)
                  ·
                    refine ⟨113467243428398839008749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1210317263236254282759989 113467243428398839008749)
                    ·
                      rfl

theorem cell23_662930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_662930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_662930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_662930 prefixEnd_662930 := by exact prefixLift 662930
  have htrace : WordTrace (prefixWord ++ tailWord_662930) baseStart_662930 baseEnd_662930 := by
    simpa [prefixWord, tailWord_662930, baseEnd_662930] using wordTrace_append hprefix tailTrace_662930
  have hstable : (prefixWord ++ tailWord_662930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662930).length < 2 ^ (prefixWord ++ tailWord_662930).sum := by decide
  have hdescent : baseEnd_662930 < baseStart_662930 := by decide
  rcases family_descends (prefixWord ++ tailWord_662930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662933 : List Nat := [1, 3, 2, 1, 1, 2, 3, 5, 1, 2, 2]
def baseStart_662933 : Nat := 118140960795 + 662933 * 2 ^ 59
def prefixEnd_662933 : Nat := 4983230072969 + 3 ^ 40 * 662933 * 2
def baseEnd_662933 : Nat := 340403270727160005288733

theorem tailTrace_662933 : CollatzResearch.WordTrace tailWord_662933 prefixEnd_662933 340403270727160005288733 := by
  unfold tailWord_662933
  simp only [CollatzResearch.WordTrace]
  refine ⟨24179152907314435787609453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16119435271542957191739635 24179152907314435787609453)
  ·
    refine ⟨9067182340242913420353545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24179152907314435787609453 9067182340242913420353545)
    ·
      refine ⟨6800386755182185065265159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9067182340242913420353545 6800386755182185065265159)
      ·
        refine ⟨10200580132773277597897739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6800386755182185065265159 10200580132773277597897739)
        ·
          refine ⟨15300870199159916396846609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10200580132773277597897739 15300870199159916396846609)
          ·
            refine ⟨11475652649369937297634957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15300870199159916396846609 11475652649369937297634957)
            ·
              refine ⟨4303369743513726486613109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11475652649369937297634957 4303369743513726486613109)
              ·
                refine ⟨403440913454411858119979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4303369743513726486613109 403440913454411858119979)
                ·
                  refine ⟨605161370181617787179969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 403440913454411858119979 605161370181617787179969)
                  ·
                    refine ⟨453871027636213340384977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 605161370181617787179969 453871027636213340384977)
                    ·
                      refine ⟨340403270727160005288733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 453871027636213340384977 340403270727160005288733)
                      ·
                        rfl

theorem cell23_662933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 5, 1, 2, 2].length) (baseStart_662933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_662933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_662933 prefixEnd_662933 := by exact prefixLift 662933
  have htrace : WordTrace (prefixWord ++ tailWord_662933) baseStart_662933 baseEnd_662933 := by
    simpa [prefixWord, tailWord_662933, baseEnd_662933] using wordTrace_append hprefix tailTrace_662933
  have hstable : (prefixWord ++ tailWord_662933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662933).length < 2 ^ (prefixWord ++ tailWord_662933).sum := by decide
  have hdescent : baseEnd_662933 < baseStart_662933 := by decide
  rcases family_descends (prefixWord ++ tailWord_662933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662959 : List Nat := [1, 1, 2, 1, 2, 2, 1, 3, 5, 3, 2]
def baseStart_662959 : Nat := 118140960795 + 662959 * 2 ^ 59
def prefixEnd_662959 : Nat := 4983230072969 + 3 ^ 40 * 662959 * 2
def baseEnd_662959 : Nat := 340416621224176903563613

theorem tailTrace_662959 : CollatzResearch.WordTrace tailWord_662959 prefixEnd_662959 340416621224176903563613 := by
  unfold tailWord_662959
  simp only [CollatzResearch.WordTrace]
  refine ⟨24180101205220242228055931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16120067470146828152037287 24180101205220242228055931)
  ·
    refine ⟨36270151807830363342083897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24180101205220242228055931 36270151807830363342083897)
    ·
      refine ⟨27202613855872772506562923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36270151807830363342083897 27202613855872772506562923)
      ·
        refine ⟨40803920783809158759844385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27202613855872772506562923 40803920783809158759844385)
        ·
          refine ⟨30602940587856869069883289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40803920783809158759844385 30602940587856869069883289)
          ·
            refine ⟨22952205440892651802412467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30602940587856869069883289 22952205440892651802412467)
            ·
              refine ⟨34428308161338977703618701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22952205440892651802412467 34428308161338977703618701)
              ·
                refine ⟨12910615560502116638857013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34428308161338977703618701 12910615560502116638857013)
                ·
                  refine ⟨1210370208797073434892845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12910615560502116638857013 1210370208797073434892845)
                  ·
                    refine ⟨453888828298902538084817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1210370208797073434892845 453888828298902538084817)
                    ·
                      refine ⟨340416621224176903563613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 453888828298902538084817 340416621224176903563613)
                      ·
                        rfl

theorem cell23_662959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 5, 3, 2].length) (baseStart_662959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_662959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_662959 prefixEnd_662959 := by exact prefixLift 662959
  have htrace : WordTrace (prefixWord ++ tailWord_662959) baseStart_662959 baseEnd_662959 := by
    simpa [prefixWord, tailWord_662959, baseEnd_662959] using wordTrace_append hprefix tailTrace_662959
  have hstable : (prefixWord ++ tailWord_662959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662959).length < 2 ^ (prefixWord ++ tailWord_662959).sum := by decide
  have hdescent : baseEnd_662959 < baseStart_662959 := by decide
  rcases family_descends (prefixWord ++ tailWord_662959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662976 : List Nat := [2, 1, 1, 2, 3, 1, 3, 4, 1, 3, 2]
def baseStart_662976 : Nat := 118140960795 + 662976 * 2 ^ 59
def prefixEnd_662976 : Nat := 4983230072969 + 3 ^ 40 * 662976 * 2
def baseEnd_662976 : Nat := 340425350395303337051035

theorem tailTrace_662976 : CollatzResearch.WordTrace tailWord_662976 prefixEnd_662976 340425350395303337051035 := by
  unfold tailWord_662976
  simp only [CollatzResearch.WordTrace]
  refine ⟨12090360623079327065712391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16120480830772436087616521 12090360623079327065712391)
  ·
    refine ⟨18135540934618990598568587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12090360623079327065712391 18135540934618990598568587)
    ·
      refine ⟨27203311401928485897852881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18135540934618990598568587 27203311401928485897852881)
      ·
        refine ⟨20402483551446364423389661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27203311401928485897852881 20402483551446364423389661)
        ·
          refine ⟨7650931331792386658771123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20402483551446364423389661 7650931331792386658771123)
          ·
            refine ⟨11476396997688579988156685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7650931331792386658771123 11476396997688579988156685)
            ·
              refine ⟨4303648874133217495558757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11476396997688579988156685 4303648874133217495558757)
              ·
                refine ⟨806934163899978280417267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4303648874133217495558757 806934163899978280417267)
                ·
                  refine ⟨1210401245849967420625901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 806934163899978280417267 1210401245849967420625901)
                  ·
                    refine ⟨453900467193737782734713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1210401245849967420625901 453900467193737782734713)
                    ·
                      refine ⟨340425350395303337051035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 453900467193737782734713 340425350395303337051035)
                      ·
                        rfl

theorem cell23_662976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 4, 1, 3, 2].length) (baseStart_662976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_662976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_662976 prefixEnd_662976 := by exact prefixLift 662976
  have htrace : WordTrace (prefixWord ++ tailWord_662976) baseStart_662976 baseEnd_662976 := by
    simpa [prefixWord, tailWord_662976, baseEnd_662976] using wordTrace_append hprefix tailTrace_662976
  have hstable : (prefixWord ++ tailWord_662976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662976).length < 2 ^ (prefixWord ++ tailWord_662976).sum := by decide
  have hdescent : baseEnd_662976 < baseStart_662976 := by decide
  rcases family_descends (prefixWord ++ tailWord_662976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662978 : List Nat := [3, 5, 2, 1, 2, 1, 1, 3, 1, 1, 3]
def baseStart_662978 : Nat := 118140960795 + 662978 * 2 ^ 59
def prefixEnd_662978 : Nat := 4983230072969 + 3 ^ 40 * 662978 * 2
def baseEnd_662978 : Nat := 340426377356612329226027

theorem tailTrace_662978 : CollatzResearch.WordTrace tailWord_662978 prefixEnd_662978 340426377356612329226027 := by
  unfold tailWord_662978
  simp only [CollatzResearch.WordTrace]
  refine ⟨6045198548037852118249397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16120529461434272315331725 6045198548037852118249397)
  ·
    refine ⟨566737363878548636085881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6045198548037852118249397 566737363878548636085881)
    ·
      refine ⟨425053022908911477064411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 566737363878548636085881 425053022908911477064411)
      ·
        refine ⟨637579534363367215596617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 425053022908911477064411 637579534363367215596617)
        ·
          refine ⟨478184650772525411697463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 637579534363367215596617 478184650772525411697463)
          ·
            refine ⟨717276976158788117546195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 478184650772525411697463 717276976158788117546195)
            ·
              refine ⟨1075915464238182176319293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 717276976158788117546195 1075915464238182176319293)
              ·
                refine ⟨403468299089318316119735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1075915464238182176319293 403468299089318316119735)
                ·
                  refine ⟨605202448633977474179603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 403468299089318316119735 605202448633977474179603)
                  ·
                    refine ⟨907803672950966211269405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 605202448633977474179603 907803672950966211269405)
                    ·
                      refine ⟨340426377356612329226027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 907803672950966211269405 340426377356612329226027)
                      ·
                        rfl

theorem cell23_662978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_662978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_662978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_662978 prefixEnd_662978 := by exact prefixLift 662978
  have htrace : WordTrace (prefixWord ++ tailWord_662978) baseStart_662978 baseEnd_662978 := by
    simpa [prefixWord, tailWord_662978, baseEnd_662978] using wordTrace_append hprefix tailTrace_662978
  have hstable : (prefixWord ++ tailWord_662978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662978).length < 2 ^ (prefixWord ++ tailWord_662978).sum := by decide
  have hdescent : baseEnd_662978 < baseStart_662978 := by decide
  rcases family_descends (prefixWord ++ tailWord_662978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662992 : List Nat := [2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 5]
def baseStart_662992 : Nat := 118140960795 + 662992 * 2 ^ 59
def prefixEnd_662992 : Nat := 4983230072969 + 3 ^ 40 * 662992 * 2
def baseEnd_662992 : Nat := 340433566085775274450961

theorem tailTrace_662992 : CollatzResearch.WordTrace tailWord_662992 prefixEnd_662992 340433566085775274450961 := by
  unfold tailWord_662992
  simp only [CollatzResearch.WordTrace]
  refine ⟨12090652407050344432003615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16120869876067125909338153 12090652407050344432003615)
  ·
    refine ⟨18135978610575516648005423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12090652407050344432003615 18135978610575516648005423)
    ·
      refine ⟨27203967915863274972008135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18135978610575516648005423 27203967915863274972008135)
      ·
        refine ⟨40805951873794912458012203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27203967915863274972008135 40805951873794912458012203)
        ·
          refine ⟨61208927810692368687018305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40805951873794912458012203 61208927810692368687018305)
          ·
            refine ⟨45906695858019276515263729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61208927810692368687018305 45906695858019276515263729)
            ·
              refine ⟨34430021893514457386447797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45906695858019276515263729 34430021893514457386447797)
              ·
                refine ⟨3227814552516980379979481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34430021893514457386447797 3227814552516980379979481)
                ·
                  refine ⟨2420860914387735284984611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3227814552516980379979481 2420860914387735284984611)
                  ·
                    refine ⟨3631291371581602927476917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2420860914387735284984611 3631291371581602927476917)
                    ·
                      refine ⟨340433566085775274450961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3631291371581602927476917 340433566085775274450961)
                      ·
                        rfl

theorem cell23_662992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 5].length) (baseStart_662992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_662992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_662992 prefixEnd_662992 := by exact prefixLift 662992
  have htrace : WordTrace (prefixWord ++ tailWord_662992) baseStart_662992 baseEnd_662992 := by
    simpa [prefixWord, tailWord_662992, baseEnd_662992] using wordTrace_append hprefix tailTrace_662992
  have hstable : (prefixWord ++ tailWord_662992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662992).length < 2 ^ (prefixWord ++ tailWord_662992).sum := by decide
  have hdescent : baseEnd_662992 < baseStart_662992 := by decide
  rcases family_descends (prefixWord ++ tailWord_662992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663059 : List Nat := [1, 1, 1, 2, 1, 6, 2, 2, 2, 5]
def baseStart_663059 : Nat := 118140960795 + 663059 * 2 ^ 59
def prefixEnd_663059 : Nat := 4983230072969 + 3 ^ 40 * 663059 * 2
def baseEnd_663059 : Nat := 113489323096542170771051

theorem tailTrace_663059 : CollatzResearch.WordTrace tailWord_663059 prefixEnd_663059 113489323096542170771051 := by
  unfold tailWord_663059
  simp only [CollatzResearch.WordTrace]
  refine ⟨24183748504857959306696231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16122499003238639537797487 24183748504857959306696231)
  ·
    refine ⟨36275622757286938960044347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24183748504857959306696231 36275622757286938960044347)
    ·
      refine ⟨54413434135930408440066521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36275622757286938960044347 54413434135930408440066521)
      ·
        refine ⟨40810075601947806330049891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54413434135930408440066521 40810075601947806330049891)
        ·
          refine ⟨61215113402921709495074837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40810075601947806330049891 61215113402921709495074837)
          ·
            refine ⟨2869458440761955132581633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 61215113402921709495074837 2869458440761955132581633)
            ·
              refine ⟨2152093830571466349436225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2869458440761955132581633 2152093830571466349436225)
              ·
                refine ⟨1614070372928599762077169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2152093830571466349436225 1614070372928599762077169)
                ·
                  refine ⟨1210552779696449821557877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1614070372928599762077169 1210552779696449821557877)
                  ·
                    refine ⟨113489323096542170771051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1210552779696449821557877 113489323096542170771051)
                    ·
                      rfl

theorem cell23_663059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 2, 5].length) (baseStart_663059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_663059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_663059 prefixEnd_663059 := by exact prefixLift 663059
  have htrace : WordTrace (prefixWord ++ tailWord_663059) baseStart_663059 baseEnd_663059 := by
    simpa [prefixWord, tailWord_663059, baseEnd_663059] using wordTrace_append hprefix tailTrace_663059
  have hstable : (prefixWord ++ tailWord_663059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663059).length < 2 ^ (prefixWord ++ tailWord_663059).sum := by decide
  have hdescent : baseEnd_663059 < baseStart_663059 := by decide
  rcases family_descends (prefixWord ++ tailWord_663059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663069 : List Nat := [1, 4, 2, 2, 1, 1, 1, 3, 1, 2, 5]
def baseStart_663069 : Nat := 118140960795 + 663069 * 2 ^ 59
def prefixEnd_663069 : Nat := 4983230072969 + 3 ^ 40 * 663069 * 2
def baseEnd_663069 : Nat := 340473104096171473188107

theorem tailTrace_663069 : CollatzResearch.WordTrace tailWord_663069 prefixEnd_663069 340473104096171473188107 := by
  unfold tailWord_663069
  simp only [CollatzResearch.WordTrace]
  refine ⟨24184113234821731014560261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16122742156547820676373507 24184113234821731014560261)
  ·
    refine ⟨4534521231529074565230049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24184113234821731014560261 4534521231529074565230049)
    ·
      refine ⟨3400890923646805923922537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4534521231529074565230049 3400890923646805923922537)
      ·
        refine ⟨2550668192735104442941903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3400890923646805923922537 2550668192735104442941903)
        ·
          refine ⟨3826002289102656664412855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2550668192735104442941903 3826002289102656664412855)
          ·
            refine ⟨5739003433653984996619283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3826002289102656664412855 5739003433653984996619283)
            ·
              refine ⟨8608505150480977494928925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5739003433653984996619283 8608505150480977494928925)
              ·
                refine ⟨3228189431430366560598347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8608505150480977494928925 3228189431430366560598347)
                ·
                  refine ⟨4842284147145549840897521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3228189431430366560598347 4842284147145549840897521)
                  ·
                    refine ⟨3631713110359162380673141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4842284147145549840897521 3631713110359162380673141)
                    ·
                      refine ⟨340473104096171473188107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3631713110359162380673141 340473104096171473188107)
                      ·
                        rfl

theorem cell23_663069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_663069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_663069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_663069 prefixEnd_663069 := by exact prefixLift 663069
  have htrace : WordTrace (prefixWord ++ tailWord_663069) baseStart_663069 baseEnd_663069 := by
    simpa [prefixWord, tailWord_663069, baseEnd_663069] using wordTrace_append hprefix tailTrace_663069
  have hstable : (prefixWord ++ tailWord_663069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663069).length < 2 ^ (prefixWord ++ tailWord_663069).sum := by decide
  have hdescent : baseEnd_663069 < baseStart_663069 := by decide
  rcases family_descends (prefixWord ++ tailWord_663069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663096 : List Nat := [2, 1, 2, 1, 4, 2, 3, 1, 2, 1, 4]
def baseStart_663096 : Nat := 118140960795 + 663096 * 2 ^ 59
def prefixEnd_663096 : Nat := 4983230072969 + 3 ^ 40 * 663096 * 2
def baseEnd_663096 : Nat := 340486968073842867550483

theorem tailTrace_663096 : CollatzResearch.WordTrace tailWord_663096 prefixEnd_663096 340486968073842867550483 := by
  unfold tailWord_663096
  simp only [CollatzResearch.WordTrace]
  refine ⟨12092549002861957312896571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16123398670482609750528761 12092549002861957312896571)
  ·
    refine ⟨18138823504292935969344857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12092549002861957312896571 18138823504292935969344857)
    ·
      refine ⟨13604117628219701977008643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18138823504292935969344857 13604117628219701977008643)
      ·
        refine ⟨20406176442329552965512965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13604117628219701977008643 20406176442329552965512965)
        ·
          refine ⟨3826158082936791181033681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20406176442329552965512965 3826158082936791181033681)
          ·
            refine ⟨2869618562202593385775261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3826158082936791181033681 2869618562202593385775261)
            ·
              refine ⟨1076106960825972519665723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2869618562202593385775261 1076106960825972519665723)
              ·
                refine ⟨1614160441238958779498585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1076106960825972519665723 1614160441238958779498585)
                ·
                  refine ⟨1210620330929219084623939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1614160441238958779498585 1210620330929219084623939)
                  ·
                    refine ⟨1815930496393828626935909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1210620330929219084623939 1815930496393828626935909)
                    ·
                      refine ⟨340486968073842867550483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1815930496393828626935909 340486968073842867550483)
                      ·
                        rfl

theorem cell23_663096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 2, 1, 4].length) (baseStart_663096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_663096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_663096 prefixEnd_663096 := by exact prefixLift 663096
  have htrace : WordTrace (prefixWord ++ tailWord_663096) baseStart_663096 baseEnd_663096 := by
    simpa [prefixWord, tailWord_663096, baseEnd_663096] using wordTrace_append hprefix tailTrace_663096
  have hstable : (prefixWord ++ tailWord_663096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663096).length < 2 ^ (prefixWord ++ tailWord_663096).sum := by decide
  have hdescent : baseEnd_663096 < baseStart_663096 := by decide
  rcases family_descends (prefixWord ++ tailWord_663096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663157 : List Nat := [1, 3, 4, 2, 1, 3, 1, 3, 1, 4]
def baseStart_663157 : Nat := 118140960795 + 663157 * 2 ^ 59
def prefixEnd_663157 : Nat := 4983230072969 + 3 ^ 40 * 663157 * 2
def baseEnd_663157 : Nat := 113506096797922376295901

theorem tailTrace_663157 : CollatzResearch.WordTrace tailWord_663157 prefixEnd_663157 113506096797922376295901 := by
  unfold tailWord_663157
  simp only [CollatzResearch.WordTrace]
  refine ⟨24187322858502922043763725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16124881905668614695842483 24187322858502922043763725)
  ·
    refine ⟨9070246071938595766411397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24187322858502922043763725 9070246071938595766411397)
    ·
      refine ⟨1700671138488486706202137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9070246071938595766411397 1700671138488486706202137)
      ·
        refine ⟨1275503353866365029651603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1700671138488486706202137 1275503353866365029651603)
        ·
          refine ⟨1913255030799547544477405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1275503353866365029651603 1913255030799547544477405)
          ·
            refine ⟨717470636549830329179027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1913255030799547544477405 717470636549830329179027)
            ·
              refine ⟨1076205954824745493768541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 717470636549830329179027 1076205954824745493768541)
              ·
                refine ⟨403577233059279560163203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1076205954824745493768541 403577233059279560163203)
                ·
                  refine ⟨605365849588919340244805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 403577233059279560163203 605365849588919340244805)
                  ·
                    refine ⟨113506096797922376295901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 605365849588919340244805 113506096797922376295901)
                    ·
                      rfl

theorem cell23_663157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_663157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_663157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_663157 prefixEnd_663157 := by exact prefixLift 663157
  have htrace : WordTrace (prefixWord ++ tailWord_663157) baseStart_663157 baseEnd_663157 := by
    simpa [prefixWord, tailWord_663157, baseEnd_663157] using wordTrace_append hprefix tailTrace_663157
  have hstable : (prefixWord ++ tailWord_663157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663157).length < 2 ^ (prefixWord ++ tailWord_663157).sum := by decide
  have hdescent : baseEnd_663157 < baseStart_663157 := by decide
  rcases family_descends (prefixWord ++ tailWord_663157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663173 : List Nat := [1, 3, 1, 1, 4, 1, 3, 2, 2, 3, 2]
def baseStart_663173 : Nat := 118140960795 + 663173 * 2 ^ 59
def prefixEnd_663173 : Nat := 4983230072969 + 3 ^ 40 * 663173 * 2
def baseEnd_663173 : Nat := 340526506084239066287629

theorem tailTrace_663173 : CollatzResearch.WordTrace tailWord_663173 prefixEnd_663173 340526506084239066287629 := by
  unfold tailWord_663173
  simp only [CollatzResearch.WordTrace]
  refine ⟨24187906426444956776346173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16125270950963304517564115 24187906426444956776346173)
  ·
    refine ⟨9070464909916858791129815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24187906426444956776346173 9070464909916858791129815)
    ·
      refine ⟨13605697364875288186694723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9070464909916858791129815 13605697364875288186694723)
      ·
        refine ⟨20408546047312932280042085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13605697364875288186694723 20408546047312932280042085)
        ·
          refine ⟨3826602383871174802507891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20408546047312932280042085 3826602383871174802507891)
          ·
            refine ⟨5739903575806762203761837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3826602383871174802507891 5739903575806762203761837)
            ·
              refine ⟨2152463840927535826410689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5739903575806762203761837 2152463840927535826410689)
              ·
                refine ⟨1614347880695651869808017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2152463840927535826410689 1614347880695651869808017)
                ·
                  refine ⟨1210760910521738902356013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1614347880695651869808017 1210760910521738902356013)
                  ·
                    refine ⟨454035341445652088383505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1210760910521738902356013 454035341445652088383505)
                    ·
                      refine ⟨340526506084239066287629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 454035341445652088383505 340526506084239066287629)
                      ·
                        rfl

theorem cell23_663173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 2, 3, 2].length) (baseStart_663173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_663173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_663173 prefixEnd_663173 := by exact prefixLift 663173
  have htrace : WordTrace (prefixWord ++ tailWord_663173) baseStart_663173 baseEnd_663173 := by
    simpa [prefixWord, tailWord_663173, baseEnd_663173] using wordTrace_append hprefix tailTrace_663173
  have hstable : (prefixWord ++ tailWord_663173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663173).length < 2 ^ (prefixWord ++ tailWord_663173).sum := by decide
  have hdescent : baseEnd_663173 < baseStart_663173 := by decide
  rcases family_descends (prefixWord ++ tailWord_663173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663203 : List Nat := [1, 1, 1, 4, 1, 1, 4, 1, 5, 2, 2]
def baseStart_663203 : Nat := 118140960795 + 663203 * 2 ^ 59
def prefixEnd_663203 : Nat := 4983230072969 + 3 ^ 40 * 663203 * 2
def baseEnd_663203 : Nat := 340541910503873948912491

theorem tailTrace_663203 : CollatzResearch.WordTrace tailWord_663203 prefixEnd_663203 340541910503873948912491 := by
  unfold tailWord_663203
  simp only [CollatzResearch.WordTrace]
  refine ⟨24189000616336271899938263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16126000410890847933292175 24189000616336271899938263)
  ·
    refine ⟨36283500924504407849907395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24189000616336271899938263 36283500924504407849907395)
    ·
      refine ⟨54425251386756611774861093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36283500924504407849907395 54425251386756611774861093)
      ·
        refine ⟨10204734635016864707786455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54425251386756611774861093 10204734635016864707786455)
        ·
          refine ⟨15307101952525297061679683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10204734635016864707786455 15307101952525297061679683)
          ·
            refine ⟨22960652928787945592519525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15307101952525297061679683 22960652928787945592519525)
            ·
              refine ⟨4305122424147739798597411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22960652928787945592519525 4305122424147739798597411)
              ·
                refine ⟨6457683636221609697896117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4305122424147739798597411 6457683636221609697896117)
                ·
                  refine ⟨605407840895775909177761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6457683636221609697896117 605407840895775909177761)
                  ·
                    refine ⟨454055880671831931883321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 605407840895775909177761 454055880671831931883321)
                    ·
                      refine ⟨340541910503873948912491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 454055880671831931883321 340541910503873948912491)
                      ·
                        rfl

theorem cell23_663203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 5, 2, 2].length) (baseStart_663203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_663203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_663203 prefixEnd_663203 := by exact prefixLift 663203
  have htrace : WordTrace (prefixWord ++ tailWord_663203) baseStart_663203 baseEnd_663203 := by
    simpa [prefixWord, tailWord_663203, baseEnd_663203] using wordTrace_append hprefix tailTrace_663203
  have hstable : (prefixWord ++ tailWord_663203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663203).length < 2 ^ (prefixWord ++ tailWord_663203).sum := by decide
  have hdescent : baseEnd_663203 < baseStart_663203 := by decide
  rcases family_descends (prefixWord ++ tailWord_663203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663223 : List Nat := [1, 1, 3, 1, 5, 3, 1, 1, 1, 1, 5]
def baseStart_663223 : Nat := 118140960795 + 663223 * 2 ^ 59
def prefixEnd_663223 : Nat := 4983230072969 + 3 ^ 40 * 663223 * 2
def baseEnd_663223 : Nat := 340552180116963870662399

theorem tailTrace_663223 : CollatzResearch.WordTrace tailWord_663223 prefixEnd_663223 340552180116963870662399 := by
  unfold tailWord_663223
  simp only [CollatzResearch.WordTrace]
  refine ⟨24189730076263815315666323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16126486717509210210444215 24189730076263815315666323)
  ·
    refine ⟨36284595114395722973499485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24189730076263815315666323 36284595114395722973499485)
    ·
      refine ⟨13606723167898396115062307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36284595114395722973499485 13606723167898396115062307)
      ·
        refine ⟨20410084751847594172593461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13606723167898396115062307 20410084751847594172593461)
        ·
          refine ⟨1913445445485711953680637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20410084751847594172593461 1913445445485711953680637)
          ·
            refine ⟨717542042057141982630239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1913445445485711953680637 717542042057141982630239)
            ·
              refine ⟨1076313063085712973945359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 717542042057141982630239 1076313063085712973945359)
              ·
                refine ⟨1614469594628569460918039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1076313063085712973945359 1614469594628569460918039)
                ·
                  refine ⟨2421704391942854191377059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1614469594628569460918039 2421704391942854191377059)
                  ·
                    refine ⟨3632556587914281287065589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2421704391942854191377059 3632556587914281287065589)
                    ·
                      refine ⟨340552180116963870662399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3632556587914281287065589 340552180116963870662399)
                      ·
                        rfl

theorem cell23_663223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 1, 5].length) (baseStart_663223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_663223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_663223 prefixEnd_663223 := by exact prefixLift 663223
  have htrace : WordTrace (prefixWord ++ tailWord_663223) baseStart_663223 baseEnd_663223 := by
    simpa [prefixWord, tailWord_663223, baseEnd_663223] using wordTrace_append hprefix tailTrace_663223
  have hstable : (prefixWord ++ tailWord_663223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663223).length < 2 ^ (prefixWord ++ tailWord_663223).sum := by decide
  have hdescent : baseEnd_663223 < baseStart_663223 := by decide
  rcases family_descends (prefixWord ++ tailWord_663223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663230 : List Nat := [4, 2, 1, 1, 2, 3, 2, 2, 2, 4]
def baseStart_663230 : Nat := 118140960795 + 663230 * 2 ^ 59
def prefixEnd_663230 : Nat := 4983230072969 + 3 ^ 40 * 663230 * 2
def baseEnd_663230 : Nat := 113518591493848447758289

theorem tailTrace_663230 : CollatzResearch.WordTrace tailWord_663230 prefixEnd_663230 113518591493848447758289 := by
  unfold tailWord_663230
  simp only [CollatzResearch.WordTrace]
  refine ⟨3023748173404806938896393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16126656924825637007447429 3023748173404806938896393)
  ·
    refine ⟨2267811130053605204172295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3023748173404806938896393 2267811130053605204172295)
    ·
      refine ⟨3401716695080407806258443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2267811130053605204172295 3401716695080407806258443)
      ·
        refine ⟨5102575042620611709387665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3401716695080407806258443 5102575042620611709387665)
        ·
          refine ⟨3826931281965458782040749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5102575042620611709387665 3826931281965458782040749)
          ·
            refine ⟨1435099230737047043265281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3826931281965458782040749 1435099230737047043265281)
            ·
              refine ⟨1076324423052785282448961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1435099230737047043265281 1076324423052785282448961)
              ·
                refine ⟨807243317289588961836721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1076324423052785282448961 807243317289588961836721)
                ·
                  refine ⟨605432487967191721377541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 807243317289588961836721 605432487967191721377541)
                  ·
                    refine ⟨113518591493848447758289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 605432487967191721377541 113518591493848447758289)
                    ·
                      rfl

theorem cell23_663230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_663230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_663230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_663230 prefixEnd_663230 := by exact prefixLift 663230
  have htrace : WordTrace (prefixWord ++ tailWord_663230) baseStart_663230 baseEnd_663230 := by
    simpa [prefixWord, tailWord_663230, baseEnd_663230] using wordTrace_append hprefix tailTrace_663230
  have hstable : (prefixWord ++ tailWord_663230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663230).length < 2 ^ (prefixWord ++ tailWord_663230).sum := by decide
  have hdescent : baseEnd_663230 < baseStart_663230 := by decide
  rcases family_descends (prefixWord ++ tailWord_663230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663239 : List Nat := [1, 1, 4, 1, 1, 1, 3, 1, 1, 9]
def baseStart_663239 : Nat := 118140960795 + 663239 * 2 ^ 59
def prefixEnd_663239 : Nat := 4983230072969 + 3 ^ 40 * 663239 * 2
def baseEnd_663239 : Nat := 113520131935811936020775

theorem tailTrace_663239 : CollatzResearch.WordTrace tailWord_663239 prefixEnd_663239 113520131935811936020775 := by
  unfold tailWord_663239
  simp only [CollatzResearch.WordTrace]
  refine ⟨24190313644205850048248771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16126875762803900032165847 24190313644205850048248771)
  ·
    refine ⟨36285470466308775072373157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24190313644205850048248771 36285470466308775072373157)
    ·
      refine ⟨6803525712432895326069967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36285470466308775072373157 6803525712432895326069967)
      ·
        refine ⟨10205288568649342989104951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6803525712432895326069967 10205288568649342989104951)
        ·
          refine ⟨15307932852974014483657427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10205288568649342989104951 15307932852974014483657427)
          ·
            refine ⟨22961899279461021725486141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15307932852974014483657427 22961899279461021725486141)
            ·
              refine ⟨8610712229797883147057303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22961899279461021725486141 8610712229797883147057303)
              ·
                refine ⟨12916068344696824720585955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8610712229797883147057303 12916068344696824720585955)
                ·
                  refine ⟨19374102517045237080878933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12916068344696824720585955 19374102517045237080878933)
                  ·
                    refine ⟨113520131935811936020775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 19374102517045237080878933 113520131935811936020775)
                    ·
                      rfl

theorem cell23_663239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 9].length) (baseStart_663239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_663239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_663239 prefixEnd_663239 := by exact prefixLift 663239
  have htrace : WordTrace (prefixWord ++ tailWord_663239) baseStart_663239 baseEnd_663239 := by
    simpa [prefixWord, tailWord_663239, baseEnd_663239] using wordTrace_append hprefix tailTrace_663239
  have hstable : (prefixWord ++ tailWord_663239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663239).length < 2 ^ (prefixWord ++ tailWord_663239).sum := by decide
  have hdescent : baseEnd_663239 < baseStart_663239 := by decide
  rcases family_descends (prefixWord ++ tailWord_663239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663260 : List Nat := [2, 2, 5, 1, 2, 1, 3, 7]
def baseStart_663260 : Nat := 118140960795 + 663260 * 2 ^ 59
def prefixEnd_663260 : Nat := 4983230072969 + 3 ^ 40 * 663260 * 2
def baseEnd_663260 : Nat := 12613747366710378737027

theorem tailTrace_663260 : CollatzResearch.WordTrace tailWord_663260 prefixEnd_663260 12613747366710378737027 := by
  unfold tailWord_663260
  simp only [CollatzResearch.WordTrace]
  refine ⟨12095539788564885317381617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16127386384753180423175489 12095539788564885317381617)
  ·
    refine ⟨9071654841423663988036213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12095539788564885317381617 9071654841423663988036213)
    ·
      refine ⟨850467641383468498878395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9071654841423663988036213 850467641383468498878395)
      ·
        refine ⟨1275701462075202748317593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 850467641383468498878395 1275701462075202748317593)
        ·
          refine ⟨956776096556402061238195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1275701462075202748317593 956776096556402061238195)
          ·
            refine ⟨1435164144834603091857293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 956776096556402061238195 1435164144834603091857293)
            ·
              refine ⟨538186554312976159446485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1435164144834603091857293 538186554312976159446485)
              ·
                refine ⟨12613747366710378737027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 538186554312976159446485 12613747366710378737027)
                ·
                  rfl

theorem cell23_663260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 7].length) (baseStart_663260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_663260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_663260 prefixEnd_663260 := by exact prefixLift 663260
  have htrace : WordTrace (prefixWord ++ tailWord_663260) baseStart_663260 baseEnd_663260 := by
    simpa [prefixWord, tailWord_663260, baseEnd_663260] using wordTrace_append hprefix tailTrace_663260
  have hstable : (prefixWord ++ tailWord_663260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663260).length < 2 ^ (prefixWord ++ tailWord_663260).sum := by decide
  have hdescent : baseEnd_663260 < baseStart_663260 := by decide
  rcases family_descends (prefixWord ++ tailWord_663260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663263 : List Nat := [1, 1, 2, 3, 2, 2, 1, 3, 3, 3, 2]
def baseStart_663263 : Nat := 118140960795 + 663263 * 2 ^ 59
def prefixEnd_663263 : Nat := 4983230072969 + 3 ^ 40 * 663263 * 2
def baseEnd_663263 : Nat := 340572719343143714162215

theorem tailTrace_663263 : CollatzResearch.WordTrace tailWord_663263 prefixEnd_663263 340572719343143714162215 := by
  unfold tailWord_663263
  simp only [CollatzResearch.WordTrace]
  refine ⟨24191188996118902147122443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16127459330745934764748295 24191188996118902147122443)
  ·
    refine ⟨36286783494178353220683665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24191188996118902147122443 36286783494178353220683665)
    ·
      refine ⟨27215087620633764915512749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36286783494178353220683665 27215087620633764915512749)
      ·
        refine ⟨10205657857737661843317281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27215087620633764915512749 10205657857737661843317281)
        ·
          refine ⟨7654243393303246382487961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10205657857737661843317281 7654243393303246382487961)
          ·
            refine ⟨5740682544977434786865971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7654243393303246382487961 5740682544977434786865971)
            ·
              refine ⟨8611023817466152180298957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5740682544977434786865971 8611023817466152180298957)
              ·
                refine ⟨3229133931549807067612109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8611023817466152180298957 3229133931549807067612109)
                ·
                  refine ⟨1210925224331177650354541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3229133931549807067612109 1210925224331177650354541)
                  ·
                    refine ⟨454096959124191618882953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1210925224331177650354541 454096959124191618882953)
                    ·
                      refine ⟨340572719343143714162215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 454096959124191618882953 340572719343143714162215)
                      ·
                        rfl

theorem cell23_663263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 3, 3, 2].length) (baseStart_663263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_663263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_663263 prefixEnd_663263 := by exact prefixLift 663263
  have htrace : WordTrace (prefixWord ++ tailWord_663263) baseStart_663263 baseEnd_663263 := by
    simpa [prefixWord, tailWord_663263, baseEnd_663263] using wordTrace_append hprefix tailTrace_663263
  have hstable : (prefixWord ++ tailWord_663263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663263).length < 2 ^ (prefixWord ++ tailWord_663263).sum := by decide
  have hdescent : baseEnd_663263 < baseStart_663263 := by decide
  rcases family_descends (prefixWord ++ tailWord_663263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663271 : List Nat := [1, 1, 5, 4, 1, 1, 2, 3, 1, 2, 2]
def baseStart_663271 : Nat := 118140960795 + 663271 * 2 ^ 59
def prefixEnd_663271 : Nat := 4983230072969 + 3 ^ 40 * 663271 * 2
def baseEnd_663271 : Nat := 340576827188379682862179

theorem tailTrace_663271 : CollatzResearch.WordTrace tailWord_663271 prefixEnd_663271 340576827188379682862179 := by
  unfold tailWord_663271
  simp only [CollatzResearch.WordTrace]
  refine ⟨24191480780089919513413667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16127653853393279675609111 24191480780089919513413667)
  ·
    refine ⟨36287221170134879270120501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24191480780089919513413667 36287221170134879270120501)
    ·
      refine ⟨3401926984700144931573797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36287221170134879270120501 3401926984700144931573797)
      ·
        refine ⟨637861309631277174670087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3401926984700144931573797 637861309631277174670087)
        ·
          refine ⟨956791964446915762005131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 637861309631277174670087 956791964446915762005131)
          ·
            refine ⟨1435187946670373643007697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 956791964446915762005131 1435187946670373643007697)
            ·
              refine ⟨1076390960002780232255773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1435187946670373643007697 1076390960002780232255773)
              ·
                refine ⟨403646610001042587095915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1076390960002780232255773 403646610001042587095915)
                ·
                  refine ⟨605469915001563880643873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 403646610001042587095915 605469915001563880643873)
                  ·
                    refine ⟨454102436251172910482905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 605469915001563880643873 454102436251172910482905)
                    ·
                      refine ⟨340576827188379682862179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 454102436251172910482905 340576827188379682862179)
                      ·
                        rfl

theorem cell23_663271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_663271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_663271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_663271 prefixEnd_663271 := by exact prefixLift 663271
  have htrace : WordTrace (prefixWord ++ tailWord_663271) baseStart_663271 baseEnd_663271 := by
    simpa [prefixWord, tailWord_663271, baseEnd_663271] using wordTrace_append hprefix tailTrace_663271
  have hstable : (prefixWord ++ tailWord_663271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663271).length < 2 ^ (prefixWord ++ tailWord_663271).sum := by decide
  have hdescent : baseEnd_663271 < baseStart_663271 := by decide
  rcases family_descends (prefixWord ++ tailWord_663271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663310 : List Nat := [4, 1, 1, 2, 1, 1, 5, 1, 1, 4, 2]
def baseStart_663310 : Nat := 118140960795 + 663310 * 2 ^ 59
def prefixEnd_663310 : Nat := 4983230072969 + 3 ^ 40 * 663310 * 2
def baseEnd_663310 : Nat := 340596852933905030274499

theorem tailTrace_663310 : CollatzResearch.WordTrace tailWord_663310 prefixEnd_663310 340596852933905030274499 := by
  unfold tailWord_663310
  simp only [CollatzResearch.WordTrace]
  refine ⟨3024112903368578646760423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16128602151299086116055589 3024112903368578646760423)
  ·
    refine ⟨4536169355052867970140635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3024112903368578646760423 4536169355052867970140635)
    ·
      refine ⟨6804254032579301955210953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4536169355052867970140635 6804254032579301955210953)
      ·
        refine ⟨5103190524434476466408215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6804254032579301955210953 5103190524434476466408215)
        ·
          refine ⟨7654785786651714699612323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5103190524434476466408215 7654785786651714699612323)
          ·
            refine ⟨11482178679977572049418485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7654785786651714699612323 11482178679977572049418485)
            ·
              refine ⟨1076454251247897379632983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11482178679977572049418485 1076454251247897379632983)
              ·
                refine ⟨1614681376871846069449475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1076454251247897379632983 1614681376871846069449475)
                ·
                  refine ⟨2422022065307769104174213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1614681376871846069449475 2422022065307769104174213)
                  ·
                    refine ⟨454129137245206707032665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2422022065307769104174213 454129137245206707032665)
                    ·
                      refine ⟨340596852933905030274499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 454129137245206707032665 340596852933905030274499)
                      ·
                        rfl

theorem cell23_663310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 1, 4, 2].length) (baseStart_663310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_663310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_663310 prefixEnd_663310 := by exact prefixLift 663310
  have htrace : WordTrace (prefixWord ++ tailWord_663310) baseStart_663310 baseEnd_663310 := by
    simpa [prefixWord, tailWord_663310, baseEnd_663310] using wordTrace_append hprefix tailTrace_663310
  have hstable : (prefixWord ++ tailWord_663310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663310).length < 2 ^ (prefixWord ++ tailWord_663310).sum := by decide
  have hdescent : baseEnd_663310 < baseStart_663310 := by decide
  rcases family_descends (prefixWord ++ tailWord_663310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663314 : List Nat := [3, 2, 4, 1, 1, 2, 2, 2, 1, 3, 2]
def baseStart_663314 : Nat := 118140960795 + 663314 * 2 ^ 59
def prefixEnd_663314 : Nat := 4983230072969 + 3 ^ 40 * 663314 * 2
def baseEnd_663314 : Nat := 340598906856523014624481

theorem tailTrace_663314 : CollatzResearch.WordTrace tailWord_663314 prefixEnd_663314 340598906856523014624481 := by
  unfold tailWord_663314
  simp only [CollatzResearch.WordTrace]
  refine ⟨6048262279733534464307249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16128699412622758571485997 6048262279733534464307249)
  ·
    refine ⟨4536196709800150848230437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6048262279733534464307249 4536196709800150848230437)
    ·
      refine ⟨850536883087528284043207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4536196709800150848230437 850536883087528284043207)
      ·
        refine ⟨1275805324631292426064811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 850536883087528284043207 1275805324631292426064811)
        ·
          refine ⟨1913707986946938639097217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1275805324631292426064811 1913707986946938639097217)
          ·
            refine ⟨1435280990210203979322913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1913707986946938639097217 1435280990210203979322913)
            ·
              refine ⟨1076460742657652984492185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1435280990210203979322913 1076460742657652984492185)
              ·
                refine ⟨807345556993239738369139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1076460742657652984492185 807345556993239738369139)
                ·
                  refine ⟨1211018335489859607553709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 807345556993239738369139 1211018335489859607553709)
                  ·
                    refine ⟨454131875808697352832641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1211018335489859607553709 454131875808697352832641)
                    ·
                      refine ⟨340598906856523014624481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 454131875808697352832641 340598906856523014624481)
                      ·
                        rfl

theorem cell23_663314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_663314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_663314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_663314 prefixEnd_663314 := by exact prefixLift 663314
  have htrace : WordTrace (prefixWord ++ tailWord_663314) baseStart_663314 baseEnd_663314 := by
    simpa [prefixWord, tailWord_663314, baseEnd_663314] using wordTrace_append hprefix tailTrace_663314
  have hstable : (prefixWord ++ tailWord_663314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663314).length < 2 ^ (prefixWord ++ tailWord_663314).sum := by decide
  have hdescent : baseEnd_663314 < baseStart_663314 := by decide
  rcases family_descends (prefixWord ++ tailWord_663314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663350 : List Nat := [5, 1, 2, 2, 1, 1, 3, 1, 7]
def baseStart_663350 : Nat := 118140960795 + 663350 * 2 ^ 59
def prefixEnd_663350 : Nat := 4983230072969 + 3 ^ 40 * 663350 * 2
def baseEnd_663350 : Nat := 37846376906676097086035

theorem tailTrace_663350 : CollatzResearch.WordTrace tailWord_663350 prefixEnd_663350 37846376906676097086035 := by
  unfold tailWord_663350
  simp only [CollatzResearch.WordTrace]
  refine ⟨1512147634175232250346219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16129574764535810670359669 1512147634175232250346219)
  ·
    refine ⟨2268221451262848375519329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1512147634175232250346219 2268221451262848375519329)
    ·
      refine ⟨1701166088447136281639497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2268221451262848375519329 1701166088447136281639497)
      ·
        refine ⟨1275874566335352211229623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1701166088447136281639497 1275874566335352211229623)
        ·
          refine ⟨1913811849503028316844435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1275874566335352211229623 1913811849503028316844435)
          ·
            refine ⟨2870717774254542475266653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1913811849503028316844435 2870717774254542475266653)
            ·
              refine ⟨1076519165345453428224995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2870717774254542475266653 1076519165345453428224995)
              ·
                refine ⟨1614778748018180142337493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1076519165345453428224995 1614778748018180142337493)
                ·
                  refine ⟨37846376906676097086035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1614778748018180142337493 37846376906676097086035)
                  ·
                    rfl

theorem cell23_663350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 7].length) (baseStart_663350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_663350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_663350 prefixEnd_663350 := by exact prefixLift 663350
  have htrace : WordTrace (prefixWord ++ tailWord_663350) baseStart_663350 baseEnd_663350 := by
    simpa [prefixWord, tailWord_663350, baseEnd_663350] using wordTrace_append hprefix tailTrace_663350
  have hstable : (prefixWord ++ tailWord_663350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663350).length < 2 ^ (prefixWord ++ tailWord_663350).sum := by decide
  have hdescent : baseEnd_663350 < baseStart_663350 := by decide
  rcases family_descends (prefixWord ++ tailWord_663350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663356 : List Nat := [2, 2, 2, 2, 1, 1, 3, 1, 1, 1, 7]
def baseStart_663356 : Nat := 118140960795 + 663356 * 2 ^ 59
def prefixEnd_663356 : Nat := 4983230072969 + 3 ^ 40 * 663356 * 2
def baseEnd_663356 : Nat := 340620473044011850299287

theorem tailTrace_663356 : CollatzResearch.WordTrace tailWord_663356 prefixEnd_663356 340620473044011850299287 := by
  unfold tailWord_663356
  simp only [CollatzResearch.WordTrace]
  refine ⟨12097290492390989515128961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16129720656521319353505281 12097290492390989515128961)
  ·
    refine ⟨9072967869293242136346721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12097290492390989515128961 9072967869293242136346721)
    ·
      refine ⟨6804725901969931602260041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9072967869293242136346721 6804725901969931602260041)
      ·
        refine ⟨5103544426477448701695031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6804725901969931602260041 5103544426477448701695031)
        ·
          refine ⟨7655316639716173052542547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5103544426477448701695031 7655316639716173052542547)
          ·
            refine ⟨11482974959574259578813821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7655316639716173052542547 11482974959574259578813821)
            ·
              refine ⟨4306115609840347342055183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11482974959574259578813821 4306115609840347342055183)
              ·
                refine ⟨6459173414760521013082775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4306115609840347342055183 6459173414760521013082775)
                ·
                  refine ⟨9688760122140781519624163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6459173414760521013082775 9688760122140781519624163)
                  ·
                    refine ⟨14533140183211172279436245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9688760122140781519624163 14533140183211172279436245)
                    ·
                      refine ⟨340620473044011850299287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 14533140183211172279436245 340620473044011850299287)
                      ·
                        rfl

theorem cell23_663356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_663356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_663356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_663356 prefixEnd_663356 := by exact prefixLift 663356
  have htrace : WordTrace (prefixWord ++ tailWord_663356) baseStart_663356 baseEnd_663356 := by
    simpa [prefixWord, tailWord_663356, baseEnd_663356] using wordTrace_append hprefix tailTrace_663356
  have hstable : (prefixWord ++ tailWord_663356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663356).length < 2 ^ (prefixWord ++ tailWord_663356).sum := by decide
  have hdescent : baseEnd_663356 < baseStart_663356 := by decide
  rcases family_descends (prefixWord ++ tailWord_663356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663380 : List Nat := [2, 4, 1, 1, 3, 2, 2, 1, 2, 5]
def baseStart_663380 : Nat := 118140960795 + 663380 * 2 ^ 59
def prefixEnd_663380 : Nat := 4983230072969 + 3 ^ 40 * 663380 * 2
def baseEnd_663380 : Nat := 113544265526573252133059

theorem tailTrace_663380 : CollatzResearch.WordTrace tailWord_663380 prefixEnd_663380 113544265526573252133059 := by
  unfold tailWord_663380
  simp only [CollatzResearch.WordTrace]
  refine ⟨12097728168347515564565797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16130304224463354086087729 12097728168347515564565797)
  ·
    refine ⟨2268324031565159168356087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12097728168347515564565797 2268324031565159168356087)
    ·
      refine ⟨3402486047347738752534131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2268324031565159168356087 3402486047347738752534131)
      ·
        refine ⟨5103729071021608128801197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3402486047347738752534131 5103729071021608128801197)
        ·
          refine ⟨1913898401633103048300449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5103729071021608128801197 1913898401633103048300449)
          ·
            refine ⟨1435423801224827286225337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1913898401633103048300449 1435423801224827286225337)
            ·
              refine ⟨1076567850918620464669003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1435423801224827286225337 1076567850918620464669003)
              ·
                refine ⟨1614851776377930697003505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1076567850918620464669003 1614851776377930697003505)
                ·
                  refine ⟨1211138832283448022752629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1614851776377930697003505 1211138832283448022752629)
                  ·
                    refine ⟨113544265526573252133059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1211138832283448022752629 113544265526573252133059)
                    ·
                      rfl

theorem cell23_663380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_663380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_663380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_663380 prefixEnd_663380 := by exact prefixLift 663380
  have htrace : WordTrace (prefixWord ++ tailWord_663380) baseStart_663380 baseEnd_663380 := by
    simpa [prefixWord, tailWord_663380, baseEnd_663380] using wordTrace_append hprefix tailTrace_663380
  have hstable : (prefixWord ++ tailWord_663380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663380).length < 2 ^ (prefixWord ++ tailWord_663380).sum := by decide
  have hdescent : baseEnd_663380 < baseStart_663380 := by decide
  rcases family_descends (prefixWord ++ tailWord_663380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663400 : List Nat := [2, 1, 4, 2, 1, 1, 2, 2, 2, 4, 2]
def baseStart_663400 : Nat := 118140960795 + 663400 * 2 ^ 59
def prefixEnd_663400 : Nat := 4983230072969 + 3 ^ 40 * 663400 * 2
def baseEnd_663400 : Nat := 340643066192809678149085

theorem tailTrace_663400 : CollatzResearch.WordTrace tailWord_663400 prefixEnd_663400 340643066192809678149085 := by
  unfold tailWord_663400
  simp only [CollatzResearch.WordTrace]
  refine ⟨12098092898311287272429827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16130790531081716363239769 12098092898311287272429827)
  ·
    refine ⟨18147139347466930908644741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12098092898311287272429827 18147139347466930908644741)
    ·
      refine ⟨3402588627650049545370889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18147139347466930908644741 3402588627650049545370889)
      ·
        refine ⟨2551941470737537159028167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3402588627650049545370889 2551941470737537159028167)
        ·
          refine ⟨3827912206106305738542251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2551941470737537159028167 3827912206106305738542251)
          ·
            refine ⟨5741868309159458607813377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3827912206106305738542251 5741868309159458607813377)
            ·
              refine ⟨4306401231869593955860033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5741868309159458607813377 4306401231869593955860033)
              ·
                refine ⟨3229800923902195466895025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4306401231869593955860033 3229800923902195466895025)
                ·
                  refine ⟨2422350692926646600171269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3229800923902195466895025 2422350692926646600171269)
                  ·
                    refine ⟨454190754923746237532113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2422350692926646600171269 454190754923746237532113)
                    ·
                      refine ⟨340643066192809678149085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 454190754923746237532113 340643066192809678149085)
                      ·
                        rfl

theorem cell23_663400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_663400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_663400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_663400 prefixEnd_663400 := by exact prefixLift 663400
  have htrace : WordTrace (prefixWord ++ tailWord_663400) baseStart_663400 baseEnd_663400 := by
    simpa [prefixWord, tailWord_663400, baseEnd_663400] using wordTrace_append hprefix tailTrace_663400
  have hstable : (prefixWord ++ tailWord_663400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663400).length < 2 ^ (prefixWord ++ tailWord_663400).sum := by decide
  have hdescent : baseEnd_663400 < baseStart_663400 := by decide
  rcases family_descends (prefixWord ++ tailWord_663400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663434 : List Nat := [3, 1, 2, 4, 3, 1, 1, 1, 2, 1, 4]
def baseStart_663434 : Nat := 118140960795 + 663434 * 2 ^ 59
def prefixEnd_663434 : Nat := 4983230072969 + 3 ^ 40 * 663434 * 2
def baseEnd_663434 : Nat := 340660524535062545123929

theorem tailTrace_663434 : CollatzResearch.WordTrace tailWord_663434 prefixEnd_663434 340660524535062545123929 := by
  unfold tailWord_663434
  simp only [CollatzResearch.WordTrace]
  refine ⟨6049356469624849587899339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16131617252332932234398237 6049356469624849587899339)
  ·
    refine ⟨9074034704437274381849009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6049356469624849587899339 9074034704437274381849009)
    ·
      refine ⟨6805526028327955786386757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9074034704437274381849009 6805526028327955786386757)
      ·
        refine ⟨1276036130311491709947517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6805526028327955786386757 1276036130311491709947517)
        ·
          refine ⟨478513548866809391230319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1276036130311491709947517 478513548866809391230319)
          ·
            refine ⟨717770323300214086845479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 478513548866809391230319 717770323300214086845479)
            ·
              refine ⟨1076655484950321130268219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 717770323300214086845479 1076655484950321130268219)
              ·
                refine ⟨1614983227425481695402329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1076655484950321130268219 1614983227425481695402329)
                ·
                  refine ⟨1211237420569111271551747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1614983227425481695402329 1211237420569111271551747)
                  ·
                    refine ⟨1816856130853666907327621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1211237420569111271551747 1816856130853666907327621)
                    ·
                      refine ⟨340660524535062545123929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1816856130853666907327621 340660524535062545123929)
                      ·
                        rfl

theorem cell23_663434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_663434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_663434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_663434 prefixEnd_663434 := by exact prefixLift 663434
  have htrace : WordTrace (prefixWord ++ tailWord_663434) baseStart_663434 baseEnd_663434 := by
    simpa [prefixWord, tailWord_663434, baseEnd_663434] using wordTrace_append hprefix tailTrace_663434
  have hstable : (prefixWord ++ tailWord_663434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663434).length < 2 ^ (prefixWord ++ tailWord_663434).sum := by decide
  have hdescent : baseEnd_663434 < baseStart_663434 := by decide
  rcases family_descends (prefixWord ++ tailWord_663434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663444 : List Nat := [2, 4, 2, 1, 1, 3, 2, 3, 1, 4]
def baseStart_663444 : Nat := 118140960795 + 663444 * 2 ^ 59
def prefixEnd_663444 : Nat := 4983230072969 + 3 ^ 40 * 663444 * 2
def baseEnd_663444 : Nat := 113555219780535835332961

theorem tailTrace_663444 : CollatzResearch.WordTrace tailWord_663444 prefixEnd_663444 113555219780535835332961 := by
  unfold tailWord_663444
  simp only [CollatzResearch.WordTrace]
  refine ⟨12098895304231585029730693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16131860405642113372974257 12098895304231585029730693)
  ·
    refine ⟨2268542869543422193074505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12098895304231585029730693 2268542869543422193074505)
    ·
      refine ⟨1701407152157566644805879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2268542869543422193074505 1701407152157566644805879)
      ·
        refine ⟨2552110728236349967208819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1701407152157566644805879 2552110728236349967208819)
        ·
          refine ⟨3828166092354524950813229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2552110728236349967208819 3828166092354524950813229)
          ·
            refine ⟨1435562284632946856554961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3828166092354524950813229 1435562284632946856554961)
            ·
              refine ⟨1076671713474710142416221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1435562284632946856554961 1076671713474710142416221)
              ·
                refine ⟨403751892553016303406083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1076671713474710142416221 403751892553016303406083)
                ·
                  refine ⟨605627838829524455109125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 403751892553016303406083 605627838829524455109125)
                  ·
                    refine ⟨113555219780535835332961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 605627838829524455109125 113555219780535835332961)
                    ·
                      rfl

theorem cell23_663444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_663444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_663444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_663444 prefixEnd_663444 := by exact prefixLift 663444
  have htrace : WordTrace (prefixWord ++ tailWord_663444) baseStart_663444 baseEnd_663444 := by
    simpa [prefixWord, tailWord_663444, baseEnd_663444] using wordTrace_append hprefix tailTrace_663444
  have hstable : (prefixWord ++ tailWord_663444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663444).length < 2 ^ (prefixWord ++ tailWord_663444).sum := by decide
  have hdescent : baseEnd_663444 < baseStart_663444 := by decide
  rcases family_descends (prefixWord ++ tailWord_663444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663457 : List Nat := [1, 2, 3, 4, 2, 2, 1, 2, 6]
def baseStart_663457 : Nat := 118140960795 + 663457 * 2 ^ 59
def prefixEnd_663457 : Nat := 4983230072969 + 3 ^ 40 * 663457 * 2
def baseEnd_663457 : Nat := 37852481621123995015147

theorem tailTrace_663457 : CollatzResearch.WordTrace tailWord_663457 prefixEnd_663457 37852481621123995015147 := by
  unfold tailWord_663457
  simp only [CollatzResearch.WordTrace]
  refine ⟨24198264757416073279684625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16132176504944048853123083 24198264757416073279684625)
  ·
    refine ⟨18148698568062054959763469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24198264757416073279684625 18148698568062054959763469)
    ·
      refine ⟨6805761963023270609911301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18148698568062054959763469 6805761963023270609911301)
      ·
        refine ⟨1276080368066863239358369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6805761963023270609911301 1276080368066863239358369)
        ·
          refine ⟨957060276050147429518777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1276080368066863239358369 957060276050147429518777)
          ·
            refine ⟨717795207037610572139083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 957060276050147429518777 717795207037610572139083)
            ·
              refine ⟨1076692810556415858208625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 717795207037610572139083 1076692810556415858208625)
              ·
                refine ⟨807519607917311893656469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1076692810556415858208625 807519607917311893656469)
                ·
                  refine ⟨37852481621123995015147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 807519607917311893656469 37852481621123995015147)
                  ·
                    rfl

theorem cell23_663457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 2, 6].length) (baseStart_663457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_663457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_663457 prefixEnd_663457 := by exact prefixLift 663457
  have htrace : WordTrace (prefixWord ++ tailWord_663457) baseStart_663457 baseEnd_663457 := by
    simpa [prefixWord, tailWord_663457, baseEnd_663457] using wordTrace_append hprefix tailTrace_663457
  have hstable : (prefixWord ++ tailWord_663457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663457).length < 2 ^ (prefixWord ++ tailWord_663457).sum := by decide
  have hdescent : baseEnd_663457 < baseStart_663457 := by decide
  rcases family_descends (prefixWord ++ tailWord_663457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663483 : List Nat := [1, 1, 1, 1, 1, 2, 2, 4, 6, 4]
def baseStart_663483 : Nat := 118140960795 + 663483 * 2 ^ 59
def prefixEnd_663483 : Nat := 4983230072969 + 3 ^ 40 * 663483 * 2
def baseEnd_663483 : Nat := 113561895029044284470401

theorem tailTrace_663483 : CollatzResearch.WordTrace tailWord_663483 prefixEnd_663483 113561895029044284470401 := by
  unfold tailWord_663483
  simp only [CollatzResearch.WordTrace]
  refine ⟨24199213055321879720131103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16132808703547919813420735 24199213055321879720131103)
  ·
    refine ⟨36298819582982819580196655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24199213055321879720131103 36298819582982819580196655)
    ·
      refine ⟨54448229374474229370294983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36298819582982819580196655 54448229374474229370294983)
      ·
        refine ⟨81672344061711344055442475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54448229374474229370294983 81672344061711344055442475)
        ·
          refine ⟨122508516092567016083163713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81672344061711344055442475 122508516092567016083163713)
          ·
            refine ⟨91881387069425262062372785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122508516092567016083163713 91881387069425262062372785)
            ·
              refine ⟨68911040302068946546779589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91881387069425262062372785 68911040302068946546779589)
              ·
                refine ⟨12920820056637927477521173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68911040302068946546779589 12920820056637927477521173)
                ·
                  refine ⟨605663440154902850508805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 12920820056637927477521173 605663440154902850508805)
                  ·
                    refine ⟨113561895029044284470401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 605663440154902850508805 113561895029044284470401)
                    ·
                      rfl

theorem cell23_663483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 6, 4].length) (baseStart_663483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_663483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_663483 prefixEnd_663483 := by exact prefixLift 663483
  have htrace : WordTrace (prefixWord ++ tailWord_663483) baseStart_663483 baseEnd_663483 := by
    simpa [prefixWord, tailWord_663483, baseEnd_663483] using wordTrace_append hprefix tailTrace_663483
  have hstable : (prefixWord ++ tailWord_663483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663483).length < 2 ^ (prefixWord ++ tailWord_663483).sum := by decide
  have hdescent : baseEnd_663483 < baseStart_663483 := by decide
  rcases family_descends (prefixWord ++ tailWord_663483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663500 : List Nat := [2, 2, 1, 4, 1, 2, 1, 2, 4, 4]
def baseStart_663500 : Nat := 118140960795 + 663500 * 2 ^ 59
def prefixEnd_663500 : Nat := 4983230072969 + 3 ^ 40 * 663500 * 2
def baseEnd_663500 : Nat := 113564804752753095632875

theorem tailTrace_663500 : CollatzResearch.WordTrace tailWord_663500 prefixEnd_663500 113564804752753095632875 := by
  unfold tailWord_663500
  simp only [CollatzResearch.WordTrace]
  refine ⟨12099916548130145811749977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16133222064173527748999969 12099916548130145811749977)
  ·
    refine ⟨9074937411097609358812483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12099916548130145811749977 9074937411097609358812483)
    ·
      refine ⟨13612406116646414038218725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9074937411097609358812483 13612406116646414038218725)
      ·
        refine ⟨2552326146871202632166011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13612406116646414038218725 2552326146871202632166011)
        ·
          refine ⟨3828489220306803948249017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2552326146871202632166011 3828489220306803948249017)
          ·
            refine ⟨2871366915230102961186763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3828489220306803948249017 2871366915230102961186763)
            ·
              refine ⟨4307050372845154441780145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2871366915230102961186763 4307050372845154441780145)
              ·
                refine ⟨3230287779633865831335109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4307050372845154441780145 3230287779633865831335109)
                ·
                  refine ⟨605678958681349843375333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3230287779633865831335109 605678958681349843375333)
                  ·
                    refine ⟨113564804752753095632875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 605678958681349843375333 113564804752753095632875)
                    ·
                      rfl

theorem cell23_663500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 4, 4].length) (baseStart_663500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_663500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_663500 prefixEnd_663500 := by exact prefixLift 663500
  have htrace : WordTrace (prefixWord ++ tailWord_663500) baseStart_663500 baseEnd_663500 := by
    simpa [prefixWord, tailWord_663500, baseEnd_663500] using wordTrace_append hprefix tailTrace_663500
  have hstable : (prefixWord ++ tailWord_663500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663500).length < 2 ^ (prefixWord ++ tailWord_663500).sum := by decide
  have hdescent : baseEnd_663500 < baseStart_663500 := by decide
  rcases family_descends (prefixWord ++ tailWord_663500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663503 : List Nat := [1, 1, 2, 1, 1, 5, 2, 1, 3, 2, 4]
def baseStart_663503 : Nat := 118140960795 + 663503 * 2 ^ 59
def prefixEnd_663503 : Nat := 4983230072969 + 3 ^ 40 * 663503 * 2
def baseEnd_663503 : Nat := 340695954700222775161111

theorem tailTrace_663503 : CollatzResearch.WordTrace tailWord_663503 prefixEnd_663503 340695954700222775161111 := by
  unfold tailWord_663503
  simp only [CollatzResearch.WordTrace]
  refine ⟨24199942515249423135859163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16133295010166282090572775 24199942515249423135859163)
  ·
    refine ⟨36299913772874134703788745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24199942515249423135859163 36299913772874134703788745)
    ·
      refine ⟨27224935329655601027841559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36299913772874134703788745 27224935329655601027841559)
      ·
        refine ⟨40837402994483401541762339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27224935329655601027841559 40837402994483401541762339)
        ·
          refine ⟨61256104491725102312643509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40837402994483401541762339 61256104491725102312643509)
          ·
            refine ⟨5742759796099228341810329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61256104491725102312643509 5742759796099228341810329)
            ·
              refine ⟨4307069847074421256357747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5742759796099228341810329 4307069847074421256357747)
              ·
                refine ⟨6460604770611631884536621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4307069847074421256357747 6460604770611631884536621)
                ·
                  refine ⟨2422726788979361956701233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6460604770611631884536621 2422726788979361956701233)
                  ·
                    refine ⟨1817045091734521467525925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2422726788979361956701233 1817045091734521467525925)
                    ·
                      refine ⟨340695954700222775161111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1817045091734521467525925 340695954700222775161111)
                      ·
                        rfl

theorem cell23_663503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 2, 4].length) (baseStart_663503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_663503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_663503 prefixEnd_663503 := by exact prefixLift 663503
  have htrace : WordTrace (prefixWord ++ tailWord_663503) baseStart_663503 baseEnd_663503 := by
    simpa [prefixWord, tailWord_663503, baseEnd_663503] using wordTrace_append hprefix tailTrace_663503
  have hstable : (prefixWord ++ tailWord_663503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663503).length < 2 ^ (prefixWord ++ tailWord_663503).sum := by decide
  have hdescent : baseEnd_663503 < baseStart_663503 := by decide
  rcases family_descends (prefixWord ++ tailWord_663503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663534 : List Nat := [4, 1, 2, 1, 3, 1, 4, 1, 2, 4]
def baseStart_663534 : Nat := 118140960795 + 663534 * 2 ^ 59
def prefixEnd_663534 : Nat := 4983230072969 + 3 ^ 40 * 663534 * 2
def baseEnd_663534 : Nat := 113570624200170717957823

theorem tailTrace_663534 : CollatzResearch.WordTrace tailWord_663534 prefixEnd_663534 113570624200170717957823 := by
  unfold tailWord_663534
  simp only [CollatzResearch.WordTrace]
  refine ⟨3025134147267139428779707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16134048785424743620158437 3025134147267139428779707)
  ·
    refine ⟨4537701220900709143169561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3025134147267139428779707 4537701220900709143169561)
    ·
      refine ⟨3403275915675531857377171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4537701220900709143169561 3403275915675531857377171)
      ·
        refine ⟨5104913873513297786065757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3403275915675531857377171 5104913873513297786065757)
        ·
          refine ⟨1914342702567486669774659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5104913873513297786065757 1914342702567486669774659)
          ·
            refine ⟨2871514053851230004661989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1914342702567486669774659 2871514053851230004661989)
            ·
              refine ⟨538408885097105625874123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2871514053851230004661989 538408885097105625874123)
              ·
                refine ⟨807613327645658438811185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 538408885097105625874123 807613327645658438811185)
                ·
                  refine ⟨605709995734243829108389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 807613327645658438811185 605709995734243829108389)
                  ·
                    refine ⟨113570624200170717957823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 605709995734243829108389 113570624200170717957823)
                    ·
                      rfl

theorem cell23_663534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_663534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_663534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_663534 prefixEnd_663534 := by exact prefixLift 663534
  have htrace : WordTrace (prefixWord ++ tailWord_663534) baseStart_663534 baseEnd_663534 := by
    simpa [prefixWord, tailWord_663534, baseEnd_663534] using wordTrace_append hprefix tailTrace_663534
  have hstable : (prefixWord ++ tailWord_663534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663534).length < 2 ^ (prefixWord ++ tailWord_663534).sum := by decide
  have hdescent : baseEnd_663534 < baseStart_663534 := by decide
  rcases family_descends (prefixWord ++ tailWord_663534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663575 : List Nat := [1, 1, 3, 5, 2, 2, 2, 2, 1, 2, 2]
def baseStart_663575 : Nat := 118140960795 + 663575 * 2 ^ 59
def prefixEnd_663575 : Nat := 4983230072969 + 3 ^ 40 * 663575 * 2
def baseEnd_663575 : Nat := 340732925307346493460781

theorem tailTrace_663575 : CollatzResearch.WordTrace tailWord_663575 prefixEnd_663575 340732925307346493460781 := by
  unfold tailWord_663575
  simp only [CollatzResearch.WordTrace]
  refine ⟨24202568570988579432480179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16135045713992386288320119 24202568570988579432480179)
  ·
    refine ⟨36303852856482869148720269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24202568570988579432480179 36303852856482869148720269)
    ·
      refine ⟨13613944821181075930770101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36303852856482869148720269 13613944821181075930770101)
      ·
        refine ⟨1276307326985725868509697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13613944821181075930770101 1276307326985725868509697)
        ·
          refine ⟨957230495239294401382273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1276307326985725868509697 957230495239294401382273)
          ·
            refine ⟨717922871429470801036705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 957230495239294401382273 717922871429470801036705)
            ·
              refine ⟨538442153572103100777529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 717922871429470801036705 538442153572103100777529)
              ·
                refine ⟨403831615179077325583147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 538442153572103100777529 403831615179077325583147)
                ·
                  refine ⟨605747422768615988374721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 403831615179077325583147 605747422768615988374721)
                  ·
                    refine ⟨454310567076461991281041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 605747422768615988374721 454310567076461991281041)
                    ·
                      refine ⟨340732925307346493460781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 454310567076461991281041 340732925307346493460781)
                      ·
                        rfl

theorem cell23_663575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_663575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_663575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_663575 prefixEnd_663575 := by exact prefixLift 663575
  have htrace : WordTrace (prefixWord ++ tailWord_663575) baseStart_663575 baseEnd_663575 := by
    simpa [prefixWord, tailWord_663575, baseEnd_663575] using wordTrace_append hprefix tailTrace_663575
  have hstable : (prefixWord ++ tailWord_663575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663575).length < 2 ^ (prefixWord ++ tailWord_663575).sum := by decide
  have hdescent : baseEnd_663575 < baseStart_663575 := by decide
  rcases family_descends (prefixWord ++ tailWord_663575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663580 : List Nat := [2, 2, 3, 1, 3, 1, 1, 1, 2, 3, 4]
def baseStart_663580 : Nat := 118140960795 + 663580 * 2 ^ 59
def prefixEnd_663580 : Nat := 4983230072969 + 3 ^ 40 * 663580 * 2
def baseEnd_663580 : Nat := 340735492710618973898257

theorem tailTrace_663580 : CollatzResearch.WordTrace tailWord_663580 prefixEnd_663580 340735492710618973898257 := by
  unfold tailWord_663580
  simp only [CollatzResearch.WordTrace]
  refine ⟨12101375467985232643206097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16135167290646976857608129 12101375467985232643206097)
  ·
    refine ⟨9076031600988924482404573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12101375467985232643206097 9076031600988924482404573)
    ·
      refine ⟨3403511850370846680901715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9076031600988924482404573 3403511850370846680901715)
      ·
        refine ⟨5105267775556270021352573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3403511850370846680901715 5105267775556270021352573)
        ·
          refine ⟨1914475415833601258007215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5105267775556270021352573 1914475415833601258007215)
          ·
            refine ⟨2871713123750401887010823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1914475415833601258007215 2871713123750401887010823)
            ·
              refine ⟨4307569685625602830516235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2871713123750401887010823 4307569685625602830516235)
              ·
                refine ⟨6461354528438404245774353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4307569685625602830516235 6461354528438404245774353)
                ·
                  refine ⟨4846015896328803184330765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6461354528438404245774353 4846015896328803184330765)
                  ·
                    refine ⟨1817255961123301194124037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4846015896328803184330765 1817255961123301194124037)
                    ·
                      refine ⟨340735492710618973898257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1817255961123301194124037 340735492710618973898257)
                      ·
                        rfl

theorem cell23_663580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_663580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_663580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_663580 prefixEnd_663580 := by exact prefixLift 663580
  have htrace : WordTrace (prefixWord ++ tailWord_663580) baseStart_663580 baseEnd_663580 := by
    simpa [prefixWord, tailWord_663580, baseEnd_663580] using wordTrace_append hprefix tailTrace_663580
  have hstable : (prefixWord ++ tailWord_663580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663580).length < 2 ^ (prefixWord ++ tailWord_663580).sum := by decide
  have hdescent : baseEnd_663580 < baseStart_663580 := by decide
  rcases family_descends (prefixWord ++ tailWord_663580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663603 : List Nat := [1, 1, 1, 2, 4, 1, 3, 1, 9]
def baseStart_663603 : Nat := 118140960795 + 663603 * 2 ^ 59
def prefixEnd_663603 : Nat := 4983230072969 + 3 ^ 40 * 663603 * 2
def baseEnd_663603 : Nat := 37860811418408042656739

theorem tailTrace_663603 : CollatzResearch.WordTrace tailWord_663603 prefixEnd_663603 37860811418408042656739 := by
  unfold tailWord_663603
  simp only [CollatzResearch.WordTrace]
  refine ⟨24203589814887140214499463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16135726543258093476332975 24203589814887140214499463)
  ·
    refine ⟨36305384722330710321749195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24203589814887140214499463 36305384722330710321749195)
    ·
      refine ⟨54458077083496065482623793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36305384722330710321749195 54458077083496065482623793)
      ·
        refine ⟨40843557812622049111967845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54458077083496065482623793 40843557812622049111967845)
        ·
          refine ⟨7658167089866634208493971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40843557812622049111967845 7658167089866634208493971)
          ·
            refine ⟨11487250634799951312740957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7658167089866634208493971 11487250634799951312740957)
            ·
              refine ⟨4307718988049981742277859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11487250634799951312740957 4307718988049981742277859)
              ·
                refine ⟨6461578482074972613416789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4307718988049981742277859 6461578482074972613416789)
                ·
                  refine ⟨37860811418408042656739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 6461578482074972613416789 37860811418408042656739)
                  ·
                    rfl

theorem cell23_663603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 9].length) (baseStart_663603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_663603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_663603 prefixEnd_663603 := by exact prefixLift 663603
  have htrace : WordTrace (prefixWord ++ tailWord_663603) baseStart_663603 baseEnd_663603 := by
    simpa [prefixWord, tailWord_663603, baseEnd_663603] using wordTrace_append hprefix tailTrace_663603
  have hstable : (prefixWord ++ tailWord_663603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663603).length < 2 ^ (prefixWord ++ tailWord_663603).sum := by decide
  have hdescent : baseEnd_663603 < baseStart_663603 := by decide
  rcases family_descends (prefixWord ++ tailWord_663603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663637 : List Nat := [1, 3, 2, 2, 1, 3, 2, 4, 5]
def baseStart_663637 : Nat := 118140960795 + 663637 * 2 ^ 59
def prefixEnd_663637 : Nat := 4983230072969 + 3 ^ 40 * 663637 * 2
def baseEnd_663637 : Nat := 37862751234213916765055

theorem tailTrace_663637 : CollatzResearch.WordTrace tailWord_663637 prefixEnd_663637 37862751234213916765055 := by
  unfold tailWord_663637
  simp only [CollatzResearch.WordTrace]
  refine ⟨24204829896763964021237165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16136553264509309347491443 24204829896763964021237165)
  ·
    refine ⟨9076811211286486507963937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24204829896763964021237165 9076811211286486507963937)
    ·
      refine ⟨6807608408464864880972953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9076811211286486507963937 6807608408464864880972953)
      ·
        refine ⟨5105706306348648660729715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6807608408464864880972953 5105706306348648660729715)
        ·
          refine ⟨7658559459522972991094573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5105706306348648660729715 7658559459522972991094573)
          ·
            refine ⟨2871959797321114871660465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7658559459522972991094573 2871959797321114871660465)
            ·
              refine ⟨2153969847990836153745349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2871959797321114871660465 2153969847990836153745349)
              ·
                refine ⟨403869346498281778827253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2153969847990836153745349 403869346498281778827253)
                ·
                  refine ⟨37862751234213916765055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 403869346498281778827253 37862751234213916765055)
                  ·
                    rfl

theorem cell23_663637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 4, 5].length) (baseStart_663637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_663637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_663637 prefixEnd_663637 := by exact prefixLift 663637
  have htrace : WordTrace (prefixWord ++ tailWord_663637) baseStart_663637 baseEnd_663637 := by
    simpa [prefixWord, tailWord_663637, baseEnd_663637] using wordTrace_append hprefix tailTrace_663637
  have hstable : (prefixWord ++ tailWord_663637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663637).length < 2 ^ (prefixWord ++ tailWord_663637).sum := by decide
  have hdescent : baseEnd_663637 < baseStart_663637 := by decide
  rcases family_descends (prefixWord ++ tailWord_663637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663687 : List Nat := [1, 1, 4, 2, 1, 1, 2, 1, 4, 4, 2]
def baseStart_663687 : Nat := 118140960795 + 663687 * 2 ^ 59
def prefixEnd_663687 : Nat := 4983230072969 + 3 ^ 40 * 663687 * 2
def baseEnd_663687 : Nat := 340790435140650055260265

theorem tailTrace_663687 : CollatzResearch.WordTrace tailWord_663687 prefixEnd_663687 340790435140650055260265 := by
  unfold tailWord_663687
  simp only [CollatzResearch.WordTrace]
  refine ⟨24206653546582822560557315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16137769031055215040371543 24206653546582822560557315)
  ·
    refine ⟨36309980319874233840835973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24206653546582822560557315 36309980319874233840835973)
    ·
      refine ⟨6808121309976418845156745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36309980319874233840835973 6808121309976418845156745)
      ·
        refine ⟨5106090982482314133867559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6808121309976418845156745 5106090982482314133867559)
        ·
          refine ⟨7659136473723471200801339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5106090982482314133867559 7659136473723471200801339)
          ·
            refine ⟨11488704710585206801202009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7659136473723471200801339 11488704710585206801202009)
            ·
              refine ⟨8616528532938905100901507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11488704710585206801202009 8616528532938905100901507)
              ·
                refine ⟨12924792799408357651352261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8616528532938905100901507 12924792799408357651352261)
                ·
                  refine ⟨2423398649889067059628549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12924792799408357651352261 2423398649889067059628549)
                  ·
                    refine ⟨454387246854200073680353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2423398649889067059628549 454387246854200073680353)
                    ·
                      refine ⟨340790435140650055260265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 454387246854200073680353 340790435140650055260265)
                      ·
                        rfl

theorem cell23_663687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 4, 2].length) (baseStart_663687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_663687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_663687 prefixEnd_663687 := by exact prefixLift 663687
  have htrace : WordTrace (prefixWord ++ tailWord_663687) baseStart_663687 baseEnd_663687 := by
    simpa [prefixWord, tailWord_663687, baseEnd_663687] using wordTrace_append hprefix tailTrace_663687
  have hstable : (prefixWord ++ tailWord_663687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663687).length < 2 ^ (prefixWord ++ tailWord_663687).sum := by decide
  have hdescent : baseEnd_663687 < baseStart_663687 := by decide
  rcases family_descends (prefixWord ++ tailWord_663687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663748 : List Nat := [2, 3, 3, 1, 2, 1, 4, 2, 1, 4]
def baseStart_663748 : Nat := 118140960795 + 663748 * 2 ^ 59
def prefixEnd_663748 : Nat := 4983230072969 + 3 ^ 40 * 663748 * 2
def baseEnd_663748 : Nat := 113607252486858105532495

theorem tailTrace_663748 : CollatzResearch.WordTrace tailWord_663748 prefixEnd_663748 113607252486858105532495 := by
  unfold tailWord_663748
  simp only [CollatzResearch.WordTrace]
  refine ⟨12104439199680914989263949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16139252266241219985685265 12104439199680914989263949)
  ·
    refine ⟨4539164699880343120973981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12104439199680914989263949 4539164699880343120973981)
    ·
      refine ⟨1702186762455128670365243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4539164699880343120973981 1702186762455128670365243)
      ·
        refine ⟨2553280143682693005547865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1702186762455128670365243 2553280143682693005547865)
        ·
          refine ⟨1914960107762019754160899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2553280143682693005547865 1914960107762019754160899)
          ·
            refine ⟨2872440161643029631241349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1914960107762019754160899 2872440161643029631241349)
            ·
              refine ⟨538582530308068055857753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2872440161643029631241349 538582530308068055857753)
              ·
                refine ⟨403936897731051041893315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 538582530308068055857753 403936897731051041893315)
                ·
                  refine ⟨605905346596576562839973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 403936897731051041893315 605905346596576562839973)
                  ·
                    refine ⟨113607252486858105532495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 605905346596576562839973 113607252486858105532495)
                    ·
                      rfl

theorem cell23_663748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_663748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_663748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_663748 prefixEnd_663748 := by exact prefixLift 663748
  have htrace : WordTrace (prefixWord ++ tailWord_663748) baseStart_663748 baseEnd_663748 := by
    simpa [prefixWord, tailWord_663748, baseEnd_663748] using wordTrace_append hprefix tailTrace_663748
  have hstable : (prefixWord ++ tailWord_663748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663748).length < 2 ^ (prefixWord ++ tailWord_663748).sum := by decide
  have hdescent : baseEnd_663748 < baseStart_663748 := by decide
  rcases family_descends (prefixWord ++ tailWord_663748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663754 : List Nat := [3, 1, 2, 1, 3, 1, 2, 3, 3, 1, 3]
def baseStart_663754 : Nat := 118140960795 + 663754 * 2 ^ 59
def prefixEnd_663754 : Nat := 4983230072969 + 3 ^ 40 * 663754 * 2
def baseEnd_663754 : Nat := 340824838344501293122457

theorem tailTrace_663754 : CollatzResearch.WordTrace tailWord_663754 prefixEnd_663754 340824838344501293122457 := by
  unfold tailWord_663754
  simp only [CollatzResearch.WordTrace]
  refine ⟨6052274309335023250811579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16139398158226728668830877 6052274309335023250811579)
  ·
    refine ⟨9078411464002534876217369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6052274309335023250811579 9078411464002534876217369)
    ·
      refine ⟨6808808598001901157163027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9078411464002534876217369 6808808598001901157163027)
      ·
        refine ⟨10213212897002851735744541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6808808598001901157163027 10213212897002851735744541)
        ·
          refine ⟨3829954836376069400904203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10213212897002851735744541 3829954836376069400904203)
          ·
            refine ⟨5744932254564104101356305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3829954836376069400904203 5744932254564104101356305)
            ·
              refine ⟨4308699190923078076017229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5744932254564104101356305 4308699190923078076017229)
              ·
                refine ⟨1615762196596154278506461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4308699190923078076017229 1615762196596154278506461)
                ·
                  refine ⟨605910823723557854439923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1615762196596154278506461 605910823723557854439923)
                  ·
                    refine ⟨908866235585336781659885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 605910823723557854439923 908866235585336781659885)
                    ·
                      refine ⟨340824838344501293122457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 908866235585336781659885 340824838344501293122457)
                      ·
                        rfl

theorem cell23_663754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 3, 1, 3].length) (baseStart_663754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_663754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_663754 prefixEnd_663754 := by exact prefixLift 663754
  have htrace : WordTrace (prefixWord ++ tailWord_663754) baseStart_663754 baseEnd_663754 := by
    simpa [prefixWord, tailWord_663754, baseEnd_663754] using wordTrace_append hprefix tailTrace_663754
  have hstable : (prefixWord ++ tailWord_663754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663754).length < 2 ^ (prefixWord ++ tailWord_663754).sum := by decide
  have hdescent : baseEnd_663754 < baseStart_663754 := by decide
  rcases family_descends (prefixWord ++ tailWord_663754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663777 : List Nat := [1, 2, 3, 1, 3, 1, 1, 3, 3, 1, 4]
def baseStart_663777 : Nat := 118140960795 + 663777 * 2 ^ 59
def prefixEnd_663777 : Nat := 4983230072969 + 3 ^ 40 * 663777 * 2
def baseEnd_663777 : Nat := 340836648399554703134851

theorem tailTrace_663777 : CollatzResearch.WordTrace tailWord_663777 prefixEnd_663777 340836648399554703134851 := by
  unfold tailWord_663777
  simp only [CollatzResearch.WordTrace]
  refine ⟨24209936116256767931333585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16139957410837845287555723 24209936116256767931333585)
  ·
    refine ⟨18157452087192575948500189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24209936116256767931333585 18157452087192575948500189)
    ·
      refine ⟨6809044532697215980687571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18157452087192575948500189 6809044532697215980687571)
      ·
        refine ⟨10213566799045823971031357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6809044532697215980687571 10213566799045823971031357)
        ·
          refine ⟨3830087549642183989136759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10213566799045823971031357 3830087549642183989136759)
          ·
            refine ⟨5745131324463275983705139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3830087549642183989136759 5745131324463275983705139)
            ·
              refine ⟨8617696986694913975557709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5745131324463275983705139 8617696986694913975557709)
              ·
                refine ⟨3231636370010592740834141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8617696986694913975557709 3231636370010592740834141)
                ·
                  refine ⟨1211863638753972277812803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3231636370010592740834141 1211863638753972277812803)
                  ·
                    refine ⟨1817795458130958416719205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1211863638753972277812803 1817795458130958416719205)
                    ·
                      refine ⟨340836648399554703134851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1817795458130958416719205 340836648399554703134851)
                      ·
                        rfl

theorem cell23_663777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_663777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_663777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_663777 prefixEnd_663777 := by exact prefixLift 663777
  have htrace : WordTrace (prefixWord ++ tailWord_663777) baseStart_663777 baseEnd_663777 := by
    simpa [prefixWord, tailWord_663777, baseEnd_663777] using wordTrace_append hprefix tailTrace_663777
  have hstable : (prefixWord ++ tailWord_663777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663777).length < 2 ^ (prefixWord ++ tailWord_663777).sum := by decide
  have hdescent : baseEnd_663777 < baseStart_663777 := by decide
  rcases family_descends (prefixWord ++ tailWord_663777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663781 : List Nat := [1, 3, 1, 4, 2, 1, 3, 1, 2, 3, 2]
def baseStart_663781 : Nat := 118140960795 + 663781 * 2 ^ 59
def prefixEnd_663781 : Nat := 4983230072969 + 3 ^ 40 * 663781 * 2
def baseEnd_663781 : Nat := 340838702322172687484833

theorem tailTrace_663781 : CollatzResearch.WordTrace tailWord_663781 prefixEnd_663781 340838702322172687484833 := by
  unfold tailWord_663781
  simp only [CollatzResearch.WordTrace]
  refine ⟨24210082008242276614479197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16140054672161517742986131 24210082008242276614479197)
  ·
    refine ⟨9078780753090853730429699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24210082008242276614479197 9078780753090853730429699)
    ·
      refine ⟨13618171129636280595644549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9078780753090853730429699 13618171129636280595644549)
      ·
        refine ⟨2553407086806802611683353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13618171129636280595644549 2553407086806802611683353)
        ·
          refine ⟨1915055315105101958762515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2553407086806802611683353 1915055315105101958762515)
          ·
            refine ⟨2872582972657652938143773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1915055315105101958762515 2872582972657652938143773)
            ·
              refine ⟨1077218614746619851803915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2872582972657652938143773 1077218614746619851803915)
              ·
                refine ⟨1615827922119929777705873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1077218614746619851803915 1615827922119929777705873)
                ·
                  refine ⟨1211870941589947333279405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1615827922119929777705873 1211870941589947333279405)
                  ·
                    refine ⟨454451603096230249979777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1211870941589947333279405 454451603096230249979777)
                    ·
                      refine ⟨340838702322172687484833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 454451603096230249979777 340838702322172687484833)
                      ·
                        rfl

theorem cell23_663781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_663781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_663781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_663781 prefixEnd_663781 := by exact prefixLift 663781
  have htrace : WordTrace (prefixWord ++ tailWord_663781) baseStart_663781 baseEnd_663781 := by
    simpa [prefixWord, tailWord_663781, baseEnd_663781] using wordTrace_append hprefix tailTrace_663781
  have hstable : (prefixWord ++ tailWord_663781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663781).length < 2 ^ (prefixWord ++ tailWord_663781).sum := by decide
  have hdescent : baseEnd_663781 < baseStart_663781 := by decide
  rcases family_descends (prefixWord ++ tailWord_663781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663787 : List Nat := [1, 1, 1, 1, 2, 5, 2, 2, 4, 4]
def baseStart_663787 : Nat := 118140960795 + 663787 * 2 ^ 59
def prefixEnd_663787 : Nat := 4983230072969 + 3 ^ 40 * 663787 * 2
def baseEnd_663787 : Nat := 113613927735366554669935

theorem tailTrace_663787 : CollatzResearch.WordTrace tailWord_663787 prefixEnd_663787 113613927735366554669935 := by
  unfold tailWord_663787
  simp only [CollatzResearch.WordTrace]
  refine ⟨24210300846220539639197615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16140200564147026426131743 24210300846220539639197615)
  ·
    refine ⟨36315451269330809458796423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24210300846220539639197615 36315451269330809458796423)
    ·
      refine ⟨54473176903996214188194635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36315451269330809458796423 54473176903996214188194635)
      ·
        refine ⟨81709765355994321282291953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54473176903996214188194635 81709765355994321282291953)
        ·
          refine ⟨61282324016995740961718965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81709765355994321282291953 61282324016995740961718965)
          ·
            refine ⟨5745217876593350715161153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61282324016995740961718965 5745217876593350715161153)
            ·
              refine ⟨4308913407445013036370865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5745217876593350715161153 4308913407445013036370865)
              ·
                refine ⟨3231685055583759777278149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4308913407445013036370865 3231685055583759777278149)
                ·
                  refine ⟨605940947921954958239653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3231685055583759777278149 605940947921954958239653)
                  ·
                    refine ⟨113613927735366554669935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 605940947921954958239653 113613927735366554669935)
                    ·
                      rfl

theorem cell23_663787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 4, 4].length) (baseStart_663787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_663787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_663787 prefixEnd_663787 := by exact prefixLift 663787
  have htrace : WordTrace (prefixWord ++ tailWord_663787) baseStart_663787 baseEnd_663787 := by
    simpa [prefixWord, tailWord_663787, baseEnd_663787] using wordTrace_append hprefix tailTrace_663787
  have hstable : (prefixWord ++ tailWord_663787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663787).length < 2 ^ (prefixWord ++ tailWord_663787).sum := by decide
  have hdescent : baseEnd_663787 < baseStart_663787 := by decide
  rcases family_descends (prefixWord ++ tailWord_663787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663791 : List Nat := [1, 1, 2, 1, 6, 3, 2, 1, 1, 5]
def baseStart_663791 : Nat := 118140960795 + 663791 * 2 ^ 59
def prefixEnd_663791 : Nat := 4983230072969 + 3 ^ 40 * 663791 * 2
def baseEnd_663791 : Nat := 113614612376239216119929

theorem tailTrace_663791 : CollatzResearch.WordTrace tailWord_663791 prefixEnd_663791 113614612376239216119929 := by
  unfold tailWord_663791
  simp only [CollatzResearch.WordTrace]
  refine ⟨24210446738206048322343227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16140297825470698881562151 24210446738206048322343227)
  ·
    refine ⟨36315670107309072483514841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24210446738206048322343227 36315670107309072483514841)
    ·
      refine ⟨27236752580481804362636131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36315670107309072483514841 27236752580481804362636131)
      ·
        refine ⟨40855128870722706543954197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27236752580481804362636131 40855128870722706543954197)
        ·
          refine ⟨1915084165815126869247853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 40855128870722706543954197 1915084165815126869247853)
          ·
            refine ⟨718156562180672575967945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1915084165815126869247853 718156562180672575967945)
            ·
              refine ⟨538617421635504431975959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 718156562180672575967945 538617421635504431975959)
              ·
                refine ⟨807926132453256647963939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 538617421635504431975959 807926132453256647963939)
                ·
                  refine ⟨1211889198679884971945909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 807926132453256647963939 1211889198679884971945909)
                  ·
                    refine ⟨113614612376239216119929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1211889198679884971945909 113614612376239216119929)
                    ·
                      rfl

theorem cell23_663791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 1, 1, 5].length) (baseStart_663791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_663791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_663791 prefixEnd_663791 := by exact prefixLift 663791
  have htrace : WordTrace (prefixWord ++ tailWord_663791) baseStart_663791 baseEnd_663791 := by
    simpa [prefixWord, tailWord_663791, baseEnd_663791] using wordTrace_append hprefix tailTrace_663791
  have hstable : (prefixWord ++ tailWord_663791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663791).length < 2 ^ (prefixWord ++ tailWord_663791).sum := by decide
  have hdescent : baseEnd_663791 < baseStart_663791 := by decide
  rcases family_descends (prefixWord ++ tailWord_663791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663804 : List Nat := [2, 2, 2, 1, 4, 2, 1, 1, 4, 4]
def baseStart_663804 : Nat := 118140960795 + 663804 * 2 ^ 59
def prefixEnd_663804 : Nat := 4983230072969 + 3 ^ 40 * 663804 * 2
def baseEnd_663804 : Nat := 113616837459075365832409

theorem tailTrace_663804 : CollatzResearch.WordTrace tailWord_663804 prefixEnd_663804 113616837459075365832409 := by
  unfold tailWord_663804
  simp only [CollatzResearch.WordTrace]
  refine ⟨12105460443579475771283233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16140613924772634361710977 12105460443579475771283233)
  ·
    refine ⟨9079095332684606828462425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12105460443579475771283233 9079095332684606828462425)
    ·
      refine ⟨6809321499513455121346819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9079095332684606828462425 6809321499513455121346819)
      ·
        refine ⟨10213982249270182682020229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6809321499513455121346819 10213982249270182682020229)
        ·
          refine ⟨1915121671738159252878793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10213982249270182682020229 1915121671738159252878793)
          ·
            refine ⟨1436341253803619439659095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1915121671738159252878793 1436341253803619439659095)
            ·
              refine ⟨2154511880705429159488643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1436341253803619439659095 2154511880705429159488643)
              ·
                refine ⟨3231767821058143739232965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2154511880705429159488643 3231767821058143739232965)
                ·
                  refine ⟨605956466448401951106181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3231767821058143739232965 605956466448401951106181)
                  ·
                    refine ⟨113616837459075365832409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 605956466448401951106181 113616837459075365832409)
                    ·
                      rfl

theorem cell23_663804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 4, 4].length) (baseStart_663804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_663804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_663804 prefixEnd_663804 := by exact prefixLift 663804
  have htrace : WordTrace (prefixWord ++ tailWord_663804) baseStart_663804 baseEnd_663804 := by
    simpa [prefixWord, tailWord_663804, baseEnd_663804] using wordTrace_append hprefix tailTrace_663804
  have hstable : (prefixWord ++ tailWord_663804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663804).length < 2 ^ (prefixWord ++ tailWord_663804).sum := by decide
  have hdescent : baseEnd_663804 < baseStart_663804 := by decide
  rcases family_descends (prefixWord ++ tailWord_663804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663811 : List Nat := [1, 1, 1, 3, 2, 3, 4, 1, 3, 2, 2]
def baseStart_663811 : Nat := 118140960795 + 663811 * 2 ^ 59
def prefixEnd_663811 : Nat := 4983230072969 + 3 ^ 40 * 663811 * 2
def baseEnd_663811 : Nat := 340854106741807570109695

theorem tailTrace_663811 : CollatzResearch.WordTrace tailWord_663811 prefixEnd_663811 340854106741807570109695 := by
  unfold tailWord_663811
  simp only [CollatzResearch.WordTrace]
  refine ⟨24211176198133591738071287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16140784132089061158714191 24211176198133591738071287)
  ·
    refine ⟨36316764297200387607106931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24211176198133591738071287 36316764297200387607106931)
    ·
      refine ⟨54475146445800581410660397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36316764297200387607106931 54475146445800581410660397)
      ·
        refine ⟨20428179917175218028997649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54475146445800581410660397 20428179917175218028997649)
        ·
          refine ⟨15321134937881413521748237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20428179917175218028997649 15321134937881413521748237)
          ·
            refine ⟨5745425601705530070655589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15321134937881413521748237 5745425601705530070655589)
            ·
              refine ⟨1077267300319786888247923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5745425601705530070655589 1077267300319786888247923)
              ·
                refine ⟨1615900950479680332371885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1077267300319786888247923 1615900950479680332371885)
                ·
                  refine ⟨605962856429880124639457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1615900950479680332371885 605962856429880124639457)
                  ·
                    refine ⟨454472142322410093479593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 605962856429880124639457 454472142322410093479593)
                    ·
                      refine ⟨340854106741807570109695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 454472142322410093479593 340854106741807570109695)
                      ·
                        rfl

theorem cell23_663811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 3, 2, 2].length) (baseStart_663811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_663811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_663811 prefixEnd_663811 := by exact prefixLift 663811
  have htrace : WordTrace (prefixWord ++ tailWord_663811) baseStart_663811 baseEnd_663811 := by
    simpa [prefixWord, tailWord_663811, baseEnd_663811] using wordTrace_append hprefix tailTrace_663811
  have hstable : (prefixWord ++ tailWord_663811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663811).length < 2 ^ (prefixWord ++ tailWord_663811).sum := by decide
  have hdescent : baseEnd_663811 < baseStart_663811 := by decide
  rcases family_descends (prefixWord ++ tailWord_663811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663831 : List Nat := [1, 1, 3, 4, 1, 3, 2, 2, 1, 2, 3]
def baseStart_663831 : Nat := 118140960795 + 663831 * 2 ^ 59
def prefixEnd_663831 : Nat := 4983230072969 + 3 ^ 40 * 663831 * 2
def baseEnd_663831 : Nat := 340864376354897491859603

theorem tailTrace_663831 : CollatzResearch.WordTrace tailWord_663831 prefixEnd_663831 340864376354897491859603 := by
  unfold tailWord_663831
  simp only [CollatzResearch.WordTrace]
  refine ⟨24211905658061135153799347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16141270438707423435866231 24211905658061135153799347)
  ·
    refine ⟨36317858487091702730699021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24211905658061135153799347 36317858487091702730699021)
    ·
      refine ⟨13619196932659388524012133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36317858487091702730699021 13619196932659388524012133)
      ·
        refine ⟨2553599424873635348252275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13619196932659388524012133 2553599424873635348252275)
        ·
          refine ⟨3830399137310453022378413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2553599424873635348252275 3830399137310453022378413)
          ·
            refine ⟨1436399676491419883391905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3830399137310453022378413 1436399676491419883391905)
            ·
              refine ⟨1077299757368564912543929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1436399676491419883391905 1077299757368564912543929)
              ·
                refine ⟨807974818026423684407947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1077299757368564912543929 807974818026423684407947)
                ·
                  refine ⟨1211962227039635526611921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 807974818026423684407947 1211962227039635526611921)
                  ·
                    refine ⟨908971670279726644958941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1211962227039635526611921 908971670279726644958941)
                    ·
                      refine ⟨340864376354897491859603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 908971670279726644958941 340864376354897491859603)
                      ·
                        rfl

theorem cell23_663831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_663831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_663831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_663831 prefixEnd_663831 := by exact prefixLift 663831
  have htrace : WordTrace (prefixWord ++ tailWord_663831) baseStart_663831 baseEnd_663831 := by
    simpa [prefixWord, tailWord_663831, baseEnd_663831] using wordTrace_append hprefix tailTrace_663831
  have hstable : (prefixWord ++ tailWord_663831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663831).length < 2 ^ (prefixWord ++ tailWord_663831).sum := by decide
  have hdescent : baseEnd_663831 < baseStart_663831 := by decide
  rcases family_descends (prefixWord ++ tailWord_663831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663861 : List Nat := [1, 3, 3, 1, 2, 1, 2, 4, 2, 1, 3]
def baseStart_663861 : Nat := 118140960795 + 663861 * 2 ^ 59
def prefixEnd_663861 : Nat := 4983230072969 + 3 ^ 40 * 663861 * 2
def baseEnd_663861 : Nat := 340879780774532374484465

theorem tailTrace_663861 : CollatzResearch.WordTrace tailWord_663861 prefixEnd_663861 340879780774532374484465 := by
  unfold tailWord_663861
  simp only [CollatzResearch.WordTrace]
  refine ⟨24212999847952450277391437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16141999898634966851594291 24212999847952450277391437)
  ·
    refine ⟨9079874942982168854021789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24212999847952450277391437 9079874942982168854021789)
    ·
      refine ⟨3404953103618313320258171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9079874942982168854021789 3404953103618313320258171)
      ·
        refine ⟨5107429655427469980387257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3404953103618313320258171 5107429655427469980387257)
        ·
          refine ⟨3830572241570602485290443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5107429655427469980387257 3830572241570602485290443)
          ·
            refine ⟨5745858362355903727935665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3830572241570602485290443 5745858362355903727935665)
            ·
              refine ⟨4309393771766927795951749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5745858362355903727935665 4309393771766927795951749)
              ·
                refine ⟨808011332206298961740953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4309393771766927795951749 808011332206298961740953)
                ·
                  refine ⟨606008499154724221305715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 808011332206298961740953 606008499154724221305715)
                  ·
                    refine ⟨909012748732086331958573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 606008499154724221305715 909012748732086331958573)
                    ·
                      refine ⟨340879780774532374484465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 909012748732086331958573 340879780774532374484465)
                      ·
                        rfl

theorem cell23_663861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_663861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_663861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_663861 prefixEnd_663861 := by exact prefixLift 663861
  have htrace : WordTrace (prefixWord ++ tailWord_663861) baseStart_663861 baseEnd_663861 := by
    simpa [prefixWord, tailWord_663861, baseEnd_663861] using wordTrace_append hprefix tailTrace_663861
  have hstable : (prefixWord ++ tailWord_663861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663861).length < 2 ^ (prefixWord ++ tailWord_663861).sum := by decide
  have hdescent : baseEnd_663861 < baseStart_663861 := by decide
  rcases family_descends (prefixWord ++ tailWord_663861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663887 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 4, 4, 3]
def baseStart_663887 : Nat := 118140960795 + 663887 * 2 ^ 59
def prefixEnd_663887 : Nat := 4983230072969 + 3 ^ 40 * 663887 * 2
def baseEnd_663887 : Nat := 340893131271549272759345

theorem tailTrace_663887 : CollatzResearch.WordTrace tailWord_663887 prefixEnd_663887 340893131271549272759345 := by
  unfold tailWord_663887
  simp only [CollatzResearch.WordTrace]
  refine ⟨24213948145858256717837915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16142632097238837811891943 24213948145858256717837915)
  ·
    refine ⟨36320922218787385076756873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24213948145858256717837915 36320922218787385076756873)
    ·
      refine ⟨27240691664090538807567655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36320922218787385076756873 27240691664090538807567655)
      ·
        refine ⟨40861037496135808211351483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27240691664090538807567655 40861037496135808211351483)
        ·
          refine ⟨61291556244203712317027225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40861037496135808211351483 61291556244203712317027225)
          ·
            refine ⟨45968667183152784237770419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61291556244203712317027225 45968667183152784237770419)
            ·
              refine ⟨68953000774729176356655629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45968667183152784237770419 68953000774729176356655629)
              ·
                refine ⟨25857375290523441133745861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68953000774729176356655629 25857375290523441133745861)
                ·
                  refine ⟨4848257866973145212577349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25857375290523441133745861 4848257866973145212577349)
                  ·
                    refine ⟨909048350057464727358253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4848257866973145212577349 909048350057464727358253)
                    ·
                      refine ⟨340893131271549272759345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 909048350057464727358253 340893131271549272759345)
                      ·
                        rfl

theorem cell23_663887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 4, 3].length) (baseStart_663887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_663887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_663887 prefixEnd_663887 := by exact prefixLift 663887
  have htrace : WordTrace (prefixWord ++ tailWord_663887) baseStart_663887 baseEnd_663887 := by
    simpa [prefixWord, tailWord_663887, baseEnd_663887] using wordTrace_append hprefix tailTrace_663887
  have hstable : (prefixWord ++ tailWord_663887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663887).length < 2 ^ (prefixWord ++ tailWord_663887).sum := by decide
  have hdescent : baseEnd_663887 < baseStart_663887 := by decide
  rcases family_descends (prefixWord ++ tailWord_663887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663888 : List Nat := [2, 1, 1, 1, 1, 8, 1, 2, 1, 3, 2]
def baseStart_663888 : Nat := 118140960795 + 663888 * 2 ^ 59
def prefixEnd_663888 : Nat := 4983230072969 + 3 ^ 40 * 663888 * 2
def baseEnd_663888 : Nat := 340893644752203768846841

theorem tailTrace_663888 : CollatzResearch.WordTrace tailWord_663888 prefixEnd_663888 340893644752203768846841 := by
  unfold tailWord_663888
  simp only [CollatzResearch.WordTrace]
  refine ⟨12106992309427316944312159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16142656412569755925749545 12106992309427316944312159)
  ·
    refine ⟨18160488464140975416468239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12106992309427316944312159 18160488464140975416468239)
    ·
      refine ⟨27240732696211463124702359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18160488464140975416468239 27240732696211463124702359)
      ·
        refine ⟨40861099044317194687053539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27240732696211463124702359 40861099044317194687053539)
        ·
          refine ⟨61291648566475792030580309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40861099044317194687053539 61291648566475792030580309)
          ·
            refine ⟨718261506638388187858363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 61291648566475792030580309 718261506638388187858363)
            ·
              refine ⟨1077392259957582281787545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 718261506638388187858363 1077392259957582281787545)
              ·
                refine ⟨808044194968186711340659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1077392259957582281787545 808044194968186711340659)
                ·
                  refine ⟨1212066292452280067010989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 808044194968186711340659 1212066292452280067010989)
                  ·
                    refine ⟨454524859669605025129121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1212066292452280067010989 454524859669605025129121)
                    ·
                      refine ⟨340893644752203768846841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 454524859669605025129121 340893644752203768846841)
                      ·
                        rfl

theorem cell23_663888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 2, 1, 3, 2].length) (baseStart_663888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_663888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_663888 prefixEnd_663888 := by exact prefixLift 663888
  have htrace : WordTrace (prefixWord ++ tailWord_663888) baseStart_663888 baseEnd_663888 := by
    simpa [prefixWord, tailWord_663888, baseEnd_663888] using wordTrace_append hprefix tailTrace_663888
  have hstable : (prefixWord ++ tailWord_663888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663888).length < 2 ^ (prefixWord ++ tailWord_663888).sum := by decide
  have hdescent : baseEnd_663888 < baseStart_663888 := by decide
  rcases family_descends (prefixWord ++ tailWord_663888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663897 : List Nat := [1, 2, 1, 2, 2, 2, 1, 2, 4, 2, 4]
def baseStart_663897 : Nat := 118140960795 + 663897 * 2 ^ 59
def prefixEnd_663897 : Nat := 4983230072969 + 3 ^ 40 * 663897 * 2
def baseEnd_663897 : Nat := 340898266078094233634299

theorem tailTrace_663897 : CollatzResearch.WordTrace tailWord_663897 prefixEnd_663897 340898266078094233634299 := by
  unfold tailWord_663897
  simp only [CollatzResearch.WordTrace]
  refine ⟨24214312875822028425701945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16142875250548018950467963 24214312875822028425701945)
  ·
    refine ⟨18160734656866521319276459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24214312875822028425701945 18160734656866521319276459)
    ·
      refine ⟨27241101985299781978914689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18160734656866521319276459 27241101985299781978914689)
      ·
        refine ⟨20430826488974836484186017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27241101985299781978914689 20430826488974836484186017)
        ·
          refine ⟨15323119866731127363139513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20430826488974836484186017 15323119866731127363139513)
          ·
            refine ⟨11492339900048345522354635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15323119866731127363139513 11492339900048345522354635)
            ·
              refine ⟨17238509850072518283531953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11492339900048345522354635 17238509850072518283531953)
              ·
                refine ⟨12928882387554388712648965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17238509850072518283531953 12928882387554388712648965)
                ·
                  refine ⟨2424165447666447883621681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12928882387554388712648965 2424165447666447883621681)
                  ·
                    refine ⟨1818124085749835912716261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2424165447666447883621681 1818124085749835912716261)
                    ·
                      refine ⟨340898266078094233634299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1818124085749835912716261 340898266078094233634299)
                      ·
                        rfl

theorem cell23_663897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 2, 4].length) (baseStart_663897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_663897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_663897 prefixEnd_663897 := by exact prefixLift 663897
  have htrace : WordTrace (prefixWord ++ tailWord_663897) baseStart_663897 baseEnd_663897 := by
    simpa [prefixWord, tailWord_663897, baseEnd_663897] using wordTrace_append hprefix tailTrace_663897
  have hstable : (prefixWord ++ tailWord_663897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663897).length < 2 ^ (prefixWord ++ tailWord_663897).sum := by decide
  have hdescent : baseEnd_663897 < baseStart_663897 := by decide
  rcases family_descends (prefixWord ++ tailWord_663897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663969 : List Nat := [1, 2, 3, 5, 2, 1, 1, 2, 2, 2, 2]
def baseStart_663969 : Nat := 118140960795 + 663969 * 2 ^ 59
def prefixEnd_663969 : Nat := 4983230072969 + 3 ^ 40 * 663969 * 2
def baseEnd_663969 : Nat := 340935236685217951933969

theorem tailTrace_663969 : CollatzResearch.WordTrace tailWord_663969 prefixEnd_663969 340935236685217951933969 := by
  unfold tailWord_663969
  simp only [CollatzResearch.WordTrace]
  refine ⟨24216938931561184722322961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16144625954374123148215307 24216938931561184722322961)
  ·
    refine ⟨18162704198670888541742221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24216938931561184722322961 18162704198670888541742221)
    ·
      refine ⟨6811014074501583203153333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18162704198670888541742221 6811014074501583203153333)
      ·
        refine ⟨638532569484523425295625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6811014074501583203153333 638532569484523425295625)
        ·
          refine ⟨478899427113392568971719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 638532569484523425295625 478899427113392568971719)
          ·
            refine ⟨718349140670088853457579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 478899427113392568971719 718349140670088853457579)
            ·
              refine ⟨1077523711005133280186369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 718349140670088853457579 1077523711005133280186369)
              ·
                refine ⟨808142783253849960139777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1077523711005133280186369 808142783253849960139777)
                ·
                  refine ⟨606107087440387470104833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 808142783253849960139777 606107087440387470104833)
                  ·
                    refine ⟨454580315580290602578625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 606107087440387470104833 454580315580290602578625)
                    ·
                      refine ⟨340935236685217951933969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 454580315580290602578625 340935236685217951933969)
                      ·
                        rfl

theorem cell23_663969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_663969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_663969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_663969 prefixEnd_663969 := by exact prefixLift 663969
  have htrace : WordTrace (prefixWord ++ tailWord_663969) baseStart_663969 baseEnd_663969 := by
    simpa [prefixWord, tailWord_663969, baseEnd_663969] using wordTrace_append hprefix tailTrace_663969
  have hstable : (prefixWord ++ tailWord_663969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663969).length < 2 ^ (prefixWord ++ tailWord_663969).sum := by decide
  have hdescent : baseEnd_663969 < baseStart_663969 := by decide
  rcases family_descends (prefixWord ++ tailWord_663969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663977 : List Nat := [1, 2, 1, 1, 1, 1, 3, 3, 2, 3, 5]
def baseStart_663977 : Nat := 118140960795 + 663977 * 2 ^ 59
def prefixEnd_663977 : Nat := 4983230072969 + 3 ^ 40 * 663977 * 2
def baseEnd_663977 : Nat := 340939344530453920633931

theorem tailTrace_663977 : CollatzResearch.WordTrace tailWord_663977 prefixEnd_663977 340939344530453920633931 := by
  unfold tailWord_663977
  simp only [CollatzResearch.WordTrace]
  refine ⟨24217230715532202088614185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16144820477021468059076123 24217230715532202088614185)
  ·
    refine ⟨18162923036649151566460639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24217230715532202088614185 18162923036649151566460639)
    ·
      refine ⟨27244384554973727349690959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18162923036649151566460639 27244384554973727349690959)
      ·
        refine ⟨40866576832460591024536439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27244384554973727349690959 40866576832460591024536439)
        ·
          refine ⟨61299865248690886536804659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40866576832460591024536439 61299865248690886536804659)
          ·
            refine ⟨91949797873036329805206989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61299865248690886536804659 91949797873036329805206989)
            ·
              refine ⟨34481174202388623676952621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91949797873036329805206989 34481174202388623676952621)
              ·
                refine ⟨12930440325895733878857233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34481174202388623676952621 12930440325895733878857233)
                ·
                  refine ⟨9697830244421800409142925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12930440325895733878857233 9697830244421800409142925)
                  ·
                    refine ⟨3636686341658175153428597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9697830244421800409142925 3636686341658175153428597)
                    ·
                      refine ⟨340939344530453920633931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3636686341658175153428597 340939344530453920633931)
                      ·
                        rfl

theorem cell23_663977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 3, 5].length) (baseStart_663977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_663977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_663977 prefixEnd_663977 := by exact prefixLift 663977
  have htrace : WordTrace (prefixWord ++ tailWord_663977) baseStart_663977 baseEnd_663977 := by
    simpa [prefixWord, tailWord_663977, baseEnd_663977] using wordTrace_append hprefix tailTrace_663977
  have hstable : (prefixWord ++ tailWord_663977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663977).length < 2 ^ (prefixWord ++ tailWord_663977).sum := by decide
  have hdescent : baseEnd_663977 < baseStart_663977 := by decide
  rcases family_descends (prefixWord ++ tailWord_663977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_663991 : List Nat := [1, 1, 3, 1, 3, 3, 2, 1, 2, 4, 2]
def baseStart_663991 : Nat := 118140960795 + 663991 * 2 ^ 59
def prefixEnd_663991 : Nat := 4983230072969 + 3 ^ 40 * 663991 * 2
def baseEnd_663991 : Nat := 340946533259616865858867

theorem tailTrace_663991 : CollatzResearch.WordTrace tailWord_663991 prefixEnd_663991 340946533259616865858867 := by
  unfold tailWord_663991
  simp only [CollatzResearch.WordTrace]
  refine ⟨24217741337481482479623827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16145160891654321653082551 24217741337481482479623827)
  ·
    refine ⟨36326612006222223719435741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24217741337481482479623827 36326612006222223719435741)
    ·
      refine ⟨13622479502333333894788403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36326612006222223719435741 13622479502333333894788403)
      ·
        refine ⟨20433719253500000842182605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13622479502333333894788403 20433719253500000842182605)
        ·
          refine ⟨7662644720062500315818477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20433719253500000842182605 7662644720062500315818477)
          ·
            refine ⟨2873491770023437618431929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7662644720062500315818477 2873491770023437618431929)
            ·
              refine ⟨2155118827517578213823947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2873491770023437618431929 2155118827517578213823947)
              ·
                refine ⟨3232678241276367320735921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2155118827517578213823947 3232678241276367320735921)
                ·
                  refine ⟨2424508680957275490551941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3232678241276367320735921 2424508680957275490551941)
                  ·
                    refine ⟨454595377679489154478489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2424508680957275490551941 454595377679489154478489)
                    ·
                      refine ⟨340946533259616865858867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 454595377679489154478489 340946533259616865858867)
                      ·
                        rfl

theorem cell23_663991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 4, 2].length) (baseStart_663991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_663991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_663991 prefixEnd_663991 := by exact prefixLift 663991
  have htrace : WordTrace (prefixWord ++ tailWord_663991) baseStart_663991 baseEnd_663991 := by
    simpa [prefixWord, tailWord_663991, baseEnd_663991] using wordTrace_append hprefix tailTrace_663991
  have hstable : (prefixWord ++ tailWord_663991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_663991).length < 2 ^ (prefixWord ++ tailWord_663991).sum := by decide
  have hdescent : baseEnd_663991 < baseStart_663991 := by decide
  rcases family_descends (prefixWord ++ tailWord_663991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664035 : List Nat := [1, 1, 1, 6, 4, 1, 1, 1, 3, 4]
def baseStart_664035 : Nat := 118140960795 + 664035 * 2 ^ 59
def prefixEnd_664035 : Nat := 4983230072969 + 3 ^ 40 * 664035 * 2
def baseEnd_664035 : Nat := 113656375469471564569555

theorem tailTrace_664035 : CollatzResearch.WordTrace tailWord_664035 prefixEnd_664035 113656375469471564569555 := by
  unfold tailWord_664035
  simp only [CollatzResearch.WordTrace]
  refine ⟨24219346149322077994225559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16146230766214718662817039 24219346149322077994225559)
  ·
    refine ⟨36329019223983116991338339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24219346149322077994225559 36329019223983116991338339)
    ·
      refine ⟨54493528835974675487007509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36329019223983116991338339 54493528835974675487007509)
      ·
        refine ⟨2554384164186312913453477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 54493528835974675487007509 2554384164186312913453477)
        ·
          refine ⟨478947030784933671272527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2554384164186312913453477 478947030784933671272527)
          ·
            refine ⟨718420546177400506908791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 478947030784933671272527 718420546177400506908791)
            ·
              refine ⟨1077630819266100760363187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 718420546177400506908791 1077630819266100760363187)
              ·
                refine ⟨1616446228899151140544781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1077630819266100760363187 1616446228899151140544781)
                ·
                  refine ⟨606167335837181677704293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1616446228899151140544781 606167335837181677704293)
                  ·
                    refine ⟨113656375469471564569555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 606167335837181677704293 113656375469471564569555)
                    ·
                      rfl

theorem cell23_664035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 3, 4].length) (baseStart_664035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_664035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_664035 prefixEnd_664035 := by exact prefixLift 664035
  have htrace : WordTrace (prefixWord ++ tailWord_664035) baseStart_664035 baseEnd_664035 := by
    simpa [prefixWord, tailWord_664035, baseEnd_664035] using wordTrace_append hprefix tailTrace_664035
  have hstable : (prefixWord ++ tailWord_664035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664035).length < 2 ^ (prefixWord ++ tailWord_664035).sum := by decide
  have hdescent : baseEnd_664035 < baseStart_664035 := by decide
  rcases family_descends (prefixWord ++ tailWord_664035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664041 : List Nat := [1, 2, 1, 1, 1, 2, 1, 7, 3, 1, 3]
def baseStart_664041 : Nat := 118140960795 + 664041 * 2 ^ 59
def prefixEnd_664041 : Nat := 4983230072969 + 3 ^ 40 * 664041 * 2
def baseEnd_664041 : Nat := 340972207292341670233637

theorem tailTrace_664041 : CollatzResearch.WordTrace tailWord_664041 prefixEnd_664041 340972207292341670233637 := by
  unfold tailWord_664041
  simp only [CollatzResearch.WordTrace]
  refine ⟨24219564987300341018943977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16146376658200227345962651 24219564987300341018943977)
  ·
    refine ⟨18164673740475255764207983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24219564987300341018943977 18164673740475255764207983)
    ·
      refine ⟨27247010610712883646311975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18164673740475255764207983 27247010610712883646311975)
      ·
        refine ⟨40870515916069325469467963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27247010610712883646311975 40870515916069325469467963)
        ·
          refine ⟨61305773874103988204201945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40870515916069325469467963 61305773874103988204201945)
          ·
            refine ⟨45979330405577991153151459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61305773874103988204201945 45979330405577991153151459)
            ·
              refine ⟨68968995608366986729727189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45979330405577991153151459 68968995608366986729727189)
              ·
                refine ⟨1616460834571101251477981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 68968995608366986729727189 1616460834571101251477981)
                ·
                  refine ⟨606172812964162969304243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1616460834571101251477981 606172812964162969304243)
                  ·
                    refine ⟨909259219446244453956365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 606172812964162969304243 909259219446244453956365)
                    ·
                      refine ⟨340972207292341670233637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 909259219446244453956365 340972207292341670233637)
                      ·
                        rfl

theorem cell23_664041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 3, 1, 3].length) (baseStart_664041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_664041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_664041 prefixEnd_664041 := by exact prefixLift 664041
  have htrace : WordTrace (prefixWord ++ tailWord_664041) baseStart_664041 baseEnd_664041 := by
    simpa [prefixWord, tailWord_664041, baseEnd_664041] using wordTrace_append hprefix tailTrace_664041
  have hstable : (prefixWord ++ tailWord_664041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664041).length < 2 ^ (prefixWord ++ tailWord_664041).sum := by decide
  have hdescent : baseEnd_664041 < baseStart_664041 := by decide
  rcases family_descends (prefixWord ++ tailWord_664041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664044 : List Nat := [2, 2, 1, 1, 2, 1, 4, 2, 3, 5]
def baseStart_664044 : Nat := 118140960795 + 664044 * 2 ^ 59
def prefixEnd_664044 : Nat := 4983230072969 + 3 ^ 40 * 664044 * 2
def baseEnd_664044 : Nat := 113657915911435052832041

theorem tailTrace_664044 : CollatzResearch.WordTrace tailWord_664044 prefixEnd_664044 113657915911435052832041 := by
  unfold tailWord_664044
  simp only [CollatzResearch.WordTrace]
  refine ⟨12109837203144736265651593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16146449604192981687535457 12109837203144736265651593)
  ·
    refine ⟨9082377902358552199238695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12109837203144736265651593 9082377902358552199238695)
    ·
      refine ⟨13623566853537828298858043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9082377902358552199238695 13623566853537828298858043)
      ·
        refine ⟨20435350280306742448287065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13623566853537828298858043 20435350280306742448287065)
        ·
          refine ⟨15326512710230056836215299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20435350280306742448287065 15326512710230056836215299)
          ·
            refine ⟨22989769065345085254322949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15326512710230056836215299 22989769065345085254322949)
            ·
              refine ⟨4310581699752203485185553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22989769065345085254322949 4310581699752203485185553)
              ·
                refine ⟨3232936274814152613889165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4310581699752203485185553 3232936274814152613889165)
                ·
                  refine ⟨1212351103055307230208437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3232936274814152613889165 1212351103055307230208437)
                  ·
                    refine ⟨113657915911435052832041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1212351103055307230208437 113657915911435052832041)
                    ·
                      rfl

theorem cell23_664044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 5].length) (baseStart_664044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_664044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_664044 prefixEnd_664044 := by exact prefixLift 664044
  have htrace : WordTrace (prefixWord ++ tailWord_664044) baseStart_664044 baseEnd_664044 := by
    simpa [prefixWord, tailWord_664044, baseEnd_664044] using wordTrace_append hprefix tailTrace_664044
  have hstable : (prefixWord ++ tailWord_664044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664044).length < 2 ^ (prefixWord ++ tailWord_664044).sum := by decide
  have hdescent : baseEnd_664044 < baseStart_664044 := by decide
  rcases family_descends (prefixWord ++ tailWord_664044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664051 : List Nat := [1, 1, 1, 2, 2, 2, 3, 2, 4, 3, 2]
def baseStart_664051 : Nat := 118140960795 + 664051 * 2 ^ 59
def prefixEnd_664051 : Nat := 4983230072969 + 3 ^ 40 * 664051 * 2
def baseEnd_664051 : Nat := 340977342098886631108591

theorem tailTrace_664051 : CollatzResearch.WordTrace tailWord_664051 prefixEnd_664051 340977342098886631108591 := by
  unfold tailWord_664051
  simp only [CollatzResearch.WordTrace]
  refine ⟨24219929717264112726808007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16146619811509408484538671 24219929717264112726808007)
  ·
    refine ⟨36329894575896169090212011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24219929717264112726808007 36329894575896169090212011)
    ·
      refine ⟨54494841863844253635318017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36329894575896169090212011 54494841863844253635318017)
      ·
        refine ⟨40871131397883190226488513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54494841863844253635318017 40871131397883190226488513)
        ·
          refine ⟨30653348548412392669866385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40871131397883190226488513 30653348548412392669866385)
          ·
            refine ⟨22990011411309294502399789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30653348548412392669866385 22990011411309294502399789)
            ·
              refine ⟨8621254279240985438399921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22990011411309294502399789 8621254279240985438399921)
              ·
                refine ⟨6465940709430739078799941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8621254279240985438399921 6465940709430739078799941)
                ·
                  refine ⟨1212363883018263577274989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6465940709430739078799941 1212363883018263577274989)
                  ·
                    refine ⟨454636456131848841478121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1212363883018263577274989 454636456131848841478121)
                    ·
                      refine ⟨340977342098886631108591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 454636456131848841478121 340977342098886631108591)
                      ·
                        rfl

theorem cell23_664051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 4, 3, 2].length) (baseStart_664051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_664051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_664051 prefixEnd_664051 := by exact prefixLift 664051
  have htrace : WordTrace (prefixWord ++ tailWord_664051) baseStart_664051 baseEnd_664051 := by
    simpa [prefixWord, tailWord_664051, baseEnd_664051] using wordTrace_append hprefix tailTrace_664051
  have hstable : (prefixWord ++ tailWord_664051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664051).length < 2 ^ (prefixWord ++ tailWord_664051).sum := by decide
  have hdescent : baseEnd_664051 < baseStart_664051 := by decide
  rcases family_descends (prefixWord ++ tailWord_664051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664092 : List Nat := [2, 2, 3, 1, 2, 2, 4, 2, 1, 1, 3]
def baseStart_664092 : Nat := 118140960795 + 664092 * 2 ^ 59
def prefixEnd_664092 : Nat := 4983230072969 + 3 ^ 40 * 664092 * 2
def baseEnd_664092 : Nat := 340998394805720970695903

theorem tailTrace_664092 : CollatzResearch.WordTrace tailWord_664092 prefixEnd_664092 340998394805720970695903 := by
  unfold tailWord_664092
  simp only [CollatzResearch.WordTrace]
  refine ⟨12110712555057788364525265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16147616740077051152700353 12110712555057788364525265)
  ·
    refine ⟨9083034416293341273393949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12110712555057788364525265 9083034416293341273393949)
    ·
      refine ⟨3406137906110002977522731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9083034416293341273393949 3406137906110002977522731)
      ·
        refine ⟨5109206859165004466284097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3406137906110002977522731 5109206859165004466284097)
        ·
          refine ⟨3831905144373753349713073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5109206859165004466284097 3831905144373753349713073)
          ·
            refine ⟨2873928858280315012284805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3831905144373753349713073 2873928858280315012284805)
            ·
              refine ⟨538861660927559064803401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2873928858280315012284805 538861660927559064803401)
              ·
                refine ⟨404146245695669298602551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 538861660927559064803401 404146245695669298602551)
                ·
                  refine ⟨606219368543503947903827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 404146245695669298602551 606219368543503947903827)
                  ·
                    refine ⟨909329052815255921855741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 606219368543503947903827 909329052815255921855741)
                    ·
                      refine ⟨340998394805720970695903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 909329052815255921855741 340998394805720970695903)
                      ·
                        rfl

theorem cell23_664092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 2, 1, 1, 3].length) (baseStart_664092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_664092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_664092 prefixEnd_664092 := by exact prefixLift 664092
  have htrace : WordTrace (prefixWord ++ tailWord_664092) baseStart_664092 baseEnd_664092 := by
    simpa [prefixWord, tailWord_664092, baseEnd_664092] using wordTrace_append hprefix tailTrace_664092
  have hstable : (prefixWord ++ tailWord_664092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664092).length < 2 ^ (prefixWord ++ tailWord_664092).sum := by decide
  have hdescent : baseEnd_664092 < baseStart_664092 := by decide
  rcases family_descends (prefixWord ++ tailWord_664092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664101 : List Nat := [1, 3, 1, 2, 2, 1, 3, 2, 3, 2, 3]
def baseStart_664101 : Nat := 118140960795 + 664101 * 2 ^ 59
def prefixEnd_664101 : Nat := 4983230072969 + 3 ^ 40 * 664101 * 2
def baseEnd_664101 : Nat := 341003016131611435483361

theorem tailTrace_664101 : CollatzResearch.WordTrace tailWord_664101 prefixEnd_664101 341003016131611435483361 := by
  unfold tailWord_664101
  simp only [CollatzResearch.WordTrace]
  refine ⟨24221753367082971266128157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16147835578055314177418771 24221753367082971266128157)
  ·
    refine ⟨9083157512656114224798059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24221753367082971266128157 9083157512656114224798059)
    ·
      refine ⟨13624736268984171337197089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9083157512656114224798059 13624736268984171337197089)
      ·
        refine ⟨10218552201738128502897817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13624736268984171337197089 10218552201738128502897817)
        ·
          refine ⟨7663914151303596377173363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10218552201738128502897817 7663914151303596377173363)
          ·
            refine ⟨11495871226955394565760045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7663914151303596377173363 11495871226955394565760045)
            ·
              refine ⟨4310951710108272962160017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11495871226955394565760045 4310951710108272962160017)
              ·
                refine ⟨3233213782581204721620013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4310951710108272962160017 3233213782581204721620013)
                ·
                  refine ⟨1212455168467951770607505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3233213782581204721620013 1212455168467951770607505)
                  ·
                    refine ⟨909341376350963827955629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1212455168467951770607505 909341376350963827955629)
                    ·
                      refine ⟨341003016131611435483361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 909341376350963827955629 341003016131611435483361)
                      ·
                        rfl

theorem cell23_664101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 3, 2, 3].length) (baseStart_664101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_664101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_664101 prefixEnd_664101 := by exact prefixLift 664101
  have htrace : WordTrace (prefixWord ++ tailWord_664101) baseStart_664101 baseEnd_664101 := by
    simpa [prefixWord, tailWord_664101, baseEnd_664101] using wordTrace_append hprefix tailTrace_664101
  have hstable : (prefixWord ++ tailWord_664101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664101).length < 2 ^ (prefixWord ++ tailWord_664101).sum := by decide
  have hdescent : baseEnd_664101 < baseStart_664101 := by decide
  rcases family_descends (prefixWord ++ tailWord_664101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664109 : List Nat := [1, 5, 4, 1, 1, 1, 1, 2, 3, 1, 3]
def baseStart_664109 : Nat := 118140960795 + 664109 * 2 ^ 59
def prefixEnd_664109 : Nat := 4983230072969 + 3 ^ 40 * 664109 * 2
def baseEnd_664109 : Nat := 341007123976847404183325

theorem tailTrace_664109 : CollatzResearch.WordTrace tailWord_664109 prefixEnd_664109 341007123976847404183325 := by
  unfold tailWord_664109
  simp only [CollatzResearch.WordTrace]
  refine ⟨24222045151053988632419381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16148030100702659088279587 24222045151053988632419381)
  ·
    refine ⟨2270816732911311434289317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24222045151053988632419381 2270816732911311434289317)
    ·
      refine ⟨425778137420870893929247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2270816732911311434289317 425778137420870893929247)
      ·
        refine ⟨638667206131306340893871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 425778137420870893929247 638667206131306340893871)
        ·
          refine ⟨958000809196959511340807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 638667206131306340893871 958000809196959511340807)
          ·
            refine ⟨1437001213795439267011211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 958000809196959511340807 1437001213795439267011211)
            ·
              refine ⟨2155501820693158900516817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1437001213795439267011211 2155501820693158900516817)
              ·
                refine ⟨1616626365519869175387613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2155501820693158900516817 1616626365519869175387613)
                ·
                  refine ⟨606234887069950940770355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1616626365519869175387613 606234887069950940770355)
                  ·
                    refine ⟨909352330604926411155533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 606234887069950940770355 909352330604926411155533)
                    ·
                      refine ⟨341007123976847404183325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 909352330604926411155533 341007123976847404183325)
                      ·
                        rfl

theorem cell23_664109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_664109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_664109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_664109 prefixEnd_664109 := by exact prefixLift 664109
  have htrace : WordTrace (prefixWord ++ tailWord_664109) baseStart_664109 baseEnd_664109 := by
    simpa [prefixWord, tailWord_664109, baseEnd_664109] using wordTrace_append hprefix tailTrace_664109
  have hstable : (prefixWord ++ tailWord_664109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664109).length < 2 ^ (prefixWord ++ tailWord_664109).sum := by decide
  have hdescent : baseEnd_664109 < baseStart_664109 := by decide
  rcases family_descends (prefixWord ++ tailWord_664109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664121 : List Nat := [1, 2, 1, 5, 1, 1, 5, 7]
def baseStart_664121 : Nat := 118140960795 + 664121 * 2 ^ 59
def prefixEnd_664121 : Nat := 4983230072969 + 3 ^ 40 * 664121 * 2
def baseEnd_664121 : Nat := 12630121694248198416047

theorem tailTrace_664121 : CollatzResearch.WordTrace tailWord_664121 prefixEnd_664121 12630121694248198416047 := by
  unfold tailWord_664121
  simp only [CollatzResearch.WordTrace]
  refine ⟨24222482827010514681856217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16148321884673676454570811 24222482827010514681856217)
  ·
    refine ⟨18166862120257886011392163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24222482827010514681856217 18166862120257886011392163)
    ·
      refine ⟨27250293180386829017088245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18166862120257886011392163 27250293180386829017088245)
      ·
        refine ⟨2554714985661265220352023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27250293180386829017088245 2554714985661265220352023)
        ·
          refine ⟨3832072478491897830528035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2554714985661265220352023 3832072478491897830528035)
          ·
            refine ⟨5748108717737846745792053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3832072478491897830528035 5748108717737846745792053)
            ·
              refine ⟨538885192287923132418005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5748108717737846745792053 538885192287923132418005)
              ·
                refine ⟨12630121694248198416047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 538885192287923132418005 12630121694248198416047)
                ·
                  rfl

theorem cell23_664121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 7].length) (baseStart_664121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_664121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_664121 prefixEnd_664121 := by exact prefixLift 664121
  have htrace : WordTrace (prefixWord ++ tailWord_664121) baseStart_664121 baseEnd_664121 := by
    simpa [prefixWord, tailWord_664121, baseEnd_664121] using wordTrace_append hprefix tailTrace_664121
  have hstable : (prefixWord ++ tailWord_664121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664121).length < 2 ^ (prefixWord ++ tailWord_664121).sum := by decide
  have hdescent : baseEnd_664121 < baseStart_664121 := by decide
  rcases family_descends (prefixWord ++ tailWord_664121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664135 : List Nat := [1, 1, 4, 1, 4, 1, 4, 1, 1, 2, 3]
def baseStart_664135 : Nat := 118140960795 + 664135 * 2 ^ 59
def prefixEnd_664135 : Nat := 4983230072969 + 3 ^ 40 * 664135 * 2
def baseEnd_664135 : Nat := 341020474473864302458205

theorem tailTrace_664135 : CollatzResearch.WordTrace tailWord_664135 prefixEnd_664135 341020474473864302458205 := by
  unfold tailWord_664135
  simp only [CollatzResearch.WordTrace]
  refine ⟨24222993448959795072865859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16148662299306530048577239 24222993448959795072865859)
  ·
    refine ⟨36334490173439692609298789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24222993448959795072865859 36334490173439692609298789)
    ·
      refine ⟨6812716907519942364243523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36334490173439692609298789 6812716907519942364243523)
      ·
        refine ⟨10219075361279913546365285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6812716907519942364243523 10219075361279913546365285)
        ·
          refine ⟨1916076630239983789943491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10219075361279913546365285 1916076630239983789943491)
          ·
            refine ⟨2874114945359975684915237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1916076630239983789943491 2874114945359975684915237)
            ·
              refine ⟨538896552254995440921607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2874114945359975684915237 538896552254995440921607)
              ·
                refine ⟨808344828382493161382411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 538896552254995440921607 808344828382493161382411)
                ·
                  refine ⟨1212517242573739742073617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 808344828382493161382411 1212517242573739742073617)
                  ·
                    refine ⟨909387931930304806555213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1212517242573739742073617 909387931930304806555213)
                    ·
                      refine ⟨341020474473864302458205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 909387931930304806555213 341020474473864302458205)
                      ·
                        rfl

theorem cell23_664135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 1, 1, 2, 3].length) (baseStart_664135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_664135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_664135 prefixEnd_664135 := by exact prefixLift 664135
  have htrace : WordTrace (prefixWord ++ tailWord_664135) baseStart_664135 baseEnd_664135 := by
    simpa [prefixWord, tailWord_664135, baseEnd_664135] using wordTrace_append hprefix tailTrace_664135
  have hstable : (prefixWord ++ tailWord_664135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664135).length < 2 ^ (prefixWord ++ tailWord_664135).sum := by decide
  have hdescent : baseEnd_664135 < baseStart_664135 := by decide
  rcases family_descends (prefixWord ++ tailWord_664135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664144 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 5]
def baseStart_664144 : Nat := 118140960795 + 664144 * 2 ^ 59
def prefixEnd_664144 : Nat := 4983230072969 + 3 ^ 40 * 664144 * 2
def baseEnd_664144 : Nat := 341025095799754767245663

theorem tailTrace_664144 : CollatzResearch.WordTrace tailWord_664144 prefixEnd_664144 341025095799754767245663 := by
  unfold tailWord_664144
  simp only [CollatzResearch.WordTrace]
  refine ⟨12111660852963594804971743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16148881137284793073295657 12111660852963594804971743)
  ·
    refine ⟨18167491279445392207457615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12111660852963594804971743 18167491279445392207457615)
    ·
      refine ⟨27251236919168088311186423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18167491279445392207457615 27251236919168088311186423)
      ·
        refine ⟨40876855378752132466779635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27251236919168088311186423 40876855378752132466779635)
        ·
          refine ⟨61315283068128198700169453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40876855378752132466779635 61315283068128198700169453)
          ·
            refine ⟨22993231150548074512563545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61315283068128198700169453 22993231150548074512563545)
            ·
              refine ⟨17244923362911055884422659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22993231150548074512563545 17244923362911055884422659)
              ·
                refine ⟨25867385044366583826633989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17244923362911055884422659 25867385044366583826633989)
                ·
                  refine ⟨4850134695818734467493873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25867385044366583826633989 4850134695818734467493873)
                  ·
                    refine ⟨3637601021864050850620405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4850134695818734467493873 3637601021864050850620405)
                    ·
                      refine ⟨341025095799754767245663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3637601021864050850620405 341025095799754767245663)
                      ·
                        rfl

theorem cell23_664144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 5].length) (baseStart_664144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_664144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_664144 prefixEnd_664144 := by exact prefixLift 664144
  have htrace : WordTrace (prefixWord ++ tailWord_664144) baseStart_664144 baseEnd_664144 := by
    simpa [prefixWord, tailWord_664144, baseEnd_664144] using wordTrace_append hprefix tailTrace_664144
  have hstable : (prefixWord ++ tailWord_664144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664144).length < 2 ^ (prefixWord ++ tailWord_664144).sum := by decide
  have hdescent : baseEnd_664144 < baseStart_664144 := by decide
  rcases family_descends (prefixWord ++ tailWord_664144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664162 : List Nat := [3, 3, 2, 3, 1, 2, 1, 1, 1, 2, 4]
def baseStart_664162 : Nat := 118140960795 + 664162 * 2 ^ 59
def prefixEnd_664162 : Nat := 4983230072969 + 3 ^ 40 * 664162 * 2
def baseEnd_664162 : Nat := 341034338451535696820581

theorem tailTrace_664162 : CollatzResearch.WordTrace tailWord_664162 prefixEnd_664162 341034338451535696820581 := by
  unfold tailWord_664162
  simp only [CollatzResearch.WordTrace]
  refine ⟨6055994554965494671024685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16149318813241319122732493 6055994554965494671024685)
  ·
    refine ⟨2270997958112060501634257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6055994554965494671024685 2270997958112060501634257)
    ·
      refine ⟨1703248468584045376225693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2270997958112060501634257 1703248468584045376225693)
      ·
        refine ⟨638718175719017016084635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1703248468584045376225693 638718175719017016084635)
        ·
          refine ⟨958077263578525524126953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 638718175719017016084635 958077263578525524126953)
          ·
            refine ⟨718557947683894143095215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 958077263578525524126953 718557947683894143095215)
            ·
              refine ⟨1077836921525841214642823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 718557947683894143095215 1077836921525841214642823)
              ·
                refine ⟨1616755382288761821964235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1077836921525841214642823 1616755382288761821964235)
                ·
                  refine ⟨2425133073433142732946353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1616755382288761821964235 2425133073433142732946353)
                  ·
                    refine ⟨1818849805074857049709765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2425133073433142732946353 1818849805074857049709765)
                    ·
                      refine ⟨341034338451535696820581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1818849805074857049709765 341034338451535696820581)
                      ·
                        rfl

theorem cell23_664162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_664162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_664162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_664162 prefixEnd_664162 := by exact prefixLift 664162
  have htrace : WordTrace (prefixWord ++ tailWord_664162) baseStart_664162 baseEnd_664162 := by
    simpa [prefixWord, tailWord_664162, baseEnd_664162] using wordTrace_append hprefix tailTrace_664162
  have hstable : (prefixWord ++ tailWord_664162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664162).length < 2 ^ (prefixWord ++ tailWord_664162).sum := by decide
  have hdescent : baseEnd_664162 < baseStart_664162 := by decide
  rcases family_descends (prefixWord ++ tailWord_664162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664165 : List Nat := [1, 3, 1, 3, 4, 2, 1, 1, 1, 3, 3]
def baseStart_664165 : Nat := 118140960795 + 664165 * 2 ^ 59
def prefixEnd_664165 : Nat := 4983230072969 + 3 ^ 40 * 664165 * 2
def baseEnd_664165 : Nat := 341035878893499185083067

theorem tailTrace_664165 : CollatzResearch.WordTrace tailWord_664165 prefixEnd_664165 341035878893499185083067 := by
  unfold tailWord_664165
  simp only [CollatzResearch.WordTrace]
  refine ⟨24224087638851110196457949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16149391759234073464305299 24224087638851110196457949)
  ·
    refine ⟨9084032864569166323671731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24224087638851110196457949 9084032864569166323671731)
    ·
      refine ⟨13626049296853749485507597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9084032864569166323671731 13626049296853749485507597)
      ·
        refine ⟨5109768486320156057065349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13626049296853749485507597 5109768486320156057065349)
        ·
          refine ⟨958081591185029260699753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5109768486320156057065349 958081591185029260699753)
          ·
            refine ⟨718561193388771945524815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 958081591185029260699753 718561193388771945524815)
            ·
              refine ⟨1077841790083157918287223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 718561193388771945524815 1077841790083157918287223)
              ·
                refine ⟨1616762685124736877430835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1077841790083157918287223 1616762685124736877430835)
                ·
                  refine ⟨2425144027687105316146253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1616762685124736877430835 2425144027687105316146253)
                  ·
                    refine ⟨909429010382664493554845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2425144027687105316146253 909429010382664493554845)
                    ·
                      refine ⟨341035878893499185083067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 909429010382664493554845 341035878893499185083067)
                      ·
                        rfl

theorem cell23_664165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_664165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_664165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_664165 prefixEnd_664165 := by exact prefixLift 664165
  have htrace : WordTrace (prefixWord ++ tailWord_664165) baseStart_664165 baseEnd_664165 := by
    simpa [prefixWord, tailWord_664165, baseEnd_664165] using wordTrace_append hprefix tailTrace_664165
  have hstable : (prefixWord ++ tailWord_664165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664165).length < 2 ^ (prefixWord ++ tailWord_664165).sum := by decide
  have hdescent : baseEnd_664165 < baseStart_664165 := by decide
  rcases family_descends (prefixWord ++ tailWord_664165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664188 : List Nat := [2, 2, 2, 1, 1, 2, 2, 4, 1, 4, 2]
def baseStart_664188 : Nat := 118140960795 + 664188 * 2 ^ 59
def prefixEnd_664188 : Nat := 4983230072969 + 3 ^ 40 * 664188 * 2
def baseEnd_664188 : Nat := 341047688948552595095461

theorem tailTrace_664188 : CollatzResearch.WordTrace tailWord_664188 prefixEnd_664188 341047688948552595095461 := by
  unfold tailWord_664188
  simp only [CollatzResearch.WordTrace]
  refine ⟨12112463258883892562272609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16149951011845190083030145 12112463258883892562272609)
  ·
    refine ⟨9084347444162919421704457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12112463258883892562272609 9084347444162919421704457)
    ·
      refine ⟨6813260583122189566278343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9084347444162919421704457 6813260583122189566278343)
      ·
        refine ⟨10219890874683284349417515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6813260583122189566278343 10219890874683284349417515)
        ·
          refine ⟨15329836312024926524126273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10219890874683284349417515 15329836312024926524126273)
          ·
            refine ⟨11497377234018694893094705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15329836312024926524126273 11497377234018694893094705)
            ·
              refine ⟨8623032925514021169821029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11497377234018694893094705 8623032925514021169821029)
              ·
                refine ⟨1616818673533878969341443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8623032925514021169821029 1616818673533878969341443)
                ·
                  refine ⟨2425228010300818454012165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1616818673533878969341443 2425228010300818454012165)
                  ·
                    refine ⟨454730251931403460127281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2425228010300818454012165 454730251931403460127281)
                    ·
                      refine ⟨341047688948552595095461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 454730251931403460127281 341047688948552595095461)
                      ·
                        rfl

theorem cell23_664188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 1, 4, 2].length) (baseStart_664188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_664188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_664188 prefixEnd_664188 := by exact prefixLift 664188
  have htrace : WordTrace (prefixWord ++ tailWord_664188) baseStart_664188 baseEnd_664188 := by
    simpa [prefixWord, tailWord_664188, baseEnd_664188] using wordTrace_append hprefix tailTrace_664188
  have hstable : (prefixWord ++ tailWord_664188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664188).length < 2 ^ (prefixWord ++ tailWord_664188).sum := by decide
  have hdescent : baseEnd_664188 < baseStart_664188 := by decide
  rcases family_descends (prefixWord ++ tailWord_664188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664268 : List Nat := [2, 2, 1, 5, 1, 1, 2, 1, 1, 2, 5]
def baseStart_664268 : Nat := 118140960795 + 664268 * 2 ^ 59
def prefixEnd_664268 : Nat := 4983230072969 + 3 ^ 40 * 664268 * 2
def baseEnd_664268 : Nat := 341088767400912282095093

theorem tailTrace_664268 : CollatzResearch.WordTrace tailWord_664268 prefixEnd_664268 341088767400912282095093 := by
  unfold tailWord_664268
  simp only [CollatzResearch.WordTrace]
  refine ⟨12113922178738979393728729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16151896238318639191638305 12113922178738979393728729)
  ·
    refine ⟨9085441634054234545296547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12113922178738979393728729 9085441634054234545296547)
    ·
      refine ⟨13628162451081351817944821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9085441634054234545296547 13628162451081351817944821)
      ·
        refine ⟨1277640229788876732932327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13628162451081351817944821 1277640229788876732932327)
        ·
          refine ⟨1916460344683315099398491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1277640229788876732932327 1916460344683315099398491)
          ·
            refine ⟨2874690517024972649097737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1916460344683315099398491 2874690517024972649097737)
            ·
              refine ⟨2156017887768729486823303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2874690517024972649097737 2156017887768729486823303)
              ·
                refine ⟨3234026831653094230234955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2156017887768729486823303 3234026831653094230234955)
                ·
                  refine ⟨4851040247479641345352433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3234026831653094230234955 4851040247479641345352433)
                  ·
                    refine ⟨3638280185609731009014325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4851040247479641345352433 3638280185609731009014325)
                    ·
                      refine ⟨341088767400912282095093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3638280185609731009014325 341088767400912282095093)
                      ·
                        rfl

theorem cell23_664268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_664268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_664268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_664268 prefixEnd_664268 := by exact prefixLift 664268
  have htrace : WordTrace (prefixWord ++ tailWord_664268) baseStart_664268 baseEnd_664268 := by
    simpa [prefixWord, tailWord_664268, baseEnd_664268] using wordTrace_append hprefix tailTrace_664268
  have hstable : (prefixWord ++ tailWord_664268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664268).length < 2 ^ (prefixWord ++ tailWord_664268).sum := by decide
  have hdescent : baseEnd_664268 < baseStart_664268 := by decide
  rcases family_descends (prefixWord ++ tailWord_664268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664322 : List Nat := [3, 4, 1, 1, 1, 3, 2, 1, 3, 4]
def baseStart_664322 : Nat := 118140960795 + 664322 * 2 ^ 59
def prefixEnd_664322 : Nat := 4983230072969 + 3 ^ 40 * 664322 * 2
def baseEnd_664322 : Nat := 113705498452085023606615

theorem tailTrace_664322 : CollatzResearch.WordTrace tailWord_664322 prefixEnd_664322 113705498452085023606615 := by
  unfold tailWord_664322
  simp only [CollatzResearch.WordTrace]
  refine ⟨6057453474820581502480805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16153209266188217339948813 6057453474820581502480805)
  ·
    refine ⟨1135772526528859031715151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6057453474820581502480805 1135772526528859031715151)
    ·
      refine ⟨1703658789793288547572727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1135772526528859031715151 1703658789793288547572727)
      ·
        refine ⟨2555488184689932821359091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1703658789793288547572727 2555488184689932821359091)
        ·
          refine ⟨3833232277034899232038637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2555488184689932821359091 3833232277034899232038637)
          ·
            refine ⟨1437462103888087212014489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3833232277034899232038637 1437462103888087212014489)
            ·
              refine ⟨1078096577916065409010867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1437462103888087212014489 1078096577916065409010867)
              ·
                refine ⟨1617144866874098113516301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1078096577916065409010867 1617144866874098113516301)
                ·
                  refine ⟨606429325077786792568613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1617144866874098113516301 606429325077786792568613)
                  ·
                    refine ⟨113705498452085023606615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 606429325077786792568613 113705498452085023606615)
                    ·
                      rfl

theorem cell23_664322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_664322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_664322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_664322 prefixEnd_664322 := by exact prefixLift 664322
  have htrace : WordTrace (prefixWord ++ tailWord_664322) baseStart_664322 baseEnd_664322 := by
    simpa [prefixWord, tailWord_664322, baseEnd_664322] using wordTrace_append hprefix tailTrace_664322
  have hstable : (prefixWord ++ tailWord_664322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664322).length < 2 ^ (prefixWord ++ tailWord_664322).sum := by decide
  have hdescent : baseEnd_664322 < baseStart_664322 := by decide
  rcases family_descends (prefixWord ++ tailWord_664322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664355 : List Nat := [1, 1, 1, 4, 2, 1, 1, 5, 2, 3, 2]
def baseStart_664355 : Nat := 118140960795 + 664355 * 2 ^ 59
def prefixEnd_664355 : Nat := 4983230072969 + 3 ^ 40 * 664355 * 2
def baseEnd_664355 : Nat := 341133440217853441707193

theorem tailTrace_664355 : CollatzResearch.WordTrace tailWord_664355 prefixEnd_664355 341133440217853441707193 := by
  unfold tailWord_664355
  simp only [CollatzResearch.WordTrace]
  refine ⟨24231017508162772645874519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16154011672108515097249679 24231017508162772645874519)
  ·
    refine ⟨36346526262244158968811779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24231017508162772645874519 36346526262244158968811779)
    ·
      refine ⟨54519789393366238453217669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36346526262244158968811779 54519789393366238453217669)
      ·
        refine ⟨10222460511256169709978313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54519789393366238453217669 10222460511256169709978313)
        ·
          refine ⟨7666845383442127282483735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10222460511256169709978313 7666845383442127282483735)
          ·
            refine ⟨11500268075163190923725603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7666845383442127282483735 11500268075163190923725603)
            ·
              refine ⟨17250402112744786385588405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11500268075163190923725603 17250402112744786385588405)
              ·
                refine ⟨1617225198069823723648913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17250402112744786385588405 1617225198069823723648913)
                ·
                  refine ⟨1212918898552367792736685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1617225198069823723648913 1212918898552367792736685)
                  ·
                    refine ⟨454844586957137922276257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1212918898552367792736685 454844586957137922276257)
                    ·
                      refine ⟨341133440217853441707193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 454844586957137922276257 341133440217853441707193)
                      ·
                        rfl

theorem cell23_664355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 2, 3, 2].length) (baseStart_664355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_664355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_664355 prefixEnd_664355 := by exact prefixLift 664355
  have htrace : WordTrace (prefixWord ++ tailWord_664355) baseStart_664355 baseEnd_664355 := by
    simpa [prefixWord, tailWord_664355, baseEnd_664355] using wordTrace_append hprefix tailTrace_664355
  have hstable : (prefixWord ++ tailWord_664355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664355).length < 2 ^ (prefixWord ++ tailWord_664355).sum := by decide
  have hdescent : baseEnd_664355 < baseStart_664355 := by decide
  rcases family_descends (prefixWord ++ tailWord_664355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664356 : List Nat := [2, 3, 1, 3, 4, 1, 1, 3, 1, 4]
def baseStart_664356 : Nat := 118140960795 + 664356 * 2 ^ 59
def prefixEnd_664356 : Nat := 4983230072969 + 3 ^ 40 * 664356 * 2
def baseEnd_664356 : Nat := 113711317899502645931563

theorem tailTrace_664356 : CollatzResearch.WordTrace tailWord_664356 prefixEnd_664356 113711317899502645931563 := by
  unfold tailWord_664356
  simp only [CollatzResearch.WordTrace]
  refine ⟨12115526990579574908330461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16154035987439433211107281 12115526990579574908330461)
  ·
    refine ⟨4543322621467340590623923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12115526990579574908330461 4543322621467340590623923)
    ·
      refine ⟨6814983932201010885935885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4543322621467340590623923 6814983932201010885935885)
      ·
        refine ⟨2555618974575379082225957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6814983932201010885935885 2555618974575379082225957)
        ·
          refine ⟨479178557732883577917367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2555618974575379082225957 479178557732883577917367)
          ·
            refine ⟨718767836599325366876051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 479178557732883577917367 718767836599325366876051)
            ·
              refine ⟨1078151754898988050314077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 718767836599325366876051 1078151754898988050314077)
              ·
                refine ⟨404306908087120518867779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1078151754898988050314077 404306908087120518867779)
                ·
                  refine ⟨606460362130680778301669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 404306908087120518867779 606460362130680778301669)
                  ·
                    refine ⟨113711317899502645931563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 606460362130680778301669 113711317899502645931563)
                    ·
                      rfl

theorem cell23_664356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 3, 1, 4].length) (baseStart_664356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_664356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_664356 prefixEnd_664356 := by exact prefixLift 664356
  have htrace : WordTrace (prefixWord ++ tailWord_664356) baseStart_664356 baseEnd_664356 := by
    simpa [prefixWord, tailWord_664356, baseEnd_664356] using wordTrace_append hprefix tailTrace_664356
  have hstable : (prefixWord ++ tailWord_664356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664356).length < 2 ^ (prefixWord ++ tailWord_664356).sum := by decide
  have hdescent : baseEnd_664356 < baseStart_664356 := by decide
  rcases family_descends (prefixWord ++ tailWord_664356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664398 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 5, 2, 4]
def baseStart_664398 : Nat := 118140960795 + 664398 * 2 ^ 59
def prefixEnd_664398 : Nat := 4983230072969 + 3 ^ 40 * 664398 * 2
def baseEnd_664398 : Nat := 341155519885996773469495

theorem tailTrace_664398 : CollatzResearch.WordTrace tailWord_664398 prefixEnd_664398 341155519885996773469495 := by
  unfold tailWord_664398
  simp only [CollatzResearch.WordTrace]
  refine ⟨3029073230875873873711231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16155057231337993993126565 3029073230875873873711231)
  ·
    refine ⟨4543609846313810810566847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3029073230875873873711231 4543609846313810810566847)
    ·
      refine ⟨6815414769470716215850271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4543609846313810810566847 6815414769470716215850271)
      ·
        refine ⟨10223122154206074323775407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6815414769470716215850271 10223122154206074323775407)
        ·
          refine ⟨15334683231309111485663111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10223122154206074323775407 15334683231309111485663111)
          ·
            refine ⟨23002024846963667228494667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15334683231309111485663111 23002024846963667228494667)
            ·
              refine ⟨34503037270445500842742001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23002024846963667228494667 34503037270445500842742001)
              ·
                refine ⟨25877277952834125632056501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34503037270445500842742001 25877277952834125632056501)
                ·
                  refine ⟨2425994808078199278005297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25877277952834125632056501 2425994808078199278005297)
                  ·
                    refine ⟨1819496106058649458503973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2425994808078199278005297 1819496106058649458503973)
                    ·
                      refine ⟨341155519885996773469495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1819496106058649458503973 341155519885996773469495)
                      ·
                        rfl

theorem cell23_664398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_664398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_664398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_664398 prefixEnd_664398 := by exact prefixLift 664398
  have htrace : WordTrace (prefixWord ++ tailWord_664398) baseStart_664398 baseEnd_664398 := by
    simpa [prefixWord, tailWord_664398, baseEnd_664398] using wordTrace_append hprefix tailTrace_664398
  have hstable : (prefixWord ++ tailWord_664398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664398).length < 2 ^ (prefixWord ++ tailWord_664398).sum := by decide
  have hdescent : baseEnd_664398 < baseStart_664398 := by decide
  rcases family_descends (prefixWord ++ tailWord_664398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664402 : List Nat := [3, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2]
def baseStart_664402 : Nat := 118140960795 + 664402 * 2 ^ 59
def prefixEnd_664402 : Nat := 4983230072969 + 3 ^ 40 * 664402 * 2
def baseEnd_664402 : Nat := 341157573808614757819477

theorem tailTrace_664402 : CollatzResearch.WordTrace tailWord_664402 prefixEnd_664402 341157573808614757819477 := by
  unfold tailWord_664402
  simp only [CollatzResearch.WordTrace]
  refine ⟨6058182934748124918208865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16155154492661666448556973 6058182934748124918208865)
  ·
    refine ⟨4543637201061093688656649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6058182934748124918208865 4543637201061093688656649)
    ·
      refine ⟨3407727900795820266492487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4543637201061093688656649 3407727900795820266492487)
      ·
        refine ⟨5111591851193730399738731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3407727900795820266492487 5111591851193730399738731)
        ·
          refine ⟨7667387776790595599608097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5111591851193730399738731 7667387776790595599608097)
          ·
            refine ⟨5750540832592946699706073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7667387776790595599608097 5750540832592946699706073)
            ·
              refine ⟨4312905624444710024779555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5750540832592946699706073 4312905624444710024779555)
              ·
                refine ⟨6469358436667065037169333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4312905624444710024779555 6469358436667065037169333)
                ·
                  refine ⟨606502353437537347234625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6469358436667065037169333 606502353437537347234625)
                  ·
                    refine ⟨454876765078153010425969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 606502353437537347234625 454876765078153010425969)
                    ·
                      refine ⟨341157573808614757819477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 454876765078153010425969 341157573808614757819477)
                      ·
                        rfl

theorem cell23_664402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2].length) (baseStart_664402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_664402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_664402 prefixEnd_664402 := by exact prefixLift 664402
  have htrace : WordTrace (prefixWord ++ tailWord_664402) baseStart_664402 baseEnd_664402 := by
    simpa [prefixWord, tailWord_664402, baseEnd_664402] using wordTrace_append hprefix tailTrace_664402
  have hstable : (prefixWord ++ tailWord_664402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664402).length < 2 ^ (prefixWord ++ tailWord_664402).sum := by decide
  have hdescent : baseEnd_664402 < baseStart_664402 := by decide
  rcases family_descends (prefixWord ++ tailWord_664402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664405 : List Nat := [1, 3, 2, 2, 2, 1, 3, 1, 3, 2, 3]
def baseStart_664405 : Nat := 118140960795 + 664405 * 2 ^ 59
def prefixEnd_664405 : Nat := 4983230072969 + 3 ^ 40 * 664405 * 2
def baseEnd_664405 : Nat := 341159114250578246081963

theorem tailTrace_664405 : CollatzResearch.WordTrace tailWord_664405 prefixEnd_664405 341159114250578246081963 := by
  unfold tailWord_664405
  simp only [CollatzResearch.WordTrace]
  refine ⟨24232841157981631185194669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16155227438654420790129779 24232841157981631185194669)
  ·
    refine ⟨9087315434243111694448001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24232841157981631185194669 9087315434243111694448001)
    ·
      refine ⟨6815486575682333770836001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9087315434243111694448001 6815486575682333770836001)
      ·
        refine ⟨5111614931761750328127001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6815486575682333770836001 5111614931761750328127001)
        ·
          refine ⟨3833711198821312746095251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5111614931761750328127001 3833711198821312746095251)
          ·
            refine ⟨5750566798231969119142877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3833711198821312746095251 5750566798231969119142877)
            ·
              refine ⟨2156462549336988419678579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5750566798231969119142877 2156462549336988419678579)
              ·
                refine ⟨3234693824005482629517869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2156462549336988419678579 3234693824005482629517869)
                ·
                  refine ⟨1213010184002055986069201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3234693824005482629517869 1213010184002055986069201)
                  ·
                    refine ⟨909757638001541989551901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1213010184002055986069201 909757638001541989551901)
                    ·
                      refine ⟨341159114250578246081963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 909757638001541989551901 341159114250578246081963)
                      ·
                        rfl

theorem cell23_664405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_664405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_664405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_664405 prefixEnd_664405 := by exact prefixLift 664405
  have htrace : WordTrace (prefixWord ++ tailWord_664405) baseStart_664405 baseEnd_664405 := by
    simpa [prefixWord, tailWord_664405, baseEnd_664405] using wordTrace_append hprefix tailTrace_664405
  have hstable : (prefixWord ++ tailWord_664405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664405).length < 2 ^ (prefixWord ++ tailWord_664405).sum := by decide
  have hdescent : baseEnd_664405 < baseStart_664405 := by decide
  rcases family_descends (prefixWord ++ tailWord_664405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664430 : List Nat := [4, 1, 2, 3, 3, 1, 2, 2, 1, 1, 3]
def baseStart_664430 : Nat := 118140960795 + 664430 * 2 ^ 59
def prefixEnd_664430 : Nat := 4983230072969 + 3 ^ 40 * 664430 * 2
def baseEnd_664430 : Nat := 341171951266940648269349

theorem tailTrace_664430 : CollatzResearch.WordTrace tailWord_664430 prefixEnd_664430 341171951266940648269349 := by
  unfold tailWord_664430
  simp only [CollatzResearch.WordTrace]
  refine ⟨3029219122861382556856843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16155835321927373636569829 3029219122861382556856843)
  ·
    refine ⟨4543828684292073835285265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3029219122861382556856843 4543828684292073835285265)
    ·
      refine ⟨3407871513219055376463949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4543828684292073835285265 3407871513219055376463949)
      ·
        refine ⟨1277951817457145766173981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3407871513219055376463949 1277951817457145766173981)
        ·
          refine ⟨479231931546429662315243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1277951817457145766173981 479231931546429662315243)
          ·
            refine ⟨718847897319644493472865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 479231931546429662315243 718847897319644493472865)
            ·
              refine ⟨539135922989733370104649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 718847897319644493472865 539135922989733370104649)
              ·
                refine ⟨404351942242300027578487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 539135922989733370104649 404351942242300027578487)
                ·
                  refine ⟨606527913363450041367731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 404351942242300027578487 606527913363450041367731)
                  ·
                    refine ⟨909791870045175062051597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 606527913363450041367731 909791870045175062051597)
                    ·
                      refine ⟨341171951266940648269349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 909791870045175062051597 341171951266940648269349)
                      ·
                        rfl

theorem cell23_664430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_664430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_664430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_664430 prefixEnd_664430 := by exact prefixLift 664430
  have htrace : WordTrace (prefixWord ++ tailWord_664430) baseStart_664430 baseEnd_664430 := by
    simpa [prefixWord, tailWord_664430, baseEnd_664430] using wordTrace_append hprefix tailTrace_664430
  have hstable : (prefixWord ++ tailWord_664430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664430).length < 2 ^ (prefixWord ++ tailWord_664430).sum := by decide
  have hdescent : baseEnd_664430 < baseStart_664430 := by decide
  rcases family_descends (prefixWord ++ tailWord_664430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664435 : List Nat := [1, 1, 1, 2, 2, 1, 4, 3, 4, 1, 3]
def baseStart_664435 : Nat := 118140960795 + 664435 * 2 ^ 59
def prefixEnd_664435 : Nat := 4983230072969 + 3 ^ 40 * 664435 * 2
def baseEnd_664435 : Nat := 341174518670213128706825

theorem tailTrace_664435 : CollatzResearch.WordTrace tailWord_664435 prefixEnd_664435 341174518670213128706825 := by
  unfold tailWord_664435
  simp only [CollatzResearch.WordTrace]
  refine ⟨24233935347872946308786759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16155956898581964205857839 24233935347872946308786759)
  ·
    refine ⟨36350903021809419463180139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24233935347872946308786759 36350903021809419463180139)
    ·
      refine ⟨54526354532714129194770209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36350903021809419463180139 54526354532714129194770209)
      ·
        refine ⟨40894765899535596896077657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54526354532714129194770209 40894765899535596896077657)
        ·
          refine ⟨30671074424651697672058243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40894765899535596896077657 30671074424651697672058243)
          ·
            refine ⟨46006611636977546508087365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30671074424651697672058243 46006611636977546508087365)
            ·
              refine ⟨8626239681933289970266381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46006611636977546508087365 8626239681933289970266381)
              ·
                refine ⟨3234839880724983738849893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8626239681933289970266381 3234839880724983738849893)
                ·
                  refine ⟨606532477635934451034355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3234839880724983738849893 606532477635934451034355)
                  ·
                    refine ⟨909798716453901676551533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 606532477635934451034355 909798716453901676551533)
                    ·
                      refine ⟨341174518670213128706825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 909798716453901676551533 341174518670213128706825)
                      ·
                        rfl

theorem cell23_664435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 4, 1, 3].length) (baseStart_664435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_664435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_664435 prefixEnd_664435 := by exact prefixLift 664435
  have htrace : WordTrace (prefixWord ++ tailWord_664435) baseStart_664435 baseEnd_664435 := by
    simpa [prefixWord, tailWord_664435, baseEnd_664435] using wordTrace_append hprefix tailTrace_664435
  have hstable : (prefixWord ++ tailWord_664435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664435).length < 2 ^ (prefixWord ++ tailWord_664435).sum := by decide
  have hdescent : baseEnd_664435 < baseStart_664435 := by decide
  rcases family_descends (prefixWord ++ tailWord_664435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664470 : List Nat := [5, 3, 1, 1, 1, 1, 1, 5, 1, 2, 2]
def baseStart_664470 : Nat := 118140960795 + 664470 * 2 ^ 59
def prefixEnd_664470 : Nat := 4983230072969 + 3 ^ 40 * 664470 * 2
def baseEnd_664470 : Nat := 341192490493120491769165

theorem tailTrace_664470 : CollatzResearch.WordTrace tailWord_664470 prefixEnd_664470 341192490493120491769165 := by
  unfold tailWord_664470
  simp only [CollatzResearch.WordTrace]
  refine ⟨1514700743921634205394429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16156807935164098190873909 1514700743921634205394429)
  ·
    refine ⟨568012778970612827022911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1514700743921634205394429 568012778970612827022911)
    ·
      refine ⟨852019168455919240534367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 568012778970612827022911 852019168455919240534367)
      ·
        refine ⟨1278028752683878860801551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 852019168455919240534367 1278028752683878860801551)
        ·
          refine ⟨1917043129025818291202327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1278028752683878860801551 1917043129025818291202327)
          ·
            refine ⟨2875564693538727436803491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1917043129025818291202327 2875564693538727436803491)
            ·
              refine ⟨4313347040308091155205237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2875564693538727436803491 4313347040308091155205237)
              ·
                refine ⟨404376285028883545800491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4313347040308091155205237 404376285028883545800491)
                ·
                  refine ⟨606564427543325318700737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 404376285028883545800491 606564427543325318700737)
                  ·
                    refine ⟨454923320657493989025553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 606564427543325318700737 454923320657493989025553)
                    ·
                      refine ⟨341192490493120491769165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 454923320657493989025553 341192490493120491769165)
                      ·
                        rfl

theorem cell23_664470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_664470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_664470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_664470 prefixEnd_664470 := by exact prefixLift 664470
  have htrace : WordTrace (prefixWord ++ tailWord_664470) baseStart_664470 baseEnd_664470 := by
    simpa [prefixWord, tailWord_664470, baseEnd_664470] using wordTrace_append hprefix tailTrace_664470
  have hstable : (prefixWord ++ tailWord_664470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664470).length < 2 ^ (prefixWord ++ tailWord_664470).sum := by decide
  have hdescent : baseEnd_664470 < baseStart_664470 := by decide
  rcases family_descends (prefixWord ++ tailWord_664470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664479 : List Nat := [1, 1, 2, 5, 2, 2, 1, 3, 1, 3, 2]
def baseStart_664479 : Nat := 118140960795 + 664479 * 2 ^ 59
def prefixEnd_664479 : Nat := 4983230072969 + 3 ^ 40 * 664479 * 2
def baseEnd_664479 : Nat := 341197111819010956556623

theorem tailTrace_664479 : CollatzResearch.WordTrace tailWord_664479 prefixEnd_664479 341197111819010956556623 := by
  unfold tailWord_664479
  simp only [CollatzResearch.WordTrace]
  refine ⟨24235540159713541823388491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16157026773142361215592327 24235540159713541823388491)
  ·
    refine ⟨36353310239570312735082737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24235540159713541823388491 36353310239570312735082737)
    ·
      refine ⟨27264982679677734551312053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36353310239570312735082737 27264982679677734551312053)
      ·
        refine ⟨2556092126219787614185505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27264982679677734551312053 2556092126219787614185505)
        ·
          refine ⟨1917069094664840710639129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2556092126219787614185505 1917069094664840710639129)
          ·
            refine ⟨1437801820998630532979347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1917069094664840710639129 1437801820998630532979347)
            ·
              refine ⟨2156702731497945799469021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1437801820998630532979347 2156702731497945799469021)
              ·
                refine ⟨808763524311729674800883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2156702731497945799469021 808763524311729674800883)
                ·
                  refine ⟨1213145286467594512201325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 808763524311729674800883 1213145286467594512201325)
                  ·
                    refine ⟨454929482425347942075497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1213145286467594512201325 454929482425347942075497)
                    ·
                      refine ⟨341197111819010956556623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 454929482425347942075497 341197111819010956556623)
                      ·
                        rfl

theorem cell23_664479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_664479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_664479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_664479 prefixEnd_664479 := by exact prefixLift 664479
  have htrace : WordTrace (prefixWord ++ tailWord_664479) baseStart_664479 baseEnd_664479 := by
    simpa [prefixWord, tailWord_664479, baseEnd_664479] using wordTrace_append hprefix tailTrace_664479
  have hstable : (prefixWord ++ tailWord_664479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664479).length < 2 ^ (prefixWord ++ tailWord_664479).sum := by decide
  have hdescent : baseEnd_664479 < baseStart_664479 := by decide
  rcases family_descends (prefixWord ++ tailWord_664479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664492 : List Nat := [2, 2, 1, 1, 1, 1, 2, 5, 4, 2, 2]
def baseStart_664492 : Nat := 118140960795 + 664492 * 2 ^ 59
def prefixEnd_664492 : Nat := 4983230072969 + 3 ^ 40 * 664492 * 2
def baseEnd_664492 : Nat := 341203787067519405694063

theorem tailTrace_664492 : CollatzResearch.WordTrace tailWord_664492 prefixEnd_664492 341203787067519405694063 := by
  unfold tailWord_664492
  simp only [CollatzResearch.WordTrace]
  refine ⟨12118007154333222521805865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16157342872444296695741153 12118007154333222521805865)
  ·
    refine ⟨9088505365749916891354399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12118007154333222521805865 9088505365749916891354399)
    ·
      refine ⟨13632758048624875337031599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9088505365749916891354399 13632758048624875337031599)
      ·
        refine ⟨20449137072937313005547399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13632758048624875337031599 20449137072937313005547399)
        ·
          refine ⟨30673705609405969508321099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20449137072937313005547399 30673705609405969508321099)
          ·
            refine ⟨46010558414108954262481649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30673705609405969508321099 46010558414108954262481649)
            ·
              refine ⟨34507918810581715696861237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46010558414108954262481649 34507918810581715696861237)
              ·
                refine ⟨3235117388492035846580741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34507918810581715696861237 3235117388492035846580741)
                ·
                  refine ⟨606584510342256721233889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3235117388492035846580741 606584510342256721233889)
                  ·
                    refine ⟨454938382756692540925417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 606584510342256721233889 454938382756692540925417)
                    ·
                      refine ⟨341203787067519405694063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 454938382756692540925417 341203787067519405694063)
                      ·
                        rfl

theorem cell23_664492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 2, 2].length) (baseStart_664492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_664492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_664492 prefixEnd_664492 := by exact prefixLift 664492
  have htrace : WordTrace (prefixWord ++ tailWord_664492) baseStart_664492 baseEnd_664492 := by
    simpa [prefixWord, tailWord_664492, baseEnd_664492] using wordTrace_append hprefix tailTrace_664492
  have hstable : (prefixWord ++ tailWord_664492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664492).length < 2 ^ (prefixWord ++ tailWord_664492).sum := by decide
  have hdescent : baseEnd_664492 < baseStart_664492 := by decide
  rcases family_descends (prefixWord ++ tailWord_664492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664505 : List Nat := [1, 2, 1, 4, 2, 2, 2, 1, 2, 2, 4]
def baseStart_664505 : Nat := 118140960795 + 664505 * 2 ^ 59
def prefixEnd_664505 : Nat := 4983230072969 + 3 ^ 40 * 664505 * 2
def baseEnd_664505 : Nat := 341210462316027854831503

theorem tailTrace_664505 : CollatzResearch.WordTrace tailWord_664505 prefixEnd_664505 341210462316027854831503 := by
  unfold tailWord_664505
  simp only [CollatzResearch.WordTrace]
  refine ⟨24236488457619348263834969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16157658971746232175889979 24236488457619348263834969)
  ·
    refine ⟨18177366343214511197876227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24236488457619348263834969 18177366343214511197876227)
    ·
      refine ⟨27266049514821766796814341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18177366343214511197876227 27266049514821766796814341)
      ·
        refine ⟨5112384284029081274402689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27266049514821766796814341 5112384284029081274402689)
        ·
          refine ⟨3834288213021810955802017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5112384284029081274402689 3834288213021810955802017)
          ·
            refine ⟨2875716159766358216851513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3834288213021810955802017 2875716159766358216851513)
            ·
              refine ⟨2156787119824768662638635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2875716159766358216851513 2156787119824768662638635)
              ·
                refine ⟨3235180679737152993957953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2156787119824768662638635 3235180679737152993957953)
                ·
                  refine ⟨2426385509802864745468465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3235180679737152993957953 2426385509802864745468465)
                  ·
                    refine ⟨1819789132352148559101349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2426385509802864745468465 1819789132352148559101349)
                    ·
                      refine ⟨341210462316027854831503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1819789132352148559101349 341210462316027854831503)
                      ·
                        rfl

theorem cell23_664505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_664505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_664505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_664505 prefixEnd_664505 := by exact prefixLift 664505
  have htrace : WordTrace (prefixWord ++ tailWord_664505) baseStart_664505 baseEnd_664505 := by
    simpa [prefixWord, tailWord_664505, baseEnd_664505] using wordTrace_append hprefix tailTrace_664505
  have hstable : (prefixWord ++ tailWord_664505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664505).length < 2 ^ (prefixWord ++ tailWord_664505).sum := by decide
  have hdescent : baseEnd_664505 < baseStart_664505 := by decide
  rcases family_descends (prefixWord ++ tailWord_664505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664549 : List Nat := [1, 3, 1, 6, 1, 2, 1, 1, 7]
def baseStart_664549 : Nat := 118140960795 + 664549 * 2 ^ 59
def prefixEnd_664549 : Nat := 4983230072969 + 3 ^ 40 * 664549 * 2
def baseEnd_664549 : Nat := 37914783940536186964589

theorem tailTrace_664549 : CollatzResearch.WordTrace tailWord_664549 prefixEnd_664549 37914783940536186964589 := by
  unfold tailWord_664549
  simp only [CollatzResearch.WordTrace]
  refine ⟨24238093269459943778436701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16158728846306629185624467 24238093269459943778436701)
  ·
    refine ⟨9089284976047478916913763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24238093269459943778436701 9089284976047478916913763)
    ·
      refine ⟨13633927464071218375370645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9089284976047478916913763 13633927464071218375370645)
      ·
        refine ⟨639090349878338361345499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 13633927464071218375370645 639090349878338361345499)
        ·
          refine ⟨958635524817507542018249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 639090349878338361345499 958635524817507542018249)
          ·
            refine ⟨718976643613130656513687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 958635524817507542018249 718976643613130656513687)
            ·
              refine ⟨1078464965419695984770531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 718976643613130656513687 1078464965419695984770531)
              ·
                refine ⟨1617697448129543977155797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1078464965419695984770531 1617697448129543977155797)
                ·
                  refine ⟨37914783940536186964589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1617697448129543977155797 37914783940536186964589)
                  ·
                    rfl

theorem cell23_664549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 7].length) (baseStart_664549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_664549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_664549 prefixEnd_664549 := by exact prefixLift 664549
  have htrace : WordTrace (prefixWord ++ tailWord_664549) baseStart_664549 baseEnd_664549 := by
    simpa [prefixWord, tailWord_664549, baseEnd_664549] using wordTrace_append hprefix tailTrace_664549
  have hstable : (prefixWord ++ tailWord_664549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664549).length < 2 ^ (prefixWord ++ tailWord_664549).sum := by decide
  have hdescent : baseEnd_664549 < baseStart_664549 := by decide
  rcases family_descends (prefixWord ++ tailWord_664549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664564 : List Nat := [2, 6, 2, 1, 2, 1, 1, 2, 1, 3, 2]
def baseStart_664564 : Nat := 118140960795 + 664564 * 2 ^ 59
def prefixEnd_664564 : Nat := 4983230072969 + 3 ^ 40 * 664564 * 2
def baseEnd_664564 : Nat := 341240757674643123993733

theorem tailTrace_664564 : CollatzResearch.WordTrace tailWord_664564 prefixEnd_664564 341240757674643123993733 := by
  unfold tailWord_664564
  simp only [CollatzResearch.WordTrace]
  refine ⟨12119320182202800670116373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16159093576270400893488497 12119320182202800670116373)
  ·
    refine ⟨568093133540756281411705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 12119320182202800670116373 568093133540756281411705)
    ·
      refine ⟨426069850155567211058779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 568093133540756281411705 426069850155567211058779)
      ·
        refine ⟨639104775233350816588169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 426069850155567211058779 639104775233350816588169)
        ·
          refine ⟨479328581425013112441127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 639104775233350816588169 479328581425013112441127)
          ·
            refine ⟨718992872137519668661691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 479328581425013112441127 718992872137519668661691)
            ·
              refine ⟨1078489308206279502992537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 718992872137519668661691 1078489308206279502992537)
              ·
                refine ⟨808866981154709627244403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1078489308206279502992537 808866981154709627244403)
                ·
                  refine ⟨1213300471732064440866605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 808866981154709627244403 1213300471732064440866605)
                  ·
                    refine ⟨454987676899524165324977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1213300471732064440866605 454987676899524165324977)
                    ·
                      refine ⟨341240757674643123993733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 454987676899524165324977 341240757674643123993733)
                      ·
                        rfl

theorem cell23_664564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_664564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_664564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_664564 prefixEnd_664564 := by exact prefixLift 664564
  have htrace : WordTrace (prefixWord ++ tailWord_664564) baseStart_664564 baseEnd_664564 := by
    simpa [prefixWord, tailWord_664564, baseEnd_664564] using wordTrace_append hprefix tailTrace_664564
  have hstable : (prefixWord ++ tailWord_664564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664564).length < 2 ^ (prefixWord ++ tailWord_664564).sum := by decide
  have hdescent : baseEnd_664564 < baseStart_664564 := by decide
  rcases family_descends (prefixWord ++ tailWord_664564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664585 : List Nat := [1, 2, 1, 1, 3, 1, 1, 5, 1, 4, 3]
def baseStart_664585 : Nat := 118140960795 + 664585 * 2 ^ 59
def prefixEnd_664585 : Nat := 4983230072969 + 3 ^ 40 * 664585 * 2
def baseEnd_664585 : Nat := 341251540768387541831135

theorem tailTrace_664585 : CollatzResearch.WordTrace tailWord_664585 prefixEnd_664585 341251540768387541831135 := by
  unfold tailWord_664585
  simp only [CollatzResearch.WordTrace]
  refine ⟨24239406297329521926747209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16159604198219681284498139 24239406297329521926747209)
  ·
    refine ⟨18179554722997141445060407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24239406297329521926747209 18179554722997141445060407)
    ·
      refine ⟨27269332084495712167590611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18179554722997141445060407 27269332084495712167590611)
      ·
        refine ⟨40903998126743568251385917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27269332084495712167590611 40903998126743568251385917)
        ·
          refine ⟨15338999297528838094269719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40903998126743568251385917 15338999297528838094269719)
          ·
            refine ⟨23008498946293257141404579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15338999297528838094269719 23008498946293257141404579)
            ·
              refine ⟨34512748419439885712106869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23008498946293257141404579 34512748419439885712106869)
              ·
                refine ⟨3235570164322489285510019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34512748419439885712106869 3235570164322489285510019)
                ·
                  refine ⟨4853355246483733928265029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3235570164322489285510019 4853355246483733928265029)
                  ·
                    refine ⟨910004108715700111549693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4853355246483733928265029 910004108715700111549693)
                    ·
                      refine ⟨341251540768387541831135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 910004108715700111549693 341251540768387541831135)
                      ·
                        rfl

theorem cell23_664585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 4, 3].length) (baseStart_664585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_664585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_664585 prefixEnd_664585 := by exact prefixLift 664585
  have htrace : WordTrace (prefixWord ++ tailWord_664585) baseStart_664585 baseEnd_664585 := by
    simpa [prefixWord, tailWord_664585, baseEnd_664585] using wordTrace_append hprefix tailTrace_664585
  have hstable : (prefixWord ++ tailWord_664585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664585).length < 2 ^ (prefixWord ++ tailWord_664585).sum := by decide
  have hdescent : baseEnd_664585 < baseStart_664585 := by decide
  rcases family_descends (prefixWord ++ tailWord_664585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664602 : List Nat := [3, 1, 1, 3, 1, 2, 1, 4, 2, 2, 3]
def baseStart_664602 : Nat := 118140960795 + 664602 * 2 ^ 59
def prefixEnd_664602 : Nat := 4983230072969 + 3 ^ 40 * 664602 * 2
def baseEnd_664602 : Nat := 341260269939513975318557

theorem tailTrace_664602 : CollatzResearch.WordTrace tailWord_664602 prefixEnd_664602 341260269939513975318557 := by
  unfold tailWord_664602
  simp only [CollatzResearch.WordTrace]
  refine ⟨6060006584566983457529015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16160017558845289220077373 6060006584566983457529015)
  ·
    refine ⟨9090009876850475186293523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6060006584566983457529015 9090009876850475186293523)
    ·
      refine ⟨13635014815275712779440285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9090009876850475186293523 13635014815275712779440285)
      ·
        refine ⟨5113130555728392292290107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13635014815275712779440285 5113130555728392292290107)
        ·
          refine ⟨7669695833592588438435161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5113130555728392292290107 7669695833592588438435161)
          ·
            refine ⟨5752271875194441328826371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7669695833592588438435161 5752271875194441328826371)
            ·
              refine ⟨8628407812791661993239557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5752271875194441328826371 8628407812791661993239557)
              ·
                refine ⟨1617826464898436623732417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8628407812791661993239557 1617826464898436623732417)
                ·
                  refine ⟨1213369848673827467799313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1617826464898436623732417 1213369848673827467799313)
                  ·
                    refine ⟨910027386505370600849485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1213369848673827467799313 910027386505370600849485)
                    ·
                      refine ⟨341260269939513975318557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 910027386505370600849485 341260269939513975318557)
                      ·
                        rfl

theorem cell23_664602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_664602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_664602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_664602 prefixEnd_664602 := by exact prefixLift 664602
  have htrace : WordTrace (prefixWord ++ tailWord_664602) baseStart_664602 baseEnd_664602 := by
    simpa [prefixWord, tailWord_664602, baseEnd_664602] using wordTrace_append hprefix tailTrace_664602
  have hstable : (prefixWord ++ tailWord_664602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664602).length < 2 ^ (prefixWord ++ tailWord_664602).sum := by decide
  have hdescent : baseEnd_664602 < baseStart_664602 := by decide
  rcases family_descends (prefixWord ++ tailWord_664602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664622 : List Nat := [4, 1, 3, 1, 1, 1, 1, 5, 6]
def baseStart_664622 : Nat := 118140960795 + 664622 * 2 ^ 59
def prefixEnd_664622 : Nat := 4983230072969 + 3 ^ 40 * 664622 * 2
def baseEnd_664622 : Nat := 37918948839178210785385

theorem tailTrace_664622 : CollatzResearch.WordTrace tailWord_664622 prefixEnd_664622 37918948839178210785385 := by
  unfold tailWord_664622
  simp only [CollatzResearch.WordTrace]
  refine ⟨3030094474774434655730515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16160503865463651497229413 3030094474774434655730515)
  ·
    refine ⟨4545141712161651983595773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3030094474774434655730515 4545141712161651983595773)
    ·
      refine ⟨1704428142060619493848415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4545141712161651983595773 1704428142060619493848415)
      ·
        refine ⟨2556642213090929240772623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1704428142060619493848415 2556642213090929240772623)
        ·
          refine ⟨3834963319636393861158935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2556642213090929240772623 3834963319636393861158935)
          ·
            refine ⟨5752444979454590791738403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3834963319636393861158935 5752444979454590791738403)
            ·
              refine ⟨8628667469181886187607605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5752444979454590791738403 8628667469181886187607605)
              ·
                refine ⟨808937575235801830088213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8628667469181886187607605 808937575235801830088213)
                ·
                  refine ⟨37918948839178210785385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 808937575235801830088213 37918948839178210785385)
                  ·
                    rfl

theorem cell23_664622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 5, 6].length) (baseStart_664622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_664622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_664622 prefixEnd_664622 := by exact prefixLift 664622
  have htrace : WordTrace (prefixWord ++ tailWord_664622) baseStart_664622 baseEnd_664622 := by
    simpa [prefixWord, tailWord_664622, baseEnd_664622] using wordTrace_append hprefix tailTrace_664622
  have hstable : (prefixWord ++ tailWord_664622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664622).length < 2 ^ (prefixWord ++ tailWord_664622).sum := by decide
  have hdescent : baseEnd_664622 < baseStart_664622 := by decide
  rcases family_descends (prefixWord ++ tailWord_664622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664689 : List Nat := [1, 2, 2, 2, 1, 1, 2, 3, 5, 2, 2]
def baseStart_664689 : Nat := 118140960795 + 664689 * 2 ^ 59
def prefixEnd_664689 : Nat := 4983230072969 + 3 ^ 40 * 664689 * 2
def baseEnd_664689 : Nat := 341304942756455134930657

theorem tailTrace_664689 : CollatzResearch.WordTrace tailWord_664689 prefixEnd_664689 341304942756455134930657 := by
  unfold tailWord_664689
  simp only [CollatzResearch.WordTrace]
  refine ⟨24243199488952747688533121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16162132992635165125688747 24243199488952747688533121)
  ·
    refine ⟨18182399616714560766399841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24243199488952747688533121 18182399616714560766399841)
    ·
      refine ⟨13636799712535920574799881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18182399616714560766399841 13636799712535920574799881)
      ·
        refine ⟨10227599784401940431099911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13636799712535920574799881 10227599784401940431099911)
        ·
          refine ⟨15341399676602910646649867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10227599784401940431099911 15341399676602910646649867)
          ·
            refine ⟨23012099514904365969974801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15341399676602910646649867 23012099514904365969974801)
            ·
              refine ⟨17259074636178274477481101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23012099514904365969974801 17259074636178274477481101)
              ·
                refine ⟨6472152988566852929055413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17259074636178274477481101 6472152988566852929055413)
                ·
                  refine ⟨606764342678142462098945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6472152988566852929055413 606764342678142462098945)
                  ·
                    refine ⟨455073257008606846574209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 606764342678142462098945 455073257008606846574209)
                    ·
                      refine ⟨341304942756455134930657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 455073257008606846574209 341304942756455134930657)
                      ·
                        rfl

theorem cell23_664689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 5, 2, 2].length) (baseStart_664689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_664689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_664689 prefixEnd_664689 := by exact prefixLift 664689
  have htrace : WordTrace (prefixWord ++ tailWord_664689) baseStart_664689 baseEnd_664689 := by
    simpa [prefixWord, tailWord_664689, baseEnd_664689] using wordTrace_append hprefix tailTrace_664689
  have hstable : (prefixWord ++ tailWord_664689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664689).length < 2 ^ (prefixWord ++ tailWord_664689).sum := by decide
  have hdescent : baseEnd_664689 < baseStart_664689 := by decide
  rcases family_descends (prefixWord ++ tailWord_664689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664695 : List Nat := [1, 1, 3, 1, 1, 4, 3, 9]
def baseStart_664695 : Nat := 118140960795 + 664695 * 2 ^ 59
def prefixEnd_664695 : Nat := 4983230072969 + 3 ^ 40 * 664695 * 2
def baseEnd_664695 : Nat := 12641037912606744868727

theorem tailTrace_664695 : CollatzResearch.WordTrace tailWord_664695 prefixEnd_664695 12641037912606744868727 := by
  unfold tailWord_664695
  simp only [CollatzResearch.WordTrace]
  refine ⟨24243418326931010713251539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16162278884620673808834359 24243418326931010713251539)
  ·
    refine ⟨36365127490396516069877309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24243418326931010713251539 36365127490396516069877309)
    ·
      refine ⟨13636922808898693526203991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36365127490396516069877309 13636922808898693526203991)
      ·
        refine ⟨20455384213348040289305987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13636922808898693526203991 20455384213348040289305987)
        ·
          refine ⟨30683076320022060433958981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20455384213348040289305987 30683076320022060433958981)
          ·
            refine ⟨5753076810004136331367309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30683076320022060433958981 5753076810004136331367309)
            ·
              refine ⟨2157403803751551124262741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5753076810004136331367309 2157403803751551124262741)
              ·
                refine ⟨12641037912606744868727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2157403803751551124262741 12641037912606744868727)
                ·
                  rfl

theorem cell23_664695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 9].length) (baseStart_664695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_664695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_664695 prefixEnd_664695 := by exact prefixLift 664695
  have htrace : WordTrace (prefixWord ++ tailWord_664695) baseStart_664695 baseEnd_664695 := by
    simpa [prefixWord, tailWord_664695, baseEnd_664695] using wordTrace_append hprefix tailTrace_664695
  have hstable : (prefixWord ++ tailWord_664695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664695).length < 2 ^ (prefixWord ++ tailWord_664695).sum := by decide
  have hdescent : baseEnd_664695 < baseStart_664695 := by decide
  rcases family_descends (prefixWord ++ tailWord_664695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664709 : List Nat := [1, 3, 1, 1, 6, 1, 2, 1, 1, 1, 5]
def baseStart_664709 : Nat := 118140960795 + 664709 * 2 ^ 59
def prefixEnd_664709 : Nat := 4983230072969 + 3 ^ 40 * 664709 * 2
def baseEnd_664709 : Nat := 341315212369545056680565

theorem tailTrace_664709 : CollatzResearch.WordTrace tailWord_664709 prefixEnd_664709 341315212369545056680565 := by
  unfold tailWord_664709
  simp only [CollatzResearch.WordTrace]
  refine ⟨24243928948880291104261181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16162619299253527402840787 24243928948880291104261181)
  ·
    refine ⟨9091473355830109164097943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24243928948880291104261181 9091473355830109164097943)
    ·
      refine ⟨13637210033745163746146915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9091473355830109164097943 13637210033745163746146915)
      ·
        refine ⟨20455815050617745619220373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13637210033745163746146915 20455815050617745619220373)
        ·
          refine ⟨958866330497706825900955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 20455815050617745619220373 958866330497706825900955)
          ·
            refine ⟨1438299495746560238851433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 958866330497706825900955 1438299495746560238851433)
            ·
              refine ⟨1078724621809920179138575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1438299495746560238851433 1078724621809920179138575)
              ·
                refine ⟨1618086932714880268707863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1078724621809920179138575 1618086932714880268707863)
                ·
                  refine ⟨2427130399072320403061795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1618086932714880268707863 2427130399072320403061795)
                  ·
                    refine ⟨3640695598608480604592693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2427130399072320403061795 3640695598608480604592693)
                    ·
                      refine ⟨341315212369545056680565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3640695598608480604592693 341315212369545056680565)
                      ·
                        rfl

theorem cell23_664709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 1, 5].length) (baseStart_664709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_664709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_664709 prefixEnd_664709 := by exact prefixLift 664709
  have htrace : WordTrace (prefixWord ++ tailWord_664709) baseStart_664709 baseEnd_664709 := by
    simpa [prefixWord, tailWord_664709, baseEnd_664709] using wordTrace_append hprefix tailTrace_664709
  have hstable : (prefixWord ++ tailWord_664709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664709).length < 2 ^ (prefixWord ++ tailWord_664709).sum := by decide
  have hdescent : baseEnd_664709 < baseStart_664709 := by decide
  rcases family_descends (prefixWord ++ tailWord_664709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664743 : List Nat := [1, 1, 6, 2, 1, 3, 1, 2, 1, 2, 3]
def baseStart_664743 : Nat := 118140960795 + 664743 * 2 ^ 59
def prefixEnd_664743 : Nat := 4983230072969 + 3 ^ 40 * 664743 * 2
def baseEnd_664743 : Nat := 341332670711797923655409

theorem tailTrace_664743 : CollatzResearch.WordTrace tailWord_664743 prefixEnd_664743 341332670711797923655409 := by
  unfold tailWord_664743
  simp only [CollatzResearch.WordTrace]
  refine ⟨24245169030757114910998883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16163446020504743273999255 24245169030757114910998883)
  ·
    refine ⟨36367753546135672366498325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24245169030757114910998883 36367753546135672366498325)
    ·
      refine ⟨1704738447475109642179609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 36367753546135672366498325 1704738447475109642179609)
      ·
        refine ⟨1278553835606332231634707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1704738447475109642179609 1278553835606332231634707)
        ·
          refine ⟨1917830753409498347452061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1278553835606332231634707 1917830753409498347452061)
          ·
            refine ⟨719186532528561880294523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1917830753409498347452061 719186532528561880294523)
            ·
              refine ⟨1078779798792842820441785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 719186532528561880294523 1078779798792842820441785)
              ·
                refine ⟨809084849094632115331339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1078779798792842820441785 809084849094632115331339)
                ·
                  refine ⟨1213627273641948172997009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 809084849094632115331339 1213627273641948172997009)
                  ·
                    refine ⟨910220455231461129747757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1213627273641948172997009 910220455231461129747757)
                    ·
                      refine ⟨341332670711797923655409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 910220455231461129747757 341332670711797923655409)
                      ·
                        rfl

theorem cell23_664743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_664743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_664743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_664743 prefixEnd_664743 := by exact prefixLift 664743
  have htrace : WordTrace (prefixWord ++ tailWord_664743) baseStart_664743 baseEnd_664743 := by
    simpa [prefixWord, tailWord_664743, baseEnd_664743] using wordTrace_append hprefix tailTrace_664743
  have hstable : (prefixWord ++ tailWord_664743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664743).length < 2 ^ (prefixWord ++ tailWord_664743).sum := by decide
  have hdescent : baseEnd_664743 < baseStart_664743 := by decide
  rcases family_descends (prefixWord ++ tailWord_664743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664789 : List Nat := [1, 3, 2, 4, 1, 2, 1, 1, 2, 6]
def baseStart_664789 : Nat := 118140960795 + 664789 * 2 ^ 59
def prefixEnd_664789 : Nat := 4983230072969 + 3 ^ 40 * 664789 * 2
def baseEnd_664789 : Nat := 113785430273968247893399

theorem tailTrace_664789 : CollatzResearch.WordTrace tailWord_664789 prefixEnd_664789 113785430273968247893399 := by
  unfold tailWord_664789
  simp only [CollatzResearch.WordTrace]
  refine ⟨24246846788590464767173421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16164564525726976511448947 24246846788590464767173421)
  ·
    refine ⟨9092567545721424287690033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24246846788590464767173421 9092567545721424287690033)
    ·
      refine ⟨6819425659291068215767525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9092567545721424287690033 6819425659291068215767525)
      ·
        refine ⟨1278642311117075290456411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6819425659291068215767525 1278642311117075290456411)
        ·
          refine ⟨1917963466675612935684617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1278642311117075290456411 1917963466675612935684617)
          ·
            refine ⟨1438472600006709701763463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1917963466675612935684617 1438472600006709701763463)
            ·
              refine ⟨2157708900010064552645195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1438472600006709701763463 2157708900010064552645195)
              ·
                refine ⟨3236563350015096828967793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2157708900010064552645195 3236563350015096828967793)
                ·
                  refine ⟨2427422512511322621725845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3236563350015096828967793 2427422512511322621725845)
                  ·
                    refine ⟨113785430273968247893399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2427422512511322621725845 113785430273968247893399)
                    ·
                      rfl

theorem cell23_664789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 6].length) (baseStart_664789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_664789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_664789 prefixEnd_664789 := by exact prefixLift 664789
  have htrace : WordTrace (prefixWord ++ tailWord_664789) baseStart_664789 baseEnd_664789 := by
    simpa [prefixWord, tailWord_664789, baseEnd_664789] using wordTrace_append hprefix tailTrace_664789
  have hstable : (prefixWord ++ tailWord_664789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664789).length < 2 ^ (prefixWord ++ tailWord_664789).sum := by decide
  have hdescent : baseEnd_664789 < baseStart_664789 := by decide
  rcases family_descends (prefixWord ++ tailWord_664789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664819 : List Nat := [1, 1, 1, 2, 2, 5, 1, 5, 5]
def baseStart_664819 : Nat := 118140960795 + 664819 * 2 ^ 59
def prefixEnd_664819 : Nat := 4983230072969 + 3 ^ 40 * 664819 * 2
def baseEnd_664819 : Nat := 37930188360171069589451

theorem tailTrace_664819 : CollatzResearch.WordTrace tailWord_664819 prefixEnd_664819 37930188360171069589451 := by
  unfold tailWord_664819
  simp only [CollatzResearch.WordTrace]
  refine ⟨24247940978481779890765511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16165293985654519927177007 24247940978481779890765511)
  ·
    refine ⟨36371911467722669836148267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24247940978481779890765511 36371911467722669836148267)
    ·
      refine ⟨54557867201584004754222401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36371911467722669836148267 54557867201584004754222401)
      ·
        refine ⟨40918400401188003565666801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54557867201584004754222401 40918400401188003565666801)
        ·
          refine ⟨30688800300891002674250101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40918400401188003565666801 30688800300891002674250101)
          ·
            refine ⟨2877075028208531500710947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30688800300891002674250101 2877075028208531500710947)
            ·
              refine ⟨4315612542312797251066421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2877075028208531500710947 4315612542312797251066421)
              ·
                refine ⟨404588675841824742287477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4315612542312797251066421 404588675841824742287477)
                ·
                  refine ⟨37930188360171069589451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 404588675841824742287477 37930188360171069589451)
                  ·
                    rfl

theorem cell23_664819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 5, 5].length) (baseStart_664819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_664819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_664819 prefixEnd_664819 := by exact prefixLift 664819
  have htrace : WordTrace (prefixWord ++ tailWord_664819) baseStart_664819 baseEnd_664819 := by
    simpa [prefixWord, tailWord_664819, baseEnd_664819] using wordTrace_append hprefix tailTrace_664819
  have hstable : (prefixWord ++ tailWord_664819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664819).length < 2 ^ (prefixWord ++ tailWord_664819).sum := by decide
  have hdescent : baseEnd_664819 < baseStart_664819 := by decide
  rcases family_descends (prefixWord ++ tailWord_664819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664830 : List Nat := [4, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2]
def baseStart_664830 : Nat := 118140960795 + 664830 * 2 ^ 59
def prefixEnd_664830 : Nat := 4983230072969 + 3 ^ 40 * 664830 * 2
def baseEnd_664830 : Nat := 341377343528739083267509

theorem tailTrace_664830 : CollatzResearch.WordTrace tailWord_664830 prefixEnd_664830 341377343528739083267509 := by
  unfold tailWord_664830
  simp only [CollatzResearch.WordTrace]
  refine ⟨3031042772680241096176993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16165561454294619179610629 3031042772680241096176993)
  ·
    refine ⟨2273282079510180822132745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3031042772680241096176993 2273282079510180822132745)
    ·
      refine ⟨1704961559632635616599559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2273282079510180822132745 1704961559632635616599559)
      ·
        refine ⟨2557442339448953424899339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1704961559632635616599559 2557442339448953424899339)
        ·
          refine ⟨3836163509173430137349009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2557442339448953424899339 3836163509173430137349009)
          ·
            refine ⟨2877122631880072603011757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3836163509173430137349009 2877122631880072603011757)
            ·
              refine ⟨1078920986955027226129409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2877122631880072603011757 1078920986955027226129409)
              ·
                refine ⟨809190740216270419597057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1078920986955027226129409 809190740216270419597057)
                ·
                  refine ⟨606893055162202814697793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 809190740216270419597057 606893055162202814697793)
                  ·
                    refine ⟨455169791371652111023345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 606893055162202814697793 455169791371652111023345)
                    ·
                      refine ⟨341377343528739083267509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 455169791371652111023345 341377343528739083267509)
                      ·
                        rfl

theorem cell23_664830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_664830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_664830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_664830 prefixEnd_664830 := by exact prefixLift 664830
  have htrace : WordTrace (prefixWord ++ tailWord_664830) baseStart_664830 baseEnd_664830 := by
    simpa [prefixWord, tailWord_664830, baseEnd_664830] using wordTrace_append hprefix tailTrace_664830
  have hstable : (prefixWord ++ tailWord_664830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664830).length < 2 ^ (prefixWord ++ tailWord_664830).sum := by decide
  have hdescent : baseEnd_664830 < baseStart_664830 := by decide
  rcases family_descends (prefixWord ++ tailWord_664830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664832 : List Nat := [2, 1, 1, 2, 1, 1, 3, 3, 4, 5]
def baseStart_664832 : Nat := 118140960795 + 664832 * 2 ^ 59
def prefixEnd_664832 : Nat := 4983230072969 + 3 ^ 40 * 664832 * 2
def baseEnd_664832 : Nat := 113792790163349358480833

theorem tailTrace_664832 : CollatzResearch.WordTrace tailWord_664832 prefixEnd_664832 113792790163349358480833 := by
  unfold tailWord_664832
  simp only [CollatzResearch.WordTrace]
  refine ⟨12124207563717341555494375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16165610084956455407325833 12124207563717341555494375)
  ·
    refine ⟨18186311345576012333241563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12124207563717341555494375 18186311345576012333241563)
    ·
      refine ⟨27279467018364018499862345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18186311345576012333241563 27279467018364018499862345)
      ·
        refine ⟨20459600263773013874896759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27279467018364018499862345 20459600263773013874896759)
        ·
          refine ⟨30689400395659520812345139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20459600263773013874896759 30689400395659520812345139)
          ·
            refine ⟨46034100593489281218517709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30689400395659520812345139 46034100593489281218517709)
            ·
              refine ⟨17262787722558480456944141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46034100593489281218517709 17262787722558480456944141)
              ·
                refine ⟨6473545395959430171354053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17262787722558480456944141 6473545395959430171354053)
                ·
                  refine ⟨1213789761742393157128885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6473545395959430171354053 1213789761742393157128885)
                  ·
                    refine ⟨113792790163349358480833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1213789761742393157128885 113792790163349358480833)
                    ·
                      rfl

theorem cell23_664832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 4, 5].length) (baseStart_664832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_664832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_664832 prefixEnd_664832 := by exact prefixLift 664832
  have htrace : WordTrace (prefixWord ++ tailWord_664832) baseStart_664832 baseEnd_664832 := by
    simpa [prefixWord, tailWord_664832, baseEnd_664832] using wordTrace_append hprefix tailTrace_664832
  have hstable : (prefixWord ++ tailWord_664832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664832).length < 2 ^ (prefixWord ++ tailWord_664832).sum := by decide
  have hdescent : baseEnd_664832 < baseStart_664832 := by decide
  rcases family_descends (prefixWord ++ tailWord_664832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664836 : List Nat := [2, 3, 2, 2, 2, 1, 2, 4, 5]
def baseStart_664836 : Nat := 118140960795 + 664836 * 2 ^ 59
def prefixEnd_664836 : Nat := 4983230072969 + 3 ^ 40 * 664836 * 2
def baseEnd_664836 : Nat := 37931158268074006643609

theorem tailTrace_664836 : CollatzResearch.WordTrace tailWord_664836 prefixEnd_664836 37931158268074006643609 := by
  unfold tailWord_664836
  simp only [CollatzResearch.WordTrace]
  refine ⟨12124280509710095897067181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16165707346280127862756241 12124280509710095897067181)
  ·
    refine ⟨4546605191141285961400193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12124280509710095897067181 4546605191141285961400193)
    ·
      refine ⟨3409953893355964471050145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4546605191141285961400193 3409953893355964471050145)
      ·
        refine ⟨2557465420016973353287609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3409953893355964471050145 2557465420016973353287609)
        ·
          refine ⟨1918099065012730014965707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2557465420016973353287609 1918099065012730014965707)
          ·
            refine ⟨2877148597519095022448561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1918099065012730014965707 2877148597519095022448561)
            ·
              refine ⟨2157861448139321266836421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2877148597519095022448561 2157861448139321266836421)
              ·
                refine ⟨404599021526122737531829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2157861448139321266836421 404599021526122737531829)
                ·
                  refine ⟨37931158268074006643609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 404599021526122737531829 37931158268074006643609)
                  ·
                    rfl

theorem cell23_664836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 4, 5].length) (baseStart_664836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_664836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_664836 prefixEnd_664836 := by exact prefixLift 664836
  have htrace : WordTrace (prefixWord ++ tailWord_664836) baseStart_664836 baseEnd_664836 := by
    simpa [prefixWord, tailWord_664836, baseEnd_664836] using wordTrace_append hprefix tailTrace_664836
  have hstable : (prefixWord ++ tailWord_664836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664836).length < 2 ^ (prefixWord ++ tailWord_664836).sum := by decide
  have hdescent : baseEnd_664836 < baseStart_664836 := by decide
  rcases family_descends (prefixWord ++ tailWord_664836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664842 : List Nat := [3, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7]
def baseStart_664842 : Nat := 118140960795 + 664842 * 2 ^ 59
def prefixEnd_664842 : Nat := 4983230072969 + 3 ^ 40 * 664842 * 2
def baseEnd_664842 : Nat := 341383505296593036317453

theorem tailTrace_664842 : CollatzResearch.WordTrace tailWord_664842 prefixEnd_664842 341383505296593036317453 := by
  unfold tailWord_664842
  simp only [CollatzResearch.WordTrace]
  refine ⟨6062194964349613704713195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16165853238265636545901853 6062194964349613704713195)
  ·
    refine ⟨9093292446524420557069793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6062194964349613704713195 9093292446524420557069793)
    ·
      refine ⟨6819969334893315417802345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9093292446524420557069793 6819969334893315417802345)
      ·
        refine ⟨5114977001169986563351759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6819969334893315417802345 5114977001169986563351759)
        ·
          refine ⟨7672465501754979845027639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5114977001169986563351759 7672465501754979845027639)
          ·
            refine ⟨11508698252632469767541459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7672465501754979845027639 11508698252632469767541459)
            ·
              refine ⟨17263047378948704651312189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11508698252632469767541459 17263047378948704651312189)
              ·
                refine ⟨6473642767105764244242071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17263047378948704651312189 6473642767105764244242071)
                ·
                  refine ⟨9710464150658646366363107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6473642767105764244242071 9710464150658646366363107)
                  ·
                    refine ⟨14565696225987969549544661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9710464150658646366363107 14565696225987969549544661)
                    ·
                      refine ⟨341383505296593036317453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 14565696225987969549544661 341383505296593036317453)
                      ·
                        rfl

theorem cell23_664842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_664842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_664842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_664842 prefixEnd_664842 := by exact prefixLift 664842
  have htrace : WordTrace (prefixWord ++ tailWord_664842) baseStart_664842 baseEnd_664842 := by
    simpa [prefixWord, tailWord_664842, baseEnd_664842] using wordTrace_append hprefix tailTrace_664842
  have hstable : (prefixWord ++ tailWord_664842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664842).length < 2 ^ (prefixWord ++ tailWord_664842).sum := by decide
  have hdescent : baseEnd_664842 < baseStart_664842 := by decide
  rcases family_descends (prefixWord ++ tailWord_664842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664869 : List Nat := [1, 3, 1, 2, 4, 1, 2, 1, 1, 3, 4]
def baseStart_664869 : Nat := 118140960795 + 664869 * 2 ^ 59
def prefixEnd_664869 : Nat := 4983230072969 + 3 ^ 40 * 664869 * 2
def baseEnd_664869 : Nat := 341397369274264430679829

theorem tailTrace_664869 : CollatzResearch.WordTrace tailWord_664869 prefixEnd_664869 341397369274264430679829 := by
  unfold tailWord_664869
  simp only [CollatzResearch.WordTrace]
  refine ⟨24249764628300638430085661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16166509752200425620057107 24249764628300638430085661)
  ·
    refine ⟨9093661735612739411282123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24249764628300638430085661 9093661735612739411282123)
    ·
      refine ⟨13640492603419109116923185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9093661735612739411282123 13640492603419109116923185)
      ·
        refine ⟨10230369452564331837692389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13640492603419109116923185 10230369452564331837692389)
        ·
          refine ⟨1918194272355812219567323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10230369452564331837692389 1918194272355812219567323)
          ·
            refine ⟨2877291408533718329350985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1918194272355812219567323 2877291408533718329350985)
            ·
              refine ⟨2157968556400288747013239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2877291408533718329350985 2157968556400288747013239)
              ·
                refine ⟨3236952834600433120519859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2157968556400288747013239 3236952834600433120519859)
                ·
                  refine ⟨4855429251900649680779789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3236952834600433120519859 4855429251900649680779789)
                  ·
                    refine ⟨1820785969462743630292421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4855429251900649680779789 1820785969462743630292421)
                    ·
                      refine ⟨341397369274264430679829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1820785969462743630292421 341397369274264430679829)
                      ·
                        rfl

theorem cell23_664869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_664869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_664869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_664869 prefixEnd_664869 := by exact prefixLift 664869
  have htrace : WordTrace (prefixWord ++ tailWord_664869) baseStart_664869 baseEnd_664869 := by
    simpa [prefixWord, tailWord_664869, baseEnd_664869] using wordTrace_append hprefix tailTrace_664869
  have hstable : (prefixWord ++ tailWord_664869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664869).length < 2 ^ (prefixWord ++ tailWord_664869).sum := by decide
  have hdescent : baseEnd_664869 < baseStart_664869 := by decide
  rcases family_descends (prefixWord ++ tailWord_664869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664980 : List Nat := [2, 4, 2, 1, 2, 1, 3, 1, 2, 3, 2]
def baseStart_664980 : Nat := 118140960795 + 664980 * 2 ^ 59
def prefixEnd_664980 : Nat := 4983230072969 + 3 ^ 40 * 664980 * 2
def baseEnd_664980 : Nat := 341454365626913496391819

theorem tailTrace_664980 : CollatzResearch.WordTrace tailWord_664980 prefixEnd_664980 341454365626913496391819 := by
  unfold tailWord_664980
  simp only [CollatzResearch.WordTrace]
  refine ⟨12126906565449252193688197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16169208753932336258250929 12126906565449252193688197)
  ·
    refine ⟨2273794981021734786316537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12126906565449252193688197 2273794981021734786316537)
    ·
      refine ⟨1705346235766301089737403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2273794981021734786316537 1705346235766301089737403)
      ·
        refine ⟨2558019353649451634606105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1705346235766301089737403 2558019353649451634606105)
        ·
          refine ⟨1918514515237088725954579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2558019353649451634606105 1918514515237088725954579)
          ·
            refine ⟨2877771772855633088931869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1918514515237088725954579 2877771772855633088931869)
            ·
              refine ⟨1079164414820862408349451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2877771772855633088931869 1079164414820862408349451)
              ·
                refine ⟨1618746622231293612524177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1079164414820862408349451 1618746622231293612524177)
                ·
                  refine ⟨1214059966673470209393133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1618746622231293612524177 1214059966673470209393133)
                  ·
                    refine ⟨455272487502551328522425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1214059966673470209393133 455272487502551328522425)
                    ·
                      refine ⟨341454365626913496391819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 455272487502551328522425 341454365626913496391819)
                      ·
                        rfl

theorem cell23_664980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_664980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_664980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_664980 prefixEnd_664980 := by exact prefixLift 664980
  have htrace : WordTrace (prefixWord ++ tailWord_664980) baseStart_664980 baseEnd_664980 := by
    simpa [prefixWord, tailWord_664980, baseEnd_664980] using wordTrace_append hprefix tailTrace_664980
  have hstable : (prefixWord ++ tailWord_664980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664980).length < 2 ^ (prefixWord ++ tailWord_664980).sum := by decide
  have hdescent : baseEnd_664980 < baseStart_664980 := by decide
  rcases family_descends (prefixWord ++ tailWord_664980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664986 : List Nat := [3, 1, 1, 4, 1, 1, 2, 2, 4, 4]
def baseStart_664986 : Nat := 118140960795 + 664986 * 2 ^ 59
def prefixEnd_664986 : Nat := 4983230072969 + 3 ^ 40 * 664986 * 2
def baseEnd_664986 : Nat := 113819148836946824305597

theorem tailTrace_664986 : CollatzResearch.WordTrace tailWord_664986 prefixEnd_664986 113819148836946824305597 := by
  unfold tailWord_664986
  simp only [CollatzResearch.WordTrace]
  refine ⟨6063507992219191853023703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16169354645917844941396541 6063507992219191853023703)
  ·
    refine ⟨9095261988328787779535555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6063507992219191853023703 9095261988328787779535555)
    ·
      refine ⟨13642892982493181669303333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9095261988328787779535555 13642892982493181669303333)
      ·
        refine ⟨2558042434217471562994375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13642892982493181669303333 2558042434217471562994375)
        ·
          refine ⟨3837063651326207344491563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2558042434217471562994375 3837063651326207344491563)
          ·
            refine ⟨5755595476989311016737345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3837063651326207344491563 5755595476989311016737345)
            ·
              refine ⟨4316696607741983262553009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5755595476989311016737345 4316696607741983262553009)
              ·
                refine ⟨3237522455806487446914757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4316696607741983262553009 3237522455806487446914757)
                ·
                  refine ⟨607035460463716396296517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3237522455806487446914757 607035460463716396296517)
                  ·
                    refine ⟨113819148836946824305597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 607035460463716396296517 113819148836946824305597)
                    ·
                      rfl

theorem cell23_664986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 4, 4].length) (baseStart_664986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_664986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_664986 prefixEnd_664986 := by exact prefixLift 664986
  have htrace : WordTrace (prefixWord ++ tailWord_664986) baseStart_664986 baseEnd_664986 := by
    simpa [prefixWord, tailWord_664986, baseEnd_664986] using wordTrace_append hprefix tailTrace_664986
  have hstable : (prefixWord ++ tailWord_664986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664986).length < 2 ^ (prefixWord ++ tailWord_664986).sum := by decide
  have hdescent : baseEnd_664986 < baseStart_664986 := by decide
  rcases family_descends (prefixWord ++ tailWord_664986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664990 : List Nat := [4, 3, 1, 2, 2, 1, 1, 3, 1, 5]
def baseStart_664990 : Nat := 118140960795 + 664990 * 2 ^ 59
def prefixEnd_664990 : Nat := 4983230072969 + 3 ^ 40 * 664990 * 2
def baseEnd_664990 : Nat := 113819833477819485755591

theorem tailTrace_664990 : CollatzResearch.WordTrace tailWord_664990 prefixEnd_664990 113819833477819485755591 := by
  unfold tailWord_664990
  simp only [CollatzResearch.WordTrace]
  refine ⟨3031772232607784511905053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16169451907241517396826949 3031772232607784511905053)
  ·
    refine ⟨1136914587227919191964395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3031772232607784511905053 1136914587227919191964395)
    ·
      refine ⟨1705371880841878787946593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1136914587227919191964395 1705371880841878787946593)
      ·
        refine ⟨1279028910631409090959945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1705371880841878787946593 1279028910631409090959945)
        ·
          refine ⟨959271682973556818219959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1279028910631409090959945 959271682973556818219959)
          ·
            refine ⟨1438907524460335227329939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 959271682973556818219959 1438907524460335227329939)
            ·
              refine ⟨2158361286690502840994909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1438907524460335227329939 2158361286690502840994909)
              ·
                refine ⟨809385482508938565373091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2158361286690502840994909 809385482508938565373091)
                ·
                  refine ⟨1214078223763407848059637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 809385482508938565373091 1214078223763407848059637)
                  ·
                    refine ⟨113819833477819485755591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1214078223763407848059637 113819833477819485755591)
                    ·
                      rfl

theorem cell23_664990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_664990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_664990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_664990 prefixEnd_664990 := by exact prefixLift 664990
  have htrace : WordTrace (prefixWord ++ tailWord_664990) baseStart_664990 baseEnd_664990 := by
    simpa [prefixWord, tailWord_664990, baseEnd_664990] using wordTrace_append hprefix tailTrace_664990
  have hstable : (prefixWord ++ tailWord_664990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664990).length < 2 ^ (prefixWord ++ tailWord_664990).sum := by decide
  have hdescent : baseEnd_664990 < baseStart_664990 := by decide
  rcases family_descends (prefixWord ++ tailWord_664990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_664999 : List Nat := [1, 1, 6, 1, 1, 1, 12]
def baseStart_664999 : Nat := 118140960795 + 664999 * 2 ^ 59
def prefixEnd_664999 : Nat := 4983230072969 + 3 ^ 40 * 664999 * 2
def baseEnd_664999 : Nat := 4215606441473443482151

theorem tailTrace_664999 : CollatzResearch.WordTrace tailWord_664999 prefixEnd_664999 4215606441473443482151 := by
  unfold tailWord_664999
  simp only [CollatzResearch.WordTrace]
  refine ⟨24254506117829670632318051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16169670745219780421545367 24254506117829670632318051)
  ·
    refine ⟨36381759176744505948477077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24254506117829670632318051 36381759176744505948477077)
    ·
      refine ⟨1705394961409898716334863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 36381759176744505948477077 1705394961409898716334863)
      ·
        refine ⟨2558092442114848074502295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1705394961409898716334863 2558092442114848074502295)
        ·
          refine ⟨3837138663172272111753443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2558092442114848074502295 3837138663172272111753443)
          ·
            refine ⟨5755707994758408167630165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3837138663172272111753443 5755707994758408167630165)
            ·
              refine ⟨4215606441473443482151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 5755707994758408167630165 4215606441473443482151)
              ·
                rfl

theorem cell23_664999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 12].length) (baseStart_664999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_664999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_664999 prefixEnd_664999 := by exact prefixLift 664999
  have htrace : WordTrace (prefixWord ++ tailWord_664999) baseStart_664999 baseEnd_664999 := by
    simpa [prefixWord, tailWord_664999, baseEnd_664999] using wordTrace_append hprefix tailTrace_664999
  have hstable : (prefixWord ++ tailWord_664999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_664999).length < 2 ^ (prefixWord ++ tailWord_664999).sum := by decide
  have hdescent : baseEnd_664999 < baseStart_664999 := by decide
  rcases family_descends (prefixWord ++ tailWord_664999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665020 : List Nat := [2, 2, 2, 4, 3, 1, 1, 1, 1, 6]
def baseStart_665020 : Nat := 118140960795 + 665020 * 2 ^ 59
def prefixEnd_665020 : Nat := 4983230072969 + 3 ^ 40 * 665020 * 2
def baseEnd_665020 : Nat := 113824968284364446630545

theorem tailTrace_665020 : CollatzResearch.WordTrace tailWord_665020 prefixEnd_665020 113824968284364446630545 := by
  unfold tailWord_665020
  simp only [CollatzResearch.WordTrace]
  refine ⟨12127636025376795609416257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16170181367169060812555009 12127636025376795609416257)
  ·
    refine ⟨9095727019032596707062193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12127636025376795609416257 9095727019032596707062193)
    ·
      refine ⟨6821795264274447530296645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9095727019032596707062193 6821795264274447530296645)
      ·
        refine ⟨1279086612051458911930621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6821795264274447530296645 1279086612051458911930621)
        ·
          refine ⟨479657479519297091973983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1279086612051458911930621 479657479519297091973983)
          ·
            refine ⟨719486219278945637960975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 479657479519297091973983 719486219278945637960975)
            ·
              refine ⟨1079229328918418456941463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 719486219278945637960975 1079229328918418456941463)
              ·
                refine ⟨1618843993377627685412195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1079229328918418456941463 1618843993377627685412195)
                ·
                  refine ⟨2428265990066441528118293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1618843993377627685412195 2428265990066441528118293)
                  ·
                    refine ⟨113824968284364446630545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2428265990066441528118293 113824968284364446630545)
                    ·
                      rfl

theorem cell23_665020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 1, 6].length) (baseStart_665020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_665020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_665020 prefixEnd_665020 := by exact prefixLift 665020
  have htrace : WordTrace (prefixWord ++ tailWord_665020) baseStart_665020 baseEnd_665020 := by
    simpa [prefixWord, tailWord_665020, baseEnd_665020] using wordTrace_append hprefix tailTrace_665020
  have hstable : (prefixWord ++ tailWord_665020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665020).length < 2 ^ (prefixWord ++ tailWord_665020).sum := by decide
  have hdescent : baseEnd_665020 < baseStart_665020 := by decide
  rcases family_descends (prefixWord ++ tailWord_665020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665039 : List Nat := [1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 5]
def baseStart_665039 : Nat := 118140960795 + 665039 * 2 ^ 59
def prefixEnd_665039 : Nat := 4983230072969 + 3 ^ 40 * 665039 * 2
def baseEnd_665039 : Nat := 341484660985528765554047

theorem tailTrace_665039 : CollatzResearch.WordTrace tailWord_665039 prefixEnd_665039 341484660985528765554047 := by
  unfold tailWord_665039
  simp only [CollatzResearch.WordTrace]
  refine ⟨24255965037684757463774171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16170643358456504975849447 24255965037684757463774171)
  ·
    refine ⟨36383947556527136195661257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24255965037684757463774171 36383947556527136195661257)
    ·
      refine ⟨27287960667395352146745943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36383947556527136195661257 27287960667395352146745943)
      ·
        refine ⟨40931941001093028220118915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27287960667395352146745943 40931941001093028220118915)
        ·
          refine ⟨61397911501639542330178373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40931941001093028220118915 61397911501639542330178373)
          ·
            refine ⟨11512108406557414186908445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61397911501639542330178373 11512108406557414186908445)
            ·
              refine ⟨4317040652459030320090667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11512108406557414186908445 4317040652459030320090667)
              ·
                refine ⟨6475560978688545480136001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4317040652459030320090667 6475560978688545480136001)
                ·
                  refine ⟨4856670734016409110102001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6475560978688545480136001 4856670734016409110102001)
                  ·
                    refine ⟨3642503050512306832576501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4856670734016409110102001 3642503050512306832576501)
                    ·
                      refine ⟨341484660985528765554047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3642503050512306832576501 341484660985528765554047)
                      ·
                        rfl

theorem cell23_665039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 5].length) (baseStart_665039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_665039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_665039 prefixEnd_665039 := by exact prefixLift 665039
  have htrace : WordTrace (prefixWord ++ tailWord_665039) baseStart_665039 baseEnd_665039 := by
    simpa [prefixWord, tailWord_665039, baseEnd_665039] using wordTrace_append hprefix tailTrace_665039
  have hstable : (prefixWord ++ tailWord_665039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665039).length < 2 ^ (prefixWord ++ tailWord_665039).sum := by decide
  have hdescent : baseEnd_665039 < baseStart_665039 := by decide
  rcases family_descends (prefixWord ++ tailWord_665039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665077 : List Nat := [1, 3, 5, 1, 1, 2, 1, 3, 2, 1, 3]
def baseStart_665077 : Nat := 118140960795 + 665077 * 2 ^ 59
def prefixEnd_665077 : Nat := 4983230072969 + 3 ^ 40 * 665077 * 2
def baseEnd_665077 : Nat := 341504173250399616878873

theorem tailTrace_665077 : CollatzResearch.WordTrace tailWord_665077 prefixEnd_665077 341504173250399616878873 := by
  unfold tailWord_665077
  simp only [CollatzResearch.WordTrace]
  refine ⟨24257351011547089953657485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16171567341031393302438323 24257351011547089953657485)
  ·
    refine ⟨9096506629330158732621557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24257351011547089953657485 9096506629330158732621557)
    ·
      refine ⟨852797496499702381183271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9096506629330158732621557 852797496499702381183271)
      ·
        refine ⟨1279196244749553571774907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 852797496499702381183271 1279196244749553571774907)
        ·
          refine ⟨1918794367124330357662361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1279196244749553571774907 1918794367124330357662361)
          ·
            refine ⟨1439095775343247768246771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1918794367124330357662361 1439095775343247768246771)
            ·
              refine ⟨2158643663014871652370157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1439095775343247768246771 2158643663014871652370157)
              ·
                refine ⟨809491373630576869638809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2158643663014871652370157 809491373630576869638809)
                ·
                  refine ⟨607118530222932652229107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 809491373630576869638809 607118530222932652229107)
                  ·
                    refine ⟨910677795334398978343661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 607118530222932652229107 910677795334398978343661)
                    ·
                      refine ⟨341504173250399616878873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 910677795334398978343661 341504173250399616878873)
                      ·
                        rfl

theorem cell23_665077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_665077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_665077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_665077 prefixEnd_665077 := by exact prefixLift 665077
  have htrace : WordTrace (prefixWord ++ tailWord_665077) baseStart_665077 baseEnd_665077 := by
    simpa [prefixWord, tailWord_665077, baseEnd_665077] using wordTrace_append hprefix tailTrace_665077
  have hstable : (prefixWord ++ tailWord_665077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665077).length < 2 ^ (prefixWord ++ tailWord_665077).sum := by decide
  have hdescent : baseEnd_665077 < baseStart_665077 := by decide
  rcases family_descends (prefixWord ++ tailWord_665077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665094 : List Nat := [6, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3]
def baseStart_665094 : Nat := 118140960795 + 665094 * 2 ^ 59
def prefixEnd_665094 : Nat := 4983230072969 + 3 ^ 40 * 665094 * 2
def baseEnd_665094 : Nat := 341512902421526050366295

theorem tailTrace_665094 : CollatzResearch.WordTrace tailWord_665094 prefixEnd_665094 341512902421526050366295 := by
  unfold tailWord_665094
  simp only [CollatzResearch.WordTrace]
  refine ⟨758061595390171933032073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16171980701657001238017557 758061595390171933032073)
  ·
    refine ⟨568546196542628949774055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 758061595390171933032073 568546196542628949774055)
    ·
      refine ⟨852819294813943424661083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 568546196542628949774055 852819294813943424661083)
      ·
        refine ⟨1279228942220915136991625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 852819294813943424661083 1279228942220915136991625)
        ·
          refine ⟨959421706665686352743719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1279228942220915136991625 959421706665686352743719)
          ·
            refine ⟨1439132559998529529115579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 959421706665686352743719 1439132559998529529115579)
            ·
              refine ⟨2158698839997794293673369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1439132559998529529115579 2158698839997794293673369)
              ·
                refine ⟨1619024129998345720255027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2158698839997794293673369 1619024129998345720255027)
                ·
                  refine ⟨2428536194997518580382541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1619024129998345720255027 2428536194997518580382541)
                  ·
                    refine ⟨910701073124069467643453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2428536194997518580382541 910701073124069467643453)
                    ·
                      refine ⟨341512902421526050366295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 910701073124069467643453 341512902421526050366295)
                      ·
                        rfl

theorem cell23_665094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_665094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_665094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_665094 prefixEnd_665094 := by exact prefixLift 665094
  have htrace : WordTrace (prefixWord ++ tailWord_665094) baseStart_665094 baseEnd_665094 := by
    simpa [prefixWord, tailWord_665094, baseEnd_665094] using wordTrace_append hprefix tailTrace_665094
  have hstable : (prefixWord ++ tailWord_665094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665094).length < 2 ^ (prefixWord ++ tailWord_665094).sum := by decide
  have hdescent : baseEnd_665094 < baseStart_665094 := by decide
  rcases family_descends (prefixWord ++ tailWord_665094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665100 : List Nat := [2, 2, 1, 2, 5, 1, 1, 2, 1, 4, 2]
def baseStart_665100 : Nat := 118140960795 + 665100 * 2 ^ 59
def prefixEnd_665100 : Nat := 4983230072969 + 3 ^ 40 * 665100 * 2
def baseEnd_665100 : Nat := 341515983305453026891267

theorem tailTrace_665100 : CollatzResearch.WordTrace tailWord_665100 prefixEnd_665100 341515983305453026891267 := by
  unfold tailWord_665100
  simp only [CollatzResearch.WordTrace]
  refine ⟨12129094945231882440872377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16172126593642509921163169 12129094945231882440872377)
  ·
    refine ⟨9096821208923911830654283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12129094945231882440872377 9096821208923911830654283)
    ·
      refine ⟨13645231813385867745981425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9096821208923911830654283 13645231813385867745981425)
      ·
        refine ⟨10233923860039400809486069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13645231813385867745981425 10233923860039400809486069)
        ·
          refine ⟨959430361878693825889319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10233923860039400809486069 959430361878693825889319)
          ·
            refine ⟨1439145542818040738833979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 959430361878693825889319 1439145542818040738833979)
            ·
              refine ⟨2158718314227061108250969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1439145542818040738833979 2158718314227061108250969)
              ·
                refine ⟨1619038735670295831188227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2158718314227061108250969 1619038735670295831188227)
                ·
                  refine ⟨2428558103505443746782341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1619038735670295831188227 2428558103505443746782341)
                  ·
                    refine ⟨455354644407270702521689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2428558103505443746782341 455354644407270702521689)
                    ·
                      refine ⟨341515983305453026891267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 455354644407270702521689 341515983305453026891267)
                      ·
                        rfl

theorem cell23_665100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 1, 4, 2].length) (baseStart_665100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_665100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_665100 prefixEnd_665100 := by exact prefixLift 665100
  have htrace : WordTrace (prefixWord ++ tailWord_665100) baseStart_665100 baseEnd_665100 := by
    simpa [prefixWord, tailWord_665100, baseEnd_665100] using wordTrace_append hprefix tailTrace_665100
  have hstable : (prefixWord ++ tailWord_665100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665100).length < 2 ^ (prefixWord ++ tailWord_665100).sum := by decide
  have hdescent : baseEnd_665100 < baseStart_665100 := by decide
  rcases family_descends (prefixWord ++ tailWord_665100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665117 : List Nat := [1, 4, 2, 2, 1, 1, 4, 2, 2, 2, 2]
def baseStart_665117 : Nat := 118140960795 + 665117 * 2 ^ 59
def prefixEnd_665117 : Nat := 4983230072969 + 3 ^ 40 * 665117 * 2
def baseEnd_665117 : Nat := 341524712476579460378689

theorem tailTrace_665117 : CollatzResearch.WordTrace tailWord_665117 prefixEnd_665117 341524712476579460378689 := by
  unfold tailWord_665117
  simp only [CollatzResearch.WordTrace]
  refine ⟨24258809931402176785113605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16172539954268117856742403 24258809931402176785113605)
  ·
    refine ⟨4548526862137908147208801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24258809931402176785113605 4548526862137908147208801)
    ·
      refine ⟨3411395146603431110406601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4548526862137908147208801 3411395146603431110406601)
      ·
        refine ⟨2558546359952573332804951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3411395146603431110406601 2558546359952573332804951)
        ·
          refine ⟨3837819539928859999207427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2558546359952573332804951 3837819539928859999207427)
          ·
            refine ⟨5756729309893289998811141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3837819539928859999207427 5756729309893289998811141)
            ·
              refine ⟨1079386745604991874777089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5756729309893289998811141 1079386745604991874777089)
              ·
                refine ⟨809540059203743906082817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1079386745604991874777089 809540059203743906082817)
                ·
                  refine ⟨607155044402807929562113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 809540059203743906082817 607155044402807929562113)
                  ·
                    refine ⟨455366283302105947171585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 607155044402807929562113 455366283302105947171585)
                    ·
                      refine ⟨341524712476579460378689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 455366283302105947171585 341524712476579460378689)
                      ·
                        rfl

theorem cell23_665117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_665117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_665117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_665117 prefixEnd_665117 := by exact prefixLift 665117
  have htrace : WordTrace (prefixWord ++ tailWord_665117) baseStart_665117 baseEnd_665117 := by
    simpa [prefixWord, tailWord_665117, baseEnd_665117] using wordTrace_append hprefix tailTrace_665117
  have hstable : (prefixWord ++ tailWord_665117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665117).length < 2 ^ (prefixWord ++ tailWord_665117).sum := by decide
  have hdescent : baseEnd_665117 < baseStart_665117 := by decide
  rcases family_descends (prefixWord ++ tailWord_665117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665217 : List Nat := [1, 2, 4, 2, 1, 2, 3, 3, 1, 4]
def baseStart_665217 : Nat := 118140960795 + 665217 * 2 ^ 59
def prefixEnd_665217 : Nat := 4983230072969 + 3 ^ 40 * 665217 * 2
def baseEnd_665217 : Nat := 113858686847343023042743

theorem tailTrace_665217 : CollatzResearch.WordTrace tailWord_665217 prefixEnd_665217 113858686847343023042743 := by
  unfold tailWord_665217
  simp only [CollatzResearch.WordTrace]
  refine ⟨24262457231039893863753905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16174971487359929242502603 24262457231039893863753905)
  ·
    refine ⟨18196842923279920397815429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24262457231039893863753905 18196842923279920397815429)
    ·
      refine ⟨3411908048114985074590393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18196842923279920397815429 3411908048114985074590393)
      ·
        refine ⟨2558931036086238805942795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3411908048114985074590393 2558931036086238805942795)
        ·
          refine ⟨3838396554129358208914193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2558931036086238805942795 3838396554129358208914193)
          ·
            refine ⟨2878797415597018656685645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3838396554129358208914193 2878797415597018656685645)
            ·
              refine ⟨1079549030848881996257117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2878797415597018656685645 1079549030848881996257117)
              ·
                refine ⟨404830886568330748596419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1079549030848881996257117 404830886568330748596419)
                ·
                  refine ⟨607246329852496122894629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 404830886568330748596419 607246329852496122894629)
                  ·
                    refine ⟨113858686847343023042743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 607246329852496122894629 113858686847343023042743)
                    ·
                      rfl

theorem cell23_665217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_665217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_665217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_665217 prefixEnd_665217 := by exact prefixLift 665217
  have htrace : WordTrace (prefixWord ++ tailWord_665217) baseStart_665217 baseEnd_665217 := by
    simpa [prefixWord, tailWord_665217, baseEnd_665217] using wordTrace_append hprefix tailTrace_665217
  have hstable : (prefixWord ++ tailWord_665217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665217).length < 2 ^ (prefixWord ++ tailWord_665217).sum := by decide
  have hdescent : baseEnd_665217 < baseStart_665217 := by decide
  rcases family_descends (prefixWord ++ tailWord_665217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665233 : List Nat := [1, 2, 2, 1, 1, 1, 1, 4, 3, 5, 2]
def baseStart_665233 : Nat := 118140960795 + 665233 * 2 ^ 59
def prefixEnd_665233 : Nat := 4983230072969 + 3 ^ 40 * 665233 * 2
def baseEnd_665233 : Nat := 341584276232501006528155

theorem tailTrace_665233 : CollatzResearch.WordTrace tailWord_665233 prefixEnd_665233 341584276232501006528155 := by
  unfold tailWord_665233
  simp only [CollatzResearch.WordTrace]
  refine ⟨24263040798981928596336353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16175360532654619064224235 24263040798981928596336353)
  ·
    refine ⟨18197280599236446447252265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24263040798981928596336353 18197280599236446447252265)
    ·
      refine ⟨13647960449427334835439199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18197280599236446447252265 13647960449427334835439199)
      ·
        refine ⟨20471940674141002253158799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13647960449427334835439199 20471940674141002253158799)
        ·
          refine ⟨30707911011211503379738199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20471940674141002253158799 30707911011211503379738199)
          ·
            refine ⟨46061866516817255069607299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30707911011211503379738199 46061866516817255069607299)
            ·
              refine ⟨69092799775225882604410949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46061866516817255069607299 69092799775225882604410949)
              ·
                refine ⟨12954899957854852988327053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69092799775225882604410949 12954899957854852988327053)
                ·
                  refine ⟨4858087484195569870622645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12954899957854852988327053 4858087484195569870622645)
                  ·
                    refine ⟨455445701643334675370873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4858087484195569870622645 455445701643334675370873)
                    ·
                      refine ⟨341584276232501006528155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 455445701643334675370873 341584276232501006528155)
                      ·
                        rfl

theorem cell23_665233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 5, 2].length) (baseStart_665233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_665233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_665233 prefixEnd_665233 := by exact prefixLift 665233
  have htrace : WordTrace (prefixWord ++ tailWord_665233) baseStart_665233 baseEnd_665233 := by
    simpa [prefixWord, tailWord_665233, baseEnd_665233] using wordTrace_append hprefix tailTrace_665233
  have hstable : (prefixWord ++ tailWord_665233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665233).length < 2 ^ (prefixWord ++ tailWord_665233).sum := by decide
  have hdescent : baseEnd_665233 < baseStart_665233 := by decide
  rcases family_descends (prefixWord ++ tailWord_665233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665234 : List Nat := [3, 2, 3, 1, 4, 1, 1, 1, 3, 4]
def baseStart_665234 : Nat := 118140960795 + 665234 * 2 ^ 59
def prefixEnd_665234 : Nat := 4983230072969 + 3 ^ 40 * 665234 * 2
def baseEnd_665234 : Nat := 113861596571051834205217

theorem tailTrace_665234 : CollatzResearch.WordTrace tailWord_665234 prefixEnd_665234 113861596571051834205217 := by
  unfold tailWord_665234
  simp only [CollatzResearch.WordTrace]
  refine ⟨6065769317994576441780689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16175384847985537178081837 6065769317994576441780689)
  ·
    refine ⟨4549326988495932331335517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6065769317994576441780689 4549326988495932331335517)
    ·
      refine ⟨1705997620685974624250819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4549326988495932331335517 1705997620685974624250819)
      ·
        refine ⟨2558996431028961936376229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1705997620685974624250819 2558996431028961936376229)
        ·
          refine ⟨479811830817930363070543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2558996431028961936376229 479811830817930363070543)
          ·
            refine ⟨719717746226895544605815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 479811830817930363070543 719717746226895544605815)
            ·
              refine ⟨1079576619340343316908723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 719717746226895544605815 1079576619340343316908723)
              ·
                refine ⟨1619364929010514975363085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1079576619340343316908723 1619364929010514975363085)
                ·
                  refine ⟨607261848378943115761157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1619364929010514975363085 607261848378943115761157)
                  ·
                    refine ⟨113861596571051834205217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 607261848378943115761157 113861596571051834205217)
                    ·
                      rfl

theorem cell23_665234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_665234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_665234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_665234 prefixEnd_665234 := by exact prefixLift 665234
  have htrace : WordTrace (prefixWord ++ tailWord_665234) baseStart_665234 baseEnd_665234 := by
    simpa [prefixWord, tailWord_665234, baseEnd_665234] using wordTrace_append hprefix tailTrace_665234
  have hstable : (prefixWord ++ tailWord_665234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665234).length < 2 ^ (prefixWord ++ tailWord_665234).sum := by decide
  have hdescent : baseEnd_665234 < baseStart_665234 := by decide
  rcases family_descends (prefixWord ++ tailWord_665234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665263 : List Nat := [1, 1, 2, 1, 2, 4, 3, 1, 3, 1, 4]
def baseStart_665263 : Nat := 118140960795 + 665263 * 2 ^ 59
def prefixEnd_665263 : Nat := 4983230072969 + 3 ^ 40 * 665263 * 2
def baseEnd_665263 : Nat := 341599680652135889153017

theorem tailTrace_665263 : CollatzResearch.WordTrace tailWord_665263 prefixEnd_665263 341599680652135889153017 := by
  unfold tailWord_665263
  simp only [CollatzResearch.WordTrace]
  refine ⟨24264134988873243719928443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16176089992582162479952295 24264134988873243719928443)
  ·
    refine ⟨36396202483309865579892665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24264134988873243719928443 36396202483309865579892665)
    ·
      refine ⟨27297151862482399184919499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36396202483309865579892665 27297151862482399184919499)
      ·
        refine ⟨40945727793723598777379249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27297151862482399184919499 40945727793723598777379249)
        ·
          refine ⟨30709295845292699083034437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40945727793723598777379249 30709295845292699083034437)
          ·
            refine ⟨5757992970992381078068957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30709295845292699083034437 5757992970992381078068957)
            ·
              refine ⟨2159247364122142904275859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5757992970992381078068957 2159247364122142904275859)
              ·
                refine ⟨3238871046183214356413789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2159247364122142904275859 3238871046183214356413789)
                ·
                  refine ⟨1214576642318705383655171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3238871046183214356413789 1214576642318705383655171)
                  ·
                    refine ⟨1821864963478058075482757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1214576642318705383655171 1821864963478058075482757)
                    ·
                      refine ⟨341599680652135889153017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1821864963478058075482757 341599680652135889153017)
                      ·
                        rfl

theorem cell23_665263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 3, 1, 4].length) (baseStart_665263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_665263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_665263 prefixEnd_665263 := by exact prefixLift 665263
  have htrace : WordTrace (prefixWord ++ tailWord_665263) baseStart_665263 baseEnd_665263 := by
    simpa [prefixWord, tailWord_665263, baseEnd_665263] using wordTrace_append hprefix tailTrace_665263
  have hstable : (prefixWord ++ tailWord_665263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665263).length < 2 ^ (prefixWord ++ tailWord_665263).sum := by decide
  have hdescent : baseEnd_665263 < baseStart_665263 := by decide
  rcases family_descends (prefixWord ++ tailWord_665263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665273 : List Nat := [1, 2, 1, 4, 1, 1, 2, 1, 6, 4]
def baseStart_665273 : Nat := 118140960795 + 665273 * 2 ^ 59
def prefixEnd_665273 : Nat := 4983230072969 + 3 ^ 40 * 665273 * 2
def baseEnd_665273 : Nat := 113868271819560283342657

theorem tailTrace_665273 : CollatzResearch.WordTrace tailWord_665273 prefixEnd_665273 113868271819560283342657 := by
  unfold tailWord_665273
  simp only [CollatzResearch.WordTrace]
  refine ⟨24264499718837015427792473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16176333145891343618528315 24264499718837015427792473)
  ·
    refine ⟨18198374789127761570844355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24264499718837015427792473 18198374789127761570844355)
    ·
      refine ⟨27297562183691642356266533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18198374789127761570844355 27297562183691642356266533)
      ·
        refine ⟨5118292909442182941799975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27297562183691642356266533 5118292909442182941799975)
        ·
          refine ⟨7677439364163274412699963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5118292909442182941799975 7677439364163274412699963)
          ·
            refine ⟨11516159046244911619049945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7677439364163274412699963 11516159046244911619049945)
            ·
              refine ⟨8637119284683683714287459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11516159046244911619049945 8637119284683683714287459)
              ·
                refine ⟨12955678927025525571431189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8637119284683683714287459 12955678927025525571431189)
                ·
                  refine ⟨607297449704321511160837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 12955678927025525571431189 607297449704321511160837)
                  ·
                    refine ⟨113868271819560283342657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 607297449704321511160837 113868271819560283342657)
                    ·
                      rfl

theorem cell23_665273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 6, 4].length) (baseStart_665273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_665273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_665273 prefixEnd_665273 := by exact prefixLift 665273
  have htrace : WordTrace (prefixWord ++ tailWord_665273) baseStart_665273 baseEnd_665273 := by
    simpa [prefixWord, tailWord_665273, baseEnd_665273] using wordTrace_append hprefix tailTrace_665273
  have hstable : (prefixWord ++ tailWord_665273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665273).length < 2 ^ (prefixWord ++ tailWord_665273).sum := by decide
  have hdescent : baseEnd_665273 < baseStart_665273 := by decide
  rcases family_descends (prefixWord ++ tailWord_665273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665296 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 7]
def baseStart_665296 : Nat := 118140960795 + 665296 * 2 ^ 59
def prefixEnd_665296 : Nat := 4983230072969 + 3 ^ 40 * 665296 * 2
def baseEnd_665296 : Nat := 341616625513734260040365

theorem tailTrace_665296 : CollatzResearch.WordTrace tailWord_665296 prefixEnd_665296 341616625513734260040365 := by
  unfold tailWord_665296
  simp only [CollatzResearch.WordTrace]
  refine ⟨12132669298876845177939871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16176892398502460237253161 12132669298876845177939871)
  ·
    refine ⟨18199003948315267766909807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12132669298876845177939871 18199003948315267766909807)
    ·
      refine ⟨27298505922472901650364711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18199003948315267766909807 27298505922472901650364711)
      ·
        refine ⟨40947758883709352475547067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27298505922472901650364711 40947758883709352475547067)
        ·
          refine ⟨61421638325564028713320601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40947758883709352475547067 61421638325564028713320601)
          ·
            refine ⟨46066228744173021534990451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61421638325564028713320601 46066228744173021534990451)
            ·
              refine ⟨69099343116259532302485677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46066228744173021534990451 69099343116259532302485677)
              ·
                refine ⟨25912253668597324613432129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69099343116259532302485677 25912253668597324613432129)
                ·
                  refine ⟨19434190251447993460074097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25912253668597324613432129 19434190251447993460074097)
                  ·
                    refine ⟨14575642688585995095055573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19434190251447993460074097 14575642688585995095055573)
                    ·
                      refine ⟨341616625513734260040365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 14575642688585995095055573 341616625513734260040365)
                      ·
                        rfl

theorem cell23_665296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 7].length) (baseStart_665296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_665296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_665296 prefixEnd_665296 := by exact prefixLift 665296
  have htrace : WordTrace (prefixWord ++ tailWord_665296) baseStart_665296 baseEnd_665296 := by
    simpa [prefixWord, tailWord_665296, baseEnd_665296] using wordTrace_append hprefix tailTrace_665296
  have hstable : (prefixWord ++ tailWord_665296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665296).length < 2 ^ (prefixWord ++ tailWord_665296).sum := by decide
  have hdescent : baseEnd_665296 < baseStart_665296 := by decide
  rcases family_descends (prefixWord ++ tailWord_665296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665320 : List Nat := [2, 1, 4, 1, 3, 2, 3, 7]
def baseStart_665320 : Nat := 118140960795 + 665320 * 2 ^ 59
def prefixEnd_665320 : Nat := 4983230072969 + 3 ^ 40 * 665320 * 2
def baseEnd_665320 : Nat := 12652924038868228375565

theorem tailTrace_665320 : CollatzResearch.WordTrace tailWord_665320 prefixEnd_665320 12652924038868228375565 := by
  unfold tailWord_665320
  simp only [CollatzResearch.WordTrace]
  refine ⟨12133106974833371227376707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16177475966444494969835609 12133106974833371227376707)
  ·
    refine ⟨18199660462250056841065061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12133106974833371227376707 18199660462250056841065061)
    ·
      refine ⟨3412436336671885657699699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18199660462250056841065061 3412436336671885657699699)
      ·
        refine ⟨5118654505007828486549549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3412436336671885657699699 5118654505007828486549549)
        ·
          refine ⟨1919495439377935682456081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5118654505007828486549549 1919495439377935682456081)
          ·
            refine ⟨1439621579533451761842061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1919495439377935682456081 1439621579533451761842061)
            ·
              refine ⟨539858092325044410690773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1439621579533451761842061 539858092325044410690773)
              ·
                refine ⟨12652924038868228375565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 539858092325044410690773 12652924038868228375565)
                ·
                  rfl

theorem cell23_665320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 7].length) (baseStart_665320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_665320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_665320 prefixEnd_665320 := by exact prefixLift 665320
  have htrace : WordTrace (prefixWord ++ tailWord_665320) baseStart_665320 baseEnd_665320 := by
    simpa [prefixWord, tailWord_665320, baseEnd_665320] using wordTrace_append hprefix tailTrace_665320
  have hstable : (prefixWord ++ tailWord_665320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665320).length < 2 ^ (prefixWord ++ tailWord_665320).sum := by decide
  have hdescent : baseEnd_665320 < baseStart_665320 := by decide
  rcases family_descends (prefixWord ++ tailWord_665320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665330 : List Nat := [3, 2, 1, 3, 1, 1, 1, 4, 1, 3, 3]
def baseStart_665330 : Nat := 118140960795 + 665330 * 2 ^ 59
def prefixEnd_665330 : Nat := 4983230072969 + 3 ^ 40 * 665330 * 2
def baseEnd_665330 : Nat := 341634083855987127015209

theorem tailTrace_665330 : CollatzResearch.WordTrace tailWord_665330 prefixEnd_665330 341634083855987127015209 := by
  unfold tailWord_665330
  simp only [CollatzResearch.WordTrace]
  refine ⟨6066644669907628540654361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16177719119753676108411629 6066644669907628540654361)
  ·
    refine ⟨4549983502430721405490771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6066644669907628540654361 4549983502430721405490771)
    ·
      refine ⟨6824975253646082108236157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4549983502430721405490771 6824975253646082108236157)
      ·
        refine ⟨2559365720117280790588559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6824975253646082108236157 2559365720117280790588559)
        ·
          refine ⟨3839048580175921185882839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2559365720117280790588559 3839048580175921185882839)
          ·
            refine ⟨5758572870263881778824259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3839048580175921185882839 5758572870263881778824259)
            ·
              refine ⟨8637859305395822668236389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5758572870263881778824259 8637859305395822668236389)
              ·
                refine ⟨1619598619761716750294323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8637859305395822668236389 1619598619761716750294323)
                ·
                  refine ⟨2429397929642575125441485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1619598619761716750294323 2429397929642575125441485)
                  ·
                    refine ⟨911024223615965672040557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2429397929642575125441485 911024223615965672040557)
                    ·
                      refine ⟨341634083855987127015209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 911024223615965672040557 341634083855987127015209)
                      ·
                        rfl

theorem cell23_665330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_665330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_665330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_665330 prefixEnd_665330 := by exact prefixLift 665330
  have htrace : WordTrace (prefixWord ++ tailWord_665330) baseStart_665330 baseEnd_665330 := by
    simpa [prefixWord, tailWord_665330, baseEnd_665330] using wordTrace_append hprefix tailTrace_665330
  have hstable : (prefixWord ++ tailWord_665330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665330).length < 2 ^ (prefixWord ++ tailWord_665330).sum := by decide
  have hdescent : baseEnd_665330 < baseStart_665330 := by decide
  rcases family_descends (prefixWord ++ tailWord_665330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665334 : List Nat := [5, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3]
def baseStart_665334 : Nat := 118140960795 + 665334 * 2 ^ 59
def prefixEnd_665334 : Nat := 4983230072969 + 3 ^ 40 * 665334 * 2
def baseEnd_665334 : Nat := 341636137778605111365191

theorem tailTrace_665334 : CollatzResearch.WordTrace tailWord_665334 prefixEnd_665334 341636137778605111365191 := by
  unfold tailWord_665334
  simp only [CollatzResearch.WordTrace]
  refine ⟨1516670285726001427860191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16177816381077348563842037 1516670285726001427860191)
  ·
    refine ⟨2275005428589002141790287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1516670285726001427860191 2275005428589002141790287)
    ·
      refine ⟨3412508142883503212685431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2275005428589002141790287 3412508142883503212685431)
      ·
        refine ⟨5118762214325254819028147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3412508142883503212685431 5118762214325254819028147)
        ·
          refine ⟨7678143321487882228542221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5118762214325254819028147 7678143321487882228542221)
          ·
            refine ⟨2879303745557955835703333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7678143321487882228542221 2879303745557955835703333)
            ·
              refine ⟨539869452292116719194375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2879303745557955835703333 539869452292116719194375)
              ·
                refine ⟨809804178438175078791563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 539869452292116719194375 809804178438175078791563)
                ·
                  refine ⟨1214706267657262618187345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 809804178438175078791563 1214706267657262618187345)
                  ·
                    refine ⟨911029700742946963640509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1214706267657262618187345 911029700742946963640509)
                    ·
                      refine ⟨341636137778605111365191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 911029700742946963640509 341636137778605111365191)
                      ·
                        rfl

theorem cell23_665334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3].length) (baseStart_665334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_665334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_665334 prefixEnd_665334 := by exact prefixLift 665334
  have htrace : WordTrace (prefixWord ++ tailWord_665334) baseStart_665334 baseEnd_665334 := by
    simpa [prefixWord, tailWord_665334, baseEnd_665334] using wordTrace_append hprefix tailTrace_665334
  have hstable : (prefixWord ++ tailWord_665334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665334).length < 2 ^ (prefixWord ++ tailWord_665334).sum := by decide
  have hdescent : baseEnd_665334 < baseStart_665334 := by decide
  rcases family_descends (prefixWord ++ tailWord_665334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665347 : List Nat := [1, 1, 1, 3, 2, 2, 5, 2, 2, 1, 3]
def baseStart_665347 : Nat := 118140960795 + 665347 * 2 ^ 59
def prefixEnd_665347 : Nat := 4983230072969 + 3 ^ 40 * 665347 * 2
def baseEnd_665347 : Nat := 341642813027113560502631

theorem tailTrace_665347 : CollatzResearch.WordTrace tailWord_665347 prefixEnd_665347 341642813027113560502631 := by
  unfold tailWord_665347
  simp only [CollatzResearch.WordTrace]
  refine ⟨24267198720568926065986295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16178132480379284043990863 24267198720568926065986295)
  ·
    refine ⟨36400798080853389098979443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24267198720568926065986295 36400798080853389098979443)
    ·
      refine ⟨54601197121280083648469165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36400798080853389098979443 54601197121280083648469165)
      ·
        refine ⟨20475448920480031368175937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54601197121280083648469165 20475448920480031368175937)
        ·
          refine ⟨15356586690360023526131953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20475448920480031368175937 15356586690360023526131953)
          ·
            refine ⟨11517440017770017644598965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15356586690360023526131953 11517440017770017644598965)
            ·
              refine ⟨1079760001665939154181153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11517440017770017644598965 1079760001665939154181153)
              ·
                refine ⟨809820001249454365635865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1079760001665939154181153 809820001249454365635865)
                ·
                  refine ⟨607365000937090774226899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 809820001249454365635865 607365000937090774226899)
                  ·
                    refine ⟨911047501405636161340349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 607365000937090774226899 911047501405636161340349)
                    ·
                      refine ⟨341642813027113560502631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 911047501405636161340349 341642813027113560502631)
                      ·
                        rfl

theorem cell23_665347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 2, 2, 1, 3].length) (baseStart_665347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_665347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_665347 prefixEnd_665347 := by exact prefixLift 665347
  have htrace : WordTrace (prefixWord ++ tailWord_665347) baseStart_665347 baseEnd_665347 := by
    simpa [prefixWord, tailWord_665347, baseEnd_665347] using wordTrace_append hprefix tailTrace_665347
  have hstable : (prefixWord ++ tailWord_665347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665347).length < 2 ^ (prefixWord ++ tailWord_665347).sum := by decide
  have hdescent : baseEnd_665347 < baseStart_665347 := by decide
  rcases family_descends (prefixWord ++ tailWord_665347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665433 : List Nat := [1, 2, 1, 2, 2, 3, 1, 2, 1, 1, 7]
def baseStart_665433 : Nat := 118140960795 + 665433 * 2 ^ 59
def prefixEnd_665433 : Nat := 4983230072969 + 3 ^ 40 * 665433 * 2
def baseEnd_665433 : Nat := 341686972363400224027235

theorem tailTrace_665433 : CollatzResearch.WordTrace tailWord_665433 prefixEnd_665433 341686972363400224027235 := by
  unfold tailWord_665433
  simp only [CollatzResearch.WordTrace]
  refine ⟨24270335398257362753616953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16180223598838241835744635 24270335398257362753616953)
  ·
    refine ⟨18202751548693022065212715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24270335398257362753616953 18202751548693022065212715)
    ·
      refine ⟨27304127323039533097819073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18202751548693022065212715 27304127323039533097819073)
      ·
        refine ⟨20478095492279649823364305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27304127323039533097819073 20478095492279649823364305)
        ·
          refine ⟨15358571619209737367523229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20478095492279649823364305 15358571619209737367523229)
          ·
            refine ⟨5759464357203651512821211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15358571619209737367523229 5759464357203651512821211)
            ·
              refine ⟨8639196535805477269231817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5759464357203651512821211 8639196535805477269231817)
              ·
                refine ⟨6479397401854107951923863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8639196535805477269231817 6479397401854107951923863)
                ·
                  refine ⟨9719096102781161927885795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6479397401854107951923863 9719096102781161927885795)
                  ·
                    refine ⟨14578644154171742891828693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9719096102781161927885795 14578644154171742891828693)
                    ·
                      refine ⟨341686972363400224027235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 14578644154171742891828693 341686972363400224027235)
                      ·
                        rfl

theorem cell23_665433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 1, 7].length) (baseStart_665433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_665433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_665433 prefixEnd_665433 := by exact prefixLift 665433
  have htrace : WordTrace (prefixWord ++ tailWord_665433) baseStart_665433 baseEnd_665433 := by
    simpa [prefixWord, tailWord_665433, baseEnd_665433] using wordTrace_append hprefix tailTrace_665433
  have hstable : (prefixWord ++ tailWord_665433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665433).length < 2 ^ (prefixWord ++ tailWord_665433).sum := by decide
  have hdescent : baseEnd_665433 < baseStart_665433 := by decide
  rcases family_descends (prefixWord ++ tailWord_665433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665440 : List Nat := [2, 1, 1, 3, 3, 2, 1, 3, 2, 5]
def baseStart_665440 : Nat := 118140960795 + 665440 * 2 ^ 59
def prefixEnd_665440 : Nat := 4983230072969 + 3 ^ 40 * 665440 * 2
def baseEnd_665440 : Nat := 113896855575993898879901

theorem tailTrace_665440 : CollatzResearch.WordTrace tailWord_665440 prefixEnd_665440 113896855575993898879901 := by
  unfold tailWord_665440
  simp only [CollatzResearch.WordTrace]
  refine ⟨12135295354616001474560887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16180393806154668632747849 12135295354616001474560887)
  ·
    refine ⟨18202943031924002211841331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12135295354616001474560887 18202943031924002211841331)
    ·
      refine ⟨27304414547886003317761997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18202943031924002211841331 27304414547886003317761997)
      ·
        refine ⟨10239155455457251244160749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27304414547886003317761997 10239155455457251244160749)
        ·
          refine ⟨3839683295796469216560281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10239155455457251244160749 3839683295796469216560281)
          ·
            refine ⟨2879762471847351912420211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3839683295796469216560281 2879762471847351912420211)
            ·
              refine ⟨4319643707771027868630317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2879762471847351912420211 4319643707771027868630317)
              ·
                refine ⟨1619866390414135450736369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4319643707771027868630317 1619866390414135450736369)
                ·
                  refine ⟨1214899792810601588052277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1619866390414135450736369 1214899792810601588052277)
                  ·
                    refine ⟨113896855575993898879901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1214899792810601588052277 113896855575993898879901)
                    ·
                      rfl

theorem cell23_665440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 2, 5].length) (baseStart_665440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_665440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_665440 prefixEnd_665440 := by exact prefixLift 665440
  have htrace : WordTrace (prefixWord ++ tailWord_665440) baseStart_665440 baseEnd_665440 := by
    simpa [prefixWord, tailWord_665440, baseEnd_665440] using wordTrace_append hprefix tailTrace_665440
  have hstable : (prefixWord ++ tailWord_665440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665440).length < 2 ^ (prefixWord ++ tailWord_665440).sum := by decide
  have hdescent : baseEnd_665440 < baseStart_665440 := by decide
  rcases family_descends (prefixWord ++ tailWord_665440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665477 : List Nat := [1, 3, 1, 1, 3, 2, 3, 1, 2, 4, 2]
def baseStart_665477 : Nat := 118140960795 + 665477 * 2 ^ 59
def prefixEnd_665477 : Nat := 4983230072969 + 3 ^ 40 * 665477 * 2
def baseEnd_665477 : Nat := 341709565512198051877033

theorem tailTrace_665477 : CollatzResearch.WordTrace tailWord_665477 prefixEnd_665477 341709565512198051877033 := by
  unfold tailWord_665477
  simp only [CollatzResearch.WordTrace]
  refine ⟨24271940210097958268218685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16181293473398638845479123 24271940210097958268218685)
  ·
    refine ⟨9101977578786734350582007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24271940210097958268218685 9101977578786734350582007)
    ·
      refine ⟨13652966368180101525873011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9101977578786734350582007 13652966368180101525873011)
      ·
        refine ⟨20479449552270152288809517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13652966368180101525873011 20479449552270152288809517)
        ·
          refine ⟨7679793582101307108303569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20479449552270152288809517 7679793582101307108303569)
          ·
            refine ⟨5759845186575980331227677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7679793582101307108303569 5759845186575980331227677)
            ·
              refine ⟨2159941944965992624210379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5759845186575980331227677 2159941944965992624210379)
              ·
                refine ⟨3239912917448988936315569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2159941944965992624210379 3239912917448988936315569)
                ·
                  refine ⟨2429934688086741702236677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3239912917448988936315569 2429934688086741702236677)
                  ·
                    refine ⟨455612754016264069169377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2429934688086741702236677 455612754016264069169377)
                    ·
                      refine ⟨341709565512198051877033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 455612754016264069169377 341709565512198051877033)
                      ·
                        rfl

theorem cell23_665477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 4, 2].length) (baseStart_665477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_665477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_665477 prefixEnd_665477 := by exact prefixLift 665477
  have htrace : WordTrace (prefixWord ++ tailWord_665477) baseStart_665477 baseEnd_665477 := by
    simpa [prefixWord, tailWord_665477, baseEnd_665477] using wordTrace_append hprefix tailTrace_665477
  have hstable : (prefixWord ++ tailWord_665477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665477).length < 2 ^ (prefixWord ++ tailWord_665477).sum := by decide
  have hdescent : baseEnd_665477 < baseStart_665477 := by decide
  rcases family_descends (prefixWord ++ tailWord_665477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665483 : List Nat := [1, 1, 1, 1, 4, 2, 1, 2, 10]
def baseStart_665483 : Nat := 118140960795 + 665483 * 2 ^ 59
def prefixEnd_665483 : Nat := 4983230072969 + 3 ^ 40 * 665483 * 2
def baseEnd_665483 : Nat := 37968071821791669822445

theorem tailTrace_665483 : CollatzResearch.WordTrace tailWord_665483 prefixEnd_665483 37968071821791669822445 := by
  unfold tailWord_665483
  simp only [CollatzResearch.WordTrace]
  refine ⟨24272159048076221292937103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16181439365384147528624735 24272159048076221292937103)
  ·
    refine ⟨36408238572114331939405655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24272159048076221292937103 36408238572114331939405655)
    ·
      refine ⟨54612357858171497909108483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36408238572114331939405655 54612357858171497909108483)
      ·
        refine ⟨81918536787257246863662725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54612357858171497909108483 81918536787257246863662725)
        ·
          refine ⟨15359725647610733786936761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81918536787257246863662725 15359725647610733786936761)
          ·
            refine ⟨11519794235708050340202571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15359725647610733786936761 11519794235708050340202571)
            ·
              refine ⟨17279691353562075510303857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11519794235708050340202571 17279691353562075510303857)
              ·
                refine ⟨12959768515171556632727893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17279691353562075510303857 12959768515171556632727893)
                ·
                  refine ⟨37968071821791669822445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 12959768515171556632727893 37968071821791669822445)
                  ·
                    rfl

theorem cell23_665483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 10].length) (baseStart_665483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_665483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_665483 prefixEnd_665483 := by exact prefixLift 665483
  have htrace : WordTrace (prefixWord ++ tailWord_665483) baseStart_665483 baseEnd_665483 := by
    simpa [prefixWord, tailWord_665483, baseEnd_665483] using wordTrace_append hprefix tailTrace_665483
  have hstable : (prefixWord ++ tailWord_665483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665483).length < 2 ^ (prefixWord ++ tailWord_665483).sum := by decide
  have hdescent : baseEnd_665483 < baseStart_665483 := by decide
  rcases family_descends (prefixWord ++ tailWord_665483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665497 : List Nat := [1, 2, 1, 2, 1, 3, 5, 1, 2, 2, 3]
def baseStart_665497 : Nat := 118140960795 + 665497 * 2 ^ 59
def prefixEnd_665497 : Nat := 4983230072969 + 3 ^ 40 * 665497 * 2
def baseEnd_665497 : Nat := 341719835125287973626941

theorem tailTrace_665497 : CollatzResearch.WordTrace tailWord_665497 prefixEnd_665497 341719835125287973626941 := by
  unfold tailWord_665497
  simp only [CollatzResearch.WordTrace]
  refine ⟨24272669670025501683946745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16181779780017001122631163 24272669670025501683946745)
  ·
    refine ⟨18204502252519126262960059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24272669670025501683946745 18204502252519126262960059)
    ·
      refine ⟨27306753378778689394440089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18204502252519126262960059 27306753378778689394440089)
      ·
        refine ⟨20480065034084017045830067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27306753378778689394440089 20480065034084017045830067)
        ·
          refine ⟨30720097551126025568745101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20480065034084017045830067 30720097551126025568745101)
          ·
            refine ⟨11520036581672259588279413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30720097551126025568745101 11520036581672259588279413)
            ·
              refine ⟨1080003429531774336401195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11520036581672259588279413 1080003429531774336401195)
              ·
                refine ⟨1620005144297661504601793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1080003429531774336401195 1620005144297661504601793)
                ·
                  refine ⟨1215003858223246128451345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1620005144297661504601793 1215003858223246128451345)
                  ·
                    refine ⟨911252893667434596338509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1215003858223246128451345 911252893667434596338509)
                    ·
                      refine ⟨341719835125287973626941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 911252893667434596338509 341719835125287973626941)
                      ·
                        rfl

theorem cell23_665497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 2, 2, 3].length) (baseStart_665497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_665497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_665497 prefixEnd_665497 := by exact prefixLift 665497
  have htrace : WordTrace (prefixWord ++ tailWord_665497) baseStart_665497 baseEnd_665497 := by
    simpa [prefixWord, tailWord_665497, baseEnd_665497] using wordTrace_append hprefix tailTrace_665497
  have hstable : (prefixWord ++ tailWord_665497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665497).length < 2 ^ (prefixWord ++ tailWord_665497).sum := by decide
  have hdescent : baseEnd_665497 < baseStart_665497 := by decide
  rcases family_descends (prefixWord ++ tailWord_665497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665530 : List Nat := [3, 1, 1, 1, 2, 1, 2, 4, 3, 5]
def baseStart_665530 : Nat := 118140960795 + 665530 * 2 ^ 59
def prefixEnd_665530 : Nat := 4983230072969 + 3 ^ 40 * 665530 * 2
def baseEnd_665530 : Nat := 113912259995628781504763

theorem tailTrace_665530 : CollatzResearch.WordTrace tailWord_665530 prefixEnd_665530 113912259995628781504763 := by
  unfold tailWord_665530
  simp only [CollatzResearch.WordTrace]
  refine ⟨6068468319726487079974511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16182582185937298879932029 6068468319726487079974511)
  ·
    refine ⟨9102702479589730619961767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6068468319726487079974511 9102702479589730619961767)
    ·
      refine ⟨13654053719384595929942651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9102702479589730619961767 13654053719384595929942651)
      ·
        refine ⟨20481080579076893894913977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13654053719384595929942651 20481080579076893894913977)
        ·
          refine ⟨15360810434307670421185483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20481080579076893894913977 15360810434307670421185483)
          ·
            refine ⟨23041215651461505631778225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15360810434307670421185483 23041215651461505631778225)
            ·
              refine ⟨17280911738596129223833669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23041215651461505631778225 17280911738596129223833669)
              ·
                refine ⟨3240170950986774229468813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17280911738596129223833669 3240170950986774229468813)
                ·
                  refine ⟨1215064106620040336050805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3240170950986774229468813 1215064106620040336050805)
                  ·
                    refine ⟨113912259995628781504763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1215064106620040336050805 113912259995628781504763)
                    ·
                      rfl

theorem cell23_665530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 3, 5].length) (baseStart_665530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_665530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_665530 prefixEnd_665530 := by exact prefixLift 665530
  have htrace : WordTrace (prefixWord ++ tailWord_665530) baseStart_665530 baseEnd_665530 := by
    simpa [prefixWord, tailWord_665530, baseEnd_665530] using wordTrace_append hprefix tailTrace_665530
  have hstable : (prefixWord ++ tailWord_665530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665530).length < 2 ^ (prefixWord ++ tailWord_665530).sum := by decide
  have hdescent : baseEnd_665530 < baseStart_665530 := by decide
  rcases family_descends (prefixWord ++ tailWord_665530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665534 : List Nat := [4, 2, 1, 1, 1, 4, 3, 1, 6]
def baseStart_665534 : Nat := 118140960795 + 665534 * 2 ^ 59
def prefixEnd_665534 : Nat := 4983230072969 + 3 ^ 40 * 665534 * 2
def baseEnd_665534 : Nat := 37970981545500480984919

theorem tailTrace_665534 : CollatzResearch.WordTrace tailWord_665534 prefixEnd_665534 37970981545500480984919 := by
  unfold tailWord_665534
  simp only [CollatzResearch.WordTrace]
  refine ⟨3034252396361432125380457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16182679447260971335362437 3034252396361432125380457)
  ·
    refine ⟨2275689297271074094035343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3034252396361432125380457 2275689297271074094035343)
    ·
      refine ⟨3413533945906611141053015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2275689297271074094035343 3413533945906611141053015)
      ·
        refine ⟨5120300918859916711579523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3413533945906611141053015 5120300918859916711579523)
        ·
          refine ⟨7680451378289875067369285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5120300918859916711579523 7680451378289875067369285)
          ·
            refine ⟨1440084633429351575131741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7680451378289875067369285 1440084633429351575131741)
            ·
              refine ⟨540031737536006840674403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1440084633429351575131741 540031737536006840674403)
              ·
                refine ⟨810047606304010261011605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 540031737536006840674403 810047606304010261011605)
                ·
                  refine ⟨37970981545500480984919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 810047606304010261011605 37970981545500480984919)
                  ·
                    rfl

theorem cell23_665534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 1, 6].length) (baseStart_665534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_665534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_665534 prefixEnd_665534 := by exact prefixLift 665534
  have htrace : WordTrace (prefixWord ++ tailWord_665534) baseStart_665534 baseEnd_665534 := by
    simpa [prefixWord, tailWord_665534, baseEnd_665534] using wordTrace_append hprefix tailTrace_665534
  have hstable : (prefixWord ++ tailWord_665534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665534).length < 2 ^ (prefixWord ++ tailWord_665534).sum := by decide
  have hdescent : baseEnd_665534 < baseStart_665534 := by decide
  rcases family_descends (prefixWord ++ tailWord_665534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665544 : List Nat := [2, 1, 3, 1, 4, 1, 2, 2, 3, 1, 3]
def baseStart_665544 : Nat := 118140960795 + 665544 * 2 ^ 59
def prefixEnd_665544 : Nat := 4983230072969 + 3 ^ 40 * 665544 * 2
def baseEnd_665544 : Nat := 341743968716049289739225

theorem tailTrace_665544 : CollatzResearch.WordTrace tailWord_665544 prefixEnd_665544 341743968716049289739225 := by
  unfold tailWord_665544
  simp only [CollatzResearch.WordTrace]
  refine ⟨12137191950427614355453843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16182922600570152473938457 12137191950427614355453843)
  ·
    refine ⟨18205787925641421533180765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12137191950427614355453843 18205787925641421533180765)
    ·
      refine ⟨6827170472115533074942787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18205787925641421533180765 6827170472115533074942787)
      ·
        refine ⟨10240755708173299612414181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6827170472115533074942787 10240755708173299612414181)
        ·
          refine ⟨1920141695282493677327659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10240755708173299612414181 1920141695282493677327659)
          ·
            refine ⟨2880212542923740515991489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1920141695282493677327659 2880212542923740515991489)
            ·
              refine ⟨2160159407192805386993617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2880212542923740515991489 2160159407192805386993617)
              ·
                refine ⟨1620119555394604040245213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2160159407192805386993617 1620119555394604040245213)
                ·
                  refine ⟨607544833272976515091955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1620119555394604040245213 607544833272976515091955)
                  ·
                    refine ⟨911317249909464772637933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 607544833272976515091955 911317249909464772637933)
                    ·
                      refine ⟨341743968716049289739225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 911317249909464772637933 341743968716049289739225)
                      ·
                        rfl

theorem cell23_665544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 3, 1, 3].length) (baseStart_665544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_665544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_665544 prefixEnd_665544 := by exact prefixLift 665544
  have htrace : WordTrace (prefixWord ++ tailWord_665544) baseStart_665544 baseEnd_665544 := by
    simpa [prefixWord, tailWord_665544, baseEnd_665544] using wordTrace_append hprefix tailTrace_665544
  have hstable : (prefixWord ++ tailWord_665544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665544).length < 2 ^ (prefixWord ++ tailWord_665544).sum := by decide
  have hdescent : baseEnd_665544 < baseStart_665544 := by decide
  rcases family_descends (prefixWord ++ tailWord_665544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665547 : List Nat := [1, 1, 1, 1, 3, 4, 4, 2, 1, 5]
def baseStart_665547 : Nat := 118140960795 + 665547 * 2 ^ 59
def prefixEnd_665547 : Nat := 4983230072969 + 3 ^ 40 * 665547 * 2
def baseEnd_665547 : Nat := 113915169719337592667237

theorem tailTrace_665547 : CollatzResearch.WordTrace tailWord_665547 prefixEnd_665547 113915169719337592667237 := by
  unfold tailWord_665547
  simp only [CollatzResearch.WordTrace]
  refine ⟨24274493319844360223266895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16182995546562906815511263 24274493319844360223266895)
  ·
    refine ⟨36411739979766540334900343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24274493319844360223266895 36411739979766540334900343)
    ·
      refine ⟨54617609969649810502350515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36411739979766540334900343 54617609969649810502350515)
      ·
        refine ⟨81926414954474715753525773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54617609969649810502350515 81926414954474715753525773)
        ·
          refine ⟨30722405607928018407572165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81926414954474715753525773 30722405607928018407572165)
          ·
            refine ⟨5760451051486503451419781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30722405607928018407572165 5760451051486503451419781)
            ·
              refine ⟨1080084572153719397141209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5760451051486503451419781 1080084572153719397141209)
              ·
                refine ⟨810063429115289547855907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1080084572153719397141209 810063429115289547855907)
                ·
                  refine ⟨1215095143672934321783861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 810063429115289547855907 1215095143672934321783861)
                  ·
                    refine ⟨113915169719337592667237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1215095143672934321783861 113915169719337592667237)
                    ·
                      rfl

theorem cell23_665547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 2, 1, 5].length) (baseStart_665547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_665547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_665547 prefixEnd_665547 := by exact prefixLift 665547
  have htrace : WordTrace (prefixWord ++ tailWord_665547) baseStart_665547 baseEnd_665547 := by
    simpa [prefixWord, tailWord_665547, baseEnd_665547] using wordTrace_append hprefix tailTrace_665547
  have hstable : (prefixWord ++ tailWord_665547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665547).length < 2 ^ (prefixWord ++ tailWord_665547).sum := by decide
  have hdescent : baseEnd_665547 < baseStart_665547 := by decide
  rcases family_descends (prefixWord ++ tailWord_665547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665560 : List Nat := [2, 1, 2, 2, 2, 2, 2, 1, 3, 6]
def baseStart_665560 : Nat := 118140960795 + 665560 * 2 ^ 59
def prefixEnd_665560 : Nat := 4983230072969 + 3 ^ 40 * 665560 * 2
def baseEnd_665560 : Nat := 113917394802173742379717

theorem tailTrace_665560 : CollatzResearch.WordTrace tailWord_665560 prefixEnd_665560 113917394802173742379717 := by
  unfold tailWord_665560
  simp only [CollatzResearch.WordTrace]
  refine ⟨12137483734398631721745067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16183311645864842295660089 12137483734398631721745067)
  ·
    refine ⟨18206225601597947582617601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12137483734398631721745067 18206225601597947582617601)
    ·
      refine ⟨13654669201198460686963201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18206225601597947582617601 13654669201198460686963201)
      ·
        refine ⟨10241001900898845515222401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13654669201198460686963201 10241001900898845515222401)
        ·
          refine ⟨7680751425674134136416801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10241001900898845515222401 7680751425674134136416801)
          ·
            refine ⟨5760563569255600602312601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7680751425674134136416801 5760563569255600602312601)
            ·
              refine ⟨4320422676941700451734451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5760563569255600602312601 4320422676941700451734451)
              ·
                refine ⟨6480634015412550677601677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4320422676941700451734451 6480634015412550677601677)
                ·
                  refine ⟨2430237755779706504100629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6480634015412550677601677 2430237755779706504100629)
                  ·
                    refine ⟨113917394802173742379717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2430237755779706504100629 113917394802173742379717)
                    ·
                      rfl

theorem cell23_665560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 3, 6].length) (baseStart_665560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_665560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_665560 prefixEnd_665560 := by exact prefixLift 665560
  have htrace : WordTrace (prefixWord ++ tailWord_665560) baseStart_665560 baseEnd_665560 := by
    simpa [prefixWord, tailWord_665560, baseEnd_665560] using wordTrace_append hprefix tailTrace_665560
  have hstable : (prefixWord ++ tailWord_665560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665560).length < 2 ^ (prefixWord ++ tailWord_665560).sum := by decide
  have hdescent : baseEnd_665560 < baseStart_665560 := by decide
  rcases family_descends (prefixWord ++ tailWord_665560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665578 : List Nat := [3, 1, 3, 1, 2, 1, 5, 2, 1, 1, 3]
def baseStart_665578 : Nat := 118140960795 + 665578 * 2 ^ 59
def prefixEnd_665578 : Nat := 4983230072969 + 3 ^ 40 * 665578 * 2
def baseEnd_665578 : Nat := 341761427058302156714069

theorem tailTrace_665578 : CollatzResearch.WordTrace tailWord_665578 prefixEnd_665578 341761427058302156714069 := by
  unfold tailWord_665578
  simp only [CollatzResearch.WordTrace]
  refine ⟨6068905995683013129411347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16183749321821368345096925 6068905995683013129411347)
  ·
    refine ⟨9103358993524519694117021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6068905995683013129411347 9103358993524519694117021)
    ·
      refine ⟨3413759622571694885293883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9103358993524519694117021 3413759622571694885293883)
      ·
        refine ⟨5120639433857542327940825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3413759622571694885293883 5120639433857542327940825)
        ·
          refine ⟨3840479575393156745955619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5120639433857542327940825 3840479575393156745955619)
          ·
            refine ⟨5760719363089735118933429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3840479575393156745955619 5760719363089735118933429)
            ·
              refine ⟨540067440289662667400009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5760719363089735118933429 540067440289662667400009)
              ·
                refine ⟨405050580217247000550007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 540067440289662667400009 405050580217247000550007)
                ·
                  refine ⟨607575870325870500825011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 405050580217247000550007 607575870325870500825011)
                  ·
                    refine ⟨911363805488805751237517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 607575870325870500825011 911363805488805751237517)
                    ·
                      refine ⟨341761427058302156714069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 911363805488805751237517 341761427058302156714069)
                      ·
                        rfl

theorem cell23_665578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 2, 1, 1, 3].length) (baseStart_665578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_665578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_665578 prefixEnd_665578 := by exact prefixLift 665578
  have htrace : WordTrace (prefixWord ++ tailWord_665578) baseStart_665578 baseEnd_665578 := by
    simpa [prefixWord, tailWord_665578, baseEnd_665578] using wordTrace_append hprefix tailTrace_665578
  have hstable : (prefixWord ++ tailWord_665578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665578).length < 2 ^ (prefixWord ++ tailWord_665578).sum := by decide
  have hdescent : baseEnd_665578 < baseStart_665578 := by decide
  rcases family_descends (prefixWord ++ tailWord_665578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665621 : List Nat := [1, 3, 2, 1, 6, 1, 1, 1, 1, 1, 5]
def baseStart_665621 : Nat := 118140960795 + 665621 * 2 ^ 59
def prefixEnd_665621 : Nat := 4983230072969 + 3 ^ 40 * 665621 * 2
def baseEnd_665621 : Nat := 341783506726445488476371

theorem tailTrace_665621 : CollatzResearch.WordTrace tailWord_665621 prefixEnd_665621 341783506726445488476371 := by
  unfold tailWord_665621
  simp only [CollatzResearch.WordTrace]
  refine ⟨24277192321576270861460717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16184794881050847240973811 24277192321576270861460717)
  ·
    refine ⟨9103947120591101573047769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24277192321576270861460717 9103947120591101573047769)
    ·
      refine ⟨6827960340443326179785827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9103947120591101573047769 6827960340443326179785827)
      ·
        refine ⟨10241940510664989269678741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6827960340443326179785827 10241940510664989269678741)
        ·
          refine ⟨480090961437421372016191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 10241940510664989269678741 480090961437421372016191)
          ·
            refine ⟨720136442156132058024287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 480090961437421372016191 720136442156132058024287)
            ·
              refine ⟨1080204663234198087036431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 720136442156132058024287 1080204663234198087036431)
              ·
                refine ⟨1620306994851297130554647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1080204663234198087036431 1620306994851297130554647)
                ·
                  refine ⟨2430460492276945695831971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1620306994851297130554647 2430460492276945695831971)
                  ·
                    refine ⟨3645690738415418543747957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2430460492276945695831971 3645690738415418543747957)
                    ·
                      refine ⟨341783506726445488476371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3645690738415418543747957 341783506726445488476371)
                      ·
                        rfl

theorem cell23_665621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 1, 1, 5].length) (baseStart_665621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_665621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_665621 prefixEnd_665621 := by exact prefixLift 665621
  have htrace : WordTrace (prefixWord ++ tailWord_665621) baseStart_665621 baseEnd_665621 := by
    simpa [prefixWord, tailWord_665621, baseEnd_665621] using wordTrace_append hprefix tailTrace_665621
  have hstable : (prefixWord ++ tailWord_665621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665621).length < 2 ^ (prefixWord ++ tailWord_665621).sum := by decide
  have hdescent : baseEnd_665621 < baseStart_665621 := by decide
  rcases family_descends (prefixWord ++ tailWord_665621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665661 : List Nat := [1, 4, 1, 3, 1, 1, 2, 4, 1, 3, 2]
def baseStart_665661 : Nat := 118140960795 + 665661 * 2 ^ 59
def prefixEnd_665661 : Nat := 4983230072969 + 3 ^ 40 * 665661 * 2
def baseEnd_665661 : Nat := 341804045952625331976187

theorem tailTrace_665661 : CollatzResearch.WordTrace tailWord_665661 prefixEnd_665661 341804045952625331976187 := by
  unfold tailWord_665661
  simp only [CollatzResearch.WordTrace]
  refine ⟨24278651241431357692916837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16185767494287571795277891 24278651241431357692916837)
  ·
    refine ⟨4552247107768379567421907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24278651241431357692916837 4552247107768379567421907)
    ·
      refine ⟨6828370661652569351132861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4552247107768379567421907 6828370661652569351132861)
      ·
        refine ⟨2560638998119713506674823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6828370661652569351132861 2560638998119713506674823)
        ·
          refine ⟨3840958497179570260012235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2560638998119713506674823 3840958497179570260012235)
          ·
            refine ⟨5761437745769355390018353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3840958497179570260012235 5761437745769355390018353)
            ·
              refine ⟨4321078309327016542513765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5761437745769355390018353 4321078309327016542513765)
              ·
                refine ⟨810202182998815601721331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4321078309327016542513765 810202182998815601721331)
                ·
                  refine ⟨1215303274498223402581997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 810202182998815601721331 1215303274498223402581997)
                  ·
                    refine ⟨455738727936833775968249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1215303274498223402581997 455738727936833775968249)
                    ·
                      refine ⟨341804045952625331976187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 455738727936833775968249 341804045952625331976187)
                      ·
                        rfl

theorem cell23_665661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_665661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_665661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_665661 prefixEnd_665661 := by exact prefixLift 665661
  have htrace : WordTrace (prefixWord ++ tailWord_665661) baseStart_665661 baseEnd_665661 := by
    simpa [prefixWord, tailWord_665661, baseEnd_665661] using wordTrace_append hprefix tailTrace_665661
  have hstable : (prefixWord ++ tailWord_665661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665661).length < 2 ^ (prefixWord ++ tailWord_665661).sum := by decide
  have hdescent : baseEnd_665661 < baseStart_665661 := by decide
  rcases family_descends (prefixWord ++ tailWord_665661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665678 : List Nat := [4, 1, 1, 1, 1, 4, 4, 1, 1, 3, 2]
def baseStart_665678 : Nat := 118140960795 + 665678 * 2 ^ 59
def prefixEnd_665678 : Nat := 4983230072969 + 3 ^ 40 * 665678 * 2
def baseEnd_665678 : Nat := 341812775123751765463609

theorem tailTrace_665678 : CollatzResearch.WordTrace tailWord_665678 prefixEnd_665678 341812775123751765463609 := by
  unfold tailWord_665678
  simp only [CollatzResearch.WordTrace]
  refine ⟨3034908910296221199535711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16186180854913179730857125 3034908910296221199535711)
  ·
    refine ⟨4552363365444331799303567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3034908910296221199535711 4552363365444331799303567)
    ·
      refine ⟨6828545048166497698955351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4552363365444331799303567 6828545048166497698955351)
      ·
        refine ⟨10242817572249746548433027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6828545048166497698955351 10242817572249746548433027)
        ·
          refine ⟨15364226358374619822649541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10242817572249746548433027 15364226358374619822649541)
          ·
            refine ⟨2880792442195241216746789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15364226358374619822649541 2880792442195241216746789)
            ·
              refine ⟨540148582911607728140023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2880792442195241216746789 540148582911607728140023)
              ·
                refine ⟨810222874367411592210035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 540148582911607728140023 810222874367411592210035)
                ·
                  refine ⟨1215334311551117388315053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 810222874367411592210035 1215334311551117388315053)
                  ·
                    refine ⟨455750366831669020618145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1215334311551117388315053 455750366831669020618145)
                    ·
                      refine ⟨341812775123751765463609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 455750366831669020618145 341812775123751765463609)
                      ·
                        rfl

theorem cell23_665678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 1, 1, 3, 2].length) (baseStart_665678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_665678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_665678 prefixEnd_665678 := by exact prefixLift 665678
  have htrace : WordTrace (prefixWord ++ tailWord_665678) baseStart_665678 baseEnd_665678 := by
    simpa [prefixWord, tailWord_665678, baseEnd_665678] using wordTrace_append hprefix tailTrace_665678
  have hstable : (prefixWord ++ tailWord_665678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665678).length < 2 ^ (prefixWord ++ tailWord_665678).sum := by decide
  have hdescent : baseEnd_665678 < baseStart_665678 := by decide
  rcases family_descends (prefixWord ++ tailWord_665678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665687 : List Nat := [1, 1, 3, 2, 2, 1, 3, 2, 2, 2, 4]
def baseStart_665687 : Nat := 118140960795 + 665687 * 2 ^ 59
def prefixEnd_665687 : Nat := 4983230072969 + 3 ^ 40 * 665687 * 2
def baseEnd_665687 : Nat := 341817396449642230251067

theorem tailTrace_665687 : CollatzResearch.WordTrace tailWord_665687 prefixEnd_665687 341817396449642230251067 := by
  unfold tailWord_665687
  simp only [CollatzResearch.WordTrace]
  refine ⟨24279599539337164133363315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16186399692891442755575543 24279599539337164133363315)
  ·
    refine ⟨36419399309005746200044973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24279599539337164133363315 36419399309005746200044973)
    ·
      refine ⟨13657274740877154825016865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36419399309005746200044973 13657274740877154825016865)
      ·
        refine ⟨10242956055657866118762649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13657274740877154825016865 10242956055657866118762649)
        ·
          refine ⟨7682217041743399589071987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10242956055657866118762649 7682217041743399589071987)
          ·
            refine ⟨11523325562615099383607981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7682217041743399589071987 11523325562615099383607981)
            ·
              refine ⟨4321247085980662268852993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11523325562615099383607981 4321247085980662268852993)
              ·
                refine ⟨3240935314485496701639745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4321247085980662268852993 3240935314485496701639745)
                ·
                  refine ⟨2430701485864122526229809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3240935314485496701639745 2430701485864122526229809)
                  ·
                    refine ⟨1823026114398091894672357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2430701485864122526229809 1823026114398091894672357)
                    ·
                      refine ⟨341817396449642230251067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1823026114398091894672357 341817396449642230251067)
                      ·
                        rfl

theorem cell23_665687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_665687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_665687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_665687 prefixEnd_665687 := by exact prefixLift 665687
  have htrace : WordTrace (prefixWord ++ tailWord_665687) baseStart_665687 baseEnd_665687 := by
    simpa [prefixWord, tailWord_665687, baseEnd_665687] using wordTrace_append hprefix tailTrace_665687
  have hstable : (prefixWord ++ tailWord_665687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665687).length < 2 ^ (prefixWord ++ tailWord_665687).sum := by decide
  have hdescent : baseEnd_665687 < baseStart_665687 := by decide
  rcases family_descends (prefixWord ++ tailWord_665687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665731 : List Nat := [1, 1, 1, 3, 3, 5, 1, 3, 5]
def baseStart_665731 : Nat := 118140960795 + 665731 * 2 ^ 59
def prefixEnd_665731 : Nat := 4983230072969 + 3 ^ 40 * 665731 * 2
def baseEnd_665731 : Nat := 37982221066493339788985

theorem tailTrace_665731 : CollatzResearch.WordTrace tailWord_665731 prefixEnd_665731 37982221066493339788985 := by
  unfold tailWord_665731
  simp only [CollatzResearch.WordTrace]
  refine ⟨24281204351177759647965047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16187469567451839765310031 24281204351177759647965047)
  ·
    refine ⟨36421806526766639471947571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24281204351177759647965047 36421806526766639471947571)
    ·
      refine ⟨54632709790149959207921357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36421806526766639471947571 54632709790149959207921357)
      ·
        refine ⟨20487266171306234702970509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54632709790149959207921357 20487266171306234702970509)
        ·
          refine ⟨7682724814239838013613941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20487266171306234702970509 7682724814239838013613941)
          ·
            refine ⟨720255451334984813776307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7682724814239838013613941 720255451334984813776307)
            ·
              refine ⟨1080383177002477220664461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 720255451334984813776307 1080383177002477220664461)
              ·
                refine ⟨405143691375928957749173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1080383177002477220664461 405143691375928957749173)
                ·
                  refine ⟨37982221066493339788985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 405143691375928957749173 37982221066493339788985)
                  ·
                    rfl

theorem cell23_665731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 3, 5].length) (baseStart_665731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_665731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_665731 prefixEnd_665731 := by exact prefixLift 665731
  have htrace : WordTrace (prefixWord ++ tailWord_665731) baseStart_665731 baseEnd_665731 := by
    simpa [prefixWord, tailWord_665731, baseEnd_665731] using wordTrace_append hprefix tailTrace_665731
  have hstable : (prefixWord ++ tailWord_665731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665731).length < 2 ^ (prefixWord ++ tailWord_665731).sum := by decide
  have hdescent : baseEnd_665731 < baseStart_665731 := by decide
  rcases family_descends (prefixWord ++ tailWord_665731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665737 : List Nat := [1, 2, 1, 1, 4, 2, 2, 2, 1, 2, 5]
def baseStart_665737 : Nat := 118140960795 + 665737 * 2 ^ 59
def prefixEnd_665737 : Nat := 4983230072969 + 3 ^ 40 * 665737 * 2
def baseEnd_665737 : Nat := 341843070482367034625837

theorem tailTrace_665737 : CollatzResearch.WordTrace tailWord_665737 prefixEnd_665737 341843070482367034625837 := by
  unfold tailWord_665737
  simp only [CollatzResearch.WordTrace]
  refine ⟨24281423189156022672683465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16187615459437348448455643 24281423189156022672683465)
  ·
    refine ⟨18211067391867017004512599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24281423189156022672683465 18211067391867017004512599)
    ·
      refine ⟨27316601087800525506768899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18211067391867017004512599 27316601087800525506768899)
      ·
        refine ⟨40974901631700788260153349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27316601087800525506768899 40974901631700788260153349)
        ·
          refine ⟨7682794055943897798778753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40974901631700788260153349 7682794055943897798778753)
          ·
            refine ⟨5762095541957923349084065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7682794055943897798778753 5762095541957923349084065)
            ·
              refine ⟨4321571656468442511813049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5762095541957923349084065 4321571656468442511813049)
              ·
                refine ⟨3241178742351331883859787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4321571656468442511813049 3241178742351331883859787)
                ·
                  refine ⟨4861768113526997825789681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3241178742351331883859787 4861768113526997825789681)
                  ·
                    refine ⟨3646326085145248369342261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4861768113526997825789681 3646326085145248369342261)
                    ·
                      refine ⟨341843070482367034625837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3646326085145248369342261 341843070482367034625837)
                      ·
                        rfl

theorem cell23_665737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 2, 5].length) (baseStart_665737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_665737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_665737 prefixEnd_665737 := by exact prefixLift 665737
  have htrace : WordTrace (prefixWord ++ tailWord_665737) baseStart_665737 baseEnd_665737 := by
    simpa [prefixWord, tailWord_665737, baseEnd_665737] using wordTrace_append hprefix tailTrace_665737
  have hstable : (prefixWord ++ tailWord_665737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665737).length < 2 ^ (prefixWord ++ tailWord_665737).sum := by decide
  have hdescent : baseEnd_665737 < baseStart_665737 := by decide
  rcases family_descends (prefixWord ++ tailWord_665737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665748 : List Nat := [2, 4, 2, 3, 1, 2, 1, 1, 7]
def baseStart_665748 : Nat := 118140960795 + 665748 * 2 ^ 59
def prefixEnd_665748 : Nat := 4983230072969 + 3 ^ 40 * 665748 * 2
def baseEnd_665748 : Nat := 37983190974396276843143

theorem tailTrace_665748 : CollatzResearch.WordTrace tailWord_665748 prefixEnd_665748 37983190974396276843143 := by
  unfold tailWord_665748
  simp only [CollatzResearch.WordTrace]
  refine ⟨12140912196058085775666949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16187882928077447700889265 12140912196058085775666949)
  ·
    refine ⟨2276421036760891082937553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12140912196058085775666949 2276421036760891082937553)
    ·
      refine ⟨1707315777570668312203165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2276421036760891082937553 1707315777570668312203165)
      ·
        refine ⟨640243416589000617076187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1707315777570668312203165 640243416589000617076187)
        ·
          refine ⟨960365124883500925614281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 640243416589000617076187 960365124883500925614281)
          ·
            refine ⟨720273843662625694210711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 960365124883500925614281 720273843662625694210711)
            ·
              refine ⟨1080410765493938541316067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 720273843662625694210711 1080410765493938541316067)
              ·
                refine ⟨1620616148240907811974101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1080410765493938541316067 1620616148240907811974101)
                ·
                  refine ⟨37983190974396276843143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1620616148240907811974101 37983190974396276843143)
                  ·
                    rfl

theorem cell23_665748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 7].length) (baseStart_665748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_665748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_665748 prefixEnd_665748 := by exact prefixLift 665748
  have htrace : WordTrace (prefixWord ++ tailWord_665748) baseStart_665748 baseEnd_665748 := by
    simpa [prefixWord, tailWord_665748, baseEnd_665748] using wordTrace_append hprefix tailTrace_665748
  have hstable : (prefixWord ++ tailWord_665748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665748).length < 2 ^ (prefixWord ++ tailWord_665748).sum := by decide
  have hdescent : baseEnd_665748 < baseStart_665748 := by decide
  rcases family_descends (prefixWord ++ tailWord_665748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665791 : List Nat := [1, 1, 2, 2, 2, 2, 1, 7, 1, 4]
def baseStart_665791 : Nat := 118140960795 + 665791 * 2 ^ 59
def prefixEnd_665791 : Nat := 4983230072969 + 3 ^ 40 * 665791 * 2
def baseEnd_665791 : Nat := 113956932812569941116863

theorem tailTrace_665791 : CollatzResearch.WordTrace tailWord_665791 prefixEnd_665791 113956932812569941116863 := by
  unfold tailWord_665791
  simp only [CollatzResearch.WordTrace]
  refine ⟨24283392730960389895149227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16188928487306926596766151 24283392730960389895149227)
  ·
    refine ⟨36425089096440584842723841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24283392730960389895149227 36425089096440584842723841)
    ·
      refine ⟨27318816822330438632042881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36425089096440584842723841 27318816822330438632042881)
      ·
        refine ⟨20489112616747828974032161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27318816822330438632042881 20489112616747828974032161)
        ·
          refine ⟨15366834462560871730524121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20489112616747828974032161 15366834462560871730524121)
          ·
            refine ⟨11525125846920653797893091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15366834462560871730524121 11525125846920653797893091)
            ·
              refine ⟨17287688770380980696839637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11525125846920653797893091 17287688770380980696839637)
              ·
                refine ⟨405180205555804235082179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 17287688770380980696839637 405180205555804235082179)
                ·
                  refine ⟨607770308333706352623269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 405180205555804235082179 607770308333706352623269)
                  ·
                    refine ⟨113956932812569941116863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 607770308333706352623269 113956932812569941116863)
                    ·
                      rfl

theorem cell23_665791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 7, 1, 4].length) (baseStart_665791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_665791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_665791 prefixEnd_665791 := by exact prefixLift 665791
  have htrace : WordTrace (prefixWord ++ tailWord_665791) baseStart_665791 baseEnd_665791 := by
    simpa [prefixWord, tailWord_665791, baseEnd_665791] using wordTrace_append hprefix tailTrace_665791
  have hstable : (prefixWord ++ tailWord_665791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665791).length < 2 ^ (prefixWord ++ tailWord_665791).sum := by decide
  have hdescent : baseEnd_665791 < baseStart_665791 := by decide
  rcases family_descends (prefixWord ++ tailWord_665791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665807 : List Nat := [1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 6]
def baseStart_665807 : Nat := 118140960795 + 665807 * 2 ^ 59
def prefixEnd_665807 : Nat := 4983230072969 + 3 ^ 40 * 665807 * 2
def baseEnd_665807 : Nat := 341879014128181760750515

theorem tailTrace_665807 : CollatzResearch.WordTrace tailWord_665807 prefixEnd_665807 341879014128181760750515 := by
  unfold tailWord_665807
  simp only [CollatzResearch.WordTrace]
  refine ⟨24283976298902424627731675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16189317532601616418487783 24283976298902424627731675)
  ·
    refine ⟨36425964448353636941597513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24283976298902424627731675 36425964448353636941597513)
    ·
      refine ⟨27319473336265227706198135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36425964448353636941597513 27319473336265227706198135)
      ·
        refine ⟨40979210004397841559297203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27319473336265227706198135 40979210004397841559297203)
        ·
          refine ⟨61468815006596762338945805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40979210004397841559297203 61468815006596762338945805)
          ·
            refine ⟨23050805627473785877104677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61468815006596762338945805 23050805627473785877104677)
            ·
              refine ⟨4322026055151334851957127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23050805627473785877104677 4322026055151334851957127)
              ·
                refine ⟨6483039082727002277935691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4322026055151334851957127 6483039082727002277935691)
                ·
                  refine ⟨9724558624090503416903537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6483039082727002277935691 9724558624090503416903537)
                  ·
                    refine ⟨7293418968067877562677653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9724558624090503416903537 7293418968067877562677653)
                    ·
                      refine ⟨341879014128181760750515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7293418968067877562677653 341879014128181760750515)
                      ·
                        rfl

theorem cell23_665807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 6].length) (baseStart_665807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_665807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_665807 prefixEnd_665807 := by exact prefixLift 665807
  have htrace : WordTrace (prefixWord ++ tailWord_665807) baseStart_665807 baseEnd_665807 := by
    simpa [prefixWord, tailWord_665807, baseEnd_665807] using wordTrace_append hprefix tailTrace_665807
  have hstable : (prefixWord ++ tailWord_665807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665807).length < 2 ^ (prefixWord ++ tailWord_665807).sum := by decide
  have hdescent : baseEnd_665807 < baseStart_665807 := by decide
  rcases family_descends (prefixWord ++ tailWord_665807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665821 : List Nat := [1, 4, 3, 2, 1, 1, 2, 3, 6]
def baseStart_665821 : Nat := 118140960795 + 665821 * 2 ^ 59
def prefixEnd_665821 : Nat := 4983230072969 + 3 ^ 40 * 665821 * 2
def baseEnd_665821 : Nat := 37987355873038300663939

theorem tailTrace_665821 : CollatzResearch.WordTrace tailWord_665821 prefixEnd_665821 37987355873038300663939 := by
  unfold tailWord_665821
  simp only [CollatzResearch.WordTrace]
  refine ⟨24284486920851705018741317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16189657947234470012494211 24284486920851705018741317)
  ·
    refine ⟨4553341297659694691013997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24284486920851705018741317 4553341297659694691013997)
    ·
      refine ⟨1707502986622385509130249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4553341297659694691013997 1707502986622385509130249)
      ·
        refine ⟨1280627239966789131847687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1707502986622385509130249 1280627239966789131847687)
        ·
          refine ⟨1920940859950183697771531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1280627239966789131847687 1920940859950183697771531)
          ·
            refine ⟨2881411289925275546657297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1920940859950183697771531 2881411289925275546657297)
            ·
              refine ⟨2161058467443956659992973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2881411289925275546657297 2161058467443956659992973)
              ·
                refine ⟨810396925291483747497365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2161058467443956659992973 810396925291483747497365)
                ·
                  refine ⟨37987355873038300663939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 810396925291483747497365 37987355873038300663939)
                  ·
                    rfl

theorem cell23_665821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 3, 6].length) (baseStart_665821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_665821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_665821 prefixEnd_665821 := by exact prefixLift 665821
  have htrace : WordTrace (prefixWord ++ tailWord_665821) baseStart_665821 baseEnd_665821 := by
    simpa [prefixWord, tailWord_665821, baseEnd_665821] using wordTrace_append hprefix tailTrace_665821
  have hstable : (prefixWord ++ tailWord_665821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665821).length < 2 ^ (prefixWord ++ tailWord_665821).sum := by decide
  have hdescent : baseEnd_665821 < baseStart_665821 := by decide
  rcases family_descends (prefixWord ++ tailWord_665821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665834 : List Nat := [3, 1, 3, 1, 1, 2, 1, 3, 3, 5]
def baseStart_665834 : Nat := 118140960795 + 665834 * 2 ^ 59
def prefixEnd_665834 : Nat := 4983230072969 + 3 ^ 40 * 665834 * 2
def baseEnd_665834 : Nat := 113964292701951051704297

theorem tailTrace_665834 : CollatzResearch.WordTrace tailWord_665834 prefixEnd_665834 113964292701951051704297 := by
  unfold tailWord_665834
  simp only [CollatzResearch.WordTrace]
  refine ⟨6071240267451152059741139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16189974046536405492643037 6071240267451152059741139)
  ·
    refine ⟨9106860401176728089611709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6071240267451152059741139 9106860401176728089611709)
    ·
      refine ⟨3415072650441273033604391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9106860401176728089611709 3415072650441273033604391)
      ·
        refine ⟨5122608975661909550406587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3415072650441273033604391 5122608975661909550406587)
        ·
          refine ⟨7683913463492864325609881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5122608975661909550406587 7683913463492864325609881)
          ·
            refine ⟨5762935097619648244207411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7683913463492864325609881 5762935097619648244207411)
            ·
              refine ⟨8644402646429472366311117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5762935097619648244207411 8644402646429472366311117)
              ·
                refine ⟨3241650992411052137366669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8644402646429472366311117 3241650992411052137366669)
                ·
                  refine ⟨1215619122154144551512501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3241650992411052137366669 1215619122154144551512501)
                  ·
                    refine ⟨113964292701951051704297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1215619122154144551512501 113964292701951051704297)
                    ·
                      rfl

theorem cell23_665834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_665834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_665834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_665834 prefixEnd_665834 := by exact prefixLift 665834
  have htrace : WordTrace (prefixWord ++ tailWord_665834) baseStart_665834 baseEnd_665834 := by
    simpa [prefixWord, tailWord_665834, baseEnd_665834] using wordTrace_append hprefix tailTrace_665834
  have hstable : (prefixWord ++ tailWord_665834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665834).length < 2 ^ (prefixWord ++ tailWord_665834).sum := by decide
  have hdescent : baseEnd_665834 < baseStart_665834 := by decide
  rcases family_descends (prefixWord ++ tailWord_665834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665888 : List Nat := [2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 4]
def baseStart_665888 : Nat := 118140960795 + 665888 * 2 ^ 59
def prefixEnd_665888 : Nat := 4983230072969 + 3 ^ 40 * 665888 * 2
def baseEnd_665888 : Nat := 341920606061195943837643

theorem tailTrace_665888 : CollatzResearch.WordTrace tailWord_665888 prefixEnd_665888 341920606061195943837643 := by
  unfold tailWord_665888
  simp only [CollatzResearch.WordTrace]
  refine ⟨12143465305804487730715159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16191287074405983640953545 12143465305804487730715159)
  ·
    refine ⟨18215197958706731596072739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12143465305804487730715159 18215197958706731596072739)
    ·
      refine ⟨27322796938060097394109109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18215197958706731596072739 27322796938060097394109109)
      ·
        refine ⟨2561512212943134130697729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27322796938060097394109109 2561512212943134130697729)
        ·
          refine ⟨1921134159707350598023297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2561512212943134130697729 1921134159707350598023297)
          ·
            refine ⟨1440850619780512948517473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1921134159707350598023297 1440850619780512948517473)
            ·
              refine ⟨1080637964835384711388105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1440850619780512948517473 1080637964835384711388105)
              ·
                refine ⟨810478473626538533541079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1080637964835384711388105 810478473626538533541079)
                ·
                  refine ⟨1215717710439807800311619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 810478473626538533541079 1215717710439807800311619)
                  ·
                    refine ⟨1823576565659711700467429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1215717710439807800311619 1823576565659711700467429)
                    ·
                      refine ⟨341920606061195943837643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1823576565659711700467429 341920606061195943837643)
                      ·
                        rfl

theorem cell23_665888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_665888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_665888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_665888 prefixEnd_665888 := by exact prefixLift 665888
  have htrace : WordTrace (prefixWord ++ tailWord_665888) baseStart_665888 baseEnd_665888 := by
    simpa [prefixWord, tailWord_665888, baseEnd_665888] using wordTrace_append hprefix tailTrace_665888
  have hstable : (prefixWord ++ tailWord_665888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665888).length < 2 ^ (prefixWord ++ tailWord_665888).sum := by decide
  have hdescent : baseEnd_665888 < baseStart_665888 := by decide
  rcases family_descends (prefixWord ++ tailWord_665888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665908 : List Nat := [2, 5, 1, 1, 1, 3, 2, 1, 1, 1, 5]
def baseStart_665908 : Nat := 118140960795 + 665908 * 2 ^ 59
def prefixEnd_665908 : Nat := 4983230072969 + 3 ^ 40 * 665908 * 2
def baseEnd_665908 : Nat := 341930875674285865587551

theorem tailTrace_665908 : CollatzResearch.WordTrace tailWord_665908 prefixEnd_665908 341930875674285865587551 := by
  unfold tailWord_665908
  simp only [CollatzResearch.WordTrace]
  refine ⟨12143830035768259438579189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16191773381024345918105585 12143830035768259438579189)
  ·
    refine ⟨1138484065853274322366799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12143830035768259438579189 1138484065853274322366799)
    ·
      refine ⟨1707726098779911483550199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1138484065853274322366799 1707726098779911483550199)
      ·
        refine ⟨2561589148169867225325299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1707726098779911483550199 2561589148169867225325299)
        ·
          refine ⟨3842383722254800837987949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2561589148169867225325299 3842383722254800837987949)
          ·
            refine ⟨1440893895845550314245481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3842383722254800837987949 1440893895845550314245481)
            ·
              refine ⟨1080670421884162735684111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1440893895845550314245481 1080670421884162735684111)
              ·
                refine ⟨1621005632826244103526167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1080670421884162735684111 1621005632826244103526167)
                ·
                  refine ⟨2431508449239366155289251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1621005632826244103526167 2431508449239366155289251)
                  ·
                    refine ⟨3647262673859049232933877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2431508449239366155289251 3647262673859049232933877)
                    ·
                      refine ⟨341930875674285865587551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3647262673859049232933877 341930875674285865587551)
                      ·
                        rfl

theorem cell23_665908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_665908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_665908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_665908 prefixEnd_665908 := by exact prefixLift 665908
  have htrace : WordTrace (prefixWord ++ tailWord_665908) baseStart_665908 baseEnd_665908 := by
    simpa [prefixWord, tailWord_665908, baseEnd_665908] using wordTrace_append hprefix tailTrace_665908
  have hstable : (prefixWord ++ tailWord_665908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665908).length < 2 ^ (prefixWord ++ tailWord_665908).sum := by decide
  have hdescent : baseEnd_665908 < baseStart_665908 := by decide
  rcases family_descends (prefixWord ++ tailWord_665908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665934 : List Nat := [4, 1, 1, 1, 1, 1, 2, 2, 1, 4, 5]
def baseStart_665934 : Nat := 118140960795 + 665934 * 2 ^ 59
def prefixEnd_665934 : Nat := 4983230072969 + 3 ^ 40 * 665934 * 2
def baseEnd_665934 : Nat := 341944226171302763862431

theorem tailTrace_665934 : CollatzResearch.WordTrace tailWord_665934 prefixEnd_665934 341944226171302763862431 := by
  unfold tailWord_665934
  simp only [CollatzResearch.WordTrace]
  refine ⟨3036076046180290664700607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16192405579628216878403237 3036076046180290664700607)
  ·
    refine ⟨4554114069270435997050911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3036076046180290664700607 4554114069270435997050911)
    ·
      refine ⟨6831171103905653995576367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4554114069270435997050911 6831171103905653995576367)
      ·
        refine ⟨10246756655858480993364551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6831171103905653995576367 10246756655858480993364551)
        ·
          refine ⟨15370134983787721490046827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10246756655858480993364551 15370134983787721490046827)
          ·
            refine ⟨23055202475681582235070241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15370134983787721490046827 23055202475681582235070241)
            ·
              refine ⟨17291401856761186676302681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23055202475681582235070241 17291401856761186676302681)
              ·
                refine ⟨12968551392570890007227011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17291401856761186676302681 12968551392570890007227011)
                ·
                  refine ⟨19452827088856335010840517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12968551392570890007227011 19452827088856335010840517)
                  ·
                    refine ⟨3647405079160562814532597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19452827088856335010840517 3647405079160562814532597)
                    ·
                      refine ⟨341944226171302763862431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3647405079160562814532597 341944226171302763862431)
                      ·
                        rfl

theorem cell23_665934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_665934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_665934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_665934 prefixEnd_665934 := by exact prefixLift 665934
  have htrace : WordTrace (prefixWord ++ tailWord_665934) baseStart_665934 baseEnd_665934 := by
    simpa [prefixWord, tailWord_665934, baseEnd_665934] using wordTrace_append hprefix tailTrace_665934
  have hstable : (prefixWord ++ tailWord_665934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665934).length < 2 ^ (prefixWord ++ tailWord_665934).sum := by decide
  have hdescent : baseEnd_665934 < baseStart_665934 := by decide
  rcases family_descends (prefixWord ++ tailWord_665934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665944 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 4, 3, 4]
def baseStart_665944 : Nat := 118140960795 + 665944 * 2 ^ 59
def prefixEnd_665944 : Nat := 4983230072969 + 3 ^ 40 * 665944 * 2
def baseEnd_665944 : Nat := 341949360977847724737385

theorem tailTrace_665944 : CollatzResearch.WordTrace tailWord_665944 prefixEnd_665944 341949360977847724737385 := by
  unfold tailWord_665944
  simp only [CollatzResearch.WordTrace]
  refine ⟨12144486549703048512734443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16192648732937398016979257 12144486549703048512734443)
  ·
    refine ⟨18216729824554572769101665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12144486549703048512734443 18216729824554572769101665)
    ·
      refine ⟨13662547368415929576826249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18216729824554572769101665 13662547368415929576826249)
      ·
        refine ⟨10246910526311947182619687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13662547368415929576826249 10246910526311947182619687)
        ·
          refine ⟨15370365789467920773929531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10246910526311947182619687 15370365789467920773929531)
          ·
            refine ⟨23055548684201881160894297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15370365789467920773929531 23055548684201881160894297)
            ·
              refine ⟨17291661513151410870670723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23055548684201881160894297 17291661513151410870670723)
              ·
                refine ⟨25937492269727116306006085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17291661513151410870670723 25937492269727116306006085)
                ·
                  refine ⟨4863279800573834307376141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25937492269727116306006085 4863279800573834307376141)
                  ·
                    refine ⟨1823729925215187865266053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4863279800573834307376141 1823729925215187865266053)
                    ·
                      refine ⟨341949360977847724737385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1823729925215187865266053 341949360977847724737385)
                      ·
                        rfl

theorem cell23_665944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_665944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_665944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_665944 prefixEnd_665944 := by exact prefixLift 665944
  have htrace : WordTrace (prefixWord ++ tailWord_665944) baseStart_665944 baseEnd_665944 := by
    simpa [prefixWord, tailWord_665944, baseEnd_665944] using wordTrace_append hprefix tailTrace_665944
  have hstable : (prefixWord ++ tailWord_665944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665944).length < 2 ^ (prefixWord ++ tailWord_665944).sum := by decide
  have hdescent : baseEnd_665944 < baseStart_665944 := by decide
  rcases family_descends (prefixWord ++ tailWord_665944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665981 : List Nat := [1, 4, 1, 1, 2, 3, 1, 1, 2, 4, 3]
def baseStart_665981 : Nat := 118140960795 + 665981 * 2 ^ 59
def prefixEnd_665981 : Nat := 4983230072969 + 3 ^ 40 * 665981 * 2
def baseEnd_665981 : Nat := 341968359762064079974715

theorem tailTrace_665981 : CollatzResearch.WordTrace tailWord_665981 prefixEnd_665981 341968359762064079974715 := by
  unfold tailWord_665981
  simp only [CollatzResearch.WordTrace]
  refine ⟨24290322600272052344565797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16193548400181368229710531 24290322600272052344565797)
  ·
    refine ⟨4554435487551009814606087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24290322600272052344565797 4554435487551009814606087)
    ·
      refine ⟨6831653231326514721909131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4554435487551009814606087 6831653231326514721909131)
      ·
        refine ⟨10247479846989772082863697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6831653231326514721909131 10247479846989772082863697)
        ·
          refine ⟨7685609885242329062147773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10247479846989772082863697 7685609885242329062147773)
          ·
            refine ⟨2882103706965873398305415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7685609885242329062147773 2882103706965873398305415)
            ·
              refine ⟨4323155560448810097458123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2882103706965873398305415 4323155560448810097458123)
              ·
                refine ⟨6484733340673215146187185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4323155560448810097458123 6484733340673215146187185)
                ·
                  refine ⟨4863550005504911359640389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6484733340673215146187185 4863550005504911359640389)
                  ·
                    refine ⟨911915626032170879932573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4863550005504911359640389 911915626032170879932573)
                    ·
                      refine ⟨341968359762064079974715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 911915626032170879932573 341968359762064079974715)
                      ·
                        rfl

theorem cell23_665981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 4, 3].length) (baseStart_665981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_665981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_665981 prefixEnd_665981 := by exact prefixLift 665981
  have htrace : WordTrace (prefixWord ++ tailWord_665981) baseStart_665981 baseEnd_665981 := by
    simpa [prefixWord, tailWord_665981, baseEnd_665981] using wordTrace_append hprefix tailTrace_665981
  have hstable : (prefixWord ++ tailWord_665981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665981).length < 2 ^ (prefixWord ++ tailWord_665981).sum := by decide
  have hdescent : baseEnd_665981 < baseStart_665981 := by decide
  rcases family_descends (prefixWord ++ tailWord_665981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665991 : List Nat := [1, 1, 4, 2, 2, 1, 3, 1, 2, 2, 4]
def baseStart_665991 : Nat := 118140960795 + 665991 * 2 ^ 59
def prefixEnd_665991 : Nat := 4983230072969 + 3 ^ 40 * 665991 * 2
def baseEnd_665991 : Nat := 341973494568609040849669

theorem tailTrace_665991 : CollatzResearch.WordTrace tailWord_665991 prefixEnd_665991 341973494568609040849669 := by
  unfold tailWord_665991
  simp only [CollatzResearch.WordTrace]
  refine ⟨24290687330235824052429827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16193791553490549368286551 24290687330235824052429827)
  ·
    refine ⟨36436030995353736078644741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24290687330235824052429827 36436030995353736078644741)
    ·
      refine ⟨6831755811628825514745889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36436030995353736078644741 6831755811628825514745889)
      ·
        refine ⟨5123816858721619136059417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6831755811628825514745889 5123816858721619136059417)
        ·
          refine ⟨3842862644041214352044563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5123816858721619136059417 3842862644041214352044563)
          ·
            refine ⟨5764293966061821528066845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3842862644041214352044563 5764293966061821528066845)
            ·
              refine ⟨2161610237273183073025067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5764293966061821528066845 2161610237273183073025067)
              ·
                refine ⟨3242415355909774609537601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2161610237273183073025067 3242415355909774609537601)
                ·
                  refine ⟨2431811516932330957153201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3242415355909774609537601 2431811516932330957153201)
                  ·
                    refine ⟨1823858637699248217864901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2431811516932330957153201 1823858637699248217864901)
                    ·
                      refine ⟨341973494568609040849669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1823858637699248217864901 341973494568609040849669)
                      ·
                        rfl

theorem cell23_665991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_665991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_665991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_665991 prefixEnd_665991 := by exact prefixLift 665991
  have htrace : WordTrace (prefixWord ++ tailWord_665991) baseStart_665991 baseEnd_665991 := by
    simpa [prefixWord, tailWord_665991, baseEnd_665991] using wordTrace_append hprefix tailTrace_665991
  have hstable : (prefixWord ++ tailWord_665991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665991).length < 2 ^ (prefixWord ++ tailWord_665991).sum := by decide
  have hdescent : baseEnd_665991 < baseStart_665991 := by decide
  rcases family_descends (prefixWord ++ tailWord_665991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_665995 : List Nat := [1, 1, 1, 1, 4, 4, 2, 3, 2, 2, 2]
def baseStart_665995 : Nat := 118140960795 + 665995 * 2 ^ 59
def prefixEnd_665995 : Nat := 4983230072969 + 3 ^ 40 * 665995 * 2
def baseEnd_665995 : Nat := 341975548491227025199651

theorem tailTrace_665995 : CollatzResearch.WordTrace tailWord_665995 prefixEnd_665995 341975548491227025199651 := by
  unfold tailWord_665995
  simp only [CollatzResearch.WordTrace]
  refine ⟨24290833222221332735575439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16193888814814221823716959 24290833222221332735575439)
  ·
    refine ⟨36436249833331999103363159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24290833222221332735575439 36436249833331999103363159)
    ·
      refine ⟨54654374749997998655044739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36436249833331999103363159 54654374749997998655044739)
      ·
        refine ⟨81981562124996997982567109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54654374749997998655044739 81981562124996997982567109)
        ·
          refine ⟨15371542898436937121731333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81981562124996997982567109 15371542898436937121731333)
          ·
            refine ⟨2882164293456925710324625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15371542898436937121731333 2882164293456925710324625)
            ·
              refine ⟨2161623220092694282743469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2882164293456925710324625 2161623220092694282743469)
              ·
                refine ⟨810608707534760356028801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2161623220092694282743469 810608707534760356028801)
                ·
                  refine ⟨607956530651070267021601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 810608707534760356028801 607956530651070267021601)
                  ·
                    refine ⟨455967397988302700266201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 607956530651070267021601 455967397988302700266201)
                    ·
                      refine ⟨341975548491227025199651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 455967397988302700266201 341975548491227025199651)
                      ·
                        rfl

theorem cell23_665995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 3, 2, 2, 2].length) (baseStart_665995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_665995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_665995 prefixEnd_665995 := by exact prefixLift 665995
  have htrace : WordTrace (prefixWord ++ tailWord_665995) baseStart_665995 baseEnd_665995 := by
    simpa [prefixWord, tailWord_665995, baseEnd_665995] using wordTrace_append hprefix tailTrace_665995
  have hstable : (prefixWord ++ tailWord_665995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_665995).length < 2 ^ (prefixWord ++ tailWord_665995).sum := by decide
  have hdescent : baseEnd_665995 < baseStart_665995 := by decide
  rcases family_descends (prefixWord ++ tailWord_665995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666068 : List Nat := [2, 4, 1, 2, 2, 1, 2, 1, 1, 3, 4]
def baseStart_666068 : Nat := 118140960795 + 666068 * 2 ^ 59
def prefixEnd_666068 : Nat := 4983230072969 + 3 ^ 40 * 666068 * 2
def baseEnd_666068 : Nat := 342013032579005239586815

theorem tailTrace_666068 : CollatzResearch.WordTrace tailWord_666068 prefixEnd_666068 342013032579005239586815 := by
  unfold tailWord_666068
  simp only [CollatzResearch.WordTrace]
  refine ⟨12146747875478433101491429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16195663833971244135321905 12146747875478433101491429)
  ·
    refine ⟨2277515226652206206529643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12146747875478433101491429 2277515226652206206529643)
    ·
      refine ⟨3416272839978309309794465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2277515226652206206529643 3416272839978309309794465)
      ·
        refine ⟨2562204629983731982345849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3416272839978309309794465 2562204629983731982345849)
        ·
          refine ⟨1921653472487798986759387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2562204629983731982345849 1921653472487798986759387)
          ·
            refine ⟨2882480208731698480139081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1921653472487798986759387 2882480208731698480139081)
            ·
              refine ⟨2161860156548773860104311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2882480208731698480139081 2161860156548773860104311)
              ·
                refine ⟨3242790234823160790156467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2161860156548773860104311 3242790234823160790156467)
                ·
                  refine ⟨4864185352234741185234701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3242790234823160790156467 4864185352234741185234701)
                  ·
                    refine ⟨1824069507088027944463013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4864185352234741185234701 1824069507088027944463013)
                    ·
                      refine ⟨342013032579005239586815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1824069507088027944463013 342013032579005239586815)
                      ·
                        rfl

theorem cell23_666068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_666068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_666068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_666068 prefixEnd_666068 := by exact prefixLift 666068
  have htrace : WordTrace (prefixWord ++ tailWord_666068) baseStart_666068 baseEnd_666068 := by
    simpa [prefixWord, tailWord_666068, baseEnd_666068] using wordTrace_append hprefix tailTrace_666068
  have hstable : (prefixWord ++ tailWord_666068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666068).length < 2 ^ (prefixWord ++ tailWord_666068).sum := by decide
  have hdescent : baseEnd_666068 < baseStart_666068 := by decide
  rcases family_descends (prefixWord ++ tailWord_666068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666082 : List Nat := [3, 3, 3, 2, 1, 1, 1, 2, 2, 5]
def baseStart_666082 : Nat := 118140960795 + 666082 * 2 ^ 59
def prefixEnd_666082 : Nat := 4983230072969 + 3 ^ 40 * 666082 * 2
def baseEnd_666082 : Nat := 114006740436056061603917

theorem tailTrace_666082 : CollatzResearch.WordTrace tailWord_666082 prefixEnd_666082 114006740436056061603917 := by
  unfold tailWord_666082
  simp only [CollatzResearch.WordTrace]
  refine ⟨6073501593226536648498125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16196004248604097729328333 6073501593226536648498125)
  ·
    refine ⟨2277563097459951243186797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6073501593226536648498125 2277563097459951243186797)
    ·
      refine ⟨854086161547481716195049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2277563097459951243186797 854086161547481716195049)
      ·
        refine ⟨640564621160611287146287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 854086161547481716195049 640564621160611287146287)
        ·
          refine ⟨960846931740916930719431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 640564621160611287146287 960846931740916930719431)
          ·
            refine ⟨1441270397611375396079147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 960846931740916930719431 1441270397611375396079147)
            ·
              refine ⟨2161905596417063094118721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1441270397611375396079147 2161905596417063094118721)
              ·
                refine ⟨1621429197312797320589041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2161905596417063094118721 1621429197312797320589041)
                ·
                  refine ⟨1216071897984597990441781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1621429197312797320589041 1216071897984597990441781)
                  ·
                    refine ⟨114006740436056061603917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1216071897984597990441781 114006740436056061603917)
                    ·
                      rfl

theorem cell23_666082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_666082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_666082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_666082 prefixEnd_666082 := by exact prefixLift 666082
  have htrace : WordTrace (prefixWord ++ tailWord_666082) baseStart_666082 baseEnd_666082 := by
    simpa [prefixWord, tailWord_666082, baseEnd_666082] using wordTrace_append hprefix tailTrace_666082
  have hstable : (prefixWord ++ tailWord_666082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666082).length < 2 ^ (prefixWord ++ tailWord_666082).sum := by decide
  have hdescent : baseEnd_666082 < baseStart_666082 := by decide
  rcases family_descends (prefixWord ++ tailWord_666082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666085 : List Nat := [1, 3, 1, 5, 2, 1, 1, 2, 2, 1, 4]
def baseStart_666085 : Nat := 118140960795 + 666085 * 2 ^ 59
def prefixEnd_666085 : Nat := 4983230072969 + 3 ^ 40 * 666085 * 2
def baseEnd_666085 : Nat := 342021761750131673074237

theorem tailTrace_666085 : CollatzResearch.WordTrace tailWord_666085 prefixEnd_666085 342021761750131673074237 := by
  unfold tailWord_666085
  simp only [CollatzResearch.WordTrace]
  refine ⟨24294115791895278106351709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16196077194596852070901139 24294115791895278106351709)
  ·
    refine ⟨9110293421960729289881891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24294115791895278106351709 9110293421960729289881891)
    ·
      refine ⟨13665440132941093934822837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9110293421960729289881891 13665440132941093934822837)
      ·
        refine ⟨1281135012463227556389641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13665440132941093934822837 1281135012463227556389641)
        ·
          refine ⟨960851259347420667292231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1281135012463227556389641 960851259347420667292231)
          ·
            refine ⟨1441276889021131000938347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 960851259347420667292231 1441276889021131000938347)
            ·
              refine ⟨2161915333531696501407521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1441276889021131000938347 2161915333531696501407521)
              ·
                refine ⟨1621436500148772376055641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2161915333531696501407521 1621436500148772376055641)
                ·
                  refine ⟨1216077375111579282041731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1621436500148772376055641 1216077375111579282041731)
                  ·
                    refine ⟨1824116062667368923062597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1216077375111579282041731 1824116062667368923062597)
                    ·
                      refine ⟨342021761750131673074237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1824116062667368923062597 342021761750131673074237)
                      ·
                        rfl

theorem cell23_666085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_666085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_666085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_666085 prefixEnd_666085 := by exact prefixLift 666085
  have htrace : WordTrace (prefixWord ++ tailWord_666085) baseStart_666085 baseEnd_666085 := by
    simpa [prefixWord, tailWord_666085, baseEnd_666085] using wordTrace_append hprefix tailTrace_666085
  have hstable : (prefixWord ++ tailWord_666085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666085).length < 2 ^ (prefixWord ++ tailWord_666085).sum := by decide
  have hdescent : baseEnd_666085 < baseStart_666085 := by decide
  rcases family_descends (prefixWord ++ tailWord_666085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666088 : List Nat := [2, 1, 4, 1, 1, 3, 1, 1, 4, 2, 3]
def baseStart_666088 : Nat := 118140960795 + 666088 * 2 ^ 59
def prefixEnd_666088 : Nat := 4983230072969 + 3 ^ 40 * 666088 * 2
def baseEnd_666088 : Nat := 342023302192095161336723

theorem tailTrace_666088 : CollatzResearch.WordTrace tailWord_666088 prefixEnd_666088 342023302192095161336723 := by
  unfold tailWord_666088
  simp only [CollatzResearch.WordTrace]
  refine ⟨12147112605442204809355459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16196150140589606412473945 12147112605442204809355459)
  ·
    refine ⟨18220668908163307214033189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12147112605442204809355459 18220668908163307214033189)
    ·
      refine ⟨3416375420280620102631223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18220668908163307214033189 3416375420280620102631223)
      ·
        refine ⟨5124563130420930153946835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3416375420280620102631223 5124563130420930153946835)
        ·
          refine ⟨7686844695631395230920253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5124563130420930153946835 7686844695631395230920253)
          ·
            refine ⟨2882566760861773211595095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7686844695631395230920253 2882566760861773211595095)
            ·
              refine ⟨4323850141292659817392643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2882566760861773211595095 4323850141292659817392643)
              ·
                refine ⟨6485775211938989726088965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4323850141292659817392643 6485775211938989726088965)
                ·
                  refine ⟨1216082852238560573641681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6485775211938989726088965 1216082852238560573641681)
                  ·
                    refine ⟨912062139178920430231261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1216082852238560573641681 912062139178920430231261)
                    ·
                      refine ⟨342023302192095161336723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 912062139178920430231261 342023302192095161336723)
                      ·
                        rfl

theorem cell23_666088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_666088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_666088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_666088 prefixEnd_666088 := by exact prefixLift 666088
  have htrace : WordTrace (prefixWord ++ tailWord_666088) baseStart_666088 baseEnd_666088 := by
    simpa [prefixWord, tailWord_666088, baseEnd_666088] using wordTrace_append hprefix tailTrace_666088
  have hstable : (prefixWord ++ tailWord_666088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666088).length < 2 ^ (prefixWord ++ tailWord_666088).sum := by decide
  have hdescent : baseEnd_666088 < baseStart_666088 := by decide
  rcases family_descends (prefixWord ++ tailWord_666088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666091 : List Nat := [1, 1, 1, 1, 2, 3, 4, 4, 6]
def baseStart_666091 : Nat := 118140960795 + 666091 * 2 ^ 59
def prefixEnd_666091 : Nat := 4983230072969 + 3 ^ 40 * 666091 * 2
def baseEnd_666091 : Nat := 38002760292673183288801

theorem tailTrace_666091 : CollatzResearch.WordTrace tailWord_666091 prefixEnd_666091 38002760292673183288801 := by
  unfold tailWord_666091
  simp only [CollatzResearch.WordTrace]
  refine ⟨24294334629873541131070127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16196223086582360754046751 24294334629873541131070127)
  ·
    refine ⟨36441501944810311696605191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24294334629873541131070127 36441501944810311696605191)
    ·
      refine ⟨54662252917215467544907787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36441501944810311696605191 54662252917215467544907787)
      ·
        refine ⟨81993379375823201317361681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54662252917215467544907787 81993379375823201317361681)
        ·
          refine ⟨61495034531867400988021261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81993379375823201317361681 61495034531867400988021261)
          ·
            refine ⟨23060637949450275370507973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61495034531867400988021261 23060637949450275370507973)
            ·
              refine ⟨4323869615521926631970245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23060637949450275370507973 4323869615521926631970245)
              ·
                refine ⟨810725552910361243494421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4323869615521926631970245 810725552910361243494421)
                ·
                  refine ⟨38002760292673183288801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 810725552910361243494421 38002760292673183288801)
                  ·
                    rfl

theorem cell23_666091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 4, 6].length) (baseStart_666091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_666091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_666091 prefixEnd_666091 := by exact prefixLift 666091
  have htrace : WordTrace (prefixWord ++ tailWord_666091) baseStart_666091 baseEnd_666091 := by
    simpa [prefixWord, tailWord_666091, baseEnd_666091] using wordTrace_append hprefix tailTrace_666091
  have hstable : (prefixWord ++ tailWord_666091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666091).length < 2 ^ (prefixWord ++ tailWord_666091).sum := by decide
  have hdescent : baseEnd_666091 < baseStart_666091 := by decide
  rcases family_descends (prefixWord ++ tailWord_666091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666138 : List Nat := [3, 1, 1, 3, 1, 1, 2, 5, 1, 5]
def baseStart_666138 : Nat := 118140960795 + 666138 * 2 ^ 59
def prefixEnd_666138 : Nat := 4983230072969 + 3 ^ 40 * 666138 * 2
def baseEnd_666138 : Nat := 114016325408273321903831

theorem tailTrace_666138 : CollatzResearch.WordTrace tailWord_666138 prefixEnd_666138 114016325408273321903831 := by
  unfold tailWord_666138
  simp only [CollatzResearch.WordTrace]
  refine ⟨6074012215175817039507767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16197365907135512105354045 6074012215175817039507767)
  ·
    refine ⟨9111018322763725559261651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6074012215175817039507767 9111018322763725559261651)
    ·
      refine ⟨13666527484145588338892477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9111018322763725559261651 13666527484145588338892477)
      ·
        refine ⟨5124947806554595627084679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13666527484145588338892477 5124947806554595627084679)
        ·
          refine ⟨7687421709831893440627019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5124947806554595627084679 7687421709831893440627019)
          ·
            refine ⟨11531132564747840160940529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7687421709831893440627019 11531132564747840160940529)
            ·
              refine ⟨8648349423560880120705397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11531132564747840160940529 8648349423560880120705397)
              ·
                refine ⟨810782758458832511316131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8648349423560880120705397 810782758458832511316131)
                ·
                  refine ⟨1216174137688248766974197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 810782758458832511316131 1216174137688248766974197)
                  ·
                    refine ⟨114016325408273321903831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1216174137688248766974197 114016325408273321903831)
                    ·
                      rfl

theorem cell23_666138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 5, 1, 5].length) (baseStart_666138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_666138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_666138 prefixEnd_666138 := by exact prefixLift 666138
  have htrace : WordTrace (prefixWord ++ tailWord_666138) baseStart_666138 baseEnd_666138 := by
    simpa [prefixWord, tailWord_666138, baseEnd_666138] using wordTrace_append hprefix tailTrace_666138
  have hstable : (prefixWord ++ tailWord_666138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666138).length < 2 ^ (prefixWord ++ tailWord_666138).sum := by decide
  have hdescent : baseEnd_666138 < baseStart_666138 := by decide
  rcases family_descends (prefixWord ++ tailWord_666138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666145 : List Nat := [1, 2, 3, 2, 2, 1, 1, 4, 2, 3, 2]
def baseStart_666145 : Nat := 118140960795 + 666145 * 2 ^ 59
def prefixEnd_666145 : Nat := 4983230072969 + 3 ^ 40 * 666145 * 2
def baseEnd_666145 : Nat := 342052570589401438323961

theorem tailTrace_666145 : CollatzResearch.WordTrace tailWord_666145 prefixEnd_666145 342052570589401438323961 := by
  unfold tailWord_666145
  simp only [CollatzResearch.WordTrace]
  refine ⟨24296304171677908353535889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16197536114451938902357259 24296304171677908353535889)
  ·
    refine ⟨18222228128758431265151917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24296304171677908353535889 18222228128758431265151917)
    ·
      refine ⟨6833335548284411724431969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18222228128758431265151917 6833335548284411724431969)
      ·
        refine ⟨5125001661213308793323977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6833335548284411724431969 5125001661213308793323977)
        ·
          refine ⟨3843751245909981594992983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5125001661213308793323977 3843751245909981594992983)
          ·
            refine ⟨5765626868864972392489475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3843751245909981594992983 5765626868864972392489475)
            ·
              refine ⟨8648440303297458588734213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5765626868864972392489475 8648440303297458588734213)
              ·
                refine ⟨1621582556868273485387665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8648440303297458588734213 1621582556868273485387665)
                ·
                  refine ⟨1216186917651205114040749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1621582556868273485387665 1216186917651205114040749)
                  ·
                    refine ⟨456070094119201917765281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1216186917651205114040749 456070094119201917765281)
                    ·
                      refine ⟨342052570589401438323961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 456070094119201917765281 342052570589401438323961)
                      ·
                        rfl

theorem cell23_666145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 2, 3, 2].length) (baseStart_666145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_666145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_666145 prefixEnd_666145 := by exact prefixLift 666145
  have htrace : WordTrace (prefixWord ++ tailWord_666145) baseStart_666145 baseEnd_666145 := by
    simpa [prefixWord, tailWord_666145, baseEnd_666145] using wordTrace_append hprefix tailTrace_666145
  have hstable : (prefixWord ++ tailWord_666145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666145).length < 2 ^ (prefixWord ++ tailWord_666145).sum := by decide
  have hdescent : baseEnd_666145 < baseStart_666145 := by decide
  rcases family_descends (prefixWord ++ tailWord_666145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666168 : List Nat := [2, 1, 2, 1, 4, 1, 4, 1, 1, 6]
def baseStart_666168 : Nat := 118140960795 + 666168 * 2 ^ 59
def prefixEnd_666168 : Nat := 4983230072969 + 3 ^ 40 * 666168 * 2
def baseEnd_666168 : Nat := 114021460214818282778785

theorem tailTrace_666168 : CollatzResearch.WordTrace tailWord_666168 prefixEnd_666168 114021460214818282778785 := by
  unfold tailWord_666168
  simp only [CollatzResearch.WordTrace]
  refine ⟨12148571525297291640811579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16198095367063055521082105 12148571525297291640811579)
  ·
    refine ⟨18222857287945937461217369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12148571525297291640811579 18222857287945937461217369)
    ·
      refine ⟨13667142965959453095913027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18222857287945937461217369 13667142965959453095913027)
      ·
        refine ⟨20500714448939179643869541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13667142965959453095913027 20500714448939179643869541)
        ·
          refine ⟨3843883959176096183225539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20500714448939179643869541 3843883959176096183225539)
          ·
            refine ⟨5765825938764144274838309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3843883959176096183225539 5765825938764144274838309)
            ·
              refine ⟨1081092363518277051532183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5765825938764144274838309 1081092363518277051532183)
              ·
                refine ⟨1621638545277415577298275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1081092363518277051532183 1621638545277415577298275)
                ·
                  refine ⟨2432457817916123365947413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1621638545277415577298275 2432457817916123365947413)
                  ·
                    refine ⟨114021460214818282778785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2432457817916123365947413 114021460214818282778785)
                    ·
                      rfl

theorem cell23_666168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 1, 6].length) (baseStart_666168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_666168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_666168 prefixEnd_666168 := by exact prefixLift 666168
  have htrace : WordTrace (prefixWord ++ tailWord_666168) baseStart_666168 baseEnd_666168 := by
    simpa [prefixWord, tailWord_666168, baseEnd_666168] using wordTrace_append hprefix tailTrace_666168
  have hstable : (prefixWord ++ tailWord_666168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666168).length < 2 ^ (prefixWord ++ tailWord_666168).sum := by decide
  have hdescent : baseEnd_666168 < baseStart_666168 := by decide
  rcases family_descends (prefixWord ++ tailWord_666168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666188 : List Nat := [2, 2, 1, 3, 1, 2, 1, 4, 1, 2, 4]
def baseStart_666188 : Nat := 118140960795 + 666188 * 2 ^ 59
def prefixEnd_666188 : Nat := 4983230072969 + 3 ^ 40 * 666188 * 2
def baseEnd_666188 : Nat := 342074650257544770086263

theorem tailTrace_666188 : CollatzResearch.WordTrace tailWord_666188 prefixEnd_666188 342074650257544770086263 := by
  unfold tailWord_666188
  simp only [CollatzResearch.WordTrace]
  refine ⟨12148936255261063348675609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16198581673681417798234145 12148936255261063348675609)
  ·
    refine ⟨9111702191445797511506707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12148936255261063348675609 9111702191445797511506707)
    ·
      refine ⟨13667553287168696267260061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9111702191445797511506707 13667553287168696267260061)
      ·
        refine ⟨5125332482688261100222523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13667553287168696267260061 5125332482688261100222523)
        ·
          refine ⟨7687998724032391650333785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5125332482688261100222523 7687998724032391650333785)
          ·
            refine ⟨5765999043024293737750339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7687998724032391650333785 5765999043024293737750339)
            ·
              refine ⟨8648998564536440606625509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5765999043024293737750339 8648998564536440606625509)
              ·
                refine ⟨1621687230850582613742283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8648998564536440606625509 1621687230850582613742283)
                ·
                  refine ⟨2432530846275873920613425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1621687230850582613742283 2432530846275873920613425)
                  ·
                    refine ⟨1824398134706905440460069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2432530846275873920613425 1824398134706905440460069)
                    ·
                      refine ⟨342074650257544770086263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1824398134706905440460069 342074650257544770086263)
                      ·
                        rfl

theorem cell23_666188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_666188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_666188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_666188 prefixEnd_666188 := by exact prefixLift 666188
  have htrace : WordTrace (prefixWord ++ tailWord_666188) baseStart_666188 baseEnd_666188 := by
    simpa [prefixWord, tailWord_666188, baseEnd_666188] using wordTrace_append hprefix tailTrace_666188
  have hstable : (prefixWord ++ tailWord_666188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666188).length < 2 ^ (prefixWord ++ tailWord_666188).sum := by decide
  have hdescent : baseEnd_666188 < baseStart_666188 := by decide
  rcases family_descends (prefixWord ++ tailWord_666188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666189 : List Nat := [1, 6, 1, 1, 2, 3, 2, 1, 1, 5]
def baseStart_666189 : Nat := 118140960795 + 666189 * 2 ^ 59
def prefixEnd_666189 : Nat := 4983230072969 + 3 ^ 40 * 666189 * 2
def baseEnd_666189 : Nat := 114025054579399755391253

theorem tailTrace_666189 : CollatzResearch.WordTrace tailWord_666189 prefixEnd_666189 114025054579399755391253 := by
  unfold tailWord_666189
  simp only [CollatzResearch.WordTrace]
  refine ⟨24297908983518503868137621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16198605989012335912091747 24297908983518503868137621)
  ·
    refine ⟨1138964483602429868818951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 24297908983518503868137621 1138964483602429868818951)
    ·
      refine ⟨1708446725403644803228427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1138964483602429868818951 1708446725403644803228427)
      ·
        refine ⟨2562670088105467204842641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1708446725403644803228427 2562670088105467204842641)
        ·
          refine ⟨1922002566079100403631981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2562670088105467204842641 1922002566079100403631981)
          ·
            refine ⟨720750962279662651361993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1922002566079100403631981 720750962279662651361993)
            ·
              refine ⟨540563221709746988521495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 720750962279662651361993 540563221709746988521495)
              ·
                refine ⟨810844832564620482782243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 540563221709746988521495 810844832564620482782243)
                ·
                  refine ⟨1216267248846930724173365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 810844832564620482782243 1216267248846930724173365)
                  ·
                    refine ⟨114025054579399755391253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1216267248846930724173365 114025054579399755391253)
                    ·
                      rfl

theorem cell23_666189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_666189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_666189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_666189 prefixEnd_666189 := by exact prefixLift 666189
  have htrace : WordTrace (prefixWord ++ tailWord_666189) baseStart_666189 baseEnd_666189 := by
    simpa [prefixWord, tailWord_666189, baseEnd_666189] using wordTrace_append hprefix tailTrace_666189
  have hstable : (prefixWord ++ tailWord_666189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666189).length < 2 ^ (prefixWord ++ tailWord_666189).sum := by decide
  have hdescent : baseEnd_666189 < baseStart_666189 := by decide
  rcases family_descends (prefixWord ++ tailWord_666189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666201 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 4, 2, 6]
def baseStart_666201 : Nat := 118140960795 + 666201 * 2 ^ 59
def prefixEnd_666201 : Nat := 4983230072969 + 3 ^ 40 * 666201 * 2
def baseEnd_666201 : Nat := 342081325506053219223703

theorem tailTrace_666201 : CollatzResearch.WordTrace tailWord_666201 prefixEnd_666201 342081325506053219223703 := by
  unfold tailWord_666201
  simp only [CollatzResearch.WordTrace]
  refine ⟨24298346659475029917574457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16198897772983353278382971 24298346659475029917574457)
  ·
    refine ⟨18223759994606272438180843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24298346659475029917574457 18223759994606272438180843)
    ·
      refine ⟨27335639991909408657271265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18223759994606272438180843 27335639991909408657271265)
      ·
        refine ⟨20501729993932056492953449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27335639991909408657271265 20501729993932056492953449)
        ·
          refine ⟨15376297495449042369715087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20501729993932056492953449 15376297495449042369715087)
          ·
            refine ⟨23064446243173563554572631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15376297495449042369715087 23064446243173563554572631)
            ·
              refine ⟨34596669364760345331858947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23064446243173563554572631 34596669364760345331858947)
              ·
                refine ⟨51895004047140517997788421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34596669364760345331858947 51895004047140517997788421)
                ·
                  refine ⟨9730313258838847124585329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51895004047140517997788421 9730313258838847124585329)
                  ·
                    refine ⟨7297734944129135343438997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9730313258838847124585329 7297734944129135343438997)
                    ·
                      refine ⟨342081325506053219223703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7297734944129135343438997 342081325506053219223703)
                      ·
                        rfl

theorem cell23_666201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 2, 6].length) (baseStart_666201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_666201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_666201 prefixEnd_666201 := by exact prefixLift 666201
  have htrace : WordTrace (prefixWord ++ tailWord_666201) baseStart_666201 baseEnd_666201 := by
    simpa [prefixWord, tailWord_666201, baseEnd_666201] using wordTrace_append hprefix tailTrace_666201
  have hstable : (prefixWord ++ tailWord_666201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666201).length < 2 ^ (prefixWord ++ tailWord_666201).sum := by decide
  have hdescent : baseEnd_666201 < baseStart_666201 := by decide
  rcases family_descends (prefixWord ++ tailWord_666201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666208 : List Nat := [2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 3]
def baseStart_666208 : Nat := 118140960795 + 666208 * 2 ^ 59
def prefixEnd_666208 : Nat := 4983230072969 + 3 ^ 40 * 666208 * 2
def baseEnd_666208 : Nat := 342084919870634691836171

theorem tailTrace_666208 : CollatzResearch.WordTrace tailWord_666208 prefixEnd_666208 342084919870634691836171 := by
  unfold tailWord_666208
  simp only [CollatzResearch.WordTrace]
  refine ⟨12149300985224835056539639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16199067980299780075386185 12149300985224835056539639)
  ·
    refine ⟨18223951477837252584809459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12149300985224835056539639 18223951477837252584809459)
    ·
      refine ⟨27335927216755878877214189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18223951477837252584809459 27335927216755878877214189)
      ·
        refine ⟨10250972706283454578955321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27335927216755878877214189 10250972706283454578955321)
        ·
          refine ⟨7688229529712590934216491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10250972706283454578955321 7688229529712590934216491)
          ·
            refine ⟨11532344294568886401324737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7688229529712590934216491 11532344294568886401324737)
            ·
              refine ⟨8649258220926664800993553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11532344294568886401324737 8649258220926664800993553)
              ·
                refine ⟨6486943665694998600745165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8649258220926664800993553 6486943665694998600745165)
                ·
                  refine ⟨2432603874635624475279437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6486943665694998600745165 2432603874635624475279437)
                  ·
                    refine ⟨912226452988359178229789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2432603874635624475279437 912226452988359178229789)
                    ·
                      refine ⟨342084919870634691836171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 912226452988359178229789 342084919870634691836171)
                      ·
                        rfl

theorem cell23_666208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 3].length) (baseStart_666208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_666208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_666208 prefixEnd_666208 := by exact prefixLift 666208
  have htrace : WordTrace (prefixWord ++ tailWord_666208) baseStart_666208 baseEnd_666208 := by
    simpa [prefixWord, tailWord_666208, baseEnd_666208] using wordTrace_append hprefix tailTrace_666208
  have hstable : (prefixWord ++ tailWord_666208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666208).length < 2 ^ (prefixWord ++ tailWord_666208).sum := by decide
  have hdescent : baseEnd_666208 < baseStart_666208 := by decide
  rcases family_descends (prefixWord ++ tailWord_666208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666209 : List Nat := [1, 2, 3, 1, 1, 4, 2, 4, 1, 2, 2]
def baseStart_666209 : Nat := 118140960795 + 666209 * 2 ^ 59
def prefixEnd_666209 : Nat := 4983230072969 + 3 ^ 40 * 666209 * 2
def baseEnd_666209 : Nat := 342085433351289187923667

theorem tailTrace_666209 : CollatzResearch.WordTrace tailWord_666209 prefixEnd_666209 342085433351289187923667 := by
  unfold tailWord_666209
  simp only [CollatzResearch.WordTrace]
  refine ⟨24298638443446047283865681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16199092295630698189243787 24298638443446047283865681)
  ·
    refine ⟨18223978832584535462899261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24298638443446047283865681 18223978832584535462899261)
    ·
      refine ⟨6833992062219200798587223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18223978832584535462899261 6833992062219200798587223)
      ·
        refine ⟨10250988093328801197880835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6833992062219200798587223 10250988093328801197880835)
        ·
          refine ⟨15376482139993201796821253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10250988093328801197880835 15376482139993201796821253)
          ·
            refine ⟨2883090401248725336903985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15376482139993201796821253 2883090401248725336903985)
            ·
              refine ⟨2162317800936544002677989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2883090401248725336903985 2162317800936544002677989)
              ·
                refine ⟨405434587675602000502123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2162317800936544002677989 405434587675602000502123)
                ·
                  refine ⟨608151881513403000753185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 405434587675602000502123 608151881513403000753185)
                  ·
                    refine ⟨456113911135052250564889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 608151881513403000753185 456113911135052250564889)
                    ·
                      refine ⟨342085433351289187923667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 456113911135052250564889 342085433351289187923667)
                      ·
                        rfl

theorem cell23_666209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 4, 1, 2, 2].length) (baseStart_666209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_666209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_666209 prefixEnd_666209 := by exact prefixLift 666209
  have htrace : WordTrace (prefixWord ++ tailWord_666209) baseStart_666209 baseEnd_666209 := by
    simpa [prefixWord, tailWord_666209, baseEnd_666209] using wordTrace_append hprefix tailTrace_666209
  have hstable : (prefixWord ++ tailWord_666209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666209).length < 2 ^ (prefixWord ++ tailWord_666209).sum := by decide
  have hdescent : baseEnd_666209 < baseStart_666209 := by decide
  rcases family_descends (prefixWord ++ tailWord_666209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666222 : List Nat := [4, 1, 2, 2, 2, 3, 1, 1, 1, 2, 4]
def baseStart_666222 : Nat := 118140960795 + 666222 * 2 ^ 59
def prefixEnd_666222 : Nat := 4983230072969 + 3 ^ 40 * 666222 * 2
def baseEnd_666222 : Nat := 342092108599797637061107

theorem tailTrace_666222 : CollatzResearch.WordTrace tailWord_666222 prefixEnd_666222 342092108599797637061107 := by
  unfold tailWord_666222
  simp only [CollatzResearch.WordTrace]
  refine ⟨3037389074049868813011115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16199408394932633669392613 3037389074049868813011115)
  ·
    refine ⟨4556083611074803219516673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3037389074049868813011115 4556083611074803219516673)
    ·
      refine ⟨3417062708306102414637505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4556083611074803219516673 3417062708306102414637505)
      ·
        refine ⟨2562797031229576810978129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3417062708306102414637505 2562797031229576810978129)
        ·
          refine ⟨1922097773422182608233597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2562797031229576810978129 1922097773422182608233597)
          ·
            refine ⟨720786665033318478087599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1922097773422182608233597 720786665033318478087599)
            ·
              refine ⟨1081179997549977717131399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 720786665033318478087599 1081179997549977717131399)
              ·
                refine ⟨1621769996324966575697099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1081179997549977717131399 1621769996324966575697099)
                ·
                  refine ⟨2432654994487449863545649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1621769996324966575697099 2432654994487449863545649)
                  ·
                    refine ⟨1824491245865587397659237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2432654994487449863545649 1824491245865587397659237)
                    ·
                      refine ⟨342092108599797637061107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1824491245865587397659237 342092108599797637061107)
                      ·
                        rfl

theorem cell23_666222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_666222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_666222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_666222 prefixEnd_666222 := by exact prefixLift 666222
  have htrace : WordTrace (prefixWord ++ tailWord_666222) baseStart_666222 baseEnd_666222 := by
    simpa [prefixWord, tailWord_666222, baseEnd_666222] using wordTrace_append hprefix tailTrace_666222
  have hstable : (prefixWord ++ tailWord_666222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666222).length < 2 ^ (prefixWord ++ tailWord_666222).sum := by decide
  have hdescent : baseEnd_666222 < baseStart_666222 := by decide
  rcases family_descends (prefixWord ++ tailWord_666222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666229 : List Nat := [1, 3, 4, 2, 2, 1, 2, 2, 1, 2, 3]
def baseStart_666229 : Nat := 118140960795 + 666229 * 2 ^ 59
def prefixEnd_666229 : Nat := 4983230072969 + 3 ^ 40 * 666229 * 2
def baseEnd_666229 : Nat := 342095702964379109673575

theorem tailTrace_666229 : CollatzResearch.WordTrace tailWord_666229 prefixEnd_666229 342095702964379109673575 := by
  unfold tailWord_666229
  simp only [CollatzResearch.WordTrace]
  refine ⟨24299367903373590699593741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16199578602249060466395827 24299367903373590699593741)
  ·
    refine ⟨9112262963765096512347653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24299367903373590699593741 9112262963765096512347653)
    ·
      refine ⟨1708549305705955596065185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9112262963765096512347653 1708549305705955596065185)
      ·
        refine ⟨1281411979279466697048889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1708549305705955596065185 1281411979279466697048889)
        ·
          refine ⟨961058984459600022786667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1281411979279466697048889 961058984459600022786667)
          ·
            refine ⟨1441588476689400034180001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 961058984459600022786667 1441588476689400034180001)
            ·
              refine ⟨1081191357517050025635001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1441588476689400034180001 1081191357517050025635001)
              ·
                refine ⟨810893518137787519226251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1081191357517050025635001 810893518137787519226251)
                ·
                  refine ⟨1216340277206681278839377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 810893518137787519226251 1216340277206681278839377)
                  ·
                    refine ⟨912255207905010959129533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1216340277206681278839377 912255207905010959129533)
                    ·
                      refine ⟨342095702964379109673575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 912255207905010959129533 342095702964379109673575)
                      ·
                        rfl

theorem cell23_666229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_666229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_666229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_666229 prefixEnd_666229 := by exact prefixLift 666229
  have htrace : WordTrace (prefixWord ++ tailWord_666229) baseStart_666229 baseEnd_666229 := by
    simpa [prefixWord, tailWord_666229, baseEnd_666229] using wordTrace_append hprefix tailTrace_666229
  have hstable : (prefixWord ++ tailWord_666229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666229).length < 2 ^ (prefixWord ++ tailWord_666229).sum := by decide
  have hdescent : baseEnd_666229 < baseStart_666229 := by decide
  rcases family_descends (prefixWord ++ tailWord_666229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666285 : List Nat := [1, 5, 2, 1, 1, 2, 1, 2, 2, 1, 5]
def baseStart_666285 : Nat := 118140960795 + 666285 * 2 ^ 59
def prefixEnd_666285 : Nat := 4983230072969 + 3 ^ 40 * 666285 * 2
def baseEnd_666285 : Nat := 342124457881030890573317

theorem tailTrace_666285 : CollatzResearch.WordTrace tailWord_666285 prefixEnd_666285 342124457881030890573317 := by
  unfold tailWord_666285
  simp only [CollatzResearch.WordTrace]
  refine ⟨24301410391170712263632309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16200940260780474842421539 24301410391170712263632309)
  ·
    refine ⟨2278257224172254274715529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24301410391170712263632309 2278257224172254274715529)
    ·
      refine ⟨1708692918129190706036647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2278257224172254274715529 1708692918129190706036647)
      ·
        refine ⟨2563039377193786059054971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1708692918129190706036647 2563039377193786059054971)
        ·
          refine ⟨3844559065790679088582457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2563039377193786059054971 3844559065790679088582457)
          ·
            refine ⟨2883419299343009316436843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3844559065790679088582457 2883419299343009316436843)
            ·
              refine ⟨4325128949014513974655265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2883419299343009316436843 4325128949014513974655265)
              ·
                refine ⟨3243846711760885480991449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4325128949014513974655265 3243846711760885480991449)
                ·
                  refine ⟨2432885033820664110743587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3243846711760885480991449 2432885033820664110743587)
                  ·
                    refine ⟨3649327550730996166115381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2432885033820664110743587 3649327550730996166115381)
                    ·
                      refine ⟨342124457881030890573317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3649327550730996166115381 342124457881030890573317)
                      ·
                        rfl

theorem cell23_666285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_666285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_666285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_666285 prefixEnd_666285 := by exact prefixLift 666285
  have htrace : WordTrace (prefixWord ++ tailWord_666285) baseStart_666285 baseEnd_666285 := by
    simpa [prefixWord, tailWord_666285, baseEnd_666285] using wordTrace_append hprefix tailTrace_666285
  have hstable : (prefixWord ++ tailWord_666285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666285).length < 2 ^ (prefixWord ++ tailWord_666285).sum := by decide
  have hdescent : baseEnd_666285 < baseStart_666285 := by decide
  rcases family_descends (prefixWord ++ tailWord_666285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666286 : List Nat := [4, 1, 4, 1, 1, 1, 3, 2, 1, 3, 2]
def baseStart_666286 : Nat := 118140960795 + 666286 * 2 ^ 59
def prefixEnd_666286 : Nat := 4983230072969 + 3 ^ 40 * 666286 * 2
def baseEnd_666286 : Nat := 342124971361685386660813

theorem tailTrace_666286 : CollatzResearch.WordTrace tailWord_666286 prefixEnd_666286 342124971361685386660813 := by
  unfold tailWord_666286
  simp only [CollatzResearch.WordTrace]
  refine ⟨3037680858020886179302339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16200964576111392956279141 3037680858020886179302339)
  ·
    refine ⟨4556521287031329268953509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3037680858020886179302339 4556521287031329268953509)
    ·
      refine ⟨854347741318374237928783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4556521287031329268953509 854347741318374237928783)
      ·
        refine ⟨1281521611977561356893175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 854347741318374237928783 1281521611977561356893175)
        ·
          refine ⟨1922282417966342035339763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1281521611977561356893175 1922282417966342035339763)
          ·
            refine ⟨2883423626949513053009645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1922282417966342035339763 2883423626949513053009645)
            ·
              refine ⟨1081283860106067394878617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2883423626949513053009645 1081283860106067394878617)
              ·
                refine ⟨810962895079550546158963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1081283860106067394878617 810962895079550546158963)
                ·
                  refine ⟨1216444342619325819238445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 810962895079550546158963 1216444342619325819238445)
                  ·
                    refine ⟨456166628482247182214417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1216444342619325819238445 456166628482247182214417)
                    ·
                      refine ⟨342124971361685386660813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 456166628482247182214417 342124971361685386660813)
                      ·
                        rfl

theorem cell23_666286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_666286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_666286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_666286 prefixEnd_666286 := by exact prefixLift 666286
  have htrace : WordTrace (prefixWord ++ tailWord_666286) baseStart_666286 baseEnd_666286 := by
    simpa [prefixWord, tailWord_666286, baseEnd_666286] using wordTrace_append hprefix tailTrace_666286
  have hstable : (prefixWord ++ tailWord_666286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666286).length < 2 ^ (prefixWord ++ tailWord_666286).sum := by decide
  have hdescent : baseEnd_666286 < baseStart_666286 := by decide
  rcases family_descends (prefixWord ++ tailWord_666286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666316 : List Nat := [2, 2, 1, 5, 1, 2, 2, 2, 2, 2, 2]
def baseStart_666316 : Nat := 118140960795 + 666316 * 2 ^ 59
def prefixEnd_666316 : Nat := 4983230072969 + 3 ^ 40 * 666316 * 2
def baseEnd_666316 : Nat := 342140375781320269285675

theorem tailTrace_666316 : CollatzResearch.WordTrace tailWord_666316 prefixEnd_666316 342140375781320269285675 := by
  unfold tailWord_666316
  simp only [CollatzResearch.WordTrace]
  refine ⟨12151270527029202279005401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16201694036038936372007201 12151270527029202279005401)
  ·
    refine ⟨9113452895271901709254051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12151270527029202279005401 9113452895271901709254051)
    ·
      refine ⟨13670179342907852563881077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9113452895271901709254051 13670179342907852563881077)
      ·
        refine ⟨1281579313397611177863851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13670179342907852563881077 1281579313397611177863851)
        ·
          refine ⟨1922368970096416766795777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1281579313397611177863851 1922368970096416766795777)
          ·
            refine ⟨1441776727572312575096833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1922368970096416766795777 1441776727572312575096833)
            ·
              refine ⟨1081332545679234431322625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1441776727572312575096833 1081332545679234431322625)
              ·
                refine ⟨810999409259425823491969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1081332545679234431322625 810999409259425823491969)
                ·
                  refine ⟨608249556944569367618977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 810999409259425823491969 608249556944569367618977)
                  ·
                    refine ⟨456187167708427025714233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 608249556944569367618977 456187167708427025714233)
                    ·
                      refine ⟨342140375781320269285675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 456187167708427025714233 342140375781320269285675)
                      ·
                        rfl

theorem cell23_666316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_666316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_666316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_666316 prefixEnd_666316 := by exact prefixLift 666316
  have htrace : WordTrace (prefixWord ++ tailWord_666316) baseStart_666316 baseEnd_666316 := by
    simpa [prefixWord, tailWord_666316, baseEnd_666316] using wordTrace_append hprefix tailTrace_666316
  have hstable : (prefixWord ++ tailWord_666316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666316).length < 2 ^ (prefixWord ++ tailWord_666316).sum := by decide
  have hdescent : baseEnd_666316 < baseStart_666316 := by decide
  rcases family_descends (prefixWord ++ tailWord_666316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666332 : List Nat := [2, 2, 5, 1, 1, 1, 1, 1, 1, 5, 3]
def baseStart_666332 : Nat := 118140960795 + 666332 * 2 ^ 59
def prefixEnd_666332 : Nat := 4983230072969 + 3 ^ 40 * 666332 * 2
def baseEnd_666332 : Nat := 342148591471792206685601

theorem tailTrace_666332 : CollatzResearch.WordTrace tailWord_666332 prefixEnd_666332 342148591471792206685601 := by
  unfold tailWord_666332
  simp only [CollatzResearch.WordTrace]
  refine ⟨12151562311000219645296625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16202083081333626193728833 12151562311000219645296625)
  ·
    refine ⟨9113671733250164733972469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12151562311000219645296625 9113671733250164733972469)
    ·
      refine ⟨854406724992202943809919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9113671733250164733972469 854406724992202943809919)
      ·
        refine ⟨1281610087488304415714879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 854406724992202943809919 1281610087488304415714879)
        ·
          refine ⟨1922415131232456623572319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1281610087488304415714879 1922415131232456623572319)
          ·
            refine ⟨2883622696848684935358479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1922415131232456623572319 2883622696848684935358479)
            ·
              refine ⟨4325434045273027403037719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2883622696848684935358479 4325434045273027403037719)
              ·
                refine ⟨6488151067909541104556579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4325434045273027403037719 6488151067909541104556579)
                ·
                  refine ⟨9732226601864311656834869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6488151067909541104556579 9732226601864311656834869)
                  ·
                    refine ⟨912396243924779217828269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9732226601864311656834869 912396243924779217828269)
                    ·
                      refine ⟨342148591471792206685601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 912396243924779217828269 342148591471792206685601)
                      ·
                        rfl

theorem cell23_666332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_666332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_666332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_666332 prefixEnd_666332 := by exact prefixLift 666332
  have htrace : WordTrace (prefixWord ++ tailWord_666332) baseStart_666332 baseEnd_666332 := by
    simpa [prefixWord, tailWord_666332, baseEnd_666332] using wordTrace_append hprefix tailTrace_666332
  have hstable : (prefixWord ++ tailWord_666332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666332).length < 2 ^ (prefixWord ++ tailWord_666332).sum := by decide
  have hdescent : baseEnd_666332 < baseStart_666332 := by decide
  rcases family_descends (prefixWord ++ tailWord_666332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666355 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 3, 6, 2]
def baseStart_666355 : Nat := 118140960795 + 666355 * 2 ^ 59
def prefixEnd_666355 : Nat := 4983230072969 + 3 ^ 40 * 666355 * 2
def baseEnd_666355 : Nat := 342160401526845616697995

theorem tailTrace_666355 : CollatzResearch.WordTrace tailWord_666355 prefixEnd_666355 342160401526845616697995 := by
  unfold tailWord_666355
  simp only [CollatzResearch.WordTrace]
  refine ⟨24303963500917114218680519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16202642333944742812453679 24303963500917114218680519)
  ·
    refine ⟨36455945251375671328020779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24303963500917114218680519 36455945251375671328020779)
    ·
      refine ⟨54683917877063506992031169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36455945251375671328020779 54683917877063506992031169)
      ·
        refine ⟨41012938407797630244023377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54683917877063506992031169 41012938407797630244023377)
        ·
          refine ⟨30759703805848222683017533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41012938407797630244023377 30759703805848222683017533)
          ·
            refine ⟨11534888927193083506131575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30759703805848222683017533 11534888927193083506131575)
            ·
              refine ⟨17302333390789625259197363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11534888927193083506131575 17302333390789625259197363)
              ·
                refine ⟨25953500086184437888796045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17302333390789625259197363 25953500086184437888796045)
                ·
                  refine ⟨9732562532319164208298517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25953500086184437888796045 9732562532319164208298517)
                  ·
                    refine ⟨456213868702460822263993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9732562532319164208298517 456213868702460822263993)
                    ·
                      refine ⟨342160401526845616697995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 456213868702460822263993 342160401526845616697995)
                      ·
                        rfl

theorem cell23_666355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 6, 2].length) (baseStart_666355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_666355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_666355 prefixEnd_666355 := by exact prefixLift 666355
  have htrace : WordTrace (prefixWord ++ tailWord_666355) baseStart_666355 baseEnd_666355 := by
    simpa [prefixWord, tailWord_666355, baseEnd_666355] using wordTrace_append hprefix tailTrace_666355
  have hstable : (prefixWord ++ tailWord_666355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666355).length < 2 ^ (prefixWord ++ tailWord_666355).sum := by decide
  have hdescent : baseEnd_666355 < baseStart_666355 := by decide
  rcases family_descends (prefixWord ++ tailWord_666355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666365 : List Nat := [1, 4, 1, 1, 1, 1, 3, 2, 5, 4]
def baseStart_666365 : Nat := 118140960795 + 666365 * 2 ^ 59
def prefixEnd_666365 : Nat := 4983230072969 + 3 ^ 40 * 666365 * 2
def baseEnd_666365 : Nat := 114055178777796859190983

theorem tailTrace_666365 : CollatzResearch.WordTrace tailWord_666365 prefixEnd_666365 114055178777796859190983 := by
  unfold tailWord_666365
  simp only [CollatzResearch.WordTrace]
  refine ⟨24304328230880885926544549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16202885487253923951029699 24304328230880885926544549)
  ·
    refine ⟨4557061543290166111227103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24304328230880885926544549 4557061543290166111227103)
    ·
      refine ⟨6835592314935249166840655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4557061543290166111227103 6835592314935249166840655)
      ·
        refine ⟨10253388472402873750260983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6835592314935249166840655 10253388472402873750260983)
        ·
          refine ⟨15380082708604310625391475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10253388472402873750260983 15380082708604310625391475)
          ·
            refine ⟨23070124062906465938087213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15380082708604310625391475 23070124062906465938087213)
            ·
              refine ⟨8651296523589924726782705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23070124062906465938087213 8651296523589924726782705)
              ·
                refine ⟨6488472392692443545087029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8651296523589924726782705 6488472392692443545087029)
                ·
                  refine ⟨608294286814916582351909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6488472392692443545087029 608294286814916582351909)
                  ·
                    refine ⟨114055178777796859190983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 608294286814916582351909 114055178777796859190983)
                    ·
                      rfl

theorem cell23_666365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 5, 4].length) (baseStart_666365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_666365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_666365 prefixEnd_666365 := by exact prefixLift 666365
  have htrace : WordTrace (prefixWord ++ tailWord_666365) baseStart_666365 baseEnd_666365 := by
    simpa [prefixWord, tailWord_666365, baseEnd_666365] using wordTrace_append hprefix tailTrace_666365
  have hstable : (prefixWord ++ tailWord_666365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666365).length < 2 ^ (prefixWord ++ tailWord_666365).sum := by decide
  have hdescent : baseEnd_666365 < baseStart_666365 := by decide
  rcases family_descends (prefixWord ++ tailWord_666365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666372 : List Nat := [2, 3, 2, 2, 1, 1, 1, 1, 4, 4, 2]
def baseStart_666372 : Nat := 118140960795 + 666372 * 2 ^ 59
def prefixEnd_666372 : Nat := 4983230072969 + 3 ^ 40 * 666372 * 2
def baseEnd_666372 : Nat := 342169130697972050185417

theorem tailTrace_666372 : CollatzResearch.WordTrace tailWord_666372 prefixEnd_666372 342169130697972050185417 := by
  unfold tailWord_666372
  simp only [CollatzResearch.WordTrace]
  refine ⟨12152291770927763061024685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16203055694570350748032913 12152291770927763061024685)
  ·
    refine ⟨4557109414097911147884257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12152291770927763061024685 4557109414097911147884257)
    ·
      refine ⟨3417832060573433360913193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4557109414097911147884257 3417832060573433360913193)
      ·
        refine ⟨2563374045430075020684895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3417832060573433360913193 2563374045430075020684895)
        ·
          refine ⟨3845061068145112531027343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2563374045430075020684895 3845061068145112531027343)
          ·
            refine ⟨5767591602217668796541015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3845061068145112531027343 5767591602217668796541015)
            ·
              refine ⟨8651387403326503194811523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5767591602217668796541015 8651387403326503194811523)
              ·
                refine ⟨12977081104989754792217285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8651387403326503194811523 12977081104989754792217285)
                ·
                  refine ⟨2433202707185579023540741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12977081104989754792217285 2433202707185579023540741)
                  ·
                    refine ⟨456225507597296066913889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2433202707185579023540741 456225507597296066913889)
                    ·
                      refine ⟨342169130697972050185417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 456225507597296066913889 342169130697972050185417)
                      ·
                        rfl

theorem cell23_666372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_666372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_666372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_666372 prefixEnd_666372 := by exact prefixLift 666372
  have htrace : WordTrace (prefixWord ++ tailWord_666372) baseStart_666372 baseEnd_666372 := by
    simpa [prefixWord, tailWord_666372, baseEnd_666372] using wordTrace_append hprefix tailTrace_666372
  have hstable : (prefixWord ++ tailWord_666372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666372).length < 2 ^ (prefixWord ++ tailWord_666372).sum := by decide
  have hdescent : baseEnd_666372 < baseStart_666372 := by decide
  rcases family_descends (prefixWord ++ tailWord_666372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666405 : List Nat := [1, 3, 1, 2, 3, 1, 1, 1, 2, 5, 3]
def baseStart_666405 : Nat := 118140960795 + 666405 * 2 ^ 59
def prefixEnd_666405 : Nat := 4983230072969 + 3 ^ 40 * 666405 * 2
def baseEnd_666405 : Nat := 342186075559570421072765

theorem tailTrace_666405 : CollatzResearch.WordTrace tailWord_666405 prefixEnd_666405 342186075559570421072765 := by
  unfold tailWord_666405
  simp only [CollatzResearch.WordTrace]
  refine ⟨24305787150735972758000669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16203858100490648505333779 24305787150735972758000669)
  ·
    refine ⟨9114670181525989784250251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24305787150735972758000669 9114670181525989784250251)
    ·
      refine ⟨13672005272288984676375377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9114670181525989784250251 13672005272288984676375377)
      ·
        refine ⟨10254003954216738507281533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13672005272288984676375377 10254003954216738507281533)
        ·
          refine ⟨3845251482831276940230575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10254003954216738507281533 3845251482831276940230575)
          ·
            refine ⟨5767877224246915410345863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3845251482831276940230575 5767877224246915410345863)
            ·
              refine ⟨8651815836370373115518795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5767877224246915410345863 8651815836370373115518795)
              ·
                refine ⟨12977723754555559673278193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8651815836370373115518795 12977723754555559673278193)
                ·
                  refine ⟨9733292815916669754958645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12977723754555559673278193 9733292815916669754958645)
                  ·
                    refine ⟨912496201492187789527373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9733292815916669754958645 912496201492187789527373)
                    ·
                      refine ⟨342186075559570421072765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 912496201492187789527373 342186075559570421072765)
                      ·
                        rfl

theorem cell23_666405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 5, 3].length) (baseStart_666405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_666405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_666405 prefixEnd_666405 := by exact prefixLift 666405
  have htrace : WordTrace (prefixWord ++ tailWord_666405) baseStart_666405 baseEnd_666405 := by
    simpa [prefixWord, tailWord_666405, baseEnd_666405] using wordTrace_append hprefix tailTrace_666405
  have hstable : (prefixWord ++ tailWord_666405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666405).length < 2 ^ (prefixWord ++ tailWord_666405).sum := by decide
  have hdescent : baseEnd_666405 < baseStart_666405 := by decide
  rcases family_descends (prefixWord ++ tailWord_666405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666433 : List Nat := [1, 2, 5, 3, 2, 1, 1, 1, 3, 4]
def baseStart_666433 : Nat := 118140960795 + 666433 * 2 ^ 59
def prefixEnd_666433 : Nat := 4983230072969 + 3 ^ 40 * 666433 * 2
def baseEnd_666433 : Nat := 114066817672632103840879

theorem tailTrace_666433 : CollatzResearch.WordTrace tailWord_666433 prefixEnd_666433 114066817672632103840879 := by
  unfold tailWord_666433
  simp only [CollatzResearch.WordTrace]
  refine ⟨24306808394634533540019953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16204538929756355693346635 24306808394634533540019953)
  ·
    refine ⟨18230106295975900155014965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24306808394634533540019953 18230106295975900155014965)
    ·
      refine ⟨1709072465247740639532653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18230106295975900155014965 1709072465247740639532653)
      ·
        refine ⟨640902174467902739824745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1709072465247740639532653 640902174467902739824745)
        ·
          refine ⟨480676630850927054868559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 640902174467902739824745 480676630850927054868559)
          ·
            refine ⟨721014946276390582302839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 480676630850927054868559 721014946276390582302839)
            ·
              refine ⟨1081522419414585873454259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 721014946276390582302839 1081522419414585873454259)
              ·
                refine ⟨1622283629121878810181389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1081522419414585873454259 1622283629121878810181389)
                ·
                  refine ⟨608356360920704553818021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1622283629121878810181389 608356360920704553818021)
                  ·
                    refine ⟨114066817672632103840879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 608356360920704553818021 114066817672632103840879)
                    ·
                      rfl

theorem cell23_666433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_666433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_666433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_666433 prefixEnd_666433 := by exact prefixLift 666433
  have htrace : WordTrace (prefixWord ++ tailWord_666433) baseStart_666433 baseEnd_666433 := by
    simpa [prefixWord, tailWord_666433, baseEnd_666433] using wordTrace_append hprefix tailTrace_666433
  have hstable : (prefixWord ++ tailWord_666433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666433).length < 2 ^ (prefixWord ++ tailWord_666433).sum := by decide
  have hdescent : baseEnd_666433 < baseStart_666433 := by decide
  rcases family_descends (prefixWord ++ tailWord_666433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666472 : List Nat := [2, 1, 4, 2, 1, 3, 1, 2, 1, 6]
def baseStart_666472 : Nat := 118140960795 + 666472 * 2 ^ 59
def prefixEnd_666472 : Nat := 4983230072969 + 3 ^ 40 * 666472 * 2
def baseEnd_666472 : Nat := 114073492921140552978319

theorem tailTrace_666472 : CollatzResearch.WordTrace tailWord_666472 prefixEnd_666472 114073492921140552978319 := by
  unfold tailWord_666472
  simp only [CollatzResearch.WordTrace]
  refine ⟨12154115420746621600344835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16205487227662162133793113 12154115420746621600344835)
  ·
    refine ⟨18231173131119932400517253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12154115420746621600344835 18231173131119932400517253)
    ·
      refine ⟨3418344962084987325096985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18231173131119932400517253 3418344962084987325096985)
      ·
        refine ⟨2563758721563740493822739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3418344962084987325096985 2563758721563740493822739)
        ·
          refine ⟨3845638082345610740734109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2563758721563740493822739 3845638082345610740734109)
          ·
            refine ⟨1442114280879604027775291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3845638082345610740734109 1442114280879604027775291)
            ·
              refine ⟨2163171421319406041662937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1442114280879604027775291 2163171421319406041662937)
              ·
                refine ⟨1622378565989554531247203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2163171421319406041662937 1622378565989554531247203)
                ·
                  refine ⟨2433567848984331796870805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1622378565989554531247203 2433567848984331796870805)
                  ·
                    refine ⟨114073492921140552978319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2433567848984331796870805 114073492921140552978319)
                    ·
                      rfl

theorem cell23_666472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_666472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_666472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_666472 prefixEnd_666472 := by exact prefixLift 666472
  have htrace : WordTrace (prefixWord ++ tailWord_666472) baseStart_666472 baseEnd_666472 := by
    simpa [prefixWord, tailWord_666472, baseEnd_666472] using wordTrace_append hprefix tailTrace_666472
  have hstable : (prefixWord ++ tailWord_666472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666472).length < 2 ^ (prefixWord ++ tailWord_666472).sum := by decide
  have hdescent : baseEnd_666472 < baseStart_666472 := by decide
  rcases family_descends (prefixWord ++ tailWord_666472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666475 : List Nat := [1, 1, 1, 1, 2, 2, 5, 1, 3, 2, 4]
def baseStart_666475 : Nat := 118140960795 + 666475 * 2 ^ 59
def prefixEnd_666475 : Nat := 4983230072969 + 3 ^ 40 * 666475 * 2
def baseEnd_666475 : Nat := 342222019205385147197443

theorem tailTrace_666475 : CollatzResearch.WordTrace tailWord_666475 prefixEnd_666475 342222019205385147197443 := by
  unfold tailWord_666475
  simp only [CollatzResearch.WordTrace]
  refine ⟨24308340260482374713048879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16205560173654916475365919 24308340260482374713048879)
  ·
    refine ⟨36462510390723562069573319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24308340260482374713048879 36462510390723562069573319)
    ·
      refine ⟨54693765586085343104359979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36462510390723562069573319 54693765586085343104359979)
      ·
        refine ⟨82040648379128014656539969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54693765586085343104359979 82040648379128014656539969)
        ·
          refine ⟨61530486284346010992404977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82040648379128014656539969 61530486284346010992404977)
          ·
            refine ⟨46147864713259508244303733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61530486284346010992404977 46147864713259508244303733)
            ·
              refine ⟨4326362316868078897903475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46147864713259508244303733 4326362316868078897903475)
              ·
                refine ⟨6489543475302118346855213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4326362316868078897903475 6489543475302118346855213)
                ·
                  refine ⟨2433578803238294380070705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6489543475302118346855213 2433578803238294380070705)
                  ·
                    refine ⟨1825184102428720785053029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2433578803238294380070705 1825184102428720785053029)
                    ·
                      refine ⟨342222019205385147197443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1825184102428720785053029 342222019205385147197443)
                      ·
                        rfl

theorem cell23_666475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 2, 4].length) (baseStart_666475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_666475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_666475 prefixEnd_666475 := by exact prefixLift 666475
  have htrace : WordTrace (prefixWord ++ tailWord_666475) baseStart_666475 baseEnd_666475 := by
    simpa [prefixWord, tailWord_666475, baseEnd_666475] using wordTrace_append hprefix tailTrace_666475
  have hstable : (prefixWord ++ tailWord_666475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666475).length < 2 ^ (prefixWord ++ tailWord_666475).sum := by decide
  have hdescent : baseEnd_666475 < baseStart_666475 := by decide
  rcases family_descends (prefixWord ++ tailWord_666475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666482 : List Nat := [3, 2, 1, 2, 1, 1, 5, 1, 1, 1, 5]
def baseStart_666482 : Nat := 118140960795 + 666482 * 2 ^ 59
def prefixEnd_666482 : Nat := 4983230072969 + 3 ^ 40 * 666482 * 2
def baseEnd_666482 : Nat := 342225613569966619809911

theorem tailTrace_666482 : CollatzResearch.WordTrace tailWord_666482 prefixEnd_666482 342225613569966619809911 := by
  unfold tailWord_666482
  simp only [CollatzResearch.WordTrace]
  refine ⟨6077148892864253727138425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16205730380971343272369133 6077148892864253727138425)
  ·
    refine ⟨4557861669648190295353819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6077148892864253727138425 4557861669648190295353819)
    ·
      refine ⟨6836792504472285443030729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4557861669648190295353819 6836792504472285443030729)
      ·
        refine ⟨5127594378354214082273047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6836792504472285443030729 5127594378354214082273047)
        ·
          refine ⟨7691391567531321123409571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5127594378354214082273047 7691391567531321123409571)
          ·
            refine ⟨11537087351296981685114357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7691391567531321123409571 11537087351296981685114357)
            ·
              refine ⟨1081601939184092032979471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11537087351296981685114357 1081601939184092032979471)
              ·
                refine ⟨1622402908776138049469207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1081601939184092032979471 1622402908776138049469207)
                ·
                  refine ⟨2433604363164207074203811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1622402908776138049469207 2433604363164207074203811)
                  ·
                    refine ⟨3650406544746310611305717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2433604363164207074203811 3650406544746310611305717)
                    ·
                      refine ⟨342225613569966619809911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3650406544746310611305717 342225613569966619809911)
                      ·
                        rfl

theorem cell23_666482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_666482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_666482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_666482 prefixEnd_666482 := by exact prefixLift 666482
  have htrace : WordTrace (prefixWord ++ tailWord_666482) baseStart_666482 baseEnd_666482 := by
    simpa [prefixWord, tailWord_666482, baseEnd_666482] using wordTrace_append hprefix tailTrace_666482
  have hstable : (prefixWord ++ tailWord_666482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666482).length < 2 ^ (prefixWord ++ tailWord_666482).sum := by decide
  have hdescent : baseEnd_666482 < baseStart_666482 := by decide
  rcases family_descends (prefixWord ++ tailWord_666482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666485 : List Nat := [1, 3, 4, 1, 1, 13]
def baseStart_666485 : Nat := 118140960795 + 666485 * 2 ^ 59
def prefixEnd_666485 : Nat := 4983230072969 + 3 ^ 40 * 666485 * 2
def baseEnd_666485 : Nat := 1408342197579959292479

theorem tailTrace_666485 : CollatzResearch.WordTrace tailWord_666485 prefixEnd_666485 1408342197579959292479 := by
  unfold tailWord_666485
  simp only [CollatzResearch.WordTrace]
  refine ⟨24308704990446146420912909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16205803326964097613941939 24308704990446146420912909)
  ·
    refine ⟨9115764371417304907842341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24308704990446146420912909 9115764371417304907842341)
    ·
      refine ⟨1709205819640744670220439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9115764371417304907842341 1709205819640744670220439)
      ·
        refine ⟨2563808729461117005330659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1709205819640744670220439 2563808729461117005330659)
        ·
          refine ⟨3845713094191675507995989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2563808729461117005330659 3845713094191675507995989)
          ·
            refine ⟨1408342197579959292479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 3845713094191675507995989 1408342197579959292479)
            ·
              rfl

theorem cell23_666485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 13].length) (baseStart_666485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_666485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_666485 prefixEnd_666485 := by exact prefixLift 666485
  have htrace : WordTrace (prefixWord ++ tailWord_666485) baseStart_666485 baseEnd_666485 := by
    simpa [prefixWord, tailWord_666485, baseEnd_666485] using wordTrace_append hprefix tailTrace_666485
  have hstable : (prefixWord ++ tailWord_666485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666485).length < 2 ^ (prefixWord ++ tailWord_666485).sum := by decide
  have hdescent : baseEnd_666485 < baseStart_666485 := by decide
  rcases family_descends (prefixWord ++ tailWord_666485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666489 : List Nat := [1, 2, 1, 3, 2, 4, 2, 2, 2, 4]
def baseStart_666489 : Nat := 118140960795 + 666489 * 2 ^ 59
def prefixEnd_666489 : Nat := 4983230072969 + 3 ^ 40 * 666489 * 2
def baseEnd_666489 : Nat := 114076402644849364140793

theorem tailTrace_666489 : CollatzResearch.WordTrace tailWord_666489 prefixEnd_666489 114076402644849364140793 := by
  unfold tailWord_666489
  simp only [CollatzResearch.WordTrace]
  refine ⟨24308850882431655104058521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16205900588287770069372347 24308850882431655104058521)
  ·
    refine ⟨18231638161823741328043891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24308850882431655104058521 18231638161823741328043891)
    ·
      refine ⟨27347457242735611992065837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18231638161823741328043891 27347457242735611992065837)
      ·
        refine ⟨10255296466025854497024689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27347457242735611992065837 10255296466025854497024689)
        ·
          refine ⟨7691472349519390872768517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10255296466025854497024689 7691472349519390872768517)
          ·
            refine ⟨1442151065534885788644097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7691472349519390872768517 1442151065534885788644097)
            ·
              refine ⟨1081613299151164341483073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1442151065534885788644097 1081613299151164341483073)
              ·
                refine ⟨811209974363373256112305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1081613299151164341483073 811209974363373256112305)
                ·
                  refine ⟨608407480772529942084229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 811209974363373256112305 608407480772529942084229)
                  ·
                    refine ⟨114076402644849364140793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 608407480772529942084229 114076402644849364140793)
                    ·
                      rfl

theorem cell23_666489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 2, 2, 4].length) (baseStart_666489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_666489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_666489 prefixEnd_666489 := by exact prefixLift 666489
  have htrace : WordTrace (prefixWord ++ tailWord_666489) baseStart_666489 baseEnd_666489 := by
    simpa [prefixWord, tailWord_666489, baseEnd_666489] using wordTrace_append hprefix tailTrace_666489
  have hstable : (prefixWord ++ tailWord_666489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666489).length < 2 ^ (prefixWord ++ tailWord_666489).sum := by decide
  have hdescent : baseEnd_666489 < baseStart_666489 := by decide
  rcases family_descends (prefixWord ++ tailWord_666489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666529 : List Nat := [1, 2, 3, 4, 1, 1, 2, 2, 1, 3, 3]
def baseStart_666529 : Nat := 118140960795 + 666529 * 2 ^ 59
def prefixEnd_666529 : Nat := 4983230072969 + 3 ^ 40 * 666529 * 2
def baseEnd_666529 : Nat := 342249747160727935922195

theorem tailTrace_666529 : CollatzResearch.WordTrace tailWord_666529 prefixEnd_666529 342249747160727935922195 := by
  unfold tailWord_666529
  simp only [CollatzResearch.WordTrace]
  refine ⟨24310309802286741935514641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16206873201524494623676427 24310309802286741935514641)
  ·
    refine ⟨18232732351715056451635981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24310309802286741935514641 18232732351715056451635981)
    ·
      refine ⟨6837274631893146169363493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18232732351715056451635981 6837274631893146169363493)
      ·
        refine ⟨1281988993479964906755655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6837274631893146169363493 1281988993479964906755655)
        ·
          refine ⟨1922983490219947360133483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1281988993479964906755655 1922983490219947360133483)
          ·
            refine ⟨2884475235329921040200225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1922983490219947360133483 2884475235329921040200225)
            ·
              refine ⟨2163356426497440780150169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2884475235329921040200225 2163356426497440780150169)
              ·
                refine ⟨1622517319873080585112627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2163356426497440780150169 1622517319873080585112627)
                ·
                  refine ⟨2433775979809620877668941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1622517319873080585112627 2433775979809620877668941)
                  ·
                    refine ⟨912665992428607829125853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2433775979809620877668941 912665992428607829125853)
                    ·
                      refine ⟨342249747160727935922195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 912665992428607829125853 342249747160727935922195)
                      ·
                        rfl

theorem cell23_666529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_666529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_666529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_666529 prefixEnd_666529 := by exact prefixLift 666529
  have htrace : WordTrace (prefixWord ++ tailWord_666529) baseStart_666529 baseEnd_666529 := by
    simpa [prefixWord, tailWord_666529, baseEnd_666529] using wordTrace_append hprefix tailTrace_666529
  have hstable : (prefixWord ++ tailWord_666529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666529).length < 2 ^ (prefixWord ++ tailWord_666529).sum := by decide
  have hdescent : baseEnd_666529 < baseStart_666529 := by decide
  rcases family_descends (prefixWord ++ tailWord_666529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666530 : List Nat := [3, 3, 1, 2, 2, 2, 2, 3, 1, 2, 2]
def baseStart_666530 : Nat := 118140960795 + 666530 * 2 ^ 59
def prefixEnd_666530 : Nat := 4983230072969 + 3 ^ 40 * 666530 * 2
def baseEnd_666530 : Nat := 342250260641382432009691

theorem tailTrace_666530 : CollatzResearch.WordTrace tailWord_666530 prefixEnd_666530 342250260641382432009691 := by
  unfold tailWord_666530
  simp only [CollatzResearch.WordTrace]
  refine ⟨6077586568820779776575261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16206897516855412737534029 6077586568820779776575261)
  ·
    refine ⟨2279094963307792416215723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6077586568820779776575261 2279094963307792416215723)
    ·
      refine ⟨3418642444961688624323585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2279094963307792416215723 3418642444961688624323585)
      ·
        refine ⟨2563981833721266468242689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3418642444961688624323585 2563981833721266468242689)
        ·
          refine ⟨1922986375290949851182017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2563981833721266468242689 1922986375290949851182017)
          ·
            refine ⟨1442239781468212388386513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1922986375290949851182017 1442239781468212388386513)
            ·
              refine ⟨1081679836101159291289885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1442239781468212388386513 1081679836101159291289885)
              ·
                refine ⟨405629938537934734233707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1081679836101159291289885 405629938537934734233707)
                ·
                  refine ⟨608444907806902101350561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 405629938537934734233707 608444907806902101350561)
                  ·
                    refine ⟨456333680855176576012921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 608444907806902101350561 456333680855176576012921)
                    ·
                      refine ⟨342250260641382432009691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 456333680855176576012921 342250260641382432009691)
                      ·
                        rfl

theorem cell23_666530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_666530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_666530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_666530 prefixEnd_666530 := by exact prefixLift 666530
  have htrace : WordTrace (prefixWord ++ tailWord_666530) baseStart_666530 baseEnd_666530 := by
    simpa [prefixWord, tailWord_666530, baseEnd_666530] using wordTrace_append hprefix tailTrace_666530
  have hstable : (prefixWord ++ tailWord_666530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666530).length < 2 ^ (prefixWord ++ tailWord_666530).sum := by decide
  have hdescent : baseEnd_666530 < baseStart_666530 := by decide
  rcases family_descends (prefixWord ++ tailWord_666530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666539 : List Nat := [1, 1, 1, 1, 2, 1, 1, 9, 1, 3, 2]
def baseStart_666539 : Nat := 118140960795 + 666539 * 2 ^ 59
def prefixEnd_666539 : Nat := 4983230072969 + 3 ^ 40 * 666539 * 2
def baseEnd_666539 : Nat := 342254881967272896797149

theorem tailTrace_666539 : CollatzResearch.WordTrace tailWord_666539 prefixEnd_666539 342254881967272896797149 := by
  unfold tailWord_666539
  simp only [CollatzResearch.WordTrace]
  refine ⟨24310674532250513643378671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16207116354833675762252447 24310674532250513643378671)
  ·
    refine ⟨36466011798375770465068007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24310674532250513643378671 36466011798375770465068007)
    ·
      refine ⟨54699017697563655697602011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36466011798375770465068007 54699017697563655697602011)
      ·
        refine ⟨82048526546345483546403017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54699017697563655697602011 82048526546345483546403017)
        ·
          refine ⟨61536394909759112659802263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82048526546345483546403017 61536394909759112659802263)
          ·
            refine ⟨92304592364638668989703395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61536394909759112659802263 92304592364638668989703395)
            ·
              refine ⟨138456888546958003484555093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92304592364638668989703395 138456888546958003484555093)
              ·
                refine ⟨811270831329832051667315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 138456888546958003484555093 811270831329832051667315)
                ·
                  refine ⟨1216906246994748077500973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 811270831329832051667315 1216906246994748077500973)
                  ·
                    refine ⟨456339842623030529062865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1216906246994748077500973 456339842623030529062865)
                    ·
                      refine ⟨342254881967272896797149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 456339842623030529062865 342254881967272896797149)
                      ·
                        rfl

theorem cell23_666539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 9, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 9, 1, 3, 2].length) (baseStart_666539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_666539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_666539 prefixEnd_666539 := by exact prefixLift 666539
  have htrace : WordTrace (prefixWord ++ tailWord_666539) baseStart_666539 baseEnd_666539 := by
    simpa [prefixWord, tailWord_666539, baseEnd_666539] using wordTrace_append hprefix tailTrace_666539
  have hstable : (prefixWord ++ tailWord_666539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666539).length < 2 ^ (prefixWord ++ tailWord_666539).sum := by decide
  have hdescent : baseEnd_666539 < baseStart_666539 := by decide
  rcases family_descends (prefixWord ++ tailWord_666539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666569 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 8, 2, 2]
def baseStart_666569 : Nat := 118140960795 + 666569 * 2 ^ 59
def prefixEnd_666569 : Nat := 4983230072969 + 3 ^ 40 * 666569 * 2
def baseEnd_666569 : Nat := 342270286386907779422011

theorem tailTrace_666569 : CollatzResearch.WordTrace tailWord_666569 prefixEnd_666569 342270286386907779422011 := by
  unfold tailWord_666569
  simp only [CollatzResearch.WordTrace]
  refine ⟨24311768722141828766970761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16207845814761219177980507 24311768722141828766970761)
  ·
    refine ⟨18233826541606371575228071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24311768722141828766970761 18233826541606371575228071)
    ·
      refine ⟨27350739812409557362842107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18233826541606371575228071 27350739812409557362842107)
      ·
        refine ⟨41026109718614336044263161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27350739812409557362842107 41026109718614336044263161)
        ·
          refine ⟨30769582288960752033197371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41026109718614336044263161 30769582288960752033197371)
          ·
            refine ⟨46154373433441128049796057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30769582288960752033197371 46154373433441128049796057)
            ·
              refine ⟨34615780075080846037347043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46154373433441128049796057 34615780075080846037347043)
              ·
                refine ⟨51923670112621269056020565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34615780075080846037347043 51923670112621269056020565)
                ·
                  refine ⟨608480509132280496750241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 51923670112621269056020565 608480509132280496750241)
                  ·
                    refine ⟨456360381849210372562681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 608480509132280496750241 456360381849210372562681)
                    ·
                      refine ⟨342270286386907779422011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 456360381849210372562681 342270286386907779422011)
                      ·
                        rfl

theorem cell23_666569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 8, 2, 2].length) (baseStart_666569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_666569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_666569 prefixEnd_666569 := by exact prefixLift 666569
  have htrace : WordTrace (prefixWord ++ tailWord_666569) baseStart_666569 baseEnd_666569 := by
    simpa [prefixWord, tailWord_666569, baseEnd_666569] using wordTrace_append hprefix tailTrace_666569
  have hstable : (prefixWord ++ tailWord_666569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666569).length < 2 ^ (prefixWord ++ tailWord_666569).sum := by decide
  have hdescent : baseEnd_666569 < baseStart_666569 := by decide
  rcases family_descends (prefixWord ++ tailWord_666569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666572 : List Nat := [2, 2, 1, 4, 1, 1, 2, 2, 2, 1, 5]
def baseStart_666572 : Nat := 118140960795 + 666572 * 2 ^ 59
def prefixEnd_666572 : Nat := 4983230072969 + 3 ^ 40 * 666572 * 2
def baseEnd_666572 : Nat := 342271826828871267684497

theorem tailTrace_666572 : CollatzResearch.WordTrace tailWord_666572 prefixEnd_666572 342271826828871267684497 := by
  unfold tailWord_666572
  simp only [CollatzResearch.WordTrace]
  refine ⟨12155939070565480139664985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16207918760753973519553313 12155939070565480139664985)
  ·
    refine ⟨9116954302924110104748739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12155939070565480139664985 9116954302924110104748739)
    ·
      refine ⟨13675431454386165157123109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9116954302924110104748739 13675431454386165157123109)
      ·
        refine ⟨2564143397697405966960583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13675431454386165157123109 2564143397697405966960583)
        ·
          refine ⟨3846215096546108950440875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2564143397697405966960583 3846215096546108950440875)
          ·
            refine ⟨5769322644819163425661313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3846215096546108950440875 5769322644819163425661313)
            ·
              refine ⟨4326991983614372569245985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5769322644819163425661313 4326991983614372569245985)
              ·
                refine ⟨3245243987710779426934489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4326991983614372569245985 3245243987710779426934489)
                ·
                  refine ⟨2433932990783084570200867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3245243987710779426934489 2433932990783084570200867)
                  ·
                    refine ⟨3650899486174626855301301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2433932990783084570200867 3650899486174626855301301)
                    ·
                      refine ⟨342271826828871267684497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3650899486174626855301301 342271826828871267684497)
                      ·
                        rfl

theorem cell23_666572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_666572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_666572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_666572 prefixEnd_666572 := by exact prefixLift 666572
  have htrace : WordTrace (prefixWord ++ tailWord_666572) baseStart_666572 baseEnd_666572 := by
    simpa [prefixWord, tailWord_666572, baseEnd_666572] using wordTrace_append hprefix tailTrace_666572
  have hstable : (prefixWord ++ tailWord_666572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666572).length < 2 ^ (prefixWord ++ tailWord_666572).sum := by decide
  have hdescent : baseEnd_666572 < baseStart_666572 := by decide
  rcases family_descends (prefixWord ++ tailWord_666572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666586 : List Nat := [3, 1, 1, 2, 4, 1, 1, 2, 4, 2, 2]
def baseStart_666586 : Nat := 118140960795 + 666586 * 2 ^ 59
def prefixEnd_666586 : Nat := 4983230072969 + 3 ^ 40 * 666586 * 2
def baseEnd_666586 : Nat := 342279015558034212909433

theorem tailTrace_666586 : CollatzResearch.WordTrace tailWord_666586 prefixEnd_666586 342279015558034212909433 := by
  unfold tailWord_666586
  simp only [CollatzResearch.WordTrace]
  refine ⟨6078097190770060167584903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16208259175386827113559741 6078097190770060167584903)
  ·
    refine ⟨9117145786155090251377355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6078097190770060167584903 9117145786155090251377355)
    ·
      refine ⟨13675718679232635377066033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9117145786155090251377355 13675718679232635377066033)
      ·
        refine ⟨10256789009424476532799525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13675718679232635377066033 10256789009424476532799525)
        ·
          refine ⟨1923147939267089349899911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10256789009424476532799525 1923147939267089349899911)
          ·
            refine ⟨2884721908900634024849867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1923147939267089349899911 2884721908900634024849867)
            ·
              refine ⟨4327082863350951037274801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2884721908900634024849867 4327082863350951037274801)
              ·
                refine ⟨3245312147513213277956101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4327082863350951037274801 3245312147513213277956101)
                ·
                  refine ⟨608496027658727489616769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3245312147513213277956101 608496027658727489616769)
                  ·
                    refine ⟨456372020744045617212577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 608496027658727489616769 456372020744045617212577)
                    ·
                      refine ⟨342279015558034212909433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 456372020744045617212577 342279015558034212909433)
                      ·
                        rfl

theorem cell23_666586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 4, 2, 2].length) (baseStart_666586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_666586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_666586 prefixEnd_666586 := by exact prefixLift 666586
  have htrace : WordTrace (prefixWord ++ tailWord_666586) baseStart_666586 baseEnd_666586 := by
    simpa [prefixWord, tailWord_666586, baseEnd_666586] using wordTrace_append hprefix tailTrace_666586
  have hstable : (prefixWord ++ tailWord_666586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666586).length < 2 ^ (prefixWord ++ tailWord_666586).sum := by decide
  have hdescent : baseEnd_666586 < baseStart_666586 := by decide
  rcases family_descends (prefixWord ++ tailWord_666586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666589 : List Nat := [1, 4, 3, 1, 2, 2, 1, 1, 2, 1, 5]
def baseStart_666589 : Nat := 118140960795 + 666589 * 2 ^ 59
def prefixEnd_666589 : Nat := 4983230072969 + 3 ^ 40 * 666589 * 2
def baseEnd_666589 : Nat := 342280555999997701171919

theorem tailTrace_666589 : CollatzResearch.WordTrace tailWord_666589 prefixEnd_666589 342280555999997701171919 := by
  unfold tailWord_666589
  simp only [CollatzResearch.WordTrace]
  refine ⟨24312498182069372182698821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16208332121379581455132547 24312498182069372182698821)
  ·
    refine ⟨4558593409138007284256029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24312498182069372182698821 4558593409138007284256029)
    ·
      refine ⟨1709472528426752731596011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4558593409138007284256029 1709472528426752731596011)
      ·
        refine ⟨2564208792640129097394017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1709472528426752731596011 2564208792640129097394017)
        ·
          refine ⟨1923156594480096823045513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2564208792640129097394017 1923156594480096823045513)
          ·
            refine ⟨1442367445860072617284135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1923156594480096823045513 1442367445860072617284135)
            ·
              refine ⟨2163551168790108925926203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1442367445860072617284135 2163551168790108925926203)
              ·
                refine ⟨3245326753185163388889305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2163551168790108925926203 3245326753185163388889305)
                ·
                  refine ⟨2433995064888872541666979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3245326753185163388889305 2433995064888872541666979)
                  ·
                    refine ⟨3650992597333308812500469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2433995064888872541666979 3650992597333308812500469)
                    ·
                      refine ⟨342280555999997701171919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3650992597333308812500469 342280555999997701171919)
                      ·
                        rfl

theorem cell23_666589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_666589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_666589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_666589 prefixEnd_666589 := by exact prefixLift 666589
  have htrace : WordTrace (prefixWord ++ tailWord_666589) baseStart_666589 baseEnd_666589 := by
    simpa [prefixWord, tailWord_666589, baseEnd_666589] using wordTrace_append hprefix tailTrace_666589
  have hstable : (prefixWord ++ tailWord_666589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666589).length < 2 ^ (prefixWord ++ tailWord_666589).sum := by decide
  have hdescent : baseEnd_666589 < baseStart_666589 := by decide
  rcases family_descends (prefixWord ++ tailWord_666589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666609 : List Nat := [1, 2, 2, 2, 4, 3, 1, 1, 7]
def baseStart_666609 : Nat := 118140960795 + 666609 * 2 ^ 59
def prefixEnd_666609 : Nat := 4983230072969 + 3 ^ 40 * 666609 * 2
def baseEnd_666609 : Nat := 38032313957009735880203

theorem tailTrace_666609 : CollatzResearch.WordTrace tailWord_666609 prefixEnd_666609 38032313957009735880203 := by
  unfold tailWord_666609
  simp only [CollatzResearch.WordTrace]
  refine ⟨24313227641996915598426881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16208818427997943732284587 24313227641996915598426881)
  ·
    refine ⟨18234920731497686698820161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24313227641996915598426881 18234920731497686698820161)
    ·
      refine ⟨13676190548623265024115121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18234920731497686698820161 13676190548623265024115121)
      ·
        refine ⟨10257142911467448768086341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13676190548623265024115121 10257142911467448768086341)
        ·
          refine ⟨1923214295900146644016189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10257142911467448768086341 1923214295900146644016189)
          ·
            refine ⟨721205360962554991506071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1923214295900146644016189 721205360962554991506071)
            ·
              refine ⟨1081808041443832487259107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 721205360962554991506071 1081808041443832487259107)
              ·
                refine ⟨1622712062165748730888661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1081808041443832487259107 1622712062165748730888661)
                ·
                  refine ⟨38032313957009735880203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1622712062165748730888661 38032313957009735880203)
                  ·
                    rfl

theorem cell23_666609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 7].length) (baseStart_666609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_666609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_666609 prefixEnd_666609 := by exact prefixLift 666609
  have htrace : WordTrace (prefixWord ++ tailWord_666609) baseStart_666609 baseEnd_666609 := by
    simpa [prefixWord, tailWord_666609, baseEnd_666609] using wordTrace_append hprefix tailTrace_666609
  have hstable : (prefixWord ++ tailWord_666609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666609).length < 2 ^ (prefixWord ++ tailWord_666609).sum := by decide
  have hdescent : baseEnd_666609 < baseStart_666609 := by decide
  rcases family_descends (prefixWord ++ tailWord_666609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666620 : List Nat := [2, 2, 2, 1, 2, 5, 2, 1, 2, 2, 2]
def baseStart_666620 : Nat := 118140960795 + 666620 * 2 ^ 59
def prefixEnd_666620 : Nat := 4983230072969 + 3 ^ 40 * 666620 * 2
def baseEnd_666620 : Nat := 342296473900287079884277

theorem tailTrace_666620 : CollatzResearch.WordTrace tailWord_666620 prefixEnd_666620 342296473900287079884277 := by
  unfold tailWord_666620
  simp only [CollatzResearch.WordTrace]
  refine ⟨12156814422478532238538657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16209085896638042984718209 12156814422478532238538657)
  ·
    refine ⟨9117610816858899178903993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12156814422478532238538657 9117610816858899178903993)
    ·
      refine ⟨6838208112644174384177995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9117610816858899178903993 6838208112644174384177995)
      ·
        refine ⟨10257312168966261576266993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6838208112644174384177995 10257312168966261576266993)
        ·
          refine ⟨7692984126724696182200245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10257312168966261576266993 7692984126724696182200245)
          ·
            refine ⟨721217261880440267081273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7692984126724696182200245 721217261880440267081273)
            ·
              refine ⟨540912946410330200310955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 721217261880440267081273 540912946410330200310955)
              ·
                refine ⟨811369419615495300466433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 540912946410330200310955 811369419615495300466433)
                ·
                  refine ⟨608527064711621475349825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 811369419615495300466433 608527064711621475349825)
                  ·
                    refine ⟨456395298533716106512369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 608527064711621475349825 456395298533716106512369)
                    ·
                      refine ⟨342296473900287079884277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 456395298533716106512369 342296473900287079884277)
                      ·
                        rfl

theorem cell23_666620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 1, 2, 2, 2].length) (baseStart_666620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_666620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_666620 prefixEnd_666620 := by exact prefixLift 666620
  have htrace : WordTrace (prefixWord ++ tailWord_666620) baseStart_666620 baseEnd_666620 := by
    simpa [prefixWord, tailWord_666620, baseEnd_666620] using wordTrace_append hprefix tailTrace_666620
  have hstable : (prefixWord ++ tailWord_666620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666620).length < 2 ^ (prefixWord ++ tailWord_666620).sum := by decide
  have hdescent : baseEnd_666620 < baseStart_666620 := by decide
  rcases family_descends (prefixWord ++ tailWord_666620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666659 : List Nat := [1, 1, 1, 4, 3, 2, 2, 2, 2, 1, 4]
def baseStart_666659 : Nat := 118140960795 + 666659 * 2 ^ 59
def prefixEnd_666659 : Nat := 4983230072969 + 3 ^ 40 * 666659 * 2
def baseEnd_666659 : Nat := 342316499645812427296597

theorem tailTrace_666659 : CollatzResearch.WordTrace tailWord_666659 prefixEnd_666659 342316499645812427296597 := by
  unfold tailWord_666659
  simp only [CollatzResearch.WordTrace]
  refine ⟨24315051291815774137747031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16210034194543849425164687 24315051291815774137747031)
  ·
    refine ⟨36472576937723661206620547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24315051291815774137747031 36472576937723661206620547)
    ·
      refine ⟨54708865406585491809930821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36472576937723661206620547 54708865406585491809930821)
      ·
        refine ⟨10257912263734779714362029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54708865406585491809930821 10257912263734779714362029)
        ·
          refine ⟨3846717098900542392885761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10257912263734779714362029 3846717098900542392885761)
          ·
            refine ⟨2885037824175406794664321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3846717098900542392885761 2885037824175406794664321)
            ·
              refine ⟨2163778368131555095998241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2885037824175406794664321 2163778368131555095998241)
              ·
                refine ⟨1622833776098666321998681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2163778368131555095998241 1622833776098666321998681)
                ·
                  refine ⟨1217125332073999741499011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1622833776098666321998681 1217125332073999741499011)
                  ·
                    refine ⟨1825687998110999612248517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1217125332073999741499011 1825687998110999612248517)
                    ·
                      refine ⟨342316499645812427296597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1825687998110999612248517 342316499645812427296597)
                      ·
                        rfl

theorem cell23_666659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_666659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_666659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_666659 prefixEnd_666659 := by exact prefixLift 666659
  have htrace : WordTrace (prefixWord ++ tailWord_666659) baseStart_666659 baseEnd_666659 := by
    simpa [prefixWord, tailWord_666659, baseEnd_666659] using wordTrace_append hprefix tailTrace_666659
  have hstable : (prefixWord ++ tailWord_666659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666659).length < 2 ^ (prefixWord ++ tailWord_666659).sum := by decide
  have hdescent : baseEnd_666659 < baseStart_666659 := by decide
  rcases family_descends (prefixWord ++ tailWord_666659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666686 : List Nat := [4, 2, 1, 3, 1, 1, 1, 1, 5, 4]
def baseStart_666686 : Nat := 118140960795 + 666686 * 2 ^ 59
def prefixEnd_666686 : Nat := 4983230072969 + 3 ^ 40 * 666686 * 2
def baseEnd_666686 : Nat := 114110121207827940552991

theorem tailTrace_666686 : CollatzResearch.WordTrace tailWord_666686 prefixEnd_666686 114110121207827940552991 := by
  unfold tailWord_666686
  simp only [CollatzResearch.WordTrace]
  refine ⟨3039504507839744718622489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16210690708478638499319941 3039504507839744718622489)
  ·
    refine ⟨2279628380879808538966867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3039504507839744718622489 2279628380879808538966867)
    ·
      refine ⟨3419442571319712808450301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2279628380879808538966867 3419442571319712808450301)
      ·
        refine ⟨1282290964244892303168863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3419442571319712808450301 1282290964244892303168863)
        ·
          refine ⟨1923436446367338454753295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1282290964244892303168863 1923436446367338454753295)
          ·
            refine ⟨2885154669551007682129943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1923436446367338454753295 2885154669551007682129943)
            ·
              refine ⟨4327732004326511523194915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2885154669551007682129943 4327732004326511523194915)
              ·
                refine ⟨6491598006489767284792373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4327732004326511523194915 6491598006489767284792373)
                ·
                  refine ⟨608587313108415682949285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6491598006489767284792373 608587313108415682949285)
                  ·
                    refine ⟨114110121207827940552991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 608587313108415682949285 114110121207827940552991)
                    ·
                      rfl

theorem cell23_666686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_666686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_666686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_666686 prefixEnd_666686 := by exact prefixLift 666686
  have htrace : WordTrace (prefixWord ++ tailWord_666686) baseStart_666686 baseEnd_666686 := by
    simpa [prefixWord, tailWord_666686, baseEnd_666686] using wordTrace_append hprefix tailTrace_666686
  have hstable : (prefixWord ++ tailWord_666686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666686).length < 2 ^ (prefixWord ++ tailWord_666686).sum := by decide
  have hdescent : baseEnd_666686 < baseStart_666686 := by decide
  rcases family_descends (prefixWord ++ tailWord_666686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666776 : List Nat := [2, 1, 2, 4, 2, 1, 2, 1, 4, 4]
def baseStart_666776 : Nat := 118140960795 + 666776 * 2 ^ 59
def prefixEnd_666776 : Nat := 4983230072969 + 3 ^ 40 * 666776 * 2
def baseEnd_666776 : Nat := 114125525627462823177853

theorem tailTrace_666776 : CollatzResearch.WordTrace tailWord_666776 prefixEnd_666776 114125525627462823177853 := by
  unfold tailWord_666776
  simp only [CollatzResearch.WordTrace]
  refine ⟨12159659316195951559878091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16212879088261268746504121 12159659316195951559878091)
  ·
    refine ⟨18239488974293927339817137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12159659316195951559878091 18239488974293927339817137)
    ·
      refine ⟨13679616730720445504862853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18239488974293927339817137 13679616730720445504862853)
      ·
        refine ⟨2564928137010083532161785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13679616730720445504862853 2564928137010083532161785)
        ·
          refine ⟨1923696102757562649121339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2564928137010083532161785 1923696102757562649121339)
          ·
            refine ⟨2885544154136343973682009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1923696102757562649121339 2885544154136343973682009)
            ·
              refine ⟨2164158115602257980261507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2885544154136343973682009 2164158115602257980261507)
              ·
                refine ⟨3246237173403386970392261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2164158115602257980261507 3246237173403386970392261)
                ·
                  refine ⟨608669470013135056948549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3246237173403386970392261 608669470013135056948549)
                  ·
                    refine ⟨114125525627462823177853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 608669470013135056948549 114125525627462823177853)
                    ·
                      rfl

theorem cell23_666776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 4, 4].length) (baseStart_666776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_666776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_666776 prefixEnd_666776 := by exact prefixLift 666776
  have htrace : WordTrace (prefixWord ++ tailWord_666776) baseStart_666776 baseEnd_666776 := by
    simpa [prefixWord, tailWord_666776, baseEnd_666776] using wordTrace_append hprefix tailTrace_666776
  have hstable : (prefixWord ++ tailWord_666776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666776).length < 2 ^ (prefixWord ++ tailWord_666776).sum := by decide
  have hdescent : baseEnd_666776 < baseStart_666776 := by decide
  rcases family_descends (prefixWord ++ tailWord_666776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666789 : List Nat := [1, 3, 1, 2, 1, 5, 2, 8]
def baseStart_666789 : Nat := 118140960795 + 666789 * 2 ^ 59
def prefixEnd_666789 : Nat := 4983230072969 + 3 ^ 40 * 666789 * 2
def baseEnd_666789 : Nat := 12680861190033219210037

theorem tailTrace_666789 : CollatzResearch.WordTrace tailWord_666789 prefixEnd_666789 12680861190033219210037 := by
  unfold tailWord_666789
  simp only [CollatzResearch.WordTrace]
  refine ⟨24319792781344806339979421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16213195187563204226652947 24319792781344806339979421)
  ·
    refine ⟨9119922293004302377492283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24319792781344806339979421 9119922293004302377492283)
    ·
      refine ⟨13679883439506453566238425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9119922293004302377492283 13679883439506453566238425)
      ·
        refine ⟨10259912579629840174678819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13679883439506453566238425 10259912579629840174678819)
        ·
          refine ⟨15389868869444760262018229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10259912579629840174678819 15389868869444760262018229)
          ·
            refine ⟨1442800206510446274564209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15389868869444760262018229 1442800206510446274564209)
            ·
              refine ⟨1082100154882834705923157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1442800206510446274564209 1082100154882834705923157)
              ·
                refine ⟨12680861190033219210037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1082100154882834705923157 12680861190033219210037)
                ·
                  rfl

theorem cell23_666789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 8].length) (baseStart_666789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_666789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_666789 prefixEnd_666789 := by exact prefixLift 666789
  have htrace : WordTrace (prefixWord ++ tailWord_666789) baseStart_666789 baseEnd_666789 := by
    simpa [prefixWord, tailWord_666789, baseEnd_666789] using wordTrace_append hprefix tailTrace_666789
  have hstable : (prefixWord ++ tailWord_666789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666789).length < 2 ^ (prefixWord ++ tailWord_666789).sum := by decide
  have hdescent : baseEnd_666789 < baseStart_666789 := by decide
  rcases family_descends (prefixWord ++ tailWord_666789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666820 : List Nat := [2, 3, 3, 1, 4, 1, 1, 1, 1, 1, 5]
def baseStart_666820 : Nat := 118140960795 + 666820 * 2 ^ 59
def prefixEnd_666820 : Nat := 4983230072969 + 3 ^ 40 * 666820 * 2
def baseEnd_666820 : Nat := 342399170031186297383357

theorem tailTrace_666820 : CollatzResearch.WordTrace tailWord_666820 prefixEnd_666820 342399170031186297383357 := by
  unfold tailWord_666820
  simp only [CollatzResearch.WordTrace]
  refine ⟨12160461722116249317178957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16213948962821665756238609 12160461722116249317178957)
  ·
    refine ⟨4560173145793593493942109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12160461722116249317178957 4560173145793593493942109)
    ·
      refine ⟨1710064929672597560228291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4560173145793593493942109 1710064929672597560228291)
      ·
        refine ⟨2565097394508896340342437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1710064929672597560228291 2565097394508896340342437)
        ·
          refine ⟨480955761470418063814207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2565097394508896340342437 480955761470418063814207)
          ·
            refine ⟨721433642205627095721311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 480955761470418063814207 721433642205627095721311)
            ·
              refine ⟨1082150463308440643581967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 721433642205627095721311 1082150463308440643581967)
              ·
                refine ⟨1623225694962660965372951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1082150463308440643581967 1623225694962660965372951)
                ·
                  refine ⟨2434838542443991448059427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1623225694962660965372951 2434838542443991448059427)
                  ·
                    refine ⟨3652257813665987172089141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2434838542443991448059427 3652257813665987172089141)
                    ·
                      refine ⟨342399170031186297383357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3652257813665987172089141 342399170031186297383357)
                      ·
                        rfl

theorem cell23_666820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_666820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_666820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_666820 prefixEnd_666820 := by exact prefixLift 666820
  have htrace : WordTrace (prefixWord ++ tailWord_666820) baseStart_666820 baseEnd_666820 := by
    simpa [prefixWord, tailWord_666820, baseEnd_666820] using wordTrace_append hprefix tailTrace_666820
  have hstable : (prefixWord ++ tailWord_666820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666820).length < 2 ^ (prefixWord ++ tailWord_666820).sum := by decide
  have hdescent : baseEnd_666820 < baseStart_666820 := by decide
  rcases family_descends (prefixWord ++ tailWord_666820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666839 : List Nat := [1, 1, 3, 2, 1, 2, 3, 1, 2, 3, 4]
def baseStart_666839 : Nat := 118140960795 + 666839 * 2 ^ 59
def prefixEnd_666839 : Nat := 4983230072969 + 3 ^ 40 * 666839 * 2
def baseEnd_666839 : Nat := 342408926163621723045769

theorem tailTrace_666839 : CollatzResearch.WordTrace tailWord_666839 prefixEnd_666839 342408926163621723045769 := by
  unfold tailWord_666839
  simp only [CollatzResearch.WordTrace]
  refine ⟨24321616431163664879299571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16214410954109109919533047 24321616431163664879299571)
  ·
    refine ⟨36482424646745497318949357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24321616431163664879299571 36482424646745497318949357)
    ·
      refine ⟨13680909242529561494606009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36482424646745497318949357 13680909242529561494606009)
      ·
        refine ⟨10260681931897171120954507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13680909242529561494606009 10260681931897171120954507)
        ·
          refine ⟨15391022897845756681431761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10260681931897171120954507 15391022897845756681431761)
          ·
            refine ⟨11543267173384317511073821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15391022897845756681431761 11543267173384317511073821)
            ·
              refine ⟨4328725190019119066652683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11543267173384317511073821 4328725190019119066652683)
              ·
                refine ⟨6493087785028678599979025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4328725190019119066652683 6493087785028678599979025)
                ·
                  refine ⟨4869815838771508949984269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6493087785028678599979025 4869815838771508949984269)
                  ·
                    refine ⟨1826180939539315856244101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4869815838771508949984269 1826180939539315856244101)
                    ·
                      refine ⟨342408926163621723045769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1826180939539315856244101 342408926163621723045769)
                      ·
                        rfl

theorem cell23_666839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_666839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_666839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_666839 prefixEnd_666839 := by exact prefixLift 666839
  have htrace : WordTrace (prefixWord ++ tailWord_666839) baseStart_666839 baseEnd_666839 := by
    simpa [prefixWord, tailWord_666839, baseEnd_666839] using wordTrace_append hprefix tailTrace_666839
  have hstable : (prefixWord ++ tailWord_666839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666839).length < 2 ^ (prefixWord ++ tailWord_666839).sum := by decide
  have hdescent : baseEnd_666839 < baseStart_666839 := by decide
  rcases family_descends (prefixWord ++ tailWord_666839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666849 : List Nat := [1, 2, 3, 1, 3, 2, 1, 1, 1, 8]
def baseStart_666849 : Nat := 118140960795 + 666849 * 2 ^ 59
def prefixEnd_666849 : Nat := 4983230072969 + 3 ^ 40 * 666849 * 2
def baseEnd_666849 : Nat := 114138020323388894640241

theorem tailTrace_666849 : CollatzResearch.WordTrace tailWord_666849 prefixEnd_666849 114138020323388894640241 := by
  unfold tailWord_666849
  simp only [CollatzResearch.WordTrace]
  refine ⟨24321981161127436587163601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16214654107418291058109067 24321981161127436587163601)
  ·
    refine ⟨18241485870845577440372701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24321981161127436587163601 18241485870845577440372701)
    ·
      refine ⟨6840557201567091540139763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18241485870845577440372701 6840557201567091540139763)
      ·
        refine ⟨10260835802350637310209645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6840557201567091540139763 10260835802350637310209645)
        ·
          refine ⟨3847813425881488991328617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10260835802350637310209645 3847813425881488991328617)
          ·
            refine ⟨2885860069411116743496463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3847813425881488991328617 2885860069411116743496463)
            ·
              refine ⟨4328790104116675115244695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2885860069411116743496463 4328790104116675115244695)
              ·
                refine ⟨6493185156175012672867043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4328790104116675115244695 6493185156175012672867043)
                ·
                  refine ⟨9739777734262519009300565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6493185156175012672867043 9739777734262519009300565)
                  ·
                    refine ⟨114138020323388894640241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 9739777734262519009300565 114138020323388894640241)
                    ·
                      rfl

theorem cell23_666849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 8].length) (baseStart_666849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_666849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_666849 prefixEnd_666849 := by exact prefixLift 666849
  have htrace : WordTrace (prefixWord ++ tailWord_666849) baseStart_666849 baseEnd_666849 := by
    simpa [prefixWord, tailWord_666849, baseEnd_666849] using wordTrace_append hprefix tailTrace_666849
  have hstable : (prefixWord ++ tailWord_666849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666849).length < 2 ^ (prefixWord ++ tailWord_666849).sum := by decide
  have hdescent : baseEnd_666849 < baseStart_666849 := by decide
  rcases family_descends (prefixWord ++ tailWord_666849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666868 : List Nat := [2, 6, 1, 2, 1, 1, 2, 3, 1, 2, 2]
def baseStart_666868 : Nat := 118140960795 + 666868 * 2 ^ 59
def prefixEnd_666868 : Nat := 4983230072969 + 3 ^ 40 * 666868 * 2
def baseEnd_666868 : Nat := 342423817102602109583137

theorem tailTrace_666868 : CollatzResearch.WordTrace tailWord_666868 prefixEnd_666868 342423817102602109583137 := by
  unfold tailWord_666868
  simp only [CollatzResearch.WordTrace]
  refine ⟨12161337074029301416052629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16215116098705735221403505 12161337074029301416052629)
  ·
    refine ⟨570062675345123503877467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 12161337074029301416052629 570062675345123503877467)
    ·
      refine ⟨855094013017685255816201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 570062675345123503877467 855094013017685255816201)
      ·
        refine ⟨641320509763263941862151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 855094013017685255816201 641320509763263941862151)
        ·
          refine ⟨961980764644895912793227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 641320509763263941862151 961980764644895912793227)
          ·
            refine ⟨1442971146967343869189841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 961980764644895912793227 1442971146967343869189841)
            ·
              refine ⟨1082228360225507901892381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1442971146967343869189841 1082228360225507901892381)
              ·
                refine ⟨405835635084565463209643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1082228360225507901892381 405835635084565463209643)
                ·
                  refine ⟨608753452626848194814465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 405835635084565463209643 608753452626848194814465)
                  ·
                    refine ⟨456565089470136146110849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 608753452626848194814465 456565089470136146110849)
                    ·
                      refine ⟨342423817102602109583137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 456565089470136146110849 342423817102602109583137)
                      ·
                        rfl

theorem cell23_666868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_666868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_666868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_666868 prefixEnd_666868 := by exact prefixLift 666868
  have htrace : WordTrace (prefixWord ++ tailWord_666868) baseStart_666868 baseEnd_666868 := by
    simpa [prefixWord, tailWord_666868, baseEnd_666868] using wordTrace_append hprefix tailTrace_666868
  have hstable : (prefixWord ++ tailWord_666868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666868).length < 2 ^ (prefixWord ++ tailWord_666868).sum := by decide
  have hdescent : baseEnd_666868 < baseStart_666868 := by decide
  rcases family_descends (prefixWord ++ tailWord_666868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666873 : List Nat := [1, 2, 1, 3, 1, 1, 4, 2, 4, 2, 2]
def baseStart_666873 : Nat := 118140960795 + 666873 * 2 ^ 59
def prefixEnd_666873 : Nat := 4983230072969 + 3 ^ 40 * 666873 * 2
def baseEnd_666873 : Nat := 342426384505874590020613

theorem tailTrace_666873 : CollatzResearch.WordTrace tailWord_666873 prefixEnd_666873 342426384505874590020613 := by
  unfold tailWord_666873
  simp only [CollatzResearch.WordTrace]
  refine ⟨24322856513040488686037273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16215237675360325790691515 24322856513040488686037273)
  ·
    refine ⟨18242142384780366514527955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24322856513040488686037273 18242142384780366514527955)
    ·
      refine ⟨27363213577170549771791933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18242142384780366514527955 27363213577170549771791933)
      ·
        refine ⟨10261205091438956164421975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27363213577170549771791933 10261205091438956164421975)
        ·
          refine ⟨15391807637158434246632963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10261205091438956164421975 15391807637158434246632963)
          ·
            refine ⟨23087711455737651369949445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15391807637158434246632963 23087711455737651369949445)
            ·
              refine ⟨4328945897950809631865521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23087711455737651369949445 4328945897950809631865521)
              ·
                refine ⟨3246709423463107223899141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4328945897950809631865521 3246709423463107223899141)
                ·
                  refine ⟨608758016899332604481089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3246709423463107223899141 608758016899332604481089)
                  ·
                    refine ⟨456568512674499453360817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 608758016899332604481089 456568512674499453360817)
                    ·
                      refine ⟨342426384505874590020613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 456568512674499453360817 342426384505874590020613)
                      ·
                        rfl

theorem cell23_666873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 4, 2, 2].length) (baseStart_666873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_666873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_666873 prefixEnd_666873 := by exact prefixLift 666873
  have htrace : WordTrace (prefixWord ++ tailWord_666873) baseStart_666873 baseEnd_666873 := by
    simpa [prefixWord, tailWord_666873, baseEnd_666873] using wordTrace_append hprefix tailTrace_666873
  have hstable : (prefixWord ++ tailWord_666873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666873).length < 2 ^ (prefixWord ++ tailWord_666873).sum := by decide
  have hdescent : baseEnd_666873 < baseStart_666873 := by decide
  rcases family_descends (prefixWord ++ tailWord_666873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666930 : List Nat := [3, 2, 1, 1, 4, 3, 1, 3, 5]
def baseStart_666930 : Nat := 118140960795 + 666930 * 2 ^ 59
def prefixEnd_666930 : Nat := 4983230072969 + 3 ^ 40 * 666930 * 2
def baseEnd_666930 : Nat := 38050628100353429667539

theorem tailTrace_666930 : CollatzResearch.WordTrace tailWord_666930 prefixEnd_666930 38050628100353429667539 := by
  unfold tailWord_666930
  simp only [CollatzResearch.WordTrace]
  refine ⟨6081233868458496855215561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16216623649222658280574829 6081233868458496855215561)
  ·
    refine ⟨4560925401343872641411671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6081233868458496855215561 4560925401343872641411671)
    ·
      refine ⟨6841388102015808962117507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4560925401343872641411671 6841388102015808962117507)
      ·
        refine ⟨10262082153023713443176261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6841388102015808962117507 10262082153023713443176261)
        ·
          refine ⟨1924140403691946270595549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10262082153023713443176261 1924140403691946270595549)
          ·
            refine ⟨721552651384479851473331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1924140403691946270595549 721552651384479851473331)
            ·
              refine ⟨1082328977076719777209997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 721552651384479851473331 1082328977076719777209997)
              ·
                refine ⟨405873366403769916453749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1082328977076719777209997 405873366403769916453749)
                ·
                  refine ⟨38050628100353429667539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 405873366403769916453749 38050628100353429667539)
                  ·
                    rfl

theorem cell23_666930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 3, 5].length) (baseStart_666930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_666930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_666930 prefixEnd_666930 := by exact prefixLift 666930
  have htrace : WordTrace (prefixWord ++ tailWord_666930) baseStart_666930 baseEnd_666930 := by
    simpa [prefixWord, tailWord_666930, baseEnd_666930] using wordTrace_append hprefix tailTrace_666930
  have hstable : (prefixWord ++ tailWord_666930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666930).length < 2 ^ (prefixWord ++ tailWord_666930).sum := by decide
  have hdescent : baseEnd_666930 < baseStart_666930 := by decide
  rcases family_descends (prefixWord ++ tailWord_666930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_666959 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 6]
def baseStart_666959 : Nat := 118140960795 + 666959 * 2 ^ 59
def prefixEnd_666959 : Nat := 4983230072969 + 3 ^ 40 * 666959 * 2
def baseEnd_666959 : Nat := 342470543842161253545217

theorem tailTrace_666959 : CollatzResearch.WordTrace tailWord_666959 prefixEnd_666959 342470543842161253545217 := by
  unfold tailWord_666959
  simp only [CollatzResearch.WordTrace]
  refine ⟨24325993190728925373667931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16217328793819283582445287 24325993190728925373667931)
  ·
    refine ⟨36488989786093388060501897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24325993190728925373667931 36488989786093388060501897)
    ·
      refine ⟨27366742339570041045376423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36488989786093388060501897 27366742339570041045376423)
      ·
        refine ⟨41050113509355061568064635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27366742339570041045376423 41050113509355061568064635)
        ·
          refine ⟨61575170264032592352096953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41050113509355061568064635 61575170264032592352096953)
          ·
            refine ⟨46181377698024444264072715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61575170264032592352096953 46181377698024444264072715)
            ·
              refine ⟨69272066547036666396109073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46181377698024444264072715 69272066547036666396109073)
              ·
                refine ⟨51954049910277499797081805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69272066547036666396109073 51954049910277499797081805)
                ·
                  refine ⟨19482768716354062423905677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51954049910277499797081805 19482768716354062423905677)
                  ·
                    refine ⟨7306038268632773408964629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19482768716354062423905677 7306038268632773408964629)
                    ·
                      refine ⟨342470543842161253545217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7306038268632773408964629 342470543842161253545217)
                      ·
                        rfl

theorem cell23_666959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 6].length) (baseStart_666959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_666959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_666959 prefixEnd_666959 := by exact prefixLift 666959
  have htrace : WordTrace (prefixWord ++ tailWord_666959) baseStart_666959 baseEnd_666959 := by
    simpa [prefixWord, tailWord_666959, baseEnd_666959] using wordTrace_append hprefix tailTrace_666959
  have hstable : (prefixWord ++ tailWord_666959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_666959).length < 2 ^ (prefixWord ++ tailWord_666959).sum := by decide
  have hdescent : baseEnd_666959 < baseStart_666959 := by decide
  rcases family_descends (prefixWord ++ tailWord_666959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667063 : List Nat := [1, 1, 3, 1, 3, 2, 3, 1, 4, 4]
def baseStart_667063 : Nat := 118140960795 + 667063 * 2 ^ 59
def prefixEnd_667063 : Nat := 4983230072969 + 3 ^ 40 * 667063 * 2
def baseEnd_667063 : Nat := 114174648610076282214913

theorem tailTrace_667063 : CollatzResearch.WordTrace tailWord_667063 prefixEnd_667063 114174648610076282214913 := by
  unfold tailWord_667063
  simp only [CollatzResearch.WordTrace]
  refine ⟨24329786382352151135453843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16219857588234767423635895 24329786382352151135453843)
  ·
    refine ⟨36494679573528226703180765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24329786382352151135453843 36494679573528226703180765)
    ·
      refine ⟨13685504840073085013692787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36494679573528226703180765 13685504840073085013692787)
      ·
        refine ⟨20528257260109627520539181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13685504840073085013692787 20528257260109627520539181)
        ·
          refine ⟨7698096472541110320202193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20528257260109627520539181 7698096472541110320202193)
          ·
            refine ⟨5773572354405832740151645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7698096472541110320202193 5773572354405832740151645)
            ·
              refine ⟨2165089632902187277556867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5773572354405832740151645 2165089632902187277556867)
              ·
                refine ⟨3247634449353280916335301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2165089632902187277556867 3247634449353280916335301)
                ·
                  refine ⟨608931459253740171812869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3247634449353280916335301 608931459253740171812869)
                  ·
                    refine ⟨114174648610076282214913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 608931459253740171812869 114174648610076282214913)
                    ·
                      rfl

theorem cell23_667063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 4, 4].length) (baseStart_667063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667063 prefixEnd_667063 := by exact prefixLift 667063
  have htrace : WordTrace (prefixWord ++ tailWord_667063) baseStart_667063 baseEnd_667063 := by
    simpa [prefixWord, tailWord_667063, baseEnd_667063] using wordTrace_append hprefix tailTrace_667063
  have hstable : (prefixWord ++ tailWord_667063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667063).length < 2 ^ (prefixWord ++ tailWord_667063).sum := by decide
  have hdescent : baseEnd_667063 < baseStart_667063 := by decide
  rcases family_descends (prefixWord ++ tailWord_667063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667066 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 2, 6, 4]
def baseStart_667066 : Nat := 118140960795 + 667066 * 2 ^ 59
def prefixEnd_667066 : Nat := 4983230072969 + 3 ^ 40 * 667066 * 2
def baseEnd_667066 : Nat := 342525486272192334907225

theorem tailTrace_667066 : CollatzResearch.WordTrace tailWord_667066 prefixEnd_667066 342525486272192334907225 := by
  unfold tailWord_667066
  simp only [CollatzResearch.WordTrace]
  refine ⟨6082473950335320661953263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16219930534227521765208701 6082473950335320661953263)
  ·
    refine ⟨9123710925502980992929895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6082473950335320661953263 9123710925502980992929895)
    ·
      refine ⟨13685566388254471489394843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9123710925502980992929895 13685566388254471489394843)
      ·
        refine ⟨20528349582381707234092265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13685566388254471489394843 20528349582381707234092265)
        ·
          refine ⟨15396262186786280425569199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20528349582381707234092265 15396262186786280425569199)
          ·
            refine ⟨23094393280179420638353799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15396262186786280425569199 23094393280179420638353799)
            ·
              refine ⟨34641589920269130957530699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23094393280179420638353799 34641589920269130957530699)
              ·
                refine ⟨51962384880403696436296049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34641589920269130957530699 51962384880403696436296049)
                ·
                  refine ⟨38971788660302772327222037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51962384880403696436296049 38971788660302772327222037)
                  ·
                    refine ⟨1826802593451692452838533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 38971788660302772327222037 1826802593451692452838533)
                    ·
                      refine ⟨342525486272192334907225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1826802593451692452838533 342525486272192334907225)
                      ·
                        rfl

theorem cell23_667066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 2, 6, 4].length) (baseStart_667066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667066 prefixEnd_667066 := by exact prefixLift 667066
  have htrace : WordTrace (prefixWord ++ tailWord_667066) baseStart_667066 baseEnd_667066 := by
    simpa [prefixWord, tailWord_667066, baseEnd_667066] using wordTrace_append hprefix tailTrace_667066
  have hstable : (prefixWord ++ tailWord_667066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667066).length < 2 ^ (prefixWord ++ tailWord_667066).sum := by decide
  have hdescent : baseEnd_667066 < baseStart_667066 := by decide
  rcases family_descends (prefixWord ++ tailWord_667066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667083 : List Nat := [1, 1, 1, 1, 3, 3, 5, 1, 1, 2, 4]
def baseStart_667083 : Nat := 118140960795 + 667083 * 2 ^ 59
def prefixEnd_667083 : Nat := 4983230072969 + 3 ^ 40 * 667083 * 2
def baseEnd_667083 : Nat := 342534215443318768394647

theorem tailTrace_667083 : CollatzResearch.WordTrace tailWord_667083 prefixEnd_667083 342534215443318768394647 := by
  unfold tailWord_667083
  simp only [CollatzResearch.WordTrace]
  refine ⟨24330515842279694551181903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16220343894853129700787935 24330515842279694551181903)
  ·
    refine ⟨36495773763419541826772855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24330515842279694551181903 36495773763419541826772855)
    ·
      refine ⟨54743660645129312740159283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36495773763419541826772855 54743660645129312740159283)
      ·
        refine ⟨82115490967693969110238925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54743660645129312740159283 82115490967693969110238925)
        ·
          refine ⟨30793309112885238416339597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82115490967693969110238925 30793309112885238416339597)
          ·
            refine ⟨11547490917331964406127349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30793309112885238416339597 11547490917331964406127349)
            ·
              refine ⟨1082577273499871663074439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11547490917331964406127349 1082577273499871663074439)
              ·
                refine ⟨1623865910249807494611659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1082577273499871663074439 1623865910249807494611659)
                ·
                  refine ⟨2435798865374711241917489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1623865910249807494611659 2435798865374711241917489)
                  ·
                    refine ⟨1826849149031033431438117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2435798865374711241917489 1826849149031033431438117)
                    ·
                      refine ⟨342534215443318768394647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1826849149031033431438117 342534215443318768394647)
                      ·
                        rfl

theorem cell23_667083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 2, 4].length) (baseStart_667083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667083 prefixEnd_667083 := by exact prefixLift 667083
  have htrace : WordTrace (prefixWord ++ tailWord_667083) baseStart_667083 baseEnd_667083 := by
    simpa [prefixWord, tailWord_667083, baseEnd_667083] using wordTrace_append hprefix tailTrace_667083
  have hstable : (prefixWord ++ tailWord_667083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667083).length < 2 ^ (prefixWord ++ tailWord_667083).sum := by decide
  have hdescent : baseEnd_667083 < baseStart_667083 := by decide
  rcases family_descends (prefixWord ++ tailWord_667083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667103 : List Nat := [1, 1, 2, 3, 3, 1, 2, 1, 3, 3, 3]
def baseStart_667103 : Nat := 118140960795 + 667103 * 2 ^ 59
def prefixEnd_667103 : Nat := 4983230072969 + 3 ^ 40 * 667103 * 2
def baseEnd_667103 : Nat := 342544485056408690144555

theorem tailTrace_667103 : CollatzResearch.WordTrace tailWord_667103 prefixEnd_667103 342544485056408690144555 := by
  unfold tailWord_667103
  simp only [CollatzResearch.WordTrace]
  refine ⟨24331245302207237966909963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16220830201471491977939975 24331245302207237966909963)
  ·
    refine ⟨36496867953310856950364945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24331245302207237966909963 36496867953310856950364945)
    ·
      refine ⟨27372650964983142712773709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36496867953310856950364945 27372650964983142712773709)
      ·
        refine ⟨10264744111868678517290141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27372650964983142712773709 10264744111868678517290141)
        ·
          refine ⟨3849279041950754443983803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10264744111868678517290141 3849279041950754443983803)
          ·
            refine ⟨5773918562926131665975705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3849279041950754443983803 5773918562926131665975705)
            ·
              refine ⟨4330438922194598749481779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5773918562926131665975705 4330438922194598749481779)
              ·
                refine ⟨6495658383291898124222669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4330438922194598749481779 6495658383291898124222669)
                ·
                  refine ⟨2435871893734461796583501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6495658383291898124222669 2435871893734461796583501)
                  ·
                    refine ⟨913451960150423173718813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2435871893734461796583501 913451960150423173718813)
                    ·
                      refine ⟨342544485056408690144555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 913451960150423173718813 342544485056408690144555)
                      ·
                        rfl

theorem cell23_667103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 3, 3].length) (baseStart_667103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667103 prefixEnd_667103 := by exact prefixLift 667103
  have htrace : WordTrace (prefixWord ++ tailWord_667103) baseStart_667103 baseEnd_667103 := by
    simpa [prefixWord, tailWord_667103, baseEnd_667103] using wordTrace_append hprefix tailTrace_667103
  have hstable : (prefixWord ++ tailWord_667103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667103).length < 2 ^ (prefixWord ++ tailWord_667103).sum := by decide
  have hdescent : baseEnd_667103 < baseStart_667103 := by decide
  rcases family_descends (prefixWord ++ tailWord_667103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667113 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 1, 9, 2]
def baseStart_667113 : Nat := 118140960795 + 667113 * 2 ^ 59
def prefixEnd_667113 : Nat := 4983230072969 + 3 ^ 40 * 667113 * 2
def baseEnd_667113 : Nat := 342549619862953651019509

theorem tailTrace_667113 : CollatzResearch.WordTrace tailWord_667113 prefixEnd_667113 342549619862953651019509 := by
  unfold tailWord_667113
  simp only [CollatzResearch.WordTrace]
  refine ⟨24331610032171009674773993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16221073354780673116515995 24331610032171009674773993)
  ·
    refine ⟨18248707524128257256080495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24331610032171009674773993 18248707524128257256080495)
    ·
      refine ⟨27373061286192385884120743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18248707524128257256080495 27373061286192385884120743)
      ·
        refine ⟨41059591929288578826181115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27373061286192385884120743 41059591929288578826181115)
        ·
          refine ⟨61589387893932868239271673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41059591929288578826181115 61589387893932868239271673)
          ·
            refine ⟨46192040920449651179453755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61589387893932868239271673 46192040920449651179453755)
            ·
              refine ⟨69288061380674476769180633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46192040920449651179453755 69288061380674476769180633)
              ·
                refine ⟨51966046035505857576885475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69288061380674476769180633 51966046035505857576885475)
                ·
                  refine ⟨77949069053258786365328213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51966046035505857576885475 77949069053258786365328213)
                  ·
                    refine ⟨456732826483938201359345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 77949069053258786365328213 456732826483938201359345)
                    ·
                      refine ⟨342549619862953651019509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 456732826483938201359345 342549619862953651019509)
                      ·
                        rfl

theorem cell23_667113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 9, 2].length) (baseStart_667113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667113 prefixEnd_667113 := by exact prefixLift 667113
  have htrace : WordTrace (prefixWord ++ tailWord_667113) baseStart_667113 baseEnd_667113 := by
    simpa [prefixWord, tailWord_667113, baseEnd_667113] using wordTrace_append hprefix tailTrace_667113
  have hstable : (prefixWord ++ tailWord_667113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667113).length < 2 ^ (prefixWord ++ tailWord_667113).sum := by decide
  have hdescent : baseEnd_667113 < baseStart_667113 := by decide
  rcases family_descends (prefixWord ++ tailWord_667113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667120 : List Nat := [2, 1, 1, 1, 3, 4, 2, 1, 4, 1, 3]
def baseStart_667120 : Nat := 118140960795 + 667120 * 2 ^ 59
def prefixEnd_667120 : Nat := 4983230072969 + 3 ^ 40 * 667120 * 2
def baseEnd_667120 : Nat := 342553214227535123631977

theorem tailTrace_667120 : CollatzResearch.WordTrace tailWord_667120 prefixEnd_667120 342553214227535123631977 := by
  unfold tailWord_667120
  simp only [CollatzResearch.WordTrace]
  refine ⟨12165932671572824935139407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16221243562097099913519209 12165932671572824935139407)
  ·
    refine ⟨18248899007359237402709111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12165932671572824935139407 18248899007359237402709111)
    ·
      refine ⟨27373348511038856104063667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18248899007359237402709111 27373348511038856104063667)
      ·
        refine ⟨41060022766558284156095501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27373348511038856104063667 41060022766558284156095501)
        ·
          refine ⟨15397508537459356558535813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41060022766558284156095501 15397508537459356558535813)
          ·
            refine ⟨2887032850773629354725465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15397508537459356558535813 2887032850773629354725465)
            ·
              refine ⟨2165274638080222016044099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2887032850773629354725465 2165274638080222016044099)
              ·
                refine ⟨3247911957120333024066149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2165274638080222016044099 3247911957120333024066149)
                ·
                  refine ⟨608983491960062442012403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3247911957120333024066149 608983491960062442012403)
                  ·
                    refine ⟨913475237940093663018605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 608983491960062442012403 913475237940093663018605)
                    ·
                      refine ⟨342553214227535123631977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 913475237940093663018605 342553214227535123631977)
                      ·
                        rfl

theorem cell23_667120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 4, 1, 3].length) (baseStart_667120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667120 prefixEnd_667120 := by exact prefixLift 667120
  have htrace : WordTrace (prefixWord ++ tailWord_667120) baseStart_667120 baseEnd_667120 := by
    simpa [prefixWord, tailWord_667120, baseEnd_667120] using wordTrace_append hprefix tailTrace_667120
  have hstable : (prefixWord ++ tailWord_667120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667120).length < 2 ^ (prefixWord ++ tailWord_667120).sum := by decide
  have hdescent : baseEnd_667120 < baseStart_667120 := by decide
  rcases family_descends (prefixWord ++ tailWord_667120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667121 : List Nat := [1, 2, 2, 2, 3, 3, 3, 2, 1, 2, 2]
def baseStart_667121 : Nat := 118140960795 + 667121 * 2 ^ 59
def prefixEnd_667121 : Nat := 4983230072969 + 3 ^ 40 * 667121 * 2
def baseEnd_667121 : Nat := 342553727708189619719473

theorem tailTrace_667121 : CollatzResearch.WordTrace tailWord_667121 prefixEnd_667121 342553727708189619719473 := by
  unfold tailWord_667121
  simp only [CollatzResearch.WordTrace]
  refine ⟨24331901816142027041065217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16221267877428018027376811 24331901816142027041065217)
  ·
    refine ⟨18248926362106520280798913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24331901816142027041065217 18248926362106520280798913)
    ·
      refine ⟨13686694771579890210599185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18248926362106520280798913 13686694771579890210599185)
      ·
        refine ⟨10265021078684917657949389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13686694771579890210599185 10265021078684917657949389)
        ·
          refine ⟨3849382904506844121731021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10265021078684917657949389 3849382904506844121731021)
          ·
            refine ⟨1443518589190066545649133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3849382904506844121731021 1443518589190066545649133)
            ·
              refine ⟨541319470946274954618425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1443518589190066545649133 541319470946274954618425)
              ·
                refine ⟨405989603209706215963819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 541319470946274954618425 405989603209706215963819)
                ·
                  refine ⟨608984404814559323945729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 405989603209706215963819 608984404814559323945729)
                  ·
                    refine ⟨456738303610919492959297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 608984404814559323945729 456738303610919492959297)
                    ·
                      refine ⟨342553727708189619719473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 456738303610919492959297 342553727708189619719473)
                      ·
                        rfl

theorem cell23_667121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 2, 1, 2, 2].length) (baseStart_667121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667121 prefixEnd_667121 := by exact prefixLift 667121
  have htrace : WordTrace (prefixWord ++ tailWord_667121) baseStart_667121 baseEnd_667121 := by
    simpa [prefixWord, tailWord_667121, baseEnd_667121] using wordTrace_append hprefix tailTrace_667121
  have hstable : (prefixWord ++ tailWord_667121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667121).length < 2 ^ (prefixWord ++ tailWord_667121).sum := by decide
  have hdescent : baseEnd_667121 < baseStart_667121 := by decide
  rcases family_descends (prefixWord ++ tailWord_667121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667130 : List Nat := [3, 1, 1, 1, 1, 2, 4, 2, 3, 3, 2]
def baseStart_667130 : Nat := 118140960795 + 667130 * 2 ^ 59
def prefixEnd_667130 : Nat := 4983230072969 + 3 ^ 40 * 667130 * 2
def baseEnd_667130 : Nat := 342558349034080084506931

theorem tailTrace_667130 : CollatzResearch.WordTrace tailWord_667130 prefixEnd_667130 342558349034080084506931 := by
  unfold tailWord_667130
  simp only [CollatzResearch.WordTrace]
  refine ⟨6083057518277355394535711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16221486715406281052095229 6083057518277355394535711)
  ·
    refine ⟨9124586277416033091803567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6083057518277355394535711 9124586277416033091803567)
    ·
      refine ⟨13686879416124049637705351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9124586277416033091803567 13686879416124049637705351)
      ·
        refine ⟨20530319124186074456558027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13686879416124049637705351 20530319124186074456558027)
        ·
          refine ⟨30795478686279111684837041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20530319124186074456558027 30795478686279111684837041)
          ·
            refine ⟨23096609014709333763627781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30795478686279111684837041 23096609014709333763627781)
            ·
              refine ⟨4330614190258000080680209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23096609014709333763627781 4330614190258000080680209)
              ·
                refine ⟨3247960642693500060510157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4330614190258000080680209 3247960642693500060510157)
                ·
                  refine ⟨1217985241010062522691309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3247960642693500060510157 1217985241010062522691309)
                  ·
                    refine ⟨456744465378773446009241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1217985241010062522691309 456744465378773446009241)
                    ·
                      refine ⟨342558349034080084506931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 456744465378773446009241 342558349034080084506931)
                      ·
                        rfl

theorem cell23_667130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 3, 3, 2].length) (baseStart_667130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667130 prefixEnd_667130 := by exact prefixLift 667130
  have htrace : WordTrace (prefixWord ++ tailWord_667130) baseStart_667130 baseEnd_667130 := by
    simpa [prefixWord, tailWord_667130, baseEnd_667130] using wordTrace_append hprefix tailTrace_667130
  have hstable : (prefixWord ++ tailWord_667130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667130).length < 2 ^ (prefixWord ++ tailWord_667130).sum := by decide
  have hdescent : baseEnd_667130 < baseStart_667130 := by decide
  rcases family_descends (prefixWord ++ tailWord_667130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667147 : List Nat := [1, 1, 1, 1, 8, 1, 1, 1, 3, 3, 2]
def baseStart_667147 : Nat := 118140960795 + 667147 * 2 ^ 59
def prefixEnd_667147 : Nat := 4983230072969 + 3 ^ 40 * 667147 * 2
def baseEnd_667147 : Nat := 342567078205206517994353

theorem tailTrace_667147 : CollatzResearch.WordTrace tailWord_667147 prefixEnd_667147 342567078205206517994353 := by
  unfold tailWord_667147
  simp only [CollatzResearch.WordTrace]
  refine ⟨24332850114047833481511695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16221900076031888987674463 24332850114047833481511695)
  ·
    refine ⟨36499275171071750222267543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24332850114047833481511695 36499275171071750222267543)
    ·
      refine ⟨54748912756607625333401315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36499275171071750222267543 54748912756607625333401315)
      ·
        refine ⟨82123369134911438000101973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54748912756607625333401315 82123369134911438000101973)
        ·
          refine ⟨962383232049743414063695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 82123369134911438000101973 962383232049743414063695)
          ·
            refine ⟨1443574848074615121095543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 962383232049743414063695 1443574848074615121095543)
            ·
              refine ⟨2165362272111922681643315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1443574848074615121095543 2165362272111922681643315)
              ·
                refine ⟨3248043408167884022464973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2165362272111922681643315 3248043408167884022464973)
                ·
                  refine ⟨1218016278062956508424365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3248043408167884022464973 1218016278062956508424365)
                  ·
                    refine ⟨456756104273608690659137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1218016278062956508424365 456756104273608690659137)
                    ·
                      refine ⟨342567078205206517994353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 456756104273608690659137 342567078205206517994353)
                      ·
                        rfl

theorem cell23_667147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 3, 3, 2].length) (baseStart_667147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667147 prefixEnd_667147 := by exact prefixLift 667147
  have htrace : WordTrace (prefixWord ++ tailWord_667147) baseStart_667147 baseEnd_667147 := by
    simpa [prefixWord, tailWord_667147, baseEnd_667147] using wordTrace_append hprefix tailTrace_667147
  have hstable : (prefixWord ++ tailWord_667147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667147).length < 2 ^ (prefixWord ++ tailWord_667147).sum := by decide
  have hdescent : baseEnd_667147 < baseStart_667147 := by decide
  rcases family_descends (prefixWord ++ tailWord_667147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667164 : List Nat := [2, 2, 3, 1, 2, 1, 5, 1, 1, 3, 2]
def baseStart_667164 : Nat := 118140960795 + 667164 * 2 ^ 59
def prefixEnd_667164 : Nat := 4983230072969 + 3 ^ 40 * 667164 * 2
def baseEnd_667164 : Nat := 342575807376332951481775

theorem tailTrace_667164 : CollatzResearch.WordTrace tailWord_667164 prefixEnd_667164 342575807376332951481775 := by
  unfold tailWord_667164
  simp only [CollatzResearch.WordTrace]
  refine ⟨12166735077493122692440273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16222313436657496923253697 12166735077493122692440273)
  ·
    refine ⟨9125051308119842019330205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12166735077493122692440273 9125051308119842019330205)
    ·
      refine ⟨3421894240544940757248827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9125051308119842019330205 3421894240544940757248827)
      ·
        refine ⟨5132841360817411135873241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3421894240544940757248827 5132841360817411135873241)
        ·
          refine ⟨3849631020613058351904931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5132841360817411135873241 3849631020613058351904931)
          ·
            refine ⟨5774446530919587527857397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3849631020613058351904931 5774446530919587527857397)
            ·
              refine ⟨541354362273711330736631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5774446530919587527857397 541354362273711330736631)
              ·
                refine ⟨812031543410566996104947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 541354362273711330736631 812031543410566996104947)
                ·
                  refine ⟨1218047315115850494157421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 812031543410566996104947 1218047315115850494157421)
                  ·
                    refine ⟨456767743168443935309033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1218047315115850494157421 456767743168443935309033)
                    ·
                      refine ⟨342575807376332951481775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 456767743168443935309033 342575807376332951481775)
                      ·
                        rfl

theorem cell23_667164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 1, 1, 3, 2].length) (baseStart_667164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667164 prefixEnd_667164 := by exact prefixLift 667164
  have htrace : WordTrace (prefixWord ++ tailWord_667164) baseStart_667164 baseEnd_667164 := by
    simpa [prefixWord, tailWord_667164, baseEnd_667164] using wordTrace_append hprefix tailTrace_667164
  have hstable : (prefixWord ++ tailWord_667164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667164).length < 2 ^ (prefixWord ++ tailWord_667164).sum := by decide
  have hdescent : baseEnd_667164 < baseStart_667164 := by decide
  rcases family_descends (prefixWord ++ tailWord_667164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667173 : List Nat := [1, 3, 1, 2, 2, 1, 1, 4, 2, 2, 4]
def baseStart_667173 : Nat := 118140960795 + 667173 * 2 ^ 59
def prefixEnd_667173 : Nat := 4983230072969 + 3 ^ 40 * 667173 * 2
def baseEnd_667173 : Nat := 342580428702223416269233

theorem tailTrace_667173 : CollatzResearch.WordTrace tailWord_667173 prefixEnd_667173 342580428702223416269233 := by
  unfold tailWord_667173
  simp only [CollatzResearch.WordTrace]
  refine ⟨24333798411953639921958173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16222532274635759947972115 24333798411953639921958173)
  ·
    refine ⟨9125174404482614970734315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24333798411953639921958173 9125174404482614970734315)
    ·
      refine ⟨13687761606723922456101473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9125174404482614970734315 13687761606723922456101473)
      ·
        refine ⟨10265821205042941842076105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13687761606723922456101473 10265821205042941842076105)
        ·
          refine ⟨7699365903782206381557079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10265821205042941842076105 7699365903782206381557079)
          ·
            refine ⟨11549048855673309572335619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7699365903782206381557079 11549048855673309572335619)
            ·
              refine ⟨17323573283509964358503429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11549048855673309572335619 17323573283509964358503429)
              ·
                refine ⟨3248169990658118317219393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17323573283509964358503429 3248169990658118317219393)
                ·
                  refine ⟨2436127492993588737914545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3248169990658118317219393 2436127492993588737914545)
                  ·
                    refine ⟨1827095619745191553435909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2436127492993588737914545 1827095619745191553435909)
                    ·
                      refine ⟨342580428702223416269233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1827095619745191553435909 342580428702223416269233)
                      ·
                        rfl

theorem cell23_667173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_667173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667173 prefixEnd_667173 := by exact prefixLift 667173
  have htrace : WordTrace (prefixWord ++ tailWord_667173) baseStart_667173 baseEnd_667173 := by
    simpa [prefixWord, tailWord_667173, baseEnd_667173] using wordTrace_append hprefix tailTrace_667173
  have hstable : (prefixWord ++ tailWord_667173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667173).length < 2 ^ (prefixWord ++ tailWord_667173).sum := by decide
  have hdescent : baseEnd_667173 < baseStart_667173 := by decide
  rcases family_descends (prefixWord ++ tailWord_667173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667250 : List Nat := [3, 2, 1, 2, 3, 1, 1, 2, 1, 3, 4]
def baseStart_667250 : Nat := 118140960795 + 667250 * 2 ^ 59
def prefixEnd_667250 : Nat := 4983230072969 + 3 ^ 40 * 667250 * 2
def baseEnd_667250 : Nat := 342619966712619615006379

theorem tailTrace_667250 : CollatzResearch.WordTrace tailWord_667250 prefixEnd_667250 342619966712619615006379 := by
  unfold tailWord_667250
  simp only [CollatzResearch.WordTrace]
  refine ⟨6084151708168670518127801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16224404555116454715007469 6084151708168670518127801)
  ·
    refine ⟨4563113781126502888595851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6084151708168670518127801 4563113781126502888595851)
    ·
      refine ⟨6844670671689754332893777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4563113781126502888595851 6844670671689754332893777)
      ·
        refine ⟨5133503003767315749670333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6844670671689754332893777 5133503003767315749670333)
        ·
          refine ⟨1925063626412743406126375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5133503003767315749670333 1925063626412743406126375)
          ·
            refine ⟨2887595439619115109189563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1925063626412743406126375 2887595439619115109189563)
            ·
              refine ⟨4331393159428672663784345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2887595439619115109189563 4331393159428672663784345)
              ·
                refine ⟨3248544869571504497838259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4331393159428672663784345 3248544869571504497838259)
                ·
                  refine ⟨4872817304357256746757389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3248544869571504497838259 4872817304357256746757389)
                  ·
                    refine ⟨1827306489133971280034021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4872817304357256746757389 1827306489133971280034021)
                    ·
                      refine ⟨342619966712619615006379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1827306489133971280034021 342619966712619615006379)
                      ·
                        rfl

theorem cell23_667250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_667250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667250 prefixEnd_667250 := by exact prefixLift 667250
  have htrace : WordTrace (prefixWord ++ tailWord_667250) baseStart_667250 baseEnd_667250 := by
    simpa [prefixWord, tailWord_667250, baseEnd_667250] using wordTrace_append hprefix tailTrace_667250
  have hstable : (prefixWord ++ tailWord_667250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667250).length < 2 ^ (prefixWord ++ tailWord_667250).sum := by decide
  have hdescent : baseEnd_667250 < baseStart_667250 := by decide
  rcases family_descends (prefixWord ++ tailWord_667250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667273 : List Nat := [1, 2, 1, 1, 4, 1, 3, 2, 8]
def baseStart_667273 : Nat := 118140960795 + 667273 * 2 ^ 59
def prefixEnd_667273 : Nat := 4983230072969 + 3 ^ 40 * 667273 * 2
def baseEnd_667273 : Nat := 38070197418630336113197

theorem tailTrace_667273 : CollatzResearch.WordTrace tailWord_667273 prefixEnd_667273 38070197418630336113197 := by
  unfold tailWord_667273
  simp only [CollatzResearch.WordTrace]
  refine ⟨24337445711591357000598473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16224963807727571333732315 24337445711591357000598473)
  ·
    refine ⟨18253084283693517750448855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24337445711591357000598473 18253084283693517750448855)
    ·
      refine ⟨27379626425540276625673283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18253084283693517750448855 27379626425540276625673283)
      ·
        refine ⟨41069439638310414938509925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27379626425540276625673283 41069439638310414938509925)
        ·
          refine ⟨7700519932183202800970611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41069439638310414938509925 7700519932183202800970611)
          ·
            refine ⟨11550779898274804201455917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7700519932183202800970611 11550779898274804201455917)
            ·
              refine ⟨4331542461853051575545969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11550779898274804201455917 4331542461853051575545969)
              ·
                refine ⟨3248656846389788681659477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4331542461853051575545969 3248656846389788681659477)
                ·
                  refine ⟨38070197418630336113197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3248656846389788681659477 38070197418630336113197)
                  ·
                    rfl

theorem cell23_667273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 8].length) (baseStart_667273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667273 prefixEnd_667273 := by exact prefixLift 667273
  have htrace : WordTrace (prefixWord ++ tailWord_667273) baseStart_667273 baseEnd_667273 := by
    simpa [prefixWord, tailWord_667273, baseEnd_667273] using wordTrace_append hprefix tailTrace_667273
  have hstable : (prefixWord ++ tailWord_667273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667273).length < 2 ^ (prefixWord ++ tailWord_667273).sum := by decide
  have hdescent : baseEnd_667273 < baseStart_667273 := by decide
  rcases family_descends (prefixWord ++ tailWord_667273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667284 : List Nat := [2, 4, 2, 2, 2, 1, 1, 2, 2, 1, 4]
def baseStart_667284 : Nat := 118140960795 + 667284 * 2 ^ 59
def prefixEnd_667284 : Nat := 4983230072969 + 3 ^ 40 * 667284 * 2
def baseEnd_667284 : Nat := 342637425054872481981223

theorem tailTrace_667284 : CollatzResearch.WordTrace tailWord_667284 prefixEnd_667284 342637425054872481981223 := by
  unfold tailWord_667284
  simp only [CollatzResearch.WordTrace]
  refine ⟨12168923457275752939624453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16225231276367670586165937 12168923457275752939624453)
  ·
    refine ⟨2281673148239203676179585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12168923457275752939624453 2281673148239203676179585)
    ·
      refine ⟨1711254861179402757134689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2281673148239203676179585 1711254861179402757134689)
      ·
        refine ⟨1283441145884552067851017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1711254861179402757134689 1283441145884552067851017)
        ·
          refine ⟨962580859413414050888263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1283441145884552067851017 962580859413414050888263)
          ·
            refine ⟨1443871289120121076332395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 962580859413414050888263 1443871289120121076332395)
            ·
              refine ⟨2165806933680181614498593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1443871289120121076332395 2165806933680181614498593)
              ·
                refine ⟨1624355200260136210873945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2165806933680181614498593 1624355200260136210873945)
                ·
                  refine ⟨1218266400195102158155459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1624355200260136210873945 1218266400195102158155459)
                  ·
                    refine ⟨1827399600292653237233189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1218266400195102158155459 1827399600292653237233189)
                    ·
                      refine ⟨342637425054872481981223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1827399600292653237233189 342637425054872481981223)
                      ·
                        rfl

theorem cell23_667284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_667284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667284 prefixEnd_667284 := by exact prefixLift 667284
  have htrace : WordTrace (prefixWord ++ tailWord_667284) baseStart_667284 baseEnd_667284 := by
    simpa [prefixWord, tailWord_667284, baseEnd_667284] using wordTrace_append hprefix tailTrace_667284
  have hstable : (prefixWord ++ tailWord_667284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667284).length < 2 ^ (prefixWord ++ tailWord_667284).sum := by decide
  have hdescent : baseEnd_667284 < baseStart_667284 := by decide
  rcases family_descends (prefixWord ++ tailWord_667284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667287 : List Nat := [1, 1, 3, 3, 2, 3, 1, 2, 2, 2, 3]
def baseStart_667287 : Nat := 118140960795 + 667287 * 2 ^ 59
def prefixEnd_667287 : Nat := 4983230072969 + 3 ^ 40 * 667287 * 2
def baseEnd_667287 : Nat := 342638965496835970243709

theorem tailTrace_667287 : CollatzResearch.WordTrace tailWord_667287 prefixEnd_667287 342638965496835970243709 := by
  unfold tailWord_667287
  simp only [CollatzResearch.WordTrace]
  refine ⟨24337956333540637391608115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16225304222360424927738743 24337956333540637391608115)
  ·
    refine ⟨36506934500310956087412173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24337956333540637391608115 36506934500310956087412173)
    ·
      refine ⟨13690100437616608532779565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36506934500310956087412173 13690100437616608532779565)
      ·
        refine ⟨5133787664106228199792337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13690100437616608532779565 5133787664106228199792337)
        ·
          refine ⟨3850340748079671149844253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5133787664106228199792337 3850340748079671149844253)
          ·
            refine ⟨1443877780529876681191595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3850340748079671149844253 1443877780529876681191595)
            ·
              refine ⟨2165816670794815021787393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1443877780529876681191595 2165816670794815021787393)
              ·
                refine ⟨1624362503096111266340545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2165816670794815021787393 1624362503096111266340545)
                ·
                  refine ⟨1218271877322083449755409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1624362503096111266340545 1218271877322083449755409)
                  ·
                    refine ⟨913703907991562587316557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1218271877322083449755409 913703907991562587316557)
                    ·
                      refine ⟨342638965496835970243709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 913703907991562587316557 342638965496835970243709)
                      ·
                        rfl

theorem cell23_667287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_667287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667287 prefixEnd_667287 := by exact prefixLift 667287
  have htrace : WordTrace (prefixWord ++ tailWord_667287) baseStart_667287 baseEnd_667287 := by
    simpa [prefixWord, tailWord_667287, baseEnd_667287] using wordTrace_append hprefix tailTrace_667287
  have hstable : (prefixWord ++ tailWord_667287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667287).length < 2 ^ (prefixWord ++ tailWord_667287).sum := by decide
  have hdescent : baseEnd_667287 < baseStart_667287 := by decide
  rcases family_descends (prefixWord ++ tailWord_667287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667294 : List Nat := [4, 3, 1, 1, 1, 2, 3, 1, 3, 4]
def baseStart_667294 : Nat := 118140960795 + 667294 * 2 ^ 59
def prefixEnd_667294 : Nat := 4983230072969 + 3 ^ 40 * 667294 * 2
def baseEnd_667294 : Nat := 114214186620472480952059

theorem tailTrace_667294 : CollatzResearch.WordTrace tailWord_667294 prefixEnd_667294 114214186620472480952059 := by
  unfold tailWord_667294
  simp only [CollatzResearch.WordTrace]
  refine ⟨3042276455564409698389117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16225474429676851724741957 3042276455564409698389117)
  ·
    refine ⟨1140853670836653636895919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3042276455564409698389117 1140853670836653636895919)
    ·
      refine ⟨1711280506254980455343879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1140853670836653636895919 1711280506254980455343879)
      ·
        refine ⟨2566920759382470683015819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1711280506254980455343879 2566920759382470683015819)
        ·
          refine ⟨3850381139073706024523729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2566920759382470683015819 3850381139073706024523729)
          ·
            refine ⟨2887785854305279518392797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3850381139073706024523729 2887785854305279518392797)
            ·
              refine ⟨1082919695364479819397299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2887785854305279518392797 1082919695364479819397299)
              ·
                refine ⟨1624379543046719729095949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1082919695364479819397299 1624379543046719729095949)
                ·
                  refine ⟨609142328642519898410981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1624379543046719729095949 609142328642519898410981)
                  ·
                    refine ⟨114214186620472480952059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 609142328642519898410981 114214186620472480952059)
                    ·
                      rfl

theorem cell23_667294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_667294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667294 prefixEnd_667294 := by exact prefixLift 667294
  have htrace : WordTrace (prefixWord ++ tailWord_667294) baseStart_667294 baseEnd_667294 := by
    simpa [prefixWord, tailWord_667294, baseEnd_667294] using wordTrace_append hprefix tailTrace_667294
  have hstable : (prefixWord ++ tailWord_667294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667294).length < 2 ^ (prefixWord ++ tailWord_667294).sum := by decide
  have hdescent : baseEnd_667294 < baseStart_667294 := by decide
  rcases family_descends (prefixWord ++ tailWord_667294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667360 : List Nat := [2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 5]
def baseStart_667360 : Nat := 118140960795 + 667360 * 2 ^ 59
def prefixEnd_667360 : Nat := 4983230072969 + 3 ^ 40 * 667360 * 2
def baseEnd_667360 : Nat := 342676449584614184630873

theorem tailTrace_667360 : CollatzResearch.WordTrace tailWord_667360 prefixEnd_667360 342676449584614184630873 := by
  unfold tailWord_667360
  simp only [CollatzResearch.WordTrace]
  refine ⟨12170309431138085429507767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16227079241517447239343689 12170309431138085429507767)
  ·
    refine ⟨18255464146707128144261651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12170309431138085429507767 18255464146707128144261651)
    ·
      refine ⟨27383196220060692216392477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18255464146707128144261651 27383196220060692216392477)
      ·
        refine ⟨10268698582522759581147179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27383196220060692216392477 10268698582522759581147179)
        ·
          refine ⟨15403047873784139371720769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10268698582522759581147179 15403047873784139371720769)
          ·
            refine ⟨11552285905338104528790577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15403047873784139371720769 11552285905338104528790577)
            ·
              refine ⟨8664214429003578396592933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11552285905338104528790577 8664214429003578396592933)
              ·
                refine ⟨1624540205438170949361175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8664214429003578396592933 1624540205438170949361175)
                ·
                  refine ⟨2436810308157256424041763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1624540205438170949361175 2436810308157256424041763)
                  ·
                    refine ⟨3655215462235884636062645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2436810308157256424041763 3655215462235884636062645)
                    ·
                      refine ⟨342676449584614184630873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3655215462235884636062645 342676449584614184630873)
                      ·
                        rfl

theorem cell23_667360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_667360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667360 prefixEnd_667360 := by exact prefixLift 667360
  have htrace : WordTrace (prefixWord ++ tailWord_667360) baseStart_667360 baseEnd_667360 := by
    simpa [prefixWord, tailWord_667360, baseEnd_667360] using wordTrace_append hprefix tailTrace_667360
  have hstable : (prefixWord ++ tailWord_667360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667360).length < 2 ^ (prefixWord ++ tailWord_667360).sum := by decide
  have hdescent : baseEnd_667360 < baseStart_667360 := by decide
  rcases family_descends (prefixWord ++ tailWord_667360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667370 : List Nat := [3, 1, 3, 1, 1, 1, 2, 3, 1, 1, 6]
def baseStart_667370 : Nat := 118140960795 + 667370 * 2 ^ 59
def prefixEnd_667370 : Nat := 4983230072969 + 3 ^ 40 * 667370 * 2
def baseEnd_667370 : Nat := 342681584391159145505827

theorem tailTrace_667370 : CollatzResearch.WordTrace tailWord_667370 prefixEnd_667370 342681584391159145505827 := by
  unfold tailWord_667370
  simp only [CollatzResearch.WordTrace]
  refine ⟨6085245898059985641719891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16227322394826628377919709 6085245898059985641719891)
  ·
    refine ⟨9127868847089978462579837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6085245898059985641719891 9127868847089978462579837)
    ·
      refine ⟨3422950817658741923467439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9127868847089978462579837 3422950817658741923467439)
      ·
        refine ⟨5134426226488112885201159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3422950817658741923467439 5134426226488112885201159)
        ·
          refine ⟨7701639339732169327801739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5134426226488112885201159 7701639339732169327801739)
          ·
            refine ⟨11552459009598253991702609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7701639339732169327801739 11552459009598253991702609)
            ·
              refine ⟨8664344257198690493776957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11552459009598253991702609 8664344257198690493776957)
              ·
                refine ⟨3249129096449508935166359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8664344257198690493776957 3249129096449508935166359)
                ·
                  refine ⟨4873693644674263402749539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3249129096449508935166359 4873693644674263402749539)
                  ·
                    refine ⟨7310540467011395104124309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4873693644674263402749539 7310540467011395104124309)
                    ·
                      refine ⟨342681584391159145505827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7310540467011395104124309 342681584391159145505827)
                      ·
                        rfl

theorem cell23_667370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_667370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667370 prefixEnd_667370 := by exact prefixLift 667370
  have htrace : WordTrace (prefixWord ++ tailWord_667370) baseStart_667370 baseEnd_667370 := by
    simpa [prefixWord, tailWord_667370, baseEnd_667370] using wordTrace_append hprefix tailTrace_667370
  have hstable : (prefixWord ++ tailWord_667370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667370).length < 2 ^ (prefixWord ++ tailWord_667370).sum := by decide
  have hdescent : baseEnd_667370 < baseStart_667370 := by decide
  rcases family_descends (prefixWord ++ tailWord_667370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667377 : List Nat := [1, 2, 2, 2, 2, 3, 2, 1, 3, 2, 3]
def baseStart_667377 : Nat := 118140960795 + 667377 * 2 ^ 59
def prefixEnd_667377 : Nat := 4983230072969 + 3 ^ 40 * 667377 * 2
def baseEnd_667377 : Nat := 342685178755740618118295

theorem tailTrace_667377 : CollatzResearch.WordTrace tailWord_667377 prefixEnd_667377 342685178755740618118295 := by
  unfold tailWord_667377
  simp only [CollatzResearch.WordTrace]
  refine ⟨24341238903214582762384385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16227492602143055174922923 24341238903214582762384385)
  ·
    refine ⟨18255929177410937071788289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24341238903214582762384385 18255929177410937071788289)
    ·
      refine ⟨13691946883058202803841217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18255929177410937071788289 13691946883058202803841217)
      ·
        refine ⟨10268960162293652102880913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13691946883058202803841217 10268960162293652102880913)
        ·
          refine ⟨7701720121720239077160685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10268960162293652102880913 7701720121720239077160685)
          ·
            refine ⟨2888145045645089653935257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7701720121720239077160685 2888145045645089653935257)
            ·
              refine ⟨2166108784233817240451443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2888145045645089653935257 2166108784233817240451443)
              ·
                refine ⟨3249163176350725860677165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2166108784233817240451443 3249163176350725860677165)
                ·
                  refine ⟨1218436191131522197753937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3249163176350725860677165 1218436191131522197753937)
                  ·
                    refine ⟨913827143348641648315453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1218436191131522197753937 913827143348641648315453)
                    ·
                      refine ⟨342685178755740618118295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 913827143348641648315453 342685178755740618118295)
                      ·
                        rfl

theorem cell23_667377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 3, 2, 3].length) (baseStart_667377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667377 prefixEnd_667377 := by exact prefixLift 667377
  have htrace : WordTrace (prefixWord ++ tailWord_667377) baseStart_667377 baseEnd_667377 := by
    simpa [prefixWord, tailWord_667377, baseEnd_667377] using wordTrace_append hprefix tailTrace_667377
  have hstable : (prefixWord ++ tailWord_667377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667377).length < 2 ^ (prefixWord ++ tailWord_667377).sum := by decide
  have hdescent : baseEnd_667377 < baseStart_667377 := by decide
  rcases family_descends (prefixWord ++ tailWord_667377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667391 : List Nat := [1, 1, 2, 2, 1, 3, 3, 5, 1, 2, 2]
def baseStart_667391 : Nat := 118140960795 + 667391 * 2 ^ 59
def prefixEnd_667391 : Nat := 4983230072969 + 3 ^ 40 * 667391 * 2
def baseEnd_667391 : Nat := 342692367484903563343231

theorem tailTrace_667391 : CollatzResearch.WordTrace tailWord_667391 prefixEnd_667391 342692367484903563343231 := by
  unfold tailWord_667391
  simp only [CollatzResearch.WordTrace]
  refine ⟨24341749525163863153394027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16227833016775908768929351 24341749525163863153394027)
  ·
    refine ⟨36512624287745794730091041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24341749525163863153394027 36512624287745794730091041)
    ·
      refine ⟨27384468215809346047568281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36512624287745794730091041 27384468215809346047568281)
      ·
        refine ⟨20538351161857009535676211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27384468215809346047568281 20538351161857009535676211)
        ·
          refine ⟨30807526742785514303514317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20538351161857009535676211 30807526742785514303514317)
          ·
            refine ⟨11552822528544567863817869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30807526742785514303514317 11552822528544567863817869)
            ·
              refine ⟨4332308448204212948931701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11552822528544567863817869 4332308448204212948931701)
              ·
                refine ⟨406153917019144963962347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4332308448204212948931701 406153917019144963962347)
                ·
                  refine ⟨609230875528717445943521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 406153917019144963962347 609230875528717445943521)
                  ·
                    refine ⟨456923156646538084457641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 609230875528717445943521 456923156646538084457641)
                    ·
                      refine ⟨342692367484903563343231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 456923156646538084457641 342692367484903563343231)
                      ·
                        rfl

theorem cell23_667391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 5, 1, 2, 2].length) (baseStart_667391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667391 prefixEnd_667391 := by exact prefixLift 667391
  have htrace : WordTrace (prefixWord ++ tailWord_667391) baseStart_667391 baseEnd_667391 := by
    simpa [prefixWord, tailWord_667391, baseEnd_667391] using wordTrace_append hprefix tailTrace_667391
  have hstable : (prefixWord ++ tailWord_667391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667391).length < 2 ^ (prefixWord ++ tailWord_667391).sum := by decide
  have hdescent : baseEnd_667391 < baseStart_667391 := by decide
  rcases family_descends (prefixWord ++ tailWord_667391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667481 : List Nat := [1, 2, 1, 2, 2, 3, 3, 3, 2, 2, 2]
def baseStart_667481 : Nat := 118140960795 + 667481 * 2 ^ 59
def prefixEnd_667481 : Nat := 4983230072969 + 3 ^ 40 * 667481 * 2
def baseEnd_667481 : Nat := 342738580743808211217817

theorem tailTrace_667481 : CollatzResearch.WordTrace tailWord_667481 prefixEnd_667481 342738580743808211217817 := by
  unfold tailWord_667481
  simp only [CollatzResearch.WordTrace]
  refine ⟨24345032094837808524170297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16230021396558539016113531 24345032094837808524170297)
  ·
    refine ⟨18258774071128356393127723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24345032094837808524170297 18258774071128356393127723)
    ·
      refine ⟨27388161106692534589691585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18258774071128356393127723 27388161106692534589691585)
      ·
        refine ⟨20541120830019400942268689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27388161106692534589691585 20541120830019400942268689)
        ·
          refine ⟨15405840622514550706701517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20541120830019400942268689 15405840622514550706701517)
          ·
            refine ⟨5777190233442956515013069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15405840622514550706701517 5777190233442956515013069)
            ·
              refine ⟨2166446337541108693129901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5777190233442956515013069 2166446337541108693129901)
              ·
                refine ⟨812417376577915759923713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2166446337541108693129901 812417376577915759923713)
                ·
                  refine ⟨609313032433436819942785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 812417376577915759923713 609313032433436819942785)
                  ·
                    refine ⟨456984774325077614957089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 609313032433436819942785 456984774325077614957089)
                    ·
                      refine ⟨342738580743808211217817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 456984774325077614957089 342738580743808211217817)
                      ·
                        rfl

theorem cell23_667481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 3, 2, 2, 2].length) (baseStart_667481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667481 prefixEnd_667481 := by exact prefixLift 667481
  have htrace : WordTrace (prefixWord ++ tailWord_667481) baseStart_667481 baseEnd_667481 := by
    simpa [prefixWord, tailWord_667481, baseEnd_667481] using wordTrace_append hprefix tailTrace_667481
  have hstable : (prefixWord ++ tailWord_667481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667481).length < 2 ^ (prefixWord ++ tailWord_667481).sum := by decide
  have hdescent : baseEnd_667481 < baseStart_667481 := by decide
  rcases family_descends (prefixWord ++ tailWord_667481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667498 : List Nat := [3, 1, 3, 4, 1, 1, 1, 2, 1, 4, 2]
def baseStart_667498 : Nat := 118140960795 + 667498 * 2 ^ 59
def prefixEnd_667498 : Nat := 4983230072969 + 3 ^ 40 * 667498 * 2
def baseEnd_667498 : Nat := 342747309914934644705239

theorem tailTrace_667498 : CollatzResearch.WordTrace tailWord_667498 prefixEnd_667498 342747309914934644705239 := by
  unfold tailWord_667498
  simp only [CollatzResearch.WordTrace]
  refine ⟨6086413033944055106884787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16230434757184146951692765 6086413033944055106884787)
  ·
    refine ⟨9129619550916082660327181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6086413033944055106884787 9129619550916082660327181)
    ·
      refine ⟨3423607331593530997622693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9129619550916082660327181 3423607331593530997622693)
      ·
        refine ⟨641926374673787062054255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3423607331593530997622693 641926374673787062054255)
        ·
          refine ⟨962889562010680593081383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 641926374673787062054255 962889562010680593081383)
          ·
            refine ⟨1444334343016020889622075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 962889562010680593081383 1444334343016020889622075)
            ·
              refine ⟨2166501514524031334433113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1444334343016020889622075 2166501514524031334433113)
              ·
                refine ⟨1624876135893023500824835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2166501514524031334433113 1624876135893023500824835)
                ·
                  refine ⟨2437314203839535251237253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1624876135893023500824835 2437314203839535251237253)
                  ·
                    refine ⟨456996413219912859606985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2437314203839535251237253 456996413219912859606985)
                    ·
                      refine ⟨342747309914934644705239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 456996413219912859606985 342747309914934644705239)
                      ·
                        rfl

theorem cell23_667498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_667498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667498 prefixEnd_667498 := by exact prefixLift 667498
  have htrace : WordTrace (prefixWord ++ tailWord_667498) baseStart_667498 baseEnd_667498 := by
    simpa [prefixWord, tailWord_667498, baseEnd_667498] using wordTrace_append hprefix tailTrace_667498
  have hstable : (prefixWord ++ tailWord_667498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667498).length < 2 ^ (prefixWord ++ tailWord_667498).sum := by decide
  have hdescent : baseEnd_667498 < baseStart_667498 := by decide
  rcases family_descends (prefixWord ++ tailWord_667498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667524 : List Nat := [2, 3, 2, 1, 1, 1, 3, 1, 2, 5, 2]
def baseStart_667524 : Nat := 118140960795 + 667524 * 2 ^ 59
def prefixEnd_667524 : Nat := 4983230072969 + 3 ^ 40 * 667524 * 2
def baseEnd_667524 : Nat := 342760660411951542980119

theorem tailTrace_667524 : CollatzResearch.WordTrace tailWord_667524 prefixEnd_667524 342760660411951542980119 := by
  unfold tailWord_667524
  simp only [CollatzResearch.WordTrace]
  refine ⟨12173300216841013433992813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16231066955788017911990417 12173300216841013433992813)
  ·
    refine ⟨4564987581315380037747305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12173300216841013433992813 4564987581315380037747305)
    ·
      refine ⟨3423740685986535028310479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4564987581315380037747305 3423740685986535028310479)
      ·
        refine ⟨5135611028979802542465719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3423740685986535028310479 5135611028979802542465719)
        ·
          refine ⟨7703416543469703813698579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5135611028979802542465719 7703416543469703813698579)
          ·
            refine ⟨11555124815204555720547869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7703416543469703813698579 11555124815204555720547869)
            ·
              refine ⟨4333171805701708395205451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11555124815204555720547869 4333171805701708395205451)
              ·
                refine ⟨6499757708552562592808177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4333171805701708395205451 6499757708552562592808177)
                ·
                  refine ⟨4874818281414421944606133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6499757708552562592808177 4874818281414421944606133)
                  ·
                    refine ⟨457014213882602057306825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4874818281414421944606133 457014213882602057306825)
                    ·
                      refine ⟨342760660411951542980119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 457014213882602057306825 342760660411951542980119)
                      ·
                        rfl

theorem cell23_667524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 2, 5, 2].length) (baseStart_667524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667524 prefixEnd_667524 := by exact prefixLift 667524
  have htrace : WordTrace (prefixWord ++ tailWord_667524) baseStart_667524 baseEnd_667524 := by
    simpa [prefixWord, tailWord_667524, baseEnd_667524] using wordTrace_append hprefix tailTrace_667524
  have hstable : (prefixWord ++ tailWord_667524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667524).length < 2 ^ (prefixWord ++ tailWord_667524).sum := by decide
  have hdescent : baseEnd_667524 < baseStart_667524 := by decide
  rcases family_descends (prefixWord ++ tailWord_667524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667537 : List Nat := [1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 4]
def baseStart_667537 : Nat := 118140960795 + 667537 * 2 ^ 59
def prefixEnd_667537 : Nat := 4983230072969 + 3 ^ 40 * 667537 * 2
def baseEnd_667537 : Nat := 342767335660459992117559

theorem tailTrace_667537 : CollatzResearch.WordTrace tailWord_667537 prefixEnd_667537 342767335660459992117559 := by
  unfold tailWord_667537
  simp only [CollatzResearch.WordTrace]
  refine ⟨24347074582634930088208865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16231383055089953392139243 24347074582634930088208865)
  ·
    refine ⟨18260305936976197566156649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24347074582634930088208865 18260305936976197566156649)
    ·
      refine ⟨13695229452732148174617487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18260305936976197566156649 13695229452732148174617487)
      ·
        refine ⟨20542844179098222261926231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13695229452732148174617487 20542844179098222261926231)
        ·
          refine ⟨30814266268647333392889347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20542844179098222261926231 30814266268647333392889347)
          ·
            refine ⟨46221399402971000089334021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30814266268647333392889347 46221399402971000089334021)
            ·
              refine ⟨8666512388057062516750129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46221399402971000089334021 8666512388057062516750129)
              ·
                refine ⟨6499884291042796887562597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8666512388057062516750129 6499884291042796887562597)
                ·
                  refine ⟨1218728304570524416417987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6499884291042796887562597 1218728304570524416417987)
                  ·
                    refine ⟨1828092456855786624626981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1218728304570524416417987 1828092456855786624626981)
                    ·
                      refine ⟨342767335660459992117559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1828092456855786624626981 342767335660459992117559)
                      ·
                        rfl

theorem cell23_667537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 4].length) (baseStart_667537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667537 prefixEnd_667537 := by exact prefixLift 667537
  have htrace : WordTrace (prefixWord ++ tailWord_667537) baseStart_667537 baseEnd_667537 := by
    simpa [prefixWord, tailWord_667537, baseEnd_667537] using wordTrace_append hprefix tailTrace_667537
  have hstable : (prefixWord ++ tailWord_667537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667537).length < 2 ^ (prefixWord ++ tailWord_667537).sum := by decide
  have hdescent : baseEnd_667537 < baseStart_667537 := by decide
  rcases family_descends (prefixWord ++ tailWord_667537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667551 : List Nat := [1, 1, 2, 5, 3, 2, 1, 1, 2, 5]
def baseStart_667551 : Nat := 118140960795 + 667551 * 2 ^ 59
def prefixEnd_667551 : Nat := 4983230072969 + 3 ^ 40 * 667551 * 2
def baseEnd_667551 : Nat := 114258174796540979114165

theorem tailTrace_667551 : CollatzResearch.WordTrace tailWord_667551 prefixEnd_667551 114258174796540979114165 := by
  unfold tailWord_667551
  simp only [CollatzResearch.WordTrace]
  refine ⟨24347585204584210479218507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16231723469722806986145671 24347585204584210479218507)
  ·
    refine ⟨36521377806876315718827761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24347585204584210479218507 36521377806876315718827761)
    ·
      refine ⟨27391033355157236789120821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36521377806876315718827761 27391033355157236789120821)
      ·
        refine ⟨2567909377045990948980077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27391033355157236789120821 2567909377045990948980077)
        ·
          refine ⟨962966016392246605867529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2567909377045990948980077 962966016392246605867529)
          ·
            refine ⟨722224512294184954400647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 962966016392246605867529 722224512294184954400647)
            ·
              refine ⟨1083336768441277431600971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 722224512294184954400647 1083336768441277431600971)
              ·
                refine ⟨1625005152661916147401457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1083336768441277431600971 1625005152661916147401457)
                ·
                  refine ⟨1218753864496437110551093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1625005152661916147401457 1218753864496437110551093)
                  ·
                    refine ⟨114258174796540979114165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1218753864496437110551093 114258174796540979114165)
                    ·
                      rfl

theorem cell23_667551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 2, 5].length) (baseStart_667551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667551 prefixEnd_667551 := by exact prefixLift 667551
  have htrace : WordTrace (prefixWord ++ tailWord_667551) baseStart_667551 baseEnd_667551 := by
    simpa [prefixWord, tailWord_667551, baseEnd_667551] using wordTrace_append hprefix tailTrace_667551
  have hstable : (prefixWord ++ tailWord_667551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667551).length < 2 ^ (prefixWord ++ tailWord_667551).sum := by decide
  have hdescent : baseEnd_667551 < baseStart_667551 := by decide
  rcases family_descends (prefixWord ++ tailWord_667551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667566 : List Nat := [4, 1, 5, 1, 2, 1, 1, 2, 2, 2, 2]
def baseStart_667566 : Nat := 118140960795 + 667566 * 2 ^ 59
def prefixEnd_667566 : Nat := 4983230072969 + 3 ^ 40 * 667566 * 2
def baseEnd_667566 : Nat := 342782226599440378654927

theorem tailTrace_667566 : CollatzResearch.WordTrace tailWord_667566 prefixEnd_667566 342782226599440378654927 := by
  unfold tailWord_667566
  simp only [CollatzResearch.WordTrace]
  refine ⟨3043516537441233505126819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16232088199686578694009701 3043516537441233505126819)
  ·
    refine ⟨4565274806161850257690229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3043516537441233505126819 4565274806161850257690229)
    ·
      refine ⟨427994513077673461658459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4565274806161850257690229 427994513077673461658459)
      ·
        refine ⟨641991769616510192487689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 427994513077673461658459 641991769616510192487689)
        ·
          refine ⟨481493827212382644365767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 641991769616510192487689 481493827212382644365767)
          ·
            refine ⟨722240740818573966548651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 481493827212382644365767 722240740818573966548651)
            ·
              refine ⟨1083361111227860949822977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 722240740818573966548651 1083361111227860949822977)
              ·
                refine ⟨812520833420895712367233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1083361111227860949822977 812520833420895712367233)
                ·
                  refine ⟨609390625065671784275425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 812520833420895712367233 609390625065671784275425)
                  ·
                    refine ⟨457042968799253838206569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 609390625065671784275425 457042968799253838206569)
                    ·
                      refine ⟨342782226599440378654927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 457042968799253838206569 342782226599440378654927)
                      ·
                        rfl

theorem cell23_667566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_667566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667566 prefixEnd_667566 := by exact prefixLift 667566
  have htrace : WordTrace (prefixWord ++ tailWord_667566) baseStart_667566 baseEnd_667566 := by
    simpa [prefixWord, tailWord_667566, baseEnd_667566] using wordTrace_append hprefix tailTrace_667566
  have hstable : (prefixWord ++ tailWord_667566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667566).length < 2 ^ (prefixWord ++ tailWord_667566).sum := by decide
  have hdescent : baseEnd_667566 < baseStart_667566 := by decide
  rcases family_descends (prefixWord ++ tailWord_667566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667577 : List Nat := [1, 2, 1, 4, 2, 1, 3, 1, 8]
def baseStart_667577 : Nat := 118140960795 + 667577 * 2 ^ 59
def prefixEnd_667577 : Nat := 4983230072969 + 3 ^ 40 * 667577 * 2
def baseEnd_667577 : Nat := 38087541654071092846375

theorem tailTrace_667577 : CollatzResearch.WordTrace tailWord_667577 prefixEnd_667577 38087541654071092846375 := by
  unfold tailWord_667577
  simp only [CollatzResearch.WordTrace]
  refine ⟨24348533502490016919664985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16232355668326677946443323 24348533502490016919664985)
  ·
    refine ⟨18261400126867512689748739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24348533502490016919664985 18261400126867512689748739)
    ·
      refine ⟨27392100190301269034623109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18261400126867512689748739 27392100190301269034623109)
      ·
        refine ⟨5136018785681487943991833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27392100190301269034623109 5136018785681487943991833)
        ·
          refine ⟨3852014089261115957993875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5136018785681487943991833 3852014089261115957993875)
          ·
            refine ⟨5778021133891673936990813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3852014089261115957993875 5778021133891673936990813)
            ·
              refine ⟨2166757925209377726371555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5778021133891673936990813 2166757925209377726371555)
              ·
                refine ⟨3250136887814066589557333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2166757925209377726371555 3250136887814066589557333)
                ·
                  refine ⟨38087541654071092846375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3250136887814066589557333 38087541654071092846375)
                  ·
                    rfl

theorem cell23_667577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 8].length) (baseStart_667577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667577 prefixEnd_667577 := by exact prefixLift 667577
  have htrace : WordTrace (prefixWord ++ tailWord_667577) baseStart_667577 baseEnd_667577 := by
    simpa [prefixWord, tailWord_667577, baseEnd_667577] using wordTrace_append hprefix tailTrace_667577
  have hstable : (prefixWord ++ tailWord_667577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667577).length < 2 ^ (prefixWord ++ tailWord_667577).sum := by decide
  have hdescent : baseEnd_667577 < baseStart_667577 := by decide
  rcases family_descends (prefixWord ++ tailWord_667577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667581 : List Nat := [1, 4, 1, 2, 3, 2, 2, 1, 3, 4]
def baseStart_667581 : Nat := 118140960795 + 667581 * 2 ^ 59
def prefixEnd_667581 : Nat := 4983230072969 + 3 ^ 40 * 667581 * 2
def baseEnd_667581 : Nat := 114263309603085939989119

theorem tailTrace_667581 : CollatzResearch.WordTrace tailWord_667581 prefixEnd_667581 114263309603085939989119 := by
  unfold tailWord_667581
  simp only [CollatzResearch.WordTrace]
  refine ⟨24348679394475525602810597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16232452929650350401873731 24348679394475525602810597)
  ·
    refine ⟨4565377386464161050526987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24348679394475525602810597 4565377386464161050526987)
    ·
      refine ⟨6848066079696241575790481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4565377386464161050526987 6848066079696241575790481)
      ·
        refine ⟨5136049559772181181842861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6848066079696241575790481 5136049559772181181842861)
        ·
          refine ⟨1926018584914567943191073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5136049559772181181842861 1926018584914567943191073)
          ·
            refine ⟨1444513938685925957393305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1926018584914567943191073 1444513938685925957393305)
            ·
              refine ⟨1083385454014444468044979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1444513938685925957393305 1083385454014444468044979)
              ·
                refine ⟨1625078181021666702067469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1083385454014444468044979 1625078181021666702067469)
                ·
                  refine ⟨609404317883125013275301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1625078181021666702067469 609404317883125013275301)
                  ·
                    refine ⟨114263309603085939989119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 609404317883125013275301 114263309603085939989119)
                    ·
                      rfl

theorem cell23_667581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 3, 4].length) (baseStart_667581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667581 prefixEnd_667581 := by exact prefixLift 667581
  have htrace : WordTrace (prefixWord ++ tailWord_667581) baseStart_667581 baseEnd_667581 := by
    simpa [prefixWord, tailWord_667581, baseEnd_667581] using wordTrace_append hprefix tailTrace_667581
  have hstable : (prefixWord ++ tailWord_667581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667581).length < 2 ^ (prefixWord ++ tailWord_667581).sum := by decide
  have hdescent : baseEnd_667581 < baseStart_667581 := by decide
  rcases family_descends (prefixWord ++ tailWord_667581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667587 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 4, 5, 3]
def baseStart_667587 : Nat := 118140960795 + 667587 * 2 ^ 59
def prefixEnd_667587 : Nat := 4983230072969 + 3 ^ 40 * 667587 * 2
def baseEnd_667587 : Nat := 342793009693184796492329

theorem tailTrace_667587 : CollatzResearch.WordTrace tailWord_667587 prefixEnd_667587 342793009693184796492329 := by
  unfold tailWord_667587
  simp only [CollatzResearch.WordTrace]
  refine ⟨24348898232453788627529015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16232598821635859085019343 24348898232453788627529015)
  ·
    refine ⟨36523347348680682941293523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24348898232453788627529015 36523347348680682941293523)
    ·
      refine ⟨54785021023021024411940285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36523347348680682941293523 54785021023021024411940285)
      ·
        refine ⟨20544382883632884154477607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54785021023021024411940285 20544382883632884154477607)
        ·
          refine ⟨30816574325449326231716411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20544382883632884154477607 30816574325449326231716411)
          ·
            refine ⟨46224861488173989347574617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30816574325449326231716411 46224861488173989347574617)
            ·
              refine ⟨34668646116130492010680963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46224861488173989347574617 34668646116130492010680963)
              ·
                refine ⟨52002969174195738016021445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34668646116130492010680963 52002969174195738016021445)
                ·
                  refine ⟨9750556720161700878004021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52002969174195738016021445 9750556720161700878004021)
                  ·
                    refine ⟨914114692515159457312877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9750556720161700878004021 914114692515159457312877)
                    ·
                      refine ⟨342793009693184796492329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 914114692515159457312877 342793009693184796492329)
                      ·
                        rfl

theorem cell23_667587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 5, 3].length) (baseStart_667587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667587 prefixEnd_667587 := by exact prefixLift 667587
  have htrace : WordTrace (prefixWord ++ tailWord_667587) baseStart_667587 baseEnd_667587 := by
    simpa [prefixWord, tailWord_667587, baseEnd_667587] using wordTrace_append hprefix tailTrace_667587
  have hstable : (prefixWord ++ tailWord_667587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667587).length < 2 ^ (prefixWord ++ tailWord_667587).sum := by decide
  have hdescent : baseEnd_667587 < baseStart_667587 := by decide
  rcases family_descends (prefixWord ++ tailWord_667587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667604 : List Nat := [2, 4, 1, 2, 1, 1, 1, 1, 2, 5, 3]
def baseStart_667604 : Nat := 118140960795 + 667604 * 2 ^ 59
def prefixEnd_667604 : Nat := 4983230072969 + 3 ^ 40 * 667604 * 2
def baseEnd_667604 : Nat := 342801738864311229979751

theorem tailTrace_667604 : CollatzResearch.WordTrace tailWord_667604 prefixEnd_667604 342801738864311229979751 := by
  unfold tailWord_667604
  simp only [CollatzResearch.WordTrace]
  refine ⟨12174759136696100265448933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16233012182261467020598577 12174759136696100265448933)
  ·
    refine ⟨2282767338130518799771675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12174759136696100265448933 2282767338130518799771675)
    ·
      refine ⟨3424151007195778199657513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2282767338130518799771675 3424151007195778199657513)
      ·
        refine ⟨2568113255396833649743135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3424151007195778199657513 2568113255396833649743135)
        ·
          refine ⟨3852169883095250474614703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2568113255396833649743135 3852169883095250474614703)
          ·
            refine ⟨5778254824642875711922055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3852169883095250474614703 5778254824642875711922055)
            ·
              refine ⟨8667382236964313567883083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5778254824642875711922055 8667382236964313567883083)
              ·
                refine ⟨13001073355446470351824625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8667382236964313567883083 13001073355446470351824625)
                ·
                  refine ⟨9750805016584852763868469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13001073355446470351824625 9750805016584852763868469)
                  ·
                    refine ⟨914137970304829946612669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9750805016584852763868469 914137970304829946612669)
                    ·
                      refine ⟨342801738864311229979751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 914137970304829946612669 342801738864311229979751)
                      ·
                        rfl

theorem cell23_667604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_667604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667604 prefixEnd_667604 := by exact prefixLift 667604
  have htrace : WordTrace (prefixWord ++ tailWord_667604) baseStart_667604 baseEnd_667604 := by
    simpa [prefixWord, tailWord_667604, baseEnd_667604] using wordTrace_append hprefix tailTrace_667604
  have hstable : (prefixWord ++ tailWord_667604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667604).length < 2 ^ (prefixWord ++ tailWord_667604).sum := by decide
  have hdescent : baseEnd_667604 < baseStart_667604 := by decide
  rcases family_descends (prefixWord ++ tailWord_667604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667631 : List Nat := [1, 1, 2, 1, 4, 2, 3, 2, 2, 3, 2]
def baseStart_667631 : Nat := 118140960795 + 667631 * 2 ^ 59
def prefixEnd_667631 : Nat := 4983230072969 + 3 ^ 40 * 667631 * 2
def baseEnd_667631 : Nat := 342815602841982624342127

theorem tailTrace_667631 : CollatzResearch.WordTrace tailWord_667631 prefixEnd_667631 342815602841982624342127 := by
  unfold tailWord_667631
  simp only [CollatzResearch.WordTrace]
  refine ⟨24350503044294384142130747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16233668696196256094753831 24350503044294384142130747)
  ·
    refine ⟨36525754566441576213196121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24350503044294384142130747 36525754566441576213196121)
    ·
      refine ⟨27394315924831182159897091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36525754566441576213196121 27394315924831182159897091)
      ·
        refine ⟨41091473887246773239845637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27394315924831182159897091 41091473887246773239845637)
        ·
          refine ⟨7704651353858769982471057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41091473887246773239845637 7704651353858769982471057)
          ·
            refine ⟨5778488515394077486853293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7704651353858769982471057 5778488515394077486853293)
            ·
              refine ⟨2166933193272779057569985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5778488515394077486853293 2166933193272779057569985)
              ·
                refine ⟨1625199894954584293177489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2166933193272779057569985 1625199894954584293177489)
                ·
                  refine ⟨1218899921215938219883117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1625199894954584293177489 1218899921215938219883117)
                  ·
                    refine ⟨457087470455976832456169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1218899921215938219883117 457087470455976832456169)
                    ·
                      refine ⟨342815602841982624342127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 457087470455976832456169 342815602841982624342127)
                      ·
                        rfl

theorem cell23_667631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 2, 3, 2].length) (baseStart_667631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667631 prefixEnd_667631 := by exact prefixLift 667631
  have htrace : WordTrace (prefixWord ++ tailWord_667631) baseStart_667631 baseEnd_667631 := by
    simpa [prefixWord, tailWord_667631, baseEnd_667631] using wordTrace_append hprefix tailTrace_667631
  have hstable : (prefixWord ++ tailWord_667631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667631).length < 2 ^ (prefixWord ++ tailWord_667631).sum := by decide
  have hdescent : baseEnd_667631 < baseStart_667631 := by decide
  rcases family_descends (prefixWord ++ tailWord_667631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667644 : List Nat := [2, 2, 2, 1, 2, 2, 2, 2, 3, 1, 4]
def baseStart_667644 : Nat := 118140960795 + 667644 * 2 ^ 59
def prefixEnd_667644 : Nat := 4983230072969 + 3 ^ 40 * 667644 * 2
def baseEnd_667644 : Nat := 342822278090491073479567

theorem tailTrace_667644 : CollatzResearch.WordTrace tailWord_667644 prefixEnd_667644 342822278090491073479567 := by
  unfold tailWord_667644
  simp only [CollatzResearch.WordTrace]
  refine ⟨12175488596623643681176993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16233984795498191574902657 12175488596623643681176993)
  ·
    refine ⟨9131616447467732760882745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12175488596623643681176993 9131616447467732760882745)
    ·
      refine ⟨6848712335600799570662059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9131616447467732760882745 6848712335600799570662059)
      ·
        refine ⟨10273068503401199355993089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6848712335600799570662059 10273068503401199355993089)
        ·
          refine ⟨7704801377550899516994817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10273068503401199355993089 7704801377550899516994817)
          ·
            refine ⟨5778601033163174637746113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7704801377550899516994817 5778601033163174637746113)
            ·
              refine ⟨4333950774872380978309585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5778601033163174637746113 4333950774872380978309585)
              ·
                refine ⟨3250463081154285733732189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4333950774872380978309585 3250463081154285733732189)
                ·
                  refine ⟨1218923655432857150149571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3250463081154285733732189 1218923655432857150149571)
                  ·
                    refine ⟨1828385483149285725224357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1218923655432857150149571 1828385483149285725224357)
                    ·
                      refine ⟨342822278090491073479567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1828385483149285725224357 342822278090491073479567)
                      ·
                        rfl

theorem cell23_667644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_667644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667644 prefixEnd_667644 := by exact prefixLift 667644
  have htrace : WordTrace (prefixWord ++ tailWord_667644) baseStart_667644 baseEnd_667644 := by
    simpa [prefixWord, tailWord_667644, baseEnd_667644] using wordTrace_append hprefix tailTrace_667644
  have hstable : (prefixWord ++ tailWord_667644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667644).length < 2 ^ (prefixWord ++ tailWord_667644).sum := by decide
  have hdescent : baseEnd_667644 < baseStart_667644 := by decide
  rcases family_descends (prefixWord ++ tailWord_667644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667658 : List Nat := [3, 1, 2, 2, 4, 2, 1, 2, 1, 5]
def baseStart_667658 : Nat := 118140960795 + 667658 * 2 ^ 59
def prefixEnd_667658 : Nat := 4983230072969 + 3 ^ 40 * 667658 * 2
def baseEnd_667658 : Nat := 114276488939884672901501

theorem tailTrace_667658 : CollatzResearch.WordTrace tailWord_667658 prefixEnd_667658 114276488939884672901501 := by
  unfold tailWord_667658
  simp only [CollatzResearch.WordTrace]
  refine ⟨6087871953799141938340907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16234325210131045168909085 6087871953799141938340907)
  ·
    refine ⟨9131807930698712907511361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6087871953799141938340907 9131807930698712907511361)
    ·
      refine ⟨6848855948024034680633521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9131807930698712907511361 6848855948024034680633521)
      ·
        refine ⟨5136641961018026010475141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6848855948024034680633521 5136641961018026010475141)
        ·
          refine ⟨963120367690879876964089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5136641961018026010475141 963120367690879876964089)
          ·
            refine ⟨722340275768159907723067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 963120367690879876964089 722340275768159907723067)
            ·
              refine ⟨1083510413652239861584601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 722340275768159907723067 1083510413652239861584601)
              ·
                refine ⟨812632810239179896188451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1083510413652239861584601 812632810239179896188451)
                ·
                  refine ⟨1218949215358769844282677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 812632810239179896188451 1218949215358769844282677)
                  ·
                    refine ⟨114276488939884672901501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1218949215358769844282677 114276488939884672901501)
                    ·
                      rfl

theorem cell23_667658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 2, 1, 5].length) (baseStart_667658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667658 prefixEnd_667658 := by exact prefixLift 667658
  have htrace : WordTrace (prefixWord ++ tailWord_667658) baseStart_667658 baseEnd_667658 := by
    simpa [prefixWord, tailWord_667658, baseEnd_667658] using wordTrace_append hprefix tailTrace_667658
  have hstable : (prefixWord ++ tailWord_667658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667658).length < 2 ^ (prefixWord ++ tailWord_667658).sum := by decide
  have hdescent : baseEnd_667658 < baseStart_667658 := by decide
  rcases family_descends (prefixWord ++ tailWord_667658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667664 : List Nat := [2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 3]
def baseStart_667664 : Nat := 118140960795 + 667664 * 2 ^ 59
def prefixEnd_667664 : Nat := 4983230072969 + 3 ^ 40 * 667664 * 2
def baseEnd_667664 : Nat := 342832547703580995229475

theorem tailTrace_667664 : CollatzResearch.WordTrace tailWord_667664 prefixEnd_667664 342832547703580995229475 := by
  unfold tailWord_667664
  simp only [CollatzResearch.WordTrace]
  refine ⟨12175853326587415389041023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16234471102116553852054697 12175853326587415389041023)
  ·
    refine ⟨18263779989881123083561535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12175853326587415389041023 18263779989881123083561535)
    ·
      refine ⟨27395669984821684625342303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18263779989881123083561535 27395669984821684625342303)
      ·
        refine ⟨41093504977232526938013455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27395669984821684625342303 41093504977232526938013455)
        ·
          refine ⟨61640257465848790407020183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41093504977232526938013455 61640257465848790407020183)
          ·
            refine ⟨92460386198773185610530275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61640257465848790407020183 92460386198773185610530275)
            ·
              refine ⟨138690579298159778415795413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92460386198773185610530275 138690579298159778415795413)
              ·
                refine ⟨3250560452300619806620205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 138690579298159778415795413 3250560452300619806620205)
                ·
                  refine ⟨1218960169612732427482577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3250560452300619806620205 1218960169612732427482577)
                  ·
                    refine ⟨914220127209549320611933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1218960169612732427482577 914220127209549320611933)
                    ·
                      refine ⟨342832547703580995229475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 914220127209549320611933 342832547703580995229475)
                      ·
                        rfl

theorem cell23_667664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 3].length) (baseStart_667664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667664 prefixEnd_667664 := by exact prefixLift 667664
  have htrace : WordTrace (prefixWord ++ tailWord_667664) baseStart_667664 baseEnd_667664 := by
    simpa [prefixWord, tailWord_667664, baseEnd_667664] using wordTrace_append hprefix tailTrace_667664
  have hstable : (prefixWord ++ tailWord_667664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667664).length < 2 ^ (prefixWord ++ tailWord_667664).sum := by decide
  have hdescent : baseEnd_667664 < baseStart_667664 := by decide
  rcases family_descends (prefixWord ++ tailWord_667664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667667 : List Nat := [1, 1, 1, 2, 1, 4, 4, 9]
def baseStart_667667 : Nat := 118140960795 + 667667 * 2 ^ 59
def prefixEnd_667667 : Nat := 4983230072969 + 3 ^ 40 * 667667 * 2
def baseEnd_667667 : Nat := 12697558820205351240443

theorem tailTrace_667667 : CollatzResearch.WordTrace tailWord_667667 prefixEnd_667667 12697558820205351240443 := by
  unfold tailWord_667667
  simp only [CollatzResearch.WordTrace]
  refine ⟨24351816072163962290441255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16234544048109308193627503 24351816072163962290441255)
  ·
    refine ⟨36527724108245943435661883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24351816072163962290441255 36527724108245943435661883)
    ·
      refine ⟨54791586162368915153492825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36527724108245943435661883 54791586162368915153492825)
      ·
        refine ⟨41093689621776686365119619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54791586162368915153492825 41093689621776686365119619)
        ·
          refine ⟨61640534432665029547679429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41093689621776686365119619 61640534432665029547679429)
          ·
            refine ⟨11557600206124693040189893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61640534432665029547679429 11557600206124693040189893)
            ·
              refine ⟨2167050038648379945035605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11557600206124693040189893 2167050038648379945035605)
              ·
                refine ⟨12697558820205351240443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2167050038648379945035605 12697558820205351240443)
                ·
                  rfl

theorem cell23_667667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 9].length) (baseStart_667667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667667 prefixEnd_667667 := by exact prefixLift 667667
  have htrace : WordTrace (prefixWord ++ tailWord_667667) baseStart_667667 baseEnd_667667 := by
    simpa [prefixWord, tailWord_667667, baseEnd_667667] using wordTrace_append hprefix tailTrace_667667
  have hstable : (prefixWord ++ tailWord_667667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667667).length < 2 ^ (prefixWord ++ tailWord_667667).sum := by decide
  have hdescent : baseEnd_667667 < baseStart_667667 := by decide
  rcases family_descends (prefixWord ++ tailWord_667667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667671 : List Nat := [1, 1, 3, 5, 2, 1, 1, 2, 1, 6]
def baseStart_667671 : Nat := 118140960795 + 667671 * 2 ^ 59
def prefixEnd_667671 : Nat := 4983230072969 + 3 ^ 40 * 667671 * 2
def baseEnd_667671 : Nat := 114278714022720822613981

theorem tailTrace_667671 : CollatzResearch.WordTrace tailWord_667671 prefixEnd_667671 114278714022720822613981 := by
  unfold tailWord_667671
  simp only [CollatzResearch.WordTrace]
  refine ⟨24351961964149470973586867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16234641309432980649057911 24351961964149470973586867)
  ·
    refine ⟨36527942946224206460380301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24351961964149470973586867 36527942946224206460380301)
    ·
      refine ⟨13697978604834077422642613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36527942946224206460380301 13697978604834077422642613)
      ·
        refine ⟨1284185494203194758372745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13697978604834077422642613 1284185494203194758372745)
        ·
          refine ⟨963139120652396068779559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1284185494203194758372745 963139120652396068779559)
          ·
            refine ⟨1444708680978594103169339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 963139120652396068779559 1444708680978594103169339)
            ·
              refine ⟨2167063021467891154754009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1444708680978594103169339 2167063021467891154754009)
              ·
                refine ⟨1625297266100918366065507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2167063021467891154754009 1625297266100918366065507)
                ·
                  refine ⟨2437945899151377549098261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1625297266100918366065507 2437945899151377549098261)
                  ·
                    refine ⟨114278714022720822613981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2437945899151377549098261 114278714022720822613981)
                    ·
                      rfl

theorem cell23_667671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 6].length) (baseStart_667671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667671 prefixEnd_667671 := by exact prefixLift 667671
  have htrace : WordTrace (prefixWord ++ tailWord_667671) baseStart_667671 baseEnd_667671 := by
    simpa [prefixWord, tailWord_667671, baseEnd_667671] using wordTrace_append hprefix tailTrace_667671
  have hstable : (prefixWord ++ tailWord_667671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667671).length < 2 ^ (prefixWord ++ tailWord_667671).sum := by decide
  have hdescent : baseEnd_667671 < baseStart_667671 := by decide
  rcases family_descends (prefixWord ++ tailWord_667671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667674 : List Nat := [3, 1, 1, 3, 1, 3, 1, 1, 3, 2, 4]
def baseStart_667674 : Nat := 118140960795 + 667674 * 2 ^ 59
def prefixEnd_667674 : Nat := 4983230072969 + 3 ^ 40 * 667674 * 2
def baseEnd_667674 : Nat := 342837682510125956104429

theorem tailTrace_667674 : CollatzResearch.WordTrace tailWord_667674 prefixEnd_667674 342837682510125956104429 := by
  unfold tailWord_667674
  simp only [CollatzResearch.WordTrace]
  refine ⟨6088017845784650621486519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16234714255425734990630717 6088017845784650621486519)
  ·
    refine ⟨9132026768676975932229779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6088017845784650621486519 9132026768676975932229779)
    ·
      refine ⟨13698040153015463898344669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9132026768676975932229779 13698040153015463898344669)
      ·
        refine ⟨5136765057380798961879251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13698040153015463898344669 5136765057380798961879251)
        ·
          refine ⟨7705147586071198442818877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5136765057380798961879251 7705147586071198442818877)
          ·
            refine ⟨2889430344776699416057079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7705147586071198442818877 2889430344776699416057079)
            ·
              refine ⟨4334145517165049124085619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2889430344776699416057079 4334145517165049124085619)
              ·
                refine ⟨6501218275747573686128429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4334145517165049124085619 6501218275747573686128429)
                ·
                  refine ⟨2437956853405340132298161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6501218275747573686128429 2437956853405340132298161)
                  ·
                    refine ⟨1828467640054005099223621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2437956853405340132298161 1828467640054005099223621)
                    ·
                      refine ⟨342837682510125956104429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1828467640054005099223621 342837682510125956104429)
                      ·
                        rfl

theorem cell23_667674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_667674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667674 prefixEnd_667674 := by exact prefixLift 667674
  have htrace : WordTrace (prefixWord ++ tailWord_667674) baseStart_667674 baseEnd_667674 := by
    simpa [prefixWord, tailWord_667674, baseEnd_667674] using wordTrace_append hprefix tailTrace_667674
  have hstable : (prefixWord ++ tailWord_667674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667674).length < 2 ^ (prefixWord ++ tailWord_667674).sum := by decide
  have hdescent : baseEnd_667674 < baseStart_667674 := by decide
  rcases family_descends (prefixWord ++ tailWord_667674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667684 : List Nat := [2, 3, 1, 4, 2, 11]
def baseStart_667684 : Nat := 118140960795 + 667684 * 2 ^ 59
def prefixEnd_667684 : Nat := 4983230072969 + 3 ^ 40 * 667684 * 2
def baseEnd_667684 : Nat := 1410875791426629287981

theorem tailTrace_667684 : CollatzResearch.WordTrace tailWord_667684 prefixEnd_667684 1410875791426629287981 := by
  unfold tailWord_667684
  simp only [CollatzResearch.WordTrace]
  refine ⟨12176218056551187096905053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16234957408734916129206737 12176218056551187096905053)
  ·
    refine ⟨4566081771206695161339395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12176218056551187096905053 4566081771206695161339395)
    ·
      refine ⟨6849122656810042742009093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4566081771206695161339395 6849122656810042742009093)
      ·
        refine ⟨1284210498151883014126705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6849122656810042742009093 1284210498151883014126705)
        ·
          refine ⟨963157873613912260595029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1284210498151883014126705 963157873613912260595029)
          ·
            refine ⟨1410875791426629287981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 963157873613912260595029 1410875791426629287981)
            ·
              rfl

theorem cell23_667684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 11].length) (baseStart_667684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667684 prefixEnd_667684 := by exact prefixLift 667684
  have htrace : WordTrace (prefixWord ++ tailWord_667684) baseStart_667684 baseEnd_667684 := by
    simpa [prefixWord, tailWord_667684, baseEnd_667684] using wordTrace_append hprefix tailTrace_667684
  have hstable : (prefixWord ++ tailWord_667684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667684).length < 2 ^ (prefixWord ++ tailWord_667684).sum := by decide
  have hdescent : baseEnd_667684 < baseStart_667684 := by decide
  rcases family_descends (prefixWord ++ tailWord_667684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667718 : List Nat := [6, 1, 1, 1, 1, 1, 5, 7]
def baseStart_667718 : Nat := 118140960795 + 667718 * 2 ^ 59
def prefixEnd_667718 : Nat := 4983230072969 + 3 ^ 40 * 667718 * 2
def baseEnd_667718 : Nat := 12698528728108288294601

theorem tailTrace_667718 : CollatzResearch.WordTrace tailWord_667718 prefixEnd_667718 12698528728108288294601 := by
  unfold tailWord_667718
  simp only [CollatzResearch.WordTrace]
  refine ⟨761052381093099937517119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16235784129986132000365205 761052381093099937517119)
  ·
    refine ⟨1141578571639649906275679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 761052381093099937517119 1141578571639649906275679)
    ·
      refine ⟨1712367857459474859413519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1141578571639649906275679 1712367857459474859413519)
      ·
        refine ⟨2568551786189212289120279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1712367857459474859413519 2568551786189212289120279)
        ·
          refine ⟨3852827679283818433680419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2568551786189212289120279 3852827679283818433680419)
          ·
            refine ⟨5779241518925727650520629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3852827679283818433680419 5779241518925727650520629)
            ·
              refine ⟨541803892399286967236309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5779241518925727650520629 541803892399286967236309)
              ·
                refine ⟨12698528728108288294601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 541803892399286967236309 12698528728108288294601)
                ·
                  rfl

theorem cell23_667718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 7].length) (baseStart_667718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667718 prefixEnd_667718 := by exact prefixLift 667718
  have htrace : WordTrace (prefixWord ++ tailWord_667718) baseStart_667718 baseEnd_667718 := by
    simpa [prefixWord, tailWord_667718, baseEnd_667718] using wordTrace_append hprefix tailTrace_667718
  have hstable : (prefixWord ++ tailWord_667718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667718).length < 2 ^ (prefixWord ++ tailWord_667718).sum := by decide
  have hdescent : baseEnd_667718 < baseStart_667718 := by decide
  rcases family_descends (prefixWord ++ tailWord_667718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667721 : List Nat := [1, 2, 1, 1, 2, 2, 3, 3, 3, 3, 2]
def baseStart_667721 : Nat := 118140960795 + 667721 * 2 ^ 59
def prefixEnd_667721 : Nat := 4983230072969 + 3 ^ 40 * 667721 * 2
def baseEnd_667721 : Nat := 342861816100887272216713

theorem tailTrace_667721 : CollatzResearch.WordTrace tailWord_667721 prefixEnd_667721 342861816100887272216713 := by
  unfold tailWord_667721
  simp only [CollatzResearch.WordTrace]
  refine ⟨24353785613968329512907017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16235857075978886341938011 24353785613968329512907017)
  ·
    refine ⟨18265339210476247134680263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24353785613968329512907017 18265339210476247134680263)
    ·
      refine ⟨27398008815714370702020395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18265339210476247134680263 27398008815714370702020395)
      ·
        refine ⟨41097013223571556053030593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27398008815714370702020395 41097013223571556053030593)
        ·
          refine ⟨30822759917678667039772945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41097013223571556053030593 30822759917678667039772945)
          ·
            refine ⟨23117069938259000279829709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30822759917678667039772945 23117069938259000279829709)
            ·
              refine ⟨8668901226847125104936141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23117069938259000279829709 8668901226847125104936141)
              ·
                refine ⟨3250837960067671914351053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8668901226847125104936141 3250837960067671914351053)
                ·
                  refine ⟨1219064235025376967881645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3250837960067671914351053 1219064235025376967881645)
                  ·
                    refine ⟨457149088134516362955617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1219064235025376967881645 457149088134516362955617)
                    ·
                      refine ⟨342861816100887272216713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 457149088134516362955617 342861816100887272216713)
                      ·
                        rfl

theorem cell23_667721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 3, 3, 2].length) (baseStart_667721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667721 prefixEnd_667721 := by exact prefixLift 667721
  have htrace : WordTrace (prefixWord ++ tailWord_667721) baseStart_667721 baseEnd_667721 := by
    simpa [prefixWord, tailWord_667721, baseEnd_667721] using wordTrace_append hprefix tailTrace_667721
  have hstable : (prefixWord ++ tailWord_667721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667721).length < 2 ^ (prefixWord ++ tailWord_667721).sum := by decide
  have hdescent : baseEnd_667721 < baseStart_667721 := by decide
  rcases family_descends (prefixWord ++ tailWord_667721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667738 : List Nat := [3, 1, 1, 2, 1, 1, 5, 3, 1, 3, 2]
def baseStart_667738 : Nat := 118140960795 + 667738 * 2 ^ 59
def prefixEnd_667738 : Nat := 4983230072969 + 3 ^ 40 * 667738 * 2
def baseEnd_667738 : Nat := 342870545272013705704135

theorem tailTrace_667738 : CollatzResearch.WordTrace tailWord_667738 prefixEnd_667738 342870545272013705704135 := by
  unfold tailWord_667738
  simp only [CollatzResearch.WordTrace]
  refine ⟨6088601413726685354068967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16236270436604494277517245 6088601413726685354068967)
  ·
    refine ⟨9132902120590028031103451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6088601413726685354068967 9132902120590028031103451)
    ·
      refine ⟨13699353180885042046655177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9132902120590028031103451 13699353180885042046655177)
      ·
        refine ⟨10274514885663781534991383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13699353180885042046655177 10274514885663781534991383)
        ·
          refine ⟨15411772328495672302487075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10274514885663781534991383 15411772328495672302487075)
          ·
            refine ⟨23117658492743508453730613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15411772328495672302487075 23117658492743508453730613)
            ·
              refine ⟨2167280483694703917537245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23117658492743508453730613 2167280483694703917537245)
              ·
                refine ⟨812730181385513969076467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2167280483694703917537245 812730181385513969076467)
                ·
                  refine ⟨1219095272078270953614701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 812730181385513969076467 1219095272078270953614701)
                  ·
                    refine ⟨457160727029351607605513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1219095272078270953614701 457160727029351607605513)
                    ·
                      refine ⟨342870545272013705704135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 457160727029351607605513 342870545272013705704135)
                      ·
                        rfl

theorem cell23_667738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 3, 1, 3, 2].length) (baseStart_667738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667738 prefixEnd_667738 := by exact prefixLift 667738
  have htrace : WordTrace (prefixWord ++ tailWord_667738) baseStart_667738 baseEnd_667738 := by
    simpa [prefixWord, tailWord_667738, baseEnd_667738] using wordTrace_append hprefix tailTrace_667738
  have hstable : (prefixWord ++ tailWord_667738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667738).length < 2 ^ (prefixWord ++ tailWord_667738).sum := by decide
  have hdescent : baseEnd_667738 < baseStart_667738 := by decide
  rcases family_descends (prefixWord ++ tailWord_667738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667744 : List Nat := [2, 1, 1, 3, 2, 3, 1, 2, 2, 6]
def baseStart_667744 : Nat := 118140960795 + 667744 * 2 ^ 59
def prefixEnd_667744 : Nat := 4983230072969 + 3 ^ 40 * 667744 * 2
def baseEnd_667744 : Nat := 114291208718646894076369

theorem tailTrace_667744 : CollatzResearch.WordTrace tailWord_667744 prefixEnd_667744 114291208718646894076369 := by
  unfold tailWord_667744
  simp only [CollatzResearch.WordTrace]
  refine ⟨12177312246442502220497143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16236416328590002960662857 12177312246442502220497143)
  ·
    refine ⟨18265968369663753330745715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12177312246442502220497143 18265968369663753330745715)
    ·
      refine ⟨27398952554495629996118573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18265968369663753330745715 27398952554495629996118573)
      ·
        refine ⟨10274607207935861248544465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27398952554495629996118573 10274607207935861248544465)
        ·
          refine ⟨7705955405951895936408349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10274607207935861248544465 7705955405951895936408349)
          ·
            refine ⟨2889733277231960976153131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7705955405951895936408349 2889733277231960976153131)
            ·
              refine ⟨4334599915847941464229697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2889733277231960976153131 4334599915847941464229697)
              ·
                refine ⟨3250949936885956098172273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4334599915847941464229697 3250949936885956098172273)
                ·
                  refine ⟨2438212452664467073629205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3250949936885956098172273 2438212452664467073629205)
                  ·
                    refine ⟨114291208718646894076369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2438212452664467073629205 114291208718646894076369)
                    ·
                      rfl

theorem cell23_667744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 2, 6].length) (baseStart_667744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667744 prefixEnd_667744 := by exact prefixLift 667744
  have htrace : WordTrace (prefixWord ++ tailWord_667744) baseStart_667744 baseEnd_667744 := by
    simpa [prefixWord, tailWord_667744, baseEnd_667744] using wordTrace_append hprefix tailTrace_667744
  have hstable : (prefixWord ++ tailWord_667744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667744).length < 2 ^ (prefixWord ++ tailWord_667744).sum := by decide
  have hdescent : baseEnd_667744 < baseStart_667744 := by decide
  rcases family_descends (prefixWord ++ tailWord_667744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667834 : List Nat := [3, 1, 1, 1, 2, 2, 2, 1, 2, 8]
def baseStart_667834 : Nat := 118140960795 + 667834 * 2 ^ 59
def prefixEnd_667834 : Nat := 4983230072969 + 3 ^ 40 * 667834 * 2
def baseEnd_667834 : Nat := 114306613138281776701231

theorem tailTrace_667834 : CollatzResearch.WordTrace tailWord_667834 prefixEnd_667834 114306613138281776701231 := by
  unfold tailWord_667834
  simp only [CollatzResearch.WordTrace]
  refine ⟨6089476765639737452942639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16238604708372633207847037 6089476765639737452942639)
  ·
    refine ⟨9134215148459606179413959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6089476765639737452942639 9134215148459606179413959)
    ·
      refine ⟨13701322722689409269120939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9134215148459606179413959 13701322722689409269120939)
      ·
        refine ⟨20551984084034113903681409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13701322722689409269120939 20551984084034113903681409)
        ·
          refine ⟨15413988063025585427761057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20551984084034113903681409 15413988063025585427761057)
          ·
            refine ⟨11560491047269189070820793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15413988063025585427761057 11560491047269189070820793)
            ·
              refine ⟨8670368285451891803115595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11560491047269189070820793 8670368285451891803115595)
              ·
                refine ⟨13005552428177837704673393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8670368285451891803115595 13005552428177837704673393)
                ·
                  refine ⟨9754164321133378278505045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13005552428177837704673393 9754164321133378278505045)
                  ·
                    refine ⟨114306613138281776701231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 9754164321133378278505045 114306613138281776701231)
                    ·
                      rfl

theorem cell23_667834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 2, 8].length) (baseStart_667834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667834 prefixEnd_667834 := by exact prefixLift 667834
  have htrace : WordTrace (prefixWord ++ tailWord_667834) baseStart_667834 baseEnd_667834 := by
    simpa [prefixWord, tailWord_667834, baseEnd_667834] using wordTrace_append hprefix tailTrace_667834
  have hstable : (prefixWord ++ tailWord_667834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667834).length < 2 ^ (prefixWord ++ tailWord_667834).sum := by decide
  have hdescent : baseEnd_667834 < baseStart_667834 := by decide
  rcases family_descends (prefixWord ++ tailWord_667834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667858 : List Nat := [3, 2, 2, 2, 1, 2, 2, 2, 2, 1, 4]
def baseStart_667858 : Nat := 118140960795 + 667858 * 2 ^ 59
def prefixEnd_667858 : Nat := 4983230072969 + 3 ^ 40 * 667858 * 2
def baseEnd_667858 : Nat := 342932162950553236203583

theorem tailTrace_667858 : CollatzResearch.WordTrace tailWord_667858 prefixEnd_667858 342932162950553236203583 := by
  unfold tailWord_667858
  simp only [CollatzResearch.WordTrace]
  refine ⟨6089695603618000477661057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16239188276314667940429485 6089695603618000477661057)
  ·
    refine ⟨4567271702713500358245793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6089695603618000477661057 4567271702713500358245793)
    ·
      refine ⟨3425453777035125268684345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4567271702713500358245793 3425453777035125268684345)
      ·
        refine ⟨2569090332776343951513259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3425453777035125268684345 2569090332776343951513259)
        ·
          refine ⟨3853635499164515927269889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2569090332776343951513259 3853635499164515927269889)
          ·
            refine ⟨2890226624373386945452417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3853635499164515927269889 2890226624373386945452417)
            ·
              refine ⟨2167669968280040209089313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2890226624373386945452417 2167669968280040209089313)
              ·
                refine ⟨1625752476210030156816985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2167669968280040209089313 1625752476210030156816985)
                ·
                  refine ⟨1219314357157522617612739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1625752476210030156816985 1219314357157522617612739)
                  ·
                    refine ⟨1828971535736283926419109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1219314357157522617612739 1828971535736283926419109)
                    ·
                      refine ⟨342932162950553236203583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1828971535736283926419109 342932162950553236203583)
                      ·
                        rfl

theorem cell23_667858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_667858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667858 prefixEnd_667858 := by exact prefixLift 667858
  have htrace : WordTrace (prefixWord ++ tailWord_667858) baseStart_667858 baseEnd_667858 := by
    simpa [prefixWord, tailWord_667858, baseEnd_667858] using wordTrace_append hprefix tailTrace_667858
  have hstable : (prefixWord ++ tailWord_667858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667858).length < 2 ^ (prefixWord ++ tailWord_667858).sum := by decide
  have hdescent : baseEnd_667858 < baseStart_667858 := by decide
  rcases family_descends (prefixWord ++ tailWord_667858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667885 : List Nat := [1, 5, 1, 2, 3, 1, 1, 2, 3, 4]
def baseStart_667885 : Nat := 118140960795 + 667885 * 2 ^ 59
def prefixEnd_667885 : Nat := 4983230072969 + 3 ^ 40 * 667885 * 2
def baseEnd_667885 : Nat := 114315342309408210188653

theorem tailTrace_667885 : CollatzResearch.WordTrace tailWord_667885 prefixEnd_667885 114315342309408210188653 := by
  unfold tailWord_667885
  simp only [CollatzResearch.WordTrace]
  refine ⟨24359767185374185521877109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16239844790249457014584739 24359767185374185521877109)
  ·
    refine ⟨2283728173628829892675979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24359767185374185521877109 2283728173628829892675979)
    ·
      refine ⟨3425592260443244839013969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2283728173628829892675979 3425592260443244839013969)
      ·
        refine ⟨2569194195332433629260477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3425592260443244839013969 2569194195332433629260477)
        ·
          refine ⟨963447823249662610972679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2569194195332433629260477 963447823249662610972679)
          ·
            refine ⟨1445171734874493916459019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 963447823249662610972679 1445171734874493916459019)
            ·
              refine ⟨2167757602311740874688529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1445171734874493916459019 2167757602311740874688529)
              ·
                refine ⟨1625818201733805656016397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2167757602311740874688529 1625818201733805656016397)
                ·
                  refine ⟨609681825650177121006149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1625818201733805656016397 609681825650177121006149)
                  ·
                    refine ⟨114315342309408210188653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 609681825650177121006149 114315342309408210188653)
                    ·
                      rfl

theorem cell23_667885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_667885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667885 prefixEnd_667885 := by exact prefixLift 667885
  have htrace : WordTrace (prefixWord ++ tailWord_667885) baseStart_667885 baseEnd_667885 := by
    simpa [prefixWord, tailWord_667885, baseEnd_667885] using wordTrace_append hprefix tailTrace_667885
  have hstable : (prefixWord ++ tailWord_667885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667885).length < 2 ^ (prefixWord ++ tailWord_667885).sum := by decide
  have hdescent : baseEnd_667885 < baseStart_667885 := by decide
  rcases family_descends (prefixWord ++ tailWord_667885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667902 : List Nat := [4, 2, 2, 1, 1, 1, 4, 3, 1, 4]
def baseStart_667902 : Nat := 118140960795 + 667902 * 2 ^ 59
def prefixEnd_667902 : Nat := 4983230072969 + 3 ^ 40 * 667902 * 2
def baseEnd_667902 : Nat := 114318252033117021351127

theorem tailTrace_667902 : CollatzResearch.WordTrace tailWord_667902 prefixEnd_667902 114318252033117021351127 := by
  unfold tailWord_667902
  simp only [CollatzResearch.WordTrace]
  refine ⟨3045048403289074678155745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16240258150875064950163973 3045048403289074678155745)
  ·
    refine ⟨2283786302466806008616809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3045048403289074678155745 2283786302466806008616809)
    ·
      refine ⟨1712839726850104506462607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2283786302466806008616809 1712839726850104506462607)
      ·
        refine ⟨2569259590275156759693911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1712839726850104506462607 2569259590275156759693911)
        ·
          refine ⟨3853889385412735139540867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2569259590275156759693911 3853889385412735139540867)
          ·
            refine ⟨5780834078119102709311301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3853889385412735139540867 5780834078119102709311301)
            ·
              refine ⟨1083906389647331757995869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5780834078119102709311301 1083906389647331757995869)
              ·
                refine ⟨406464896117749409248451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1083906389647331757995869 406464896117749409248451)
                ·
                  refine ⟨609697344176624113872677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 406464896117749409248451 609697344176624113872677)
                  ·
                    refine ⟨114318252033117021351127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 609697344176624113872677 114318252033117021351127)
                    ·
                      rfl

theorem cell23_667902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_667902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667902 prefixEnd_667902 := by exact prefixLift 667902
  have htrace : WordTrace (prefixWord ++ tailWord_667902) baseStart_667902 baseEnd_667902 := by
    simpa [prefixWord, tailWord_667902, baseEnd_667902] using wordTrace_append hprefix tailTrace_667902
  have hstable : (prefixWord ++ tailWord_667902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667902).length < 2 ^ (prefixWord ++ tailWord_667902).sum := by decide
  have hdescent : baseEnd_667902 < baseStart_667902 := by decide
  rcases family_descends (prefixWord ++ tailWord_667902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667931 : List Nat := [1, 1, 1, 1, 1, 1, 6, 1, 5, 1, 4]
def baseStart_667931 : Nat := 118140960795 + 667931 * 2 ^ 59
def prefixEnd_667931 : Nat := 4983230072969 + 3 ^ 40 * 667931 * 2
def baseEnd_667931 : Nat := 342969647038331450590747

theorem tailTrace_667931 : CollatzResearch.WordTrace tailWord_667931 prefixEnd_667931 342969647038331450590747 := by
  unfold tailWord_667931
  simp only [CollatzResearch.WordTrace]
  refine ⟨24361444943207535378051647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16240963295471690252034431 24361444943207535378051647)
  ·
    refine ⟨36542167414811303067077471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24361444943207535378051647 36542167414811303067077471)
    ·
      refine ⟨54813251122216954600616207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36542167414811303067077471 54813251122216954600616207)
      ·
        refine ⟨82219876683325431900924311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54813251122216954600616207 82219876683325431900924311)
        ·
          refine ⟨123329815024988147851386467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82219876683325431900924311 123329815024988147851386467)
          ·
            refine ⟨184994722537482221777079701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123329815024988147851386467 184994722537482221777079701)
            ·
              refine ⟨8671627618944479145800611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 184994722537482221777079701 8671627618944479145800611)
              ·
                refine ⟨13007441428416718718700917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8671627618944479145800611 13007441428416718718700917)
                ·
                  refine ⟨1219447633914067379878211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13007441428416718718700917 1219447633914067379878211)
                  ·
                    refine ⟨1829171450871101069817317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1219447633914067379878211 1829171450871101069817317)
                    ·
                      refine ⟨342969647038331450590747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1829171450871101069817317 342969647038331450590747)
                      ·
                        rfl

theorem cell23_667931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 5, 1, 4].length) (baseStart_667931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667931 prefixEnd_667931 := by exact prefixLift 667931
  have htrace : WordTrace (prefixWord ++ tailWord_667931) baseStart_667931 baseEnd_667931 := by
    simpa [prefixWord, tailWord_667931, baseEnd_667931] using wordTrace_append hprefix tailTrace_667931
  have hstable : (prefixWord ++ tailWord_667931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667931).length < 2 ^ (prefixWord ++ tailWord_667931).sum := by decide
  have hdescent : baseEnd_667931 < baseStart_667931 := by decide
  rcases family_descends (prefixWord ++ tailWord_667931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667948 : List Nat := [2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 4]
def baseStart_667948 : Nat := 118140960795 + 667948 * 2 ^ 59
def prefixEnd_667948 : Nat := 4983230072969 + 3 ^ 40 * 667948 * 2
def baseEnd_667948 : Nat := 342978376209457884078169

theorem tailTrace_667948 : CollatzResearch.WordTrace tailWord_667948 prefixEnd_667948 342978376209457884078169 := by
  unfold tailWord_667948
  simp only [CollatzResearch.WordTrace]
  refine ⟨12181032492072973640710249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16241376656097298187613665 12181032492072973640710249)
  ·
    refine ⟨9135774369054730230532687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12181032492072973640710249 9135774369054730230532687)
    ·
      refine ⟨13703661553582095345799031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9135774369054730230532687 13703661553582095345799031)
      ·
        refine ⟨20555492330373143018698547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13703661553582095345799031 20555492330373143018698547)
        ·
          refine ⟨30833238495559714528047821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20555492330373143018698547 30833238495559714528047821)
          ·
            refine ⟨11562464435834892948017933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30833238495559714528047821 11562464435834892948017933)
            ·
              refine ⟨4335924163438084855506725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11562464435834892948017933 4335924163438084855506725)
              ·
                refine ⟨812985780644640910407511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4335924163438084855506725 812985780644640910407511)
                ·
                  refine ⟨1219478670966961365611267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 812985780644640910407511 1219478670966961365611267)
                  ·
                    refine ⟨1829218006450442048416901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1219478670966961365611267 1829218006450442048416901)
                    ·
                      refine ⟨342978376209457884078169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1829218006450442048416901 342978376209457884078169)
                      ·
                        rfl

theorem cell23_667948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 4].length) (baseStart_667948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667948 prefixEnd_667948 := by exact prefixLift 667948
  have htrace : WordTrace (prefixWord ++ tailWord_667948) baseStart_667948 baseEnd_667948 := by
    simpa [prefixWord, tailWord_667948, baseEnd_667948] using wordTrace_append hprefix tailTrace_667948
  have hstable : (prefixWord ++ tailWord_667948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667948).length < 2 ^ (prefixWord ++ tailWord_667948).sum := by decide
  have hdescent : baseEnd_667948 < baseStart_667948 := by decide
  rcases family_descends (prefixWord ++ tailWord_667948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667988 : List Nat := [2, 4, 1, 1, 2, 3, 2, 8]
def baseStart_667988 : Nat := 118140960795 + 667988 * 2 ^ 59
def prefixEnd_667988 : Nat := 4983230072969 + 3 ^ 40 * 667988 * 2
def baseEnd_667988 : Nat := 12703663534653249169555

theorem tailTrace_667988 : CollatzResearch.WordTrace tailWord_667988 prefixEnd_667988 12703663534653249169555 := by
  unfold tailWord_667988
  simp only [CollatzResearch.WordTrace]
  refine ⟨12181761952000517056438309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16242349269334022741917745 12181761952000517056438309)
  ·
    refine ⟨2284080366000096948082183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12181761952000517056438309 2284080366000096948082183)
    ·
      refine ⟨3426120549000145422123275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2284080366000096948082183 3426120549000145422123275)
      ·
        refine ⟨5139180823500218133184913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3426120549000145422123275 5139180823500218133184913)
        ·
          refine ⟨3854385617625163599888685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5139180823500218133184913 3854385617625163599888685)
          ·
            refine ⟨1445394606609436349958257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3854385617625163599888685 1445394606609436349958257)
            ·
              refine ⟨1084045954957077262468693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1445394606609436349958257 1084045954957077262468693)
              ·
                refine ⟨12703663534653249169555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1084045954957077262468693 12703663534653249169555)
                ·
                  rfl

theorem cell23_667988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 8].length) (baseStart_667988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667988 prefixEnd_667988 := by exact prefixLift 667988
  have htrace : WordTrace (prefixWord ++ tailWord_667988) baseStart_667988 baseEnd_667988 := by
    simpa [prefixWord, tailWord_667988, baseEnd_667988] using wordTrace_append hprefix tailTrace_667988
  have hstable : (prefixWord ++ tailWord_667988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667988).length < 2 ^ (prefixWord ++ tailWord_667988).sum := by decide
  have hdescent : baseEnd_667988 < baseStart_667988 := by decide
  rcases family_descends (prefixWord ++ tailWord_667988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_667991 : List Nat := [1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 6]
def baseStart_667991 : Nat := 118140960795 + 667991 * 2 ^ 59
def prefixEnd_667991 : Nat := 4983230072969 + 3 ^ 40 * 667991 * 2
def baseEnd_667991 : Nat := 343000455877601215840471

theorem tailTrace_667991 : CollatzResearch.WordTrace tailWord_667991 prefixEnd_667991 343000455877601215840471 := by
  unfold tailWord_667991
  simp only [CollatzResearch.WordTrace]
  refine ⟨24363633322990165625235827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16242422215326777083490551 24363633322990165625235827)
  ·
    refine ⟨36545449984485248437853741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24363633322990165625235827 36545449984485248437853741)
    ·
      refine ⟨13704543744181968164195153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36545449984485248437853741 13704543744181968164195153)
      ·
        refine ⟨10278407808136476123146365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13704543744181968164195153 10278407808136476123146365)
        ·
          refine ⟨3854402928051178546179887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10278407808136476123146365 3854402928051178546179887)
          ·
            refine ⟨5781604392076767819269831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3854402928051178546179887 5781604392076767819269831)
            ·
              refine ⟨8672406588115151728904747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5781604392076767819269831 8672406588115151728904747)
              ·
                refine ⟨13008609882172727593357121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8672406588115151728904747 13008609882172727593357121)
                ·
                  refine ⟨9756457411629545695017841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13008609882172727593357121 9756457411629545695017841)
                  ·
                    refine ⟨7317343058722159271263381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9756457411629545695017841 7317343058722159271263381)
                    ·
                      refine ⟨343000455877601215840471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7317343058722159271263381 343000455877601215840471)
                      ·
                        rfl

theorem cell23_667991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_667991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_667991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_667991 prefixEnd_667991 := by exact prefixLift 667991
  have htrace : WordTrace (prefixWord ++ tailWord_667991) baseStart_667991 baseEnd_667991 := by
    simpa [prefixWord, tailWord_667991, baseEnd_667991] using wordTrace_append hprefix tailTrace_667991
  have hstable : (prefixWord ++ tailWord_667991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_667991).length < 2 ^ (prefixWord ++ tailWord_667991).sum := by decide
  have hdescent : baseEnd_667991 < baseStart_667991 := by decide
  rcases family_descends (prefixWord ++ tailWord_667991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668002 : List Nat := [3, 3, 2, 1, 1, 2, 3, 2, 1, 2, 3]
def baseStart_668002 : Nat := 118140960795 + 668002 * 2 ^ 59
def prefixEnd_668002 : Nat := 4983230072969 + 3 ^ 40 * 668002 * 2
def baseEnd_668002 : Nat := 343006104164800672802921

theorem tailTrace_668002 : CollatzResearch.WordTrace tailWord_668002 prefixEnd_668002 343006104164800672802921 := by
  unfold tailWord_668002
  simp only [CollatzResearch.WordTrace]
  refine ⟨6091008631487578625971565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16242689683966876335924173 6091008631487578625971565)
  ·
    refine ⟨2284128236807841984739337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6091008631487578625971565 2284128236807841984739337)
    ·
      refine ⟨1713096177605881488554503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2284128236807841984739337 1713096177605881488554503)
      ·
        refine ⟨2569644266408822232831755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1713096177605881488554503 2569644266408822232831755)
        ·
          refine ⟨3854466399613233349247633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2569644266408822232831755 3854466399613233349247633)
          ·
            refine ⟨2890849799709925011935725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3854466399613233349247633 2890849799709925011935725)
            ·
              refine ⟨1084068674891221879475897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2890849799709925011935725 1084068674891221879475897)
              ·
                refine ⟨813051506168416409606923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1084068674891221879475897 813051506168416409606923)
                ·
                  refine ⟨1219577259252624614410385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 813051506168416409606923 1219577259252624614410385)
                  ·
                    refine ⟨914682944439468460807789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1219577259252624614410385 914682944439468460807789)
                    ·
                      refine ⟨343006104164800672802921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 914682944439468460807789 343006104164800672802921)
                      ·
                        rfl

theorem cell23_668002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_668002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_668002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_668002 prefixEnd_668002 := by exact prefixLift 668002
  have htrace : WordTrace (prefixWord ++ tailWord_668002) baseStart_668002 baseEnd_668002 := by
    simpa [prefixWord, tailWord_668002, baseEnd_668002] using wordTrace_append hprefix tailTrace_668002
  have hstable : (prefixWord ++ tailWord_668002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668002).length < 2 ^ (prefixWord ++ tailWord_668002).sum := by decide
  have hdescent : baseEnd_668002 < baseStart_668002 := by decide
  rcases family_descends (prefixWord ++ tailWord_668002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668031 : List Nat := [1, 1, 2, 2, 1, 1, 2, 3, 4, 6]
def baseStart_668031 : Nat := 118140960795 + 668031 * 2 ^ 59
def prefixEnd_668031 : Nat := 4983230072969 + 3 ^ 40 * 668031 * 2
def baseEnd_668031 : Nat := 114340331701260353113429

theorem tailTrace_668031 : CollatzResearch.WordTrace tailWord_668031 prefixEnd_668031 114340331701260353113429 := by
  unfold tailWord_668031
  simp only [CollatzResearch.WordTrace]
  refine ⟨24365092242845252456691947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16243394828563501637794631 24365092242845252456691947)
  ·
    refine ⟨36547638364267878685037921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24365092242845252456691947 36547638364267878685037921)
    ·
      refine ⟨27410728773200909013778441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36547638364267878685037921 27410728773200909013778441)
      ·
        refine ⟨20558046579900681760333831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27410728773200909013778441 20558046579900681760333831)
        ·
          refine ⟨30837069869851022640500747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20558046579900681760333831 30837069869851022640500747)
          ·
            refine ⟨46255604804776533960751121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30837069869851022640500747 46255604804776533960751121)
            ·
              refine ⟨34691703603582400470563341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46255604804776533960751121 34691703603582400470563341)
              ·
                refine ⟨13009388851343400176461253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34691703603582400470563341 13009388851343400176461253)
                ·
                  refine ⟨2439260409626887533086485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13009388851343400176461253 2439260409626887533086485)
                  ·
                    refine ⟨114340331701260353113429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2439260409626887533086485 114340331701260353113429)
                    ·
                      rfl

theorem cell23_668031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 6].length) (baseStart_668031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_668031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_668031 prefixEnd_668031 := by exact prefixLift 668031
  have htrace : WordTrace (prefixWord ++ tailWord_668031) baseStart_668031 baseEnd_668031 := by
    simpa [prefixWord, tailWord_668031, baseEnd_668031] using wordTrace_append hprefix tailTrace_668031
  have hstable : (prefixWord ++ tailWord_668031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668031).length < 2 ^ (prefixWord ++ tailWord_668031).sum := by decide
  have hdescent : baseEnd_668031 < baseStart_668031 := by decide
  rcases family_descends (prefixWord ++ tailWord_668031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668033 : List Nat := [1, 2, 4, 3, 1, 3, 2, 2, 1, 2, 2]
def baseStart_668033 : Nat := 118140960795 + 668033 * 2 ^ 59
def prefixEnd_668033 : Nat := 4983230072969 + 3 ^ 40 * 668033 * 2
def baseEnd_668033 : Nat := 343022022065090051515279

theorem tailTrace_668033 : CollatzResearch.WordTrace tailWord_668033 prefixEnd_668033 343022022065090051515279 := by
  unfold tailWord_668033
  simp only [CollatzResearch.WordTrace]
  refine ⟨24365165188838006798264753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16243443459225337865509835 24365165188838006798264753)
  ·
    refine ⟨18273873891628505098698565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24365165188838006798264753 18273873891628505098698565)
    ·
      refine ⟨3426351354680344706005981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18273873891628505098698565 3426351354680344706005981)
      ·
        refine ⟨1284881758005129264752243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3426351354680344706005981 1284881758005129264752243)
        ·
          refine ⟨1927322637007693897128365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1284881758005129264752243 1927322637007693897128365)
          ·
            refine ⟨722745988877885211423137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1927322637007693897128365 722745988877885211423137)
            ·
              refine ⟨542059491658413908567353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 722745988877885211423137 542059491658413908567353)
              ·
                refine ⟨406544618743810431425515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 542059491658413908567353 406544618743810431425515)
                ·
                  refine ⟨609816928115715647138273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 406544618743810431425515 609816928115715647138273)
                  ·
                    refine ⟨457362696086786735353705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 609816928115715647138273 457362696086786735353705)
                    ·
                      refine ⟨343022022065090051515279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 457362696086786735353705 343022022065090051515279)
                      ·
                        rfl

theorem cell23_668033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_668033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_668033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_668033 prefixEnd_668033 := by exact prefixLift 668033
  have htrace : WordTrace (prefixWord ++ tailWord_668033) baseStart_668033 baseEnd_668033 := by
    simpa [prefixWord, tailWord_668033, baseEnd_668033] using wordTrace_append hprefix tailTrace_668033
  have hstable : (prefixWord ++ tailWord_668033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668033).length < 2 ^ (prefixWord ++ tailWord_668033).sum := by decide
  have hdescent : baseEnd_668033 < baseStart_668033 := by decide
  rcases family_descends (prefixWord ++ tailWord_668033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668055 : List Nat := [1, 1, 3, 3, 1, 1, 3, 3, 1, 4, 2]
def baseStart_668055 : Nat := 118140960795 + 668055 * 2 ^ 59
def prefixEnd_668055 : Nat := 4983230072969 + 3 ^ 40 * 668055 * 2
def baseEnd_668055 : Nat := 343033318639488965440177

theorem tailTrace_668055 : CollatzResearch.WordTrace tailWord_668055 prefixEnd_668055 343033318639488965440177 := by
  unfold tailWord_668055
  simp only [CollatzResearch.WordTrace]
  refine ⟨24365967594758304555565619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16243978396505536370377079 24365967594758304555565619)
  ·
    refine ⟨36548951392137456833348429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24365967594758304555565619 36548951392137456833348429)
    ·
      refine ⟨13705856772051546312505661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36548951392137456833348429 13705856772051546312505661)
      ·
        refine ⟨5139696289519329867189623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13705856772051546312505661 5139696289519329867189623)
        ·
          refine ⟨7709544434278994800784435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5139696289519329867189623 7709544434278994800784435)
          ·
            refine ⟨11564316651418492201176653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7709544434278994800784435 11564316651418492201176653)
            ·
              refine ⟨4336618744281934575441245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11564316651418492201176653 4336618744281934575441245)
              ·
                refine ⟨1626232029105725465790467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4336618744281934575441245 1626232029105725465790467)
                ·
                  refine ⟨2439348043658588198685701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1626232029105725465790467 2439348043658588198685701)
                  ·
                    refine ⟨457377758185985287253569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2439348043658588198685701 457377758185985287253569)
                    ·
                      refine ⟨343033318639488965440177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 457377758185985287253569 343033318639488965440177)
                      ·
                        rfl

theorem cell23_668055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 4, 2].length) (baseStart_668055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_668055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_668055 prefixEnd_668055 := by exact prefixLift 668055
  have htrace : WordTrace (prefixWord ++ tailWord_668055) baseStart_668055 baseEnd_668055 := by
    simpa [prefixWord, tailWord_668055, baseEnd_668055] using wordTrace_append hprefix tailTrace_668055
  have hstable : (prefixWord ++ tailWord_668055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668055).length < 2 ^ (prefixWord ++ tailWord_668055).sum := by decide
  have hdescent : baseEnd_668055 < baseStart_668055 := by decide
  rcases family_descends (prefixWord ++ tailWord_668055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668089 : List Nat := [1, 2, 1, 4, 3, 1, 3, 2, 2, 2, 2]
def baseStart_668089 : Nat := 118140960795 + 668089 * 2 ^ 59
def prefixEnd_668089 : Nat := 4983230072969 + 3 ^ 40 * 668089 * 2
def baseEnd_668089 : Nat := 343050776981741832415021

theorem tailTrace_668089 : CollatzResearch.WordTrace tailWord_668089 prefixEnd_668089 343050776981741832415021 := by
  unfold tailWord_668089
  simp only [CollatzResearch.WordTrace]
  refine ⟨24367207676635128362303321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16244805117756752241535547 24367207676635128362303321)
  ·
    refine ⟨18275405757476346271727491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24367207676635128362303321 18275405757476346271727491)
    ·
      refine ⟨27413108636214519407591237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18275405757476346271727491 27413108636214519407591237)
      ·
        refine ⟨5139957869290222388923357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27413108636214519407591237 5139957869290222388923357)
        ·
          refine ⟨1927484200983833395846259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5139957869290222388923357 1927484200983833395846259)
          ·
            refine ⟨2891226301475750093769389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1927484200983833395846259 2891226301475750093769389)
            ·
              refine ⟨1084209863053406285163521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2891226301475750093769389 1084209863053406285163521)
              ·
                refine ⟨813157397290054713872641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1084209863053406285163521 813157397290054713872641)
                ·
                  refine ⟨609868047967541035404481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 813157397290054713872641 609868047967541035404481)
                  ·
                    refine ⟨457401035975655776553361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 609868047967541035404481 457401035975655776553361)
                    ·
                      refine ⟨343050776981741832415021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 457401035975655776553361 343050776981741832415021)
                      ·
                        rfl

theorem cell23_668089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 2, 2, 2, 2].length) (baseStart_668089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_668089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_668089 prefixEnd_668089 := by exact prefixLift 668089
  have htrace : WordTrace (prefixWord ++ tailWord_668089) baseStart_668089 baseEnd_668089 := by
    simpa [prefixWord, tailWord_668089, baseEnd_668089] using wordTrace_append hprefix tailTrace_668089
  have hstable : (prefixWord ++ tailWord_668089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668089).length < 2 ^ (prefixWord ++ tailWord_668089).sum := by decide
  have hdescent : baseEnd_668089 < baseStart_668089 := by decide
  rcases family_descends (prefixWord ++ tailWord_668089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668091 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 2, 11]
def baseStart_668091 : Nat := 118140960795 + 668091 * 2 ^ 59
def prefixEnd_668091 : Nat := 4983230072969 + 3 ^ 40 * 668091 * 2
def baseEnd_668091 : Nat := 114350601314350274863337

theorem tailTrace_668091 : CollatzResearch.WordTrace tailWord_668091 prefixEnd_668091 114350601314350274863337 := by
  unfold tailWord_668091
  simp only [CollatzResearch.WordTrace]
  refine ⟨24367280622627882703876127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16244853748418588469250751 24367280622627882703876127)
  ·
    refine ⟨36550920933941824055814191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24367280622627882703876127 36550920933941824055814191)
    ·
      refine ⟨54826381400912736083721287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36550920933941824055814191 54826381400912736083721287)
      ·
        refine ⟨82239572101369104125581931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54826381400912736083721287 82239572101369104125581931)
        ·
          refine ⟨123359358152053656188372897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82239572101369104125581931 123359358152053656188372897)
          ·
            refine ⟨92519518614040242141279673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123359358152053656188372897 92519518614040242141279673)
            ·
              refine ⟨69389638960530181605959755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92519518614040242141279673 69389638960530181605959755)
              ·
                refine ⟨104084458440795272408939633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69389638960530181605959755 104084458440795272408939633)
                ·
                  refine ⟨78063343830596454306704725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104084458440795272408939633 78063343830596454306704725)
                  ·
                    refine ⟨114350601314350274863337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 78063343830596454306704725 114350601314350274863337)
                    ·
                      rfl

theorem cell23_668091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 11].length) (baseStart_668091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_668091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_668091 prefixEnd_668091 := by exact prefixLift 668091
  have htrace : WordTrace (prefixWord ++ tailWord_668091) baseStart_668091 baseEnd_668091 := by
    simpa [prefixWord, tailWord_668091, baseEnd_668091] using wordTrace_append hprefix tailTrace_668091
  have hstable : (prefixWord ++ tailWord_668091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668091).length < 2 ^ (prefixWord ++ tailWord_668091).sum := by decide
  have hdescent : baseEnd_668091 < baseStart_668091 := by decide
  rcases family_descends (prefixWord ++ tailWord_668091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668125 : List Nat := [1, 4, 3, 1, 1, 1, 2, 3, 2, 5]
def baseStart_668125 : Nat := 118140960795 + 668125 * 2 ^ 59
def prefixEnd_668125 : Nat := 4983230072969 + 3 ^ 40 * 668125 * 2
def baseEnd_668125 : Nat := 114356420761767897188285

theorem tailTrace_668125 : CollatzResearch.WordTrace tailWord_668125 prefixEnd_668125 114356420761767897188285 := by
  unfold tailWord_668125
  simp only [CollatzResearch.WordTrace]
  refine ⟨24368520704504706510613829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16245680469669804340409219 24368520704504706510613829)
  ·
    refine ⟨4569097632094632470740093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24368520704504706510613829 4569097632094632470740093)
    ·
      refine ⟨1713411612035487176527535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4569097632094632470740093 1713411612035487176527535)
      ·
        refine ⟨2570117418053230764791303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1713411612035487176527535 2570117418053230764791303)
        ·
          refine ⟨3855176127079846147186955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2570117418053230764791303 3855176127079846147186955)
          ·
            refine ⟨5782764190619769220780433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3855176127079846147186955 5782764190619769220780433)
            ·
              refine ⟨4337073142964826915585325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5782764190619769220780433 4337073142964826915585325)
              ·
                refine ⟨1626402428611810093344497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4337073142964826915585325 1626402428611810093344497)
                ·
                  refine ⟨1219801821458857570008373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1626402428611810093344497 1219801821458857570008373)
                  ·
                    refine ⟨114356420761767897188285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1219801821458857570008373 114356420761767897188285)
                    ·
                      rfl

theorem cell23_668125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_668125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_668125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_668125 prefixEnd_668125 := by exact prefixLift 668125
  have htrace : WordTrace (prefixWord ++ tailWord_668125) baseStart_668125 baseEnd_668125 := by
    simpa [prefixWord, tailWord_668125, baseEnd_668125] using wordTrace_append hprefix tailTrace_668125
  have hstable : (prefixWord ++ tailWord_668125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668125).length < 2 ^ (prefixWord ++ tailWord_668125).sum := by decide
  have hdescent : baseEnd_668125 < baseStart_668125 := by decide
  rcases family_descends (prefixWord ++ tailWord_668125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668128 : List Nat := [2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 4]
def baseStart_668128 : Nat := 118140960795 + 668128 * 2 ^ 59
def prefixEnd_668128 : Nat := 4983230072969 + 3 ^ 40 * 668128 * 2
def baseEnd_668128 : Nat := 343070802727267179827341

theorem tailTrace_668128 : CollatzResearch.WordTrace tailWord_668128 prefixEnd_668128 343070802727267179827341 := by
  unfold tailWord_668128
  simp only [CollatzResearch.WordTrace]
  refine ⟨12184315061746919011486519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16245753415662558681982025 12184315061746919011486519)
  ·
    refine ⟨18276472592620378517229779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12184315061746919011486519 18276472592620378517229779)
    ·
      refine ⟨27414708888930567775844669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18276472592620378517229779 27414708888930567775844669)
      ·
        refine ⟨10280515833348962915941751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27414708888930567775844669 10280515833348962915941751)
        ·
          refine ⟨15420773750023444373912627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10280515833348962915941751 15420773750023444373912627)
          ·
            refine ⟨23131160625035166560868941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15420773750023444373912627 23131160625035166560868941)
            ·
              refine ⟨8674185234388187460325853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23131160625035166560868941 8674185234388187460325853)
              ·
                refine ⟨3252819462895570297622195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8674185234388187460325853 3252819462895570297622195)
                ·
                  refine ⟨4879229194343355446433293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3252819462895570297622195 4879229194343355446433293)
                  ·
                    refine ⟨1829710947878758292412485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4879229194343355446433293 1829710947878758292412485)
                    ·
                      refine ⟨343070802727267179827341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1829710947878758292412485 343070802727267179827341)
                      ·
                        rfl

theorem cell23_668128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_668128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_668128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_668128 prefixEnd_668128 := by exact prefixLift 668128
  have htrace : WordTrace (prefixWord ++ tailWord_668128) baseStart_668128 baseEnd_668128 := by
    simpa [prefixWord, tailWord_668128, baseEnd_668128] using wordTrace_append hprefix tailTrace_668128
  have hstable : (prefixWord ++ tailWord_668128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668128).length < 2 ^ (prefixWord ++ tailWord_668128).sum := by decide
  have hdescent : baseEnd_668128 < baseStart_668128 := by decide
  rcases family_descends (prefixWord ++ tailWord_668128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668145 : List Nat := [1, 2, 2, 2, 3, 1, 3, 2, 2, 1, 4]
def baseStart_668145 : Nat := 118140960795 + 668145 * 2 ^ 59
def prefixEnd_668145 : Nat := 4983230072969 + 3 ^ 40 * 668145 * 2
def baseEnd_668145 : Nat := 343079531898393613314763

theorem tailTrace_668145 : CollatzResearch.WordTrace tailWord_668145 prefixEnd_668145 343079531898393613314763 := by
  unfold tailWord_668145
  simp only [CollatzResearch.WordTrace]
  refine ⟨24369250164432249926341889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16246166776288166617561259 24369250164432249926341889)
  ·
    refine ⟨18276937623324187444756417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24369250164432249926341889 18276937623324187444756417)
    ·
      refine ⟨13707703217493140583567313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18276937623324187444756417 13707703217493140583567313)
      ·
        refine ⟨10280777413119855437675485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13707703217493140583567313 10280777413119855437675485)
        ·
          refine ⟨3855291529919945789128307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10280777413119855437675485 3855291529919945789128307)
          ·
            refine ⟨5782937294879918683692461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3855291529919945789128307 5782937294879918683692461)
            ·
              refine ⟨2168601485579969506384673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5782937294879918683692461 2168601485579969506384673)
              ·
                refine ⟨1626451114184977129788505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2168601485579969506384673 1626451114184977129788505)
                ·
                  refine ⟨1219838335638732847341379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1626451114184977129788505 1219838335638732847341379)
                  ·
                    refine ⟨1829757503458099271012069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1219838335638732847341379 1829757503458099271012069)
                    ·
                      refine ⟨343079531898393613314763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1829757503458099271012069 343079531898393613314763)
                      ·
                        rfl

theorem cell23_668145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_668145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_668145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_668145 prefixEnd_668145 := by exact prefixLift 668145
  have htrace : WordTrace (prefixWord ++ tailWord_668145) baseStart_668145 baseEnd_668145 := by
    simpa [prefixWord, tailWord_668145, baseEnd_668145] using wordTrace_append hprefix tailTrace_668145
  have hstable : (prefixWord ++ tailWord_668145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668145).length < 2 ^ (prefixWord ++ tailWord_668145).sum := by decide
  have hdescent : baseEnd_668145 < baseStart_668145 := by decide
  rcases family_descends (prefixWord ++ tailWord_668145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668202 : List Nat := [3, 1, 4, 1, 1, 3, 2, 2, 6]
def baseStart_668202 : Nat := 118140960795 + 668202 * 2 ^ 59
def prefixEnd_668202 : Nat := 4983230072969 + 3 ^ 40 * 668202 * 2
def baseEnd_668202 : Nat := 38123200032855543366889

theorem tailTrace_668202 : CollatzResearch.WordTrace tailWord_668202 prefixEnd_668202 38123200032855543366889 := by
  unfold tailWord_668202
  simp only [CollatzResearch.WordTrace]
  refine ⟨6092832281306437165291715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16247552750150499107444573 6092832281306437165291715)
  ·
    refine ⟨9139248421959655747937573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6092832281306437165291715 9139248421959655747937573)
    ·
      refine ⟨1713609079117435452738295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9139248421959655747937573 1713609079117435452738295)
      ·
        refine ⟨2570413618676153179107443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1713609079117435452738295 2570413618676153179107443)
        ·
          refine ⟨3855620428014229768661165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2570413618676153179107443 3855620428014229768661165)
          ·
            refine ⟨1445857660505336163247937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3855620428014229768661165 1445857660505336163247937)
            ·
              refine ⟨1084393245379002122435953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1445857660505336163247937 1084393245379002122435953)
              ·
                refine ⟨813294934034251591826965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1084393245379002122435953 813294934034251591826965)
                ·
                  refine ⟨38123200032855543366889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 813294934034251591826965 38123200032855543366889)
                  ·
                    rfl

theorem cell23_668202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 2, 6].length) (baseStart_668202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_668202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_668202 prefixEnd_668202 := by exact prefixLift 668202
  have htrace : WordTrace (prefixWord ++ tailWord_668202) baseStart_668202 baseEnd_668202 := by
    simpa [prefixWord, tailWord_668202, baseEnd_668202] using wordTrace_append hprefix tailTrace_668202
  have hstable : (prefixWord ++ tailWord_668202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668202).length < 2 ^ (prefixWord ++ tailWord_668202).sum := by decide
  have hdescent : baseEnd_668202 < baseStart_668202 := by decide
  rcases family_descends (prefixWord ++ tailWord_668202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668206 : List Nat := [4, 1, 3, 1, 3, 1, 1, 4, 1, 4]
def baseStart_668206 : Nat := 118140960795 + 668206 * 2 ^ 59
def prefixEnd_668206 : Nat := 4983230072969 + 3 ^ 40 * 668206 * 2
def baseEnd_668206 : Nat := 114370284739439291550661

theorem tailTrace_668206 : CollatzResearch.WordTrace tailWord_668206 prefixEnd_668206 114370284739439291550661 := by
  unfold tailWord_668206
  simp only [CollatzResearch.WordTrace]
  refine ⟨3046434377151407168039059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16247650011474171562874981 3046434377151407168039059)
  ·
    refine ⟨4569651565727110752058589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3046434377151407168039059 4569651565727110752058589)
    ·
      refine ⟨1713619337147666532021971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4569651565727110752058589 1713619337147666532021971)
      ·
        refine ⟨2570429005721499798032957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1713619337147666532021971 2570429005721499798032957)
        ·
          refine ⟨963910877145562424262359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2570429005721499798032957 963910877145562424262359)
          ·
            refine ⟨1445866315718343636393539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 963910877145562424262359 1445866315718343636393539)
            ·
              refine ⟨2168799473577515454590309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1445866315718343636393539 2168799473577515454590309)
              ·
                refine ⟨406649901295784147735683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2168799473577515454590309 406649901295784147735683)
                ·
                  refine ⟨609974851943676221603525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 406649901295784147735683 609974851943676221603525)
                  ·
                    refine ⟨114370284739439291550661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 609974851943676221603525 114370284739439291550661)
                    ·
                      rfl

theorem cell23_668206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_668206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_668206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_668206 prefixEnd_668206 := by exact prefixLift 668206
  have htrace : WordTrace (prefixWord ++ tailWord_668206) baseStart_668206 baseEnd_668206 := by
    simpa [prefixWord, tailWord_668206, baseEnd_668206] using wordTrace_append hprefix tailTrace_668206
  have hstable : (prefixWord ++ tailWord_668206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668206).length < 2 ^ (prefixWord ++ tailWord_668206).sum := by decide
  have hdescent : baseEnd_668206 < baseStart_668206 := by decide
  rcases family_descends (prefixWord ++ tailWord_668206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668235 : List Nat := [1, 1, 1, 1, 3, 1, 6, 1, 3, 1, 4]
def baseStart_668235 : Nat := 118140960795 + 668235 * 2 ^ 59
def prefixEnd_668235 : Nat := 4983230072969 + 3 ^ 40 * 668235 * 2
def baseEnd_668235 : Nat := 343125745157298261189349

theorem tailTrace_668235 : CollatzResearch.WordTrace tailWord_668235 prefixEnd_668235 343125745157298261189349 := by
  unfold tailWord_668235
  simp only [CollatzResearch.WordTrace]
  refine ⟨24372532734106195297118159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16248355156070796864745439 24372532734106195297118159)
  ·
    refine ⟨36558799101159292945677239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24372532734106195297118159 36558799101159292945677239)
    ·
      refine ⟨54838198651738939418515859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36558799101159292945677239 54838198651738939418515859)
      ·
        refine ⟨82257297977608409127773789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54838198651738939418515859 82257297977608409127773789)
        ·
          refine ⟨30846486741603153422915171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82257297977608409127773789 30846486741603153422915171)
          ·
            refine ⟨46269730112404730134372757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30846486741603153422915171 46269730112404730134372757)
            ·
              refine ⟨2168893599018971725048723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 46269730112404730134372757 2168893599018971725048723)
              ·
                refine ⟨3253340398528457587573085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2168893599018971725048723 3253340398528457587573085)
                ·
                  refine ⟨1220002649448171595339907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3253340398528457587573085 1220002649448171595339907)
                  ·
                    refine ⟨1830003974172257393009861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1220002649448171595339907 1830003974172257393009861)
                    ·
                      refine ⟨343125745157298261189349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1830003974172257393009861 343125745157298261189349)
                      ·
                        rfl

theorem cell23_668235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 3, 1, 4].length) (baseStart_668235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_668235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_668235 prefixEnd_668235 := by exact prefixLift 668235
  have htrace : WordTrace (prefixWord ++ tailWord_668235) baseStart_668235 baseEnd_668235 := by
    simpa [prefixWord, tailWord_668235, baseEnd_668235] using wordTrace_append hprefix tailTrace_668235
  have hstable : (prefixWord ++ tailWord_668235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668235).length < 2 ^ (prefixWord ++ tailWord_668235).sum := by decide
  have hdescent : baseEnd_668235 < baseStart_668235 := by decide
  rcases family_descends (prefixWord ++ tailWord_668235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_668245 : List Nat := [1, 3, 2, 2, 1, 1, 4, 2, 1, 6]
def baseStart_668245 : Nat := 118140960795 + 668245 * 2 ^ 59
def prefixEnd_668245 : Nat := 4983230072969 + 3 ^ 40 * 668245 * 2
def baseEnd_668245 : Nat := 114376959987947740688101

theorem tailTrace_668245 : CollatzResearch.WordTrace tailWord_668245 prefixEnd_668245 114376959987947740688101 := by
  unfold tailWord_668245
  simp only [CollatzResearch.WordTrace]
  refine ⟨24372897464069967004982189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16248598309379978003321459 24372897464069967004982189)
  ·
    refine ⟨9139836549026237626868321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24372897464069967004982189 9139836549026237626868321)
    ·
      refine ⟨6854877411769678220151241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9139836549026237626868321 6854877411769678220151241)
      ·
        refine ⟨5141158058827258665113431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6854877411769678220151241 5141158058827258665113431)
        ·
          refine ⟨7711737088240887997670147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5141158058827258665113431 7711737088240887997670147)
          ·
            refine ⟨11567605632361331996505221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7711737088240887997670147 11567605632361331996505221)
            ·
              refine ⟨2168926056067749749344729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11567605632361331996505221 2168926056067749749344729)
              ·
                refine ⟨1626694542050812312008547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2168926056067749749344729 1626694542050812312008547)
                ·
                  refine ⟨2440041813076218468012821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1626694542050812312008547 2440041813076218468012821)
                  ·
                    refine ⟨114376959987947740688101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2440041813076218468012821 114376959987947740688101)
                    ·
                      rfl

theorem cell23_668245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 6].length) (baseStart_668245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_668245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_668245 prefixEnd_668245 := by exact prefixLift 668245
  have htrace : WordTrace (prefixWord ++ tailWord_668245) baseStart_668245 baseEnd_668245 := by
    simpa [prefixWord, tailWord_668245, baseEnd_668245] using wordTrace_append hprefix tailTrace_668245
  have hstable : (prefixWord ++ tailWord_668245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_668245).length < 2 ^ (prefixWord ++ tailWord_668245).sum := by decide
  have hdescent : baseEnd_668245 < baseStart_668245 := by decide
  rcases family_descends (prefixWord ++ tailWord_668245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
