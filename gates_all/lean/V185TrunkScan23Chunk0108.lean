import V185TrunkScan23Chunk0107

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_638391 : List Nat := [1, 1, 3, 1, 3, 2, 2, 2, 1, 3, 4]
def baseStart_638391 : Nat := 118140960795 + 638391 * 2 ^ 59
def prefixEnd_638391 : Nat := 4983230072969 + 3 ^ 40 * 638391 * 2
def baseEnd_638391 : Nat := 327801428504517025976599

theorem tailTrace_638391 : CollatzResearch.WordTrace tailWord_638391 prefixEnd_638391 327801428504517025976599 := by
  unfold tailWord_638391
  simp only [CollatzResearch.WordTrace]
  refine ⟨23284032630225910347707027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15522688420150606898471351 23284032630225910347707027)
  ·
    refine ⟨34926048945338865521560541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23284032630225910347707027 34926048945338865521560541)
    ·
      refine ⟨13097268354502074570585203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34926048945338865521560541 13097268354502074570585203)
      ·
        refine ⟨19645902531753111855877805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13097268354502074570585203 19645902531753111855877805)
        ·
          refine ⟨7367213449407416945954177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19645902531753111855877805 7367213449407416945954177)
          ·
            refine ⟨5525410087055562709465633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7367213449407416945954177 5525410087055562709465633)
            ·
              refine ⟨4144057565291672032099225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5525410087055562709465633 4144057565291672032099225)
              ·
                refine ⟨3108043173968754024074419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4144057565291672032099225 3108043173968754024074419)
                ·
                  refine ⟨4662064760953131036111629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3108043173968754024074419 4662064760953131036111629)
                  ·
                    refine ⟨1748274285357424138541861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4662064760953131036111629 1748274285357424138541861)
                    ·
                      refine ⟨327801428504517025976599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1748274285357424138541861 327801428504517025976599)
                      ·
                        rfl

theorem cell23_638391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 3, 4].length) (baseStart_638391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_638391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_638391 prefixEnd_638391 := by exact prefixLift 638391
  have htrace : WordTrace (prefixWord ++ tailWord_638391) baseStart_638391 baseEnd_638391 := by
    simpa [prefixWord, tailWord_638391, baseEnd_638391] using wordTrace_append hprefix tailTrace_638391
  have hstable : (prefixWord ++ tailWord_638391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638391).length < 2 ^ (prefixWord ++ tailWord_638391).sum := by decide
  have hdescent : baseEnd_638391 < baseStart_638391 := by decide
  rcases family_descends (prefixWord ++ tailWord_638391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638408 : List Nat := [2, 1, 3, 1, 3, 1, 1, 2, 1, 6, 2]
def baseStart_638408 : Nat := 118140960795 + 638408 * 2 ^ 59
def prefixEnd_638408 : Nat := 4983230072969 + 3 ^ 40 * 638408 * 2
def baseEnd_638408 : Nat := 327810157675643459464021

theorem tailTrace_638408 : CollatzResearch.WordTrace tailWord_638408 prefixEnd_638408 327810157675643459464021 := by
  unfold tailWord_638408
  simp only [CollatzResearch.WordTrace]
  refine ⟨11642326335582161125537939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15523101780776214834050585 11642326335582161125537939)
  ·
    refine ⟨17463489503373241688306909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11642326335582161125537939 17463489503373241688306909)
    ·
      refine ⟨6548808563764965633115091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17463489503373241688306909 6548808563764965633115091)
      ·
        refine ⟨9823212845647448449672637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6548808563764965633115091 9823212845647448449672637)
        ·
          refine ⟨3683704817117793168627239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9823212845647448449672637 3683704817117793168627239)
          ·
            refine ⟨5525557225676689752940859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3683704817117793168627239 5525557225676689752940859)
            ·
              refine ⟨8288335838515034629411289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5525557225676689752940859 8288335838515034629411289)
              ·
                refine ⟨6216251878886275972058467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8288335838515034629411289 6216251878886275972058467)
                ·
                  refine ⟨9324377818329413958087701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6216251878886275972058467 9324377818329413958087701)
                  ·
                    refine ⟨437080210234191279285361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9324377818329413958087701 437080210234191279285361)
                    ·
                      refine ⟨327810157675643459464021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 437080210234191279285361 327810157675643459464021)
                      ·
                        rfl

theorem cell23_638408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 1, 6, 2].length) (baseStart_638408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_638408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_638408 prefixEnd_638408 := by exact prefixLift 638408
  have htrace : WordTrace (prefixWord ++ tailWord_638408) baseStart_638408 baseEnd_638408 := by
    simpa [prefixWord, tailWord_638408, baseEnd_638408] using wordTrace_append hprefix tailTrace_638408
  have hstable : (prefixWord ++ tailWord_638408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638408).length < 2 ^ (prefixWord ++ tailWord_638408).sum := by decide
  have hdescent : baseEnd_638408 < baseStart_638408 := by decide
  rcases family_descends (prefixWord ++ tailWord_638408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638421 : List Nat := [1, 3, 2, 3, 1, 1, 1, 1, 1, 3, 6]
def baseStart_638421 : Nat := 118140960795 + 638421 * 2 ^ 59
def prefixEnd_638421 : Nat := 4983230072969 + 3 ^ 40 * 638421 * 2
def baseEnd_638421 : Nat := 327816832924151908601461

theorem tailTrace_638421 : CollatzResearch.WordTrace tailWord_638421 prefixEnd_638421 327816832924151908601461 := by
  unfold tailWord_638421
  simp only [CollatzResearch.WordTrace]
  refine ⟨23285126820117225471299117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15523417880078150314199411 23285126820117225471299117)
  ·
    refine ⟨8731922557543959551737169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23285126820117225471299117 8731922557543959551737169)
    ·
      refine ⟨6548941918157969663802877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8731922557543959551737169 6548941918157969663802877)
      ·
        refine ⟨2455853219309238623926079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6548941918157969663802877 2455853219309238623926079)
        ·
          refine ⟨3683779828963857935889119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2455853219309238623926079 3683779828963857935889119)
          ·
            refine ⟨5525669743445786903833679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3683779828963857935889119 5525669743445786903833679)
            ·
              refine ⟨8288504615168680355750519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5525669743445786903833679 8288504615168680355750519)
              ·
                refine ⟨12432756922753020533625779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8288504615168680355750519 12432756922753020533625779)
                ·
                  refine ⟨18649135384129530800438669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12432756922753020533625779 18649135384129530800438669)
                  ·
                    refine ⟨6993425769048574050164501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18649135384129530800438669 6993425769048574050164501)
                    ·
                      refine ⟨327816832924151908601461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6993425769048574050164501 327816832924151908601461)
                      ·
                        rfl

theorem cell23_638421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_638421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_638421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_638421 prefixEnd_638421 := by exact prefixLift 638421
  have htrace : WordTrace (prefixWord ++ tailWord_638421) baseStart_638421 baseEnd_638421 := by
    simpa [prefixWord, tailWord_638421, baseEnd_638421] using wordTrace_append hprefix tailTrace_638421
  have hstable : (prefixWord ++ tailWord_638421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638421).length < 2 ^ (prefixWord ++ tailWord_638421).sum := by decide
  have hdescent : baseEnd_638421 < baseStart_638421 := by decide
  rcases family_descends (prefixWord ++ tailWord_638421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638431 : List Nat := [1, 1, 2, 3, 3, 1, 3, 1, 8]
def baseStart_638431 : Nat := 118140960795 + 638431 * 2 ^ 59
def prefixEnd_638431 : Nat := 4983230072969 + 3 ^ 40 * 638431 * 2
def baseEnd_638431 : Nat := 36424663081188541052935

theorem tailTrace_638431 : CollatzResearch.WordTrace tailWord_638431 prefixEnd_638431 36424663081188541052935 := by
  unfold tailWord_638431
  simp only [CollatzResearch.WordTrace]
  refine ⟨23285491550080997179163147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15523661033387331452775431 23285491550080997179163147)
  ·
    refine ⟨34928237325121495768744721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23285491550080997179163147 34928237325121495768744721)
    ·
      refine ⟨26196177993841121826558541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34928237325121495768744721 26196177993841121826558541)
      ·
        refine ⟨9823566747690420684959453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26196177993841121826558541 9823566747690420684959453)
        ·
          refine ⟨3683837530383907756859795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9823566747690420684959453 3683837530383907756859795)
          ·
            refine ⟨5525756295575861635289693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3683837530383907756859795 5525756295575861635289693)
            ·
              refine ⟨2072158610840948113233635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5525756295575861635289693 2072158610840948113233635)
              ·
                refine ⟨3108237916261422169850453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2072158610840948113233635 3108237916261422169850453)
                ·
                  refine ⟨36424663081188541052935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3108237916261422169850453 36424663081188541052935)
                  ·
                    rfl

theorem cell23_638431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 8].length) (baseStart_638431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_638431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_638431 prefixEnd_638431 := by exact prefixLift 638431
  have htrace : WordTrace (prefixWord ++ tailWord_638431) baseStart_638431 baseEnd_638431 := by
    simpa [prefixWord, tailWord_638431, baseEnd_638431] using wordTrace_append hprefix tailTrace_638431
  have hstable : (prefixWord ++ tailWord_638431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638431).length < 2 ^ (prefixWord ++ tailWord_638431).sum := by decide
  have hdescent : baseEnd_638431 < baseStart_638431 := by decide
  rcases family_descends (prefixWord ++ tailWord_638431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638435 : List Nat := [1, 1, 1, 6, 2, 2, 2, 1, 3, 4]
def baseStart_638435 : Nat := 118140960795 + 638435 * 2 ^ 59
def prefixEnd_638435 : Nat := 4983230072969 + 3 ^ 40 * 638435 * 2
def baseEnd_638435 : Nat := 109274673884438284608799

theorem tailTrace_638435 : CollatzResearch.WordTrace tailWord_638435 prefixEnd_638435 109274673884438284608799 := by
  unfold tailWord_638435
  simp only [CollatzResearch.WordTrace]
  refine ⟨23285637442066505862308759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15523758294711003908205839 23285637442066505862308759)
  ·
    refine ⟨34928456163099758793463139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23285637442066505862308759 34928456163099758793463139)
    ·
      refine ⟨52392684244649638190194709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34928456163099758793463139 52392684244649638190194709)
      ·
        refine ⟨2455907073967951790165377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 52392684244649638190194709 2455907073967951790165377)
        ·
          refine ⟨1841930305475963842624033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2455907073967951790165377 1841930305475963842624033)
          ·
            refine ⟨1381447729106972881968025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1841930305475963842624033 1381447729106972881968025)
            ·
              refine ⟨1036085796830229661476019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1381447729106972881968025 1036085796830229661476019)
              ·
                refine ⟨1554128695245344492214029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1036085796830229661476019 1554128695245344492214029)
                ·
                  refine ⟨582798260717004184580261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1554128695245344492214029 582798260717004184580261)
                  ·
                    refine ⟨109274673884438284608799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 582798260717004184580261 109274673884438284608799)
                    ·
                      rfl

theorem cell23_638435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 3, 4].length) (baseStart_638435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_638435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_638435 prefixEnd_638435 := by exact prefixLift 638435
  have htrace : WordTrace (prefixWord ++ tailWord_638435) baseStart_638435 baseEnd_638435 := by
    simpa [prefixWord, tailWord_638435, baseEnd_638435] using wordTrace_append hprefix tailTrace_638435
  have hstable : (prefixWord ++ tailWord_638435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638435).length < 2 ^ (prefixWord ++ tailWord_638435).sum := by decide
  have hdescent : baseEnd_638435 < baseStart_638435 := by decide
  rcases family_descends (prefixWord ++ tailWord_638435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638485 : List Nat := [1, 3, 2, 1, 3, 2, 1, 1, 4, 3, 2]
def baseStart_638485 : Nat := 118140960795 + 638485 * 2 ^ 59
def prefixEnd_638485 : Nat := 4983230072969 + 3 ^ 40 * 638485 * 2
def baseEnd_638485 : Nat := 327849695686039658201167

theorem tailTrace_638485 : CollatzResearch.WordTrace tailWord_638485 prefixEnd_638485 327849695686039658201167 := by
  unfold tailWord_638485
  simp only [CollatzResearch.WordTrace]
  refine ⟨23287461091885364401628909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15524974061256909601085939 23287461091885364401628909)
  ·
    refine ⟨8732797909457011650610841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23287461091885364401628909 8732797909457011650610841)
    ·
      refine ⟨6549598432092758737958131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8732797909457011650610841 6549598432092758737958131)
      ·
        refine ⟨9824397648139138106937197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6549598432092758737958131 9824397648139138106937197)
        ·
          refine ⟨3684149118052176790101449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9824397648139138106937197 3684149118052176790101449)
          ·
            refine ⟨2763111838539132592576087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3684149118052176790101449 2763111838539132592576087)
            ·
              refine ⟨4144667757808698888864131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2763111838539132592576087 4144667757808698888864131)
              ·
                refine ⟨6217001636713048333296197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4144667757808698888864131 6217001636713048333296197)
                ·
                  refine ⟨1165687806883696562493037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6217001636713048333296197 1165687806883696562493037)
                  ·
                    refine ⟨437132927581386210934889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1165687806883696562493037 437132927581386210934889)
                    ·
                      refine ⟨327849695686039658201167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 437132927581386210934889 327849695686039658201167)
                      ·
                        rfl

theorem cell23_638485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 4, 3, 2].length) (baseStart_638485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_638485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_638485 prefixEnd_638485 := by exact prefixLift 638485
  have htrace : WordTrace (prefixWord ++ tailWord_638485) baseStart_638485 baseEnd_638485 := by
    simpa [prefixWord, tailWord_638485, baseEnd_638485] using wordTrace_append hprefix tailTrace_638485
  have hstable : (prefixWord ++ tailWord_638485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638485).length < 2 ^ (prefixWord ++ tailWord_638485).sum := by decide
  have hdescent : baseEnd_638485 < baseStart_638485 := by decide
  rcases family_descends (prefixWord ++ tailWord_638485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638515 : List Nat := [1, 1, 1, 2, 4, 3, 3, 2, 1, 1, 4]
def baseStart_638515 : Nat := 118140960795 + 638515 * 2 ^ 59
def prefixEnd_638515 : Nat := 4983230072969 + 3 ^ 40 * 638515 * 2
def baseEnd_638515 : Nat := 327865100105674540826029

theorem tailTrace_638515 : CollatzResearch.WordTrace tailWord_638515 prefixEnd_638515 327865100105674540826029 := by
  unfold tailWord_638515
  simp only [CollatzResearch.WordTrace]
  refine ⟨23288555281776679525220999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15525703521184453016813999 23288555281776679525220999)
  ·
    refine ⟨34932832922665019287831499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23288555281776679525220999 34932832922665019287831499)
    ·
      refine ⟨52399249383997528931747249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34932832922665019287831499 52399249383997528931747249)
      ·
        refine ⟨39299437037998146698810437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52399249383997528931747249 39299437037998146698810437)
        ·
          refine ⟨7368644444624652506026957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39299437037998146698810437 7368644444624652506026957)
          ·
            refine ⟨2763241666734244689760109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7368644444624652506026957 2763241666734244689760109)
            ·
              refine ⟨1036215625025341758660041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2763241666734244689760109 1036215625025341758660041)
              ·
                refine ⟨777161718769006318995031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1036215625025341758660041 777161718769006318995031)
                ·
                  refine ⟨1165742578153509478492547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 777161718769006318995031 1165742578153509478492547)
                  ·
                    refine ⟨1748613867230264217738821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1165742578153509478492547 1748613867230264217738821)
                    ·
                      refine ⟨327865100105674540826029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1748613867230264217738821 327865100105674540826029)
                      ·
                        rfl

theorem cell23_638515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 2, 1, 1, 4].length) (baseStart_638515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_638515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_638515 prefixEnd_638515 := by exact prefixLift 638515
  have htrace : WordTrace (prefixWord ++ tailWord_638515) baseStart_638515 baseEnd_638515 := by
    simpa [prefixWord, tailWord_638515, baseEnd_638515] using wordTrace_append hprefix tailTrace_638515
  have hstable : (prefixWord ++ tailWord_638515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638515).length < 2 ^ (prefixWord ++ tailWord_638515).sum := by decide
  have hdescent : baseEnd_638515 < baseStart_638515 := by decide
  rcases family_descends (prefixWord ++ tailWord_638515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638525 : List Nat := [1, 4, 1, 3, 3, 1, 1, 2, 1, 6]
def baseStart_638525 : Nat := 118140960795 + 638525 * 2 ^ 59
def prefixEnd_638525 : Nat := 4983230072969 + 3 ^ 40 * 638525 * 2
def baseEnd_638525 : Nat := 109290078304073167233661

theorem tailTrace_638525 : CollatzResearch.WordTrace tailWord_638525 prefixEnd_638525 109290078304073167233661 := by
  unfold tailWord_638525
  simp only [CollatzResearch.WordTrace]
  refine ⟨23288920011740451233085029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15525946674493634155390019 23288920011740451233085029)
  ·
    refine ⟨4366672502201334606203443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23288920011740451233085029 4366672502201334606203443)
    ·
      refine ⟨6550008753302001909305165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4366672502201334606203443 6550008753302001909305165)
      ·
        refine ⟨2456253282488250715989437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6550008753302001909305165 2456253282488250715989437)
        ·
          refine ⟨921094980933094018496039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2456253282488250715989437 921094980933094018496039)
          ·
            refine ⟨1381642471399641027744059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 921094980933094018496039 1381642471399641027744059)
            ·
              refine ⟨2072463707099461541616089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1381642471399641027744059 2072463707099461541616089)
              ·
                refine ⟨1554347780324596156212067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2072463707099461541616089 1554347780324596156212067)
                ·
                  refine ⟨2331521670486894234318101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1554347780324596156212067 2331521670486894234318101)
                  ·
                    refine ⟨109290078304073167233661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2331521670486894234318101 109290078304073167233661)
                    ·
                      rfl

theorem cell23_638525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 6].length) (baseStart_638525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_638525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_638525 prefixEnd_638525 := by exact prefixLift 638525
  have htrace : WordTrace (prefixWord ++ tailWord_638525) baseStart_638525 baseEnd_638525 := by
    simpa [prefixWord, tailWord_638525, baseEnd_638525] using wordTrace_append hprefix tailTrace_638525
  have hstable : (prefixWord ++ tailWord_638525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638525).length < 2 ^ (prefixWord ++ tailWord_638525).sum := by decide
  have hdescent : baseEnd_638525 < baseStart_638525 := by decide
  rcases family_descends (prefixWord ++ tailWord_638525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638565 : List Nat := [1, 3, 1, 3, 3, 1, 1, 3, 1, 3, 3]
def baseStart_638565 : Nat := 118140960795 + 638565 * 2 ^ 59
def prefixEnd_638565 : Nat := 4983230072969 + 3 ^ 40 * 638565 * 2
def baseEnd_638565 : Nat := 327890774138399345200799

theorem tailTrace_638565 : CollatzResearch.WordTrace tailWord_638565 prefixEnd_638565 327890774138399345200799 := by
  unfold tailWord_638565
  simp only [CollatzResearch.WordTrace]
  refine ⟨23290378931595538064541149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15526919287730358709694099 23290378931595538064541149)
  ·
    refine ⟨8733892099348326774202931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23290378931595538064541149 8733892099348326774202931)
    ·
      refine ⟨13100838149022490161304397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8733892099348326774202931 13100838149022490161304397)
      ·
        refine ⟨4912814305883433810489149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13100838149022490161304397 4912814305883433810489149)
        ·
          refine ⟨1842305364706287678933431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4912814305883433810489149 1842305364706287678933431)
          ·
            refine ⟨2763458047059431518400147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1842305364706287678933431 2763458047059431518400147)
            ·
              refine ⟨4145187070589147277600221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2763458047059431518400147 4145187070589147277600221)
              ·
                refine ⟨1554445151470930229100083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4145187070589147277600221 1554445151470930229100083)
                ·
                  refine ⟨2331667727206395343650125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1554445151470930229100083 2331667727206395343650125)
                  ·
                    refine ⟨874375397702398253868797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2331667727206395343650125 874375397702398253868797)
                    ·
                      refine ⟨327890774138399345200799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 874375397702398253868797 327890774138399345200799)
                      ·
                        rfl

theorem cell23_638565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_638565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_638565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_638565 prefixEnd_638565 := by exact prefixLift 638565
  have htrace : WordTrace (prefixWord ++ tailWord_638565) baseStart_638565 baseEnd_638565 := by
    simpa [prefixWord, tailWord_638565, baseEnd_638565] using wordTrace_append hprefix tailTrace_638565
  have hstable : (prefixWord ++ tailWord_638565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638565).length < 2 ^ (prefixWord ++ tailWord_638565).sum := by decide
  have hdescent : baseEnd_638565 < baseStart_638565 := by decide
  rcases family_descends (prefixWord ++ tailWord_638565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638582 : List Nat := [5, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3]
def baseStart_638582 : Nat := 118140960795 + 638582 * 2 ^ 59
def prefixEnd_638582 : Nat := 4983230072969 + 3 ^ 40 * 638582 * 2
def baseEnd_638582 : Nat := 327899503309525778688221

theorem tailTrace_638582 : CollatzResearch.WordTrace tailWord_638582 prefixEnd_638582 327899503309525778688221 := by
  unfold tailWord_638582
  simp only [CollatzResearch.WordTrace]
  refine ⟨1455687435783371872994375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15527332648355966645273333 1455687435783371872994375)
  ·
    refine ⟨2183531153675057809491563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1455687435783371872994375 2183531153675057809491563)
    ·
      refine ⟨3275296730512586714237345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2183531153675057809491563 3275296730512586714237345)
      ·
        refine ⟨2456472547884440035678009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3275296730512586714237345 2456472547884440035678009)
        ·
          refine ⟨1842354410913330026758507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2456472547884440035678009 1842354410913330026758507)
          ·
            refine ⟨2763531616369995040137761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1842354410913330026758507 2763531616369995040137761)
            ·
              refine ⟨2072648712277496280103321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2763531616369995040137761 2072648712277496280103321)
              ·
                refine ⟨1554486534208122210077491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2072648712277496280103321 1554486534208122210077491)
                ·
                  refine ⟨2331729801312183315116237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1554486534208122210077491 2331729801312183315116237)
                  ·
                    refine ⟨874398675492068743168589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2331729801312183315116237 874398675492068743168589)
                    ·
                      refine ⟨327899503309525778688221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 874398675492068743168589 327899503309525778688221)
                      ·
                        rfl

theorem cell23_638582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_638582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_638582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_638582 prefixEnd_638582 := by exact prefixLift 638582
  have htrace : WordTrace (prefixWord ++ tailWord_638582) baseStart_638582 baseEnd_638582 := by
    simpa [prefixWord, tailWord_638582, baseEnd_638582] using wordTrace_append hprefix tailTrace_638582
  have hstable : (prefixWord ++ tailWord_638582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638582).length < 2 ^ (prefixWord ++ tailWord_638582).sum := by decide
  have hdescent : baseEnd_638582 < baseStart_638582 := by decide
  rcases family_descends (prefixWord ++ tailWord_638582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638592 : List Nat := [2, 1, 1, 2, 1, 4, 3, 3, 1, 3, 2]
def baseStart_638592 : Nat := 118140960795 + 638592 * 2 ^ 59
def prefixEnd_638592 : Nat := 4983230072969 + 3 ^ 40 * 638592 * 2
def baseEnd_638592 : Nat := 327904638116070739563175

theorem tailTrace_638592 : CollatzResearch.WordTrace tailWord_638592 prefixEnd_638592 327904638116070739563175 := by
  unfold tailWord_638592
  simp only [CollatzResearch.WordTrace]
  refine ⟨11645681851248860837887015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15527575801665147783849353 11645681851248860837887015)
  ·
    refine ⟨17468522776873291256830523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11645681851248860837887015 17468522776873291256830523)
    ·
      refine ⟨26202784165309936885245785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17468522776873291256830523 26202784165309936885245785)
      ·
        refine ⟨19652088123982452663934339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26202784165309936885245785 19652088123982452663934339)
        ·
          refine ⟨29478132185973678995901509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19652088123982452663934339 29478132185973678995901509)
          ·
            refine ⟨5527149784870064811731533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29478132185973678995901509 5527149784870064811731533)
            ·
              refine ⟨2072681169326274304399325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5527149784870064811731533 2072681169326274304399325)
              ·
                refine ⟨777255438497352864149747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2072681169326274304399325 777255438497352864149747)
                ·
                  refine ⟨1165883157746029296224621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 777255438497352864149747 1165883157746029296224621)
                  ·
                    refine ⟨437206184154760986084233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1165883157746029296224621 437206184154760986084233)
                    ·
                      refine ⟨327904638116070739563175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 437206184154760986084233 327904638116070739563175)
                      ·
                        rfl

theorem cell23_638592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 3, 1, 3, 2].length) (baseStart_638592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_638592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_638592 prefixEnd_638592 := by exact prefixLift 638592
  have htrace : WordTrace (prefixWord ++ tailWord_638592) baseStart_638592 baseEnd_638592 := by
    simpa [prefixWord, tailWord_638592, baseEnd_638592] using wordTrace_append hprefix tailTrace_638592
  have hstable : (prefixWord ++ tailWord_638592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638592).length < 2 ^ (prefixWord ++ tailWord_638592).sum := by decide
  have hdescent : baseEnd_638592 < baseStart_638592 := by decide
  rcases family_descends (prefixWord ++ tailWord_638592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638599 : List Nat := [1, 1, 4, 2, 1, 5, 1, 2, 2, 1, 3]
def baseStart_638599 : Nat := 118140960795 + 638599 * 2 ^ 59
def prefixEnd_638599 : Nat := 4983230072969 + 3 ^ 40 * 638599 * 2
def baseEnd_638599 : Nat := 327908232480652212175643

theorem tailTrace_638599 : CollatzResearch.WordTrace tailWord_638599 prefixEnd_638599 327908232480652212175643 := by
  unfold tailWord_638599
  simp only [CollatzResearch.WordTrace]
  refine ⟨23291619013472361871278851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15527746008981574580852567 23291619013472361871278851)
  ·
    refine ⟨34937428520208542806918277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23291619013472361871278851 34937428520208542806918277)
    ·
      refine ⟨6550767847539101776297177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34937428520208542806918277 6550767847539101776297177)
      ·
        refine ⟨4913075885654326332222883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6550767847539101776297177 4913075885654326332222883)
        ·
          refine ⟨7369613828481489498334325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4913075885654326332222883 7369613828481489498334325)
          ·
            refine ⟨690901296420139640468843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7369613828481489498334325 690901296420139640468843)
            ·
              refine ⟨1036351944630209460703265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 690901296420139640468843 1036351944630209460703265)
              ·
                refine ⟨777263958472657095527449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1036351944630209460703265 777263958472657095527449)
                ·
                  refine ⟨582947968854492821645587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 777263958472657095527449 582947968854492821645587)
                  ·
                    refine ⟨874421953281739232468381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 582947968854492821645587 874421953281739232468381)
                    ·
                      refine ⟨327908232480652212175643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 874421953281739232468381 327908232480652212175643)
                      ·
                        rfl

theorem cell23_638599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_638599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_638599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_638599 prefixEnd_638599 := by exact prefixLift 638599
  have htrace : WordTrace (prefixWord ++ tailWord_638599) baseStart_638599 baseEnd_638599 := by
    simpa [prefixWord, tailWord_638599, baseEnd_638599] using wordTrace_append hprefix tailTrace_638599
  have hstable : (prefixWord ++ tailWord_638599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638599).length < 2 ^ (prefixWord ++ tailWord_638599).sum := by decide
  have hdescent : baseEnd_638599 < baseStart_638599 := by decide
  rcases family_descends (prefixWord ++ tailWord_638599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638608 : List Nat := [2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 3]
def baseStart_638608 : Nat := 118140960795 + 638608 * 2 ^ 59
def prefixEnd_638608 : Nat := 4983230072969 + 3 ^ 40 * 638608 * 2
def baseEnd_638608 : Nat := 327912853806542676963101

theorem tailTrace_638608 : CollatzResearch.WordTrace tailWord_638608 prefixEnd_638608 327912853806542676963101 := by
  unfold tailWord_638608
  simp only [CollatzResearch.WordTrace]
  refine ⟨11645973635219878204178239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15527964846959837605570985 11645973635219878204178239)
  ·
    refine ⟨17468960452829817306267359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11645973635219878204178239 17468960452829817306267359)
    ·
      refine ⟨26203440679244725959401039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17468960452829817306267359 26203440679244725959401039)
      ·
        refine ⟨39305161018867088939101559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26203440679244725959401039 39305161018867088939101559)
        ·
          refine ⟨58957741528300633408652339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39305161018867088939101559 58957741528300633408652339)
          ·
            refine ⟨88436612292450950112978509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58957741528300633408652339 88436612292450950112978509)
            ·
              refine ⟨33163729609669106292366941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88436612292450950112978509 33163729609669106292366941)
              ·
                refine ⟨12436398603625914859637603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33163729609669106292366941 12436398603625914859637603)
                ·
                  refine ⟨18654597905438872289456405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12436398603625914859637603 18654597905438872289456405)
                  ·
                    refine ⟨874434276817447138568269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18654597905438872289456405 874434276817447138568269)
                    ·
                      refine ⟨327912853806542676963101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 874434276817447138568269 327912853806542676963101)
                      ·
                        rfl

theorem cell23_638608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 3].length) (baseStart_638608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_638608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_638608 prefixEnd_638608 := by exact prefixLift 638608
  have htrace : WordTrace (prefixWord ++ tailWord_638608) baseStart_638608 baseEnd_638608 := by
    simpa [prefixWord, tailWord_638608, baseEnd_638608] using wordTrace_append hprefix tailTrace_638608
  have hstable : (prefixWord ++ tailWord_638608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638608).length < 2 ^ (prefixWord ++ tailWord_638608).sum := by decide
  have hdescent : baseEnd_638608 < baseStart_638608 := by decide
  rcases family_descends (prefixWord ++ tailWord_638608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638688 : List Nat := [2, 1, 1, 3, 1, 2, 2, 1, 2, 8]
def baseStart_638688 : Nat := 118140960795 + 638688 * 2 ^ 59
def prefixEnd_638688 : Nat := 4983230072969 + 3 ^ 40 * 638688 * 2
def baseEnd_638688 : Nat := 109317977419634121320911

theorem tailTrace_638688 : CollatzResearch.WordTrace tailWord_638688 prefixEnd_638688 109317977419634121320911 := by
  unfold tailWord_638688
  simp only [CollatzResearch.WordTrace]
  refine ⟨11647432555074965035634359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15529910073433286714179145 11647432555074965035634359)
  ·
    refine ⟨17471148832612447553451539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11647432555074965035634359 17471148832612447553451539)
    ·
      refine ⟨26206723248918671330177309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17471148832612447553451539 26206723248918671330177309)
      ·
        refine ⟨9827521218344501748816491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26206723248918671330177309 9827521218344501748816491)
        ·
          refine ⟨14741281827516752623224737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9827521218344501748816491 14741281827516752623224737)
          ·
            refine ⟨11055961370637564467418553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14741281827516752623224737 11055961370637564467418553)
            ·
              refine ⟨8291971027978173350563915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11055961370637564467418553 8291971027978173350563915)
              ·
                refine ⟨12437956541967260025845873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8291971027978173350563915 12437956541967260025845873)
                ·
                  refine ⟨9328467406475445019384405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12437956541967260025845873 9328467406475445019384405)
                  ·
                    refine ⟨109317977419634121320911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 9328467406475445019384405 109317977419634121320911)
                    ·
                      rfl

theorem cell23_638688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 2, 8].length) (baseStart_638688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_638688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_638688 prefixEnd_638688 := by exact prefixLift 638688
  have htrace : WordTrace (prefixWord ++ tailWord_638688) baseStart_638688 baseEnd_638688 := by
    simpa [prefixWord, tailWord_638688, baseEnd_638688] using wordTrace_append hprefix tailTrace_638688
  have hstable : (prefixWord ++ tailWord_638688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638688).length < 2 ^ (prefixWord ++ tailWord_638688).sum := by decide
  have hdescent : baseEnd_638688 < baseStart_638688 := by decide
  rcases family_descends (prefixWord ++ tailWord_638688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638715 : List Nat := [1, 1, 1, 1, 1, 3, 1, 5, 4, 2, 3]
def baseStart_638715 : Nat := 118140960795 + 638715 * 2 ^ 59
def prefixEnd_638715 : Nat := 4983230072969 + 3 ^ 40 * 638715 * 2
def baseEnd_638715 : Nat := 327967796236573758325109

theorem tailTrace_638715 : CollatzResearch.WordTrace tailWord_638715 prefixEnd_638715 327967796236573758325109 := by
  unfold tailWord_638715
  simp only [CollatzResearch.WordTrace]
  refine ⟨23295849881052113682501599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15530566587368075788334399 23295849881052113682501599)
  ·
    refine ⟨34943774821578170523752399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23295849881052113682501599 34943774821578170523752399)
    ·
      refine ⟨52415662232367255785628599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34943774821578170523752399 52415662232367255785628599)
      ·
        refine ⟨78623493348550883678442899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52415662232367255785628599 78623493348550883678442899)
        ·
          refine ⟨117935240022826325517664349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78623493348550883678442899 117935240022826325517664349)
          ·
            refine ⟨44225715008559872069124131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117935240022826325517664349 44225715008559872069124131)
            ·
              refine ⟨66338572512839808103686197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44225715008559872069124131 66338572512839808103686197)
              ·
                refine ⟨6219241173078732009720581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66338572512839808103686197 6219241173078732009720581)
                ·
                  refine ⟨1166107719952262251822609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6219241173078732009720581 1166107719952262251822609)
                  ·
                    refine ⟨874580789964196688866957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1166107719952262251822609 874580789964196688866957)
                    ·
                      refine ⟨327967796236573758325109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 874580789964196688866957 327967796236573758325109)
                      ·
                        rfl

theorem cell23_638715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 4, 2, 3].length) (baseStart_638715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_638715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_638715 prefixEnd_638715 := by exact prefixLift 638715
  have htrace : WordTrace (prefixWord ++ tailWord_638715) baseStart_638715 baseEnd_638715 := by
    simpa [prefixWord, tailWord_638715, baseEnd_638715] using wordTrace_append hprefix tailTrace_638715
  have hstable : (prefixWord ++ tailWord_638715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638715).length < 2 ^ (prefixWord ++ tailWord_638715).sum := by decide
  have hdescent : baseEnd_638715 < baseStart_638715 := by decide
  rcases family_descends (prefixWord ++ tailWord_638715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638756 : List Nat := [2, 3, 1, 3, 2, 2, 2, 3, 1, 4]
def baseStart_638756 : Nat := 118140960795 + 638756 * 2 ^ 59
def prefixEnd_638756 : Nat := 4983230072969 + 3 ^ 40 * 638756 * 2
def baseEnd_638756 : Nat := 109329616314469365970807

theorem tailTrace_638756 : CollatzResearch.WordTrace tailWord_638756 prefixEnd_638756 109329616314469365970807 := by
  unfold tailWord_638756
  simp only [CollatzResearch.WordTrace]
  refine ⟨11648672636951788842372061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15531563515935718456496081 11648672636951788842372061)
  ·
    refine ⟨4368252238856920815889523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11648672636951788842372061 4368252238856920815889523)
    ·
      refine ⟨6552378358285381223834285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4368252238856920815889523 6552378358285381223834285)
      ·
        refine ⟨2457141884357017958937857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6552378358285381223834285 2457141884357017958937857)
        ·
          refine ⟨1842856413267763469203393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2457141884357017958937857 1842856413267763469203393)
          ·
            refine ⟨1382142309950822601902545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1842856413267763469203393 1382142309950822601902545)
            ·
              refine ⟨1036606732463116951426909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1382142309950822601902545 1036606732463116951426909)
              ·
                refine ⟨388727524673668856785091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1036606732463116951426909 388727524673668856785091)
                ·
                  refine ⟨583091287010503285177637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 388727524673668856785091 583091287010503285177637)
                  ·
                    refine ⟨109329616314469365970807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 583091287010503285177637 109329616314469365970807)
                    ·
                      rfl

theorem cell23_638756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 3, 1, 4].length) (baseStart_638756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_638756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_638756 prefixEnd_638756 := by exact prefixLift 638756
  have htrace : WordTrace (prefixWord ++ tailWord_638756) baseStart_638756 baseEnd_638756 := by
    simpa [prefixWord, tailWord_638756, baseEnd_638756] using wordTrace_append hprefix tailTrace_638756
  have hstable : (prefixWord ++ tailWord_638756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638756).length < 2 ^ (prefixWord ++ tailWord_638756).sum := by decide
  have hdescent : baseEnd_638756 < baseStart_638756 := by decide
  rcases family_descends (prefixWord ++ tailWord_638756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638772 : List Nat := [2, 5, 1, 1, 2, 1, 1, 1, 1, 2, 6]
def baseStart_638772 : Nat := 118140960795 + 638772 * 2 ^ 59
def prefixEnd_638772 : Nat := 4983230072969 + 3 ^ 40 * 638772 * 2
def baseEnd_638772 : Nat := 327997064633880035312347

theorem tailTrace_638772 : CollatzResearch.WordTrace tailWord_638772 prefixEnd_638772 327997064633880035312347 := by
  unfold tailWord_638772
  simp only [CollatzResearch.WordTrace]
  refine ⟨11648964420922806208663285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15531952561230408278217713 11648964420922806208663285)
  ·
    refine ⟨1092090414461513082062183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11648964420922806208663285 1092090414461513082062183)
    ·
      refine ⟨1638135621692269623093275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1092090414461513082062183 1638135621692269623093275)
      ·
        refine ⟨2457203432538404434639913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1638135621692269623093275 2457203432538404434639913)
        ·
          refine ⟨1842902574403803325979935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2457203432538404434639913 1842902574403803325979935)
          ·
            refine ⟨2764353861605704988969903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1842902574403803325979935 2764353861605704988969903)
            ·
              refine ⟨4146530792408557483454855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2764353861605704988969903 4146530792408557483454855)
              ·
                refine ⟨6219796188612836225182283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4146530792408557483454855 6219796188612836225182283)
                ·
                  refine ⟨9329694282919254337773425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6219796188612836225182283 9329694282919254337773425)
                  ·
                    refine ⟨6997270712189440753330069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9329694282919254337773425 6997270712189440753330069)
                    ·
                      refine ⟨327997064633880035312347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6997270712189440753330069 327997064633880035312347)
                      ·
                        rfl

theorem cell23_638772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_638772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_638772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_638772 prefixEnd_638772 := by exact prefixLift 638772
  have htrace : WordTrace (prefixWord ++ tailWord_638772) baseStart_638772 baseEnd_638772 := by
    simpa [prefixWord, tailWord_638772, baseEnd_638772] using wordTrace_append hprefix tailTrace_638772
  have hstable : (prefixWord ++ tailWord_638772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638772).length < 2 ^ (prefixWord ++ tailWord_638772).sum := by decide
  have hdescent : baseEnd_638772 < baseStart_638772 := by decide
  rcases family_descends (prefixWord ++ tailWord_638772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638830 : List Nat := [4, 1, 2, 3, 1, 2, 3, 2, 1, 1, 3]
def baseStart_638830 : Nat := 118140960795 + 638830 * 2 ^ 59
def prefixEnd_638830 : Nat := 4983230072969 + 3 ^ 40 * 638830 * 2
def baseEnd_638830 : Nat := 328026846511840808387081

theorem tailTrace_638830 : CollatzResearch.WordTrace tailWord_638830 prefixEnd_638830 328026846511840808387081 := by
  unfold tailWord_638830
  simp only [CollatzResearch.WordTrace]
  refine ⟨2912505534454436040367243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15533362850423658881958629 2912505534454436040367243)
  ·
    refine ⟨4368758301681654060550865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2912505534454436040367243 4368758301681654060550865)
    ·
      refine ⟨3276568726261240545413149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4368758301681654060550865 3276568726261240545413149)
      ·
        refine ⟨1228713272347965204529931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3276568726261240545413149 1228713272347965204529931)
        ·
          refine ⟨1843069908521947806794897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1228713272347965204529931 1843069908521947806794897)
          ·
            refine ⟨1382302431391460855096173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1843069908521947806794897 1382302431391460855096173)
            ·
              refine ⟨518363411771797820661065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1382302431391460855096173 518363411771797820661065)
              ·
                refine ⟨388772558828848365495799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 518363411771797820661065 388772558828848365495799)
                ·
                  refine ⟨583158838243272548243699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 388772558828848365495799 583158838243272548243699)
                  ·
                    refine ⟨874738257364908822365549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 583158838243272548243699 874738257364908822365549)
                    ·
                      refine ⟨328026846511840808387081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 874738257364908822365549 328026846511840808387081)
                      ·
                        rfl

theorem cell23_638830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_638830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_638830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_638830 prefixEnd_638830 := by exact prefixLift 638830
  have htrace : WordTrace (prefixWord ++ tailWord_638830) baseStart_638830 baseEnd_638830 := by
    simpa [prefixWord, tailWord_638830, baseEnd_638830] using wordTrace_append hprefix tailTrace_638830
  have hstable : (prefixWord ++ tailWord_638830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638830).length < 2 ^ (prefixWord ++ tailWord_638830).sum := by decide
  have hdescent : baseEnd_638830 < baseStart_638830 := by decide
  rcases family_descends (prefixWord ++ tailWord_638830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638845 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 1, 4, 6]
def baseStart_638845 : Nat := 118140960795 + 638845 * 2 ^ 59
def prefixEnd_638845 : Nat := 4983230072969 + 3 ^ 40 * 638845 * 2
def baseEnd_638845 : Nat := 328034548721658249699511

theorem tailTrace_638845 : CollatzResearch.WordTrace tailWord_638845 prefixEnd_638845 328034548721658249699511 := by
  unfold tailWord_638845
  simp only [CollatzResearch.WordTrace]
  refine ⟨23300591370581145884733989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15533727580387430589822659 23300591370581145884733989)
  ·
    refine ⟨4368860881983964853387623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23300591370581145884733989 4368860881983964853387623)
    ·
      refine ⟨6553291322975947280081435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4368860881983964853387623 6553291322975947280081435)
      ·
        refine ⟨9829936984463920920122153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6553291322975947280081435 9829936984463920920122153)
        ·
          refine ⟨7372452738347940690091615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9829936984463920920122153 7372452738347940690091615)
          ·
            refine ⟨11058679107521911035137423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7372452738347940690091615 11058679107521911035137423)
            ·
              refine ⟨16588018661282866552706135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11058679107521911035137423 16588018661282866552706135)
              ·
                refine ⟨24882027991924299829059203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16588018661282866552706135 24882027991924299829059203)
                ·
                  refine ⟨37323041987886449743588805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24882027991924299829059203 37323041987886449743588805)
                  ·
                    refine ⟨6998070372728709326922901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37323041987886449743588805 6998070372728709326922901)
                    ·
                      refine ⟨328034548721658249699511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6998070372728709326922901 328034548721658249699511)
                      ·
                        rfl

theorem cell23_638845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_638845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_638845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_638845 prefixEnd_638845 := by exact prefixLift 638845
  have htrace : WordTrace (prefixWord ++ tailWord_638845) baseStart_638845 baseEnd_638845 := by
    simpa [prefixWord, tailWord_638845, baseEnd_638845] using wordTrace_append hprefix tailTrace_638845
  have hstable : (prefixWord ++ tailWord_638845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638845).length < 2 ^ (prefixWord ++ tailWord_638845).sum := by decide
  have hdescent : baseEnd_638845 < baseStart_638845 := by decide
  rcases family_descends (prefixWord ++ tailWord_638845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638865 : List Nat := [1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 5]
def baseStart_638865 : Nat := 118140960795 + 638865 * 2 ^ 59
def prefixEnd_638865 : Nat := 4983230072969 + 3 ^ 40 * 638865 * 2
def baseEnd_638865 : Nat := 328044818334748171449419

theorem tailTrace_638865 : CollatzResearch.WordTrace tailWord_638865 prefixEnd_638865 328044818334748171449419 := by
  unfold tailWord_638865
  simp only [CollatzResearch.WordTrace]
  refine ⟨23301320830508689300462049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15534213887005792866974699 23301320830508689300462049)
  ·
    refine ⟨17475990622881516975346537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23301320830508689300462049 17475990622881516975346537)
    ·
      refine ⟨13106992967161137731509903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17475990622881516975346537 13106992967161137731509903)
      ·
        refine ⟨19660489450741706597264855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13106992967161137731509903 19660489450741706597264855)
        ·
          refine ⟨29490734176112559895897283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19660489450741706597264855 29490734176112559895897283)
          ·
            refine ⟨44236101264168839843845925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29490734176112559895897283 44236101264168839843845925)
            ·
              refine ⟨8294268987031657470721111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44236101264168839843845925 8294268987031657470721111)
              ·
                refine ⟨12441403480547486206081667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8294268987031657470721111 12441403480547486206081667)
                ·
                  refine ⟨18662105220821229309122501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12441403480547486206081667 18662105220821229309122501)
                  ·
                    refine ⟨3499144728903980495460469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18662105220821229309122501 3499144728903980495460469)
                    ·
                      refine ⟨328044818334748171449419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3499144728903980495460469 328044818334748171449419)
                      ·
                        rfl

theorem cell23_638865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 5].length) (baseStart_638865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_638865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_638865 prefixEnd_638865 := by exact prefixLift 638865
  have htrace : WordTrace (prefixWord ++ tailWord_638865) baseStart_638865 baseEnd_638865 := by
    simpa [prefixWord, tailWord_638865, baseEnd_638865] using wordTrace_append hprefix tailTrace_638865
  have hstable : (prefixWord ++ tailWord_638865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638865).length < 2 ^ (prefixWord ++ tailWord_638865).sum := by decide
  have hdescent : baseEnd_638865 < baseStart_638865 := by decide
  rcases family_descends (prefixWord ++ tailWord_638865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638885 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 3, 8]
def baseStart_638885 : Nat := 118140960795 + 638885 * 2 ^ 59
def prefixEnd_638885 : Nat := 4983230072969 + 3 ^ 40 * 638885 * 2
def baseEnd_638885 : Nat := 109351695982612697733109

theorem tailTrace_638885 : CollatzResearch.WordTrace tailWord_638885 prefixEnd_638885 109351695982612697733109 := by
  unfold tailWord_638885
  simp only [CollatzResearch.WordTrace]
  refine ⟨23302050290436232716190109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15534700193624155144126739 23302050290436232716190109)
  ·
    refine ⟨8738268858913587268571291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23302050290436232716190109 8738268858913587268571291)
    ·
      refine ⟨13107403288370380902856937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8738268858913587268571291 13107403288370380902856937)
      ·
        refine ⟨9830552466277785677142703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13107403288370380902856937 9830552466277785677142703)
        ·
          refine ⟨14745828699416678515714055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9830552466277785677142703 14745828699416678515714055)
          ·
            refine ⟨22118743049125017773571083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14745828699416678515714055 22118743049125017773571083)
            ·
              refine ⟨33178114573687526660356625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22118743049125017773571083 33178114573687526660356625)
              ·
                refine ⟨24883585930265644995267469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33178114573687526660356625 24883585930265644995267469)
                ·
                  refine ⟨9331344723849616873225301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24883585930265644995267469 9331344723849616873225301)
                  ·
                    refine ⟨109351695982612697733109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 9331344723849616873225301 109351695982612697733109)
                    ·
                      rfl

theorem cell23_638885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 8].length) (baseStart_638885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_638885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_638885 prefixEnd_638885 := by exact prefixLift 638885
  have htrace : WordTrace (prefixWord ++ tailWord_638885) baseStart_638885 baseEnd_638885 := by
    simpa [prefixWord, tailWord_638885, baseEnd_638885] using wordTrace_append hprefix tailTrace_638885
  have hstable : (prefixWord ++ tailWord_638885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638885).length < 2 ^ (prefixWord ++ tailWord_638885).sum := by decide
  have hdescent : baseEnd_638885 < baseStart_638885 := by decide
  rcases family_descends (prefixWord ++ tailWord_638885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638887 : List Nat := [1, 1, 6, 1, 2, 3, 2, 2, 1, 2, 2]
def baseStart_638887 : Nat := 118140960795 + 638887 * 2 ^ 59
def prefixEnd_638887 : Nat := 4983230072969 + 3 ^ 40 * 638887 * 2
def baseEnd_638887 : Nat := 328056114909147085374319

theorem tailTrace_638887 : CollatzResearch.WordTrace tailWord_638887 prefixEnd_638887 328056114909147085374319 := by
  unfold tailWord_638887
  simp only [CollatzResearch.WordTrace]
  refine ⟨23302123236428987057762915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15534748824285991371841943 23302123236428987057762915)
  ·
    refine ⟨34953184854643480586644373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23302123236428987057762915 34953184854643480586644373)
    ·
      refine ⟨1638430540061413152498955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 34953184854643480586644373 1638430540061413152498955)
      ·
        refine ⟨2457645810092119728748433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1638430540061413152498955 2457645810092119728748433)
        ·
          refine ⟨1843234357569089796561325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2457645810092119728748433 1843234357569089796561325)
          ·
            refine ⟨691212884088408673710497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1843234357569089796561325 691212884088408673710497)
            ·
              refine ⟨518409663066306505282873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 691212884088408673710497 518409663066306505282873)
              ·
                refine ⟨388807247299729878962155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 518409663066306505282873 388807247299729878962155)
                ·
                  refine ⟨583210870949594818443233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 388807247299729878962155 583210870949594818443233)
                  ·
                    refine ⟨437408153212196113832425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 583210870949594818443233 437408153212196113832425)
                    ·
                      refine ⟨328056114909147085374319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 437408153212196113832425 328056114909147085374319)
                      ·
                        rfl

theorem cell23_638887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_638887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_638887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_638887 prefixEnd_638887 := by exact prefixLift 638887
  have htrace : WordTrace (prefixWord ++ tailWord_638887) baseStart_638887 baseEnd_638887 := by
    simpa [prefixWord, tailWord_638887, baseEnd_638887] using wordTrace_append hprefix tailTrace_638887
  have hstable : (prefixWord ++ tailWord_638887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638887).length < 2 ^ (prefixWord ++ tailWord_638887).sum := by decide
  have hdescent : baseEnd_638887 < baseStart_638887 := by decide
  rcases family_descends (prefixWord ++ tailWord_638887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638912 : List Nat := [2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 3]
def baseStart_638912 : Nat := 118140960795 + 638912 * 2 ^ 59
def prefixEnd_638912 : Nat := 4983230072969 + 3 ^ 40 * 638912 * 2
def baseEnd_638912 : Nat := 328068951925509487561703

theorem tailTrace_638912 : CollatzResearch.WordTrace tailWord_638912 prefixEnd_638912 328068951925509487561703 := by
  unfold tailWord_638912
  simp only [CollatzResearch.WordTrace]
  refine ⟨11651517530669208163711495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15535356707558944218281993 11651517530669208163711495)
  ·
    refine ⟨17477276296003812245567243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11651517530669208163711495 17477276296003812245567243)
    ·
      refine ⟨26215914444005718368350865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17477276296003812245567243 26215914444005718368350865)
      ·
        refine ⟨19661935833004288776263149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26215914444005718368350865 19661935833004288776263149)
        ·
          refine ⟨7373225937376608291098681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19661935833004288776263149 7373225937376608291098681)
          ·
            refine ⟨5529919453032456218324011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7373225937376608291098681 5529919453032456218324011)
            ·
              refine ⟨8294879179548684327486017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5529919453032456218324011 8294879179548684327486017)
              ·
                refine ⟨6221159384661513245614513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8294879179548684327486017 6221159384661513245614513)
                ·
                  refine ⟨4665869538496134934210885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6221159384661513245614513 4665869538496134934210885)
                  ·
                    refine ⟨874850538468025300164541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4665869538496134934210885 874850538468025300164541)
                    ·
                      refine ⟨328068951925509487561703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 874850538468025300164541 328068951925509487561703)
                      ·
                        rfl

theorem cell23_638912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 3].length) (baseStart_638912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_638912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_638912 prefixEnd_638912 := by exact prefixLift 638912
  have htrace : WordTrace (prefixWord ++ tailWord_638912) baseStart_638912 baseEnd_638912 := by
    simpa [prefixWord, tailWord_638912, baseEnd_638912] using wordTrace_append hprefix tailTrace_638912
  have hstable : (prefixWord ++ tailWord_638912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638912).length < 2 ^ (prefixWord ++ tailWord_638912).sum := by decide
  have hdescent : baseEnd_638912 < baseStart_638912 := by decide
  rcases family_descends (prefixWord ++ tailWord_638912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638926 : List Nat := [4, 1, 1, 1, 2, 2, 2, 2, 4, 2, 2]
def baseStart_638926 : Nat := 118140960795 + 638926 * 2 ^ 59
def prefixEnd_638926 : Nat := 4983230072969 + 3 ^ 40 * 638926 * 2
def baseEnd_638926 : Nat := 328076140654672432786639

theorem tailTrace_638926 : CollatzResearch.WordTrace tailWord_638926 prefixEnd_638926 328076140654672432786639 := by
  unfold tailWord_638926
  simp only [CollatzResearch.WordTrace]
  refine ⟨2912943210410962089804079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15535697122191797812288421 2912943210410962089804079)
  ·
    refine ⟨4369414815616443134706119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2912943210410962089804079 4369414815616443134706119)
    ·
      refine ⟨6554122223424664702059179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4369414815616443134706119 6554122223424664702059179)
      ·
        refine ⟨9831183335136997053088769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6554122223424664702059179 9831183335136997053088769)
        ·
          refine ⟨7373387501352747789816577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9831183335136997053088769 7373387501352747789816577)
          ·
            refine ⟨5530040626014560842362433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7373387501352747789816577 5530040626014560842362433)
            ·
              refine ⟨4147530469510920631771825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5530040626014560842362433 4147530469510920631771825)
              ·
                refine ⟨3110647852133190473828869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4147530469510920631771825 3110647852133190473828869)
                ·
                  refine ⟨583246472274973213842913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3110647852133190473828869 583246472274973213842913)
                  ·
                    refine ⟨437434854206229910382185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 583246472274973213842913 437434854206229910382185)
                    ·
                      refine ⟨328076140654672432786639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 437434854206229910382185 328076140654672432786639)
                      ·
                        rfl

theorem cell23_638926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 4, 2, 2].length) (baseStart_638926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_638926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_638926 prefixEnd_638926 := by exact prefixLift 638926
  have htrace : WordTrace (prefixWord ++ tailWord_638926) baseStart_638926 baseEnd_638926 := by
    simpa [prefixWord, tailWord_638926, baseEnd_638926] using wordTrace_append hprefix tailTrace_638926
  have hstable : (prefixWord ++ tailWord_638926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638926).length < 2 ^ (prefixWord ++ tailWord_638926).sum := by decide
  have hdescent : baseEnd_638926 < baseStart_638926 := by decide
  rcases family_descends (prefixWord ++ tailWord_638926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638932 : List Nat := [2, 4, 1, 2, 1, 1, 1, 2, 9]
def baseStart_638932 : Nat := 118140960795 + 638932 * 2 ^ 59
def prefixEnd_638932 : Nat := 4983230072969 + 3 ^ 40 * 638932 * 2
def baseEnd_638932 : Nat := 36453246837622156590179

theorem tailTrace_638932 : CollatzResearch.WordTrace tailWord_638932 prefixEnd_638932 36453246837622156590179 := by
  unfold tailWord_638932
  simp only [CollatzResearch.WordTrace]
  refine ⟨11651882260632979871575525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15535843014177306495434033 11651882260632979871575525)
  ·
    refine ⟨2184727923868683725920411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11651882260632979871575525 2184727923868683725920411)
    ·
      refine ⟨3277091885803025588880617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2184727923868683725920411 3277091885803025588880617)
      ·
        refine ⟨2457818914352269191660463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3277091885803025588880617 2457818914352269191660463)
        ·
          refine ⟨3686728371528403787490695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2457818914352269191660463 3686728371528403787490695)
          ·
            refine ⟨5530092557292605681236043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3686728371528403787490695 5530092557292605681236043)
            ·
              refine ⟨8295138835938908521854065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5530092557292605681236043 8295138835938908521854065)
              ·
                refine ⟨6221354126954181391390549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8295138835938908521854065 6221354126954181391390549)
                ·
                  refine ⟨36453246837622156590179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 6221354126954181391390549 36453246837622156590179)
                  ·
                    rfl

theorem cell23_638932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 9].length) (baseStart_638932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_638932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_638932 prefixEnd_638932 := by exact prefixLift 638932
  have htrace : WordTrace (prefixWord ++ tailWord_638932) baseStart_638932 baseEnd_638932 := by
    simpa [prefixWord, tailWord_638932, baseEnd_638932] using wordTrace_append hprefix tailTrace_638932
  have hstable : (prefixWord ++ tailWord_638932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638932).length < 2 ^ (prefixWord ++ tailWord_638932).sum := by decide
  have hdescent : baseEnd_638932 < baseStart_638932 := by decide
  rcases family_descends (prefixWord ++ tailWord_638932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638943 : List Nat := [1, 1, 2, 3, 4, 1, 3, 2, 2, 2, 2]
def baseStart_638943 : Nat := 118140960795 + 638943 * 2 ^ 59
def prefixEnd_638943 : Nat := 4983230072969 + 3 ^ 40 * 638943 * 2
def baseEnd_638943 : Nat := 328084869825798866274061

theorem tailTrace_638943 : CollatzResearch.WordTrace tailWord_638943 prefixEnd_638943 328084869825798866274061 := by
  unfold tailWord_638943
  simp only [CollatzResearch.WordTrace]
  refine ⟨23304165724226108621801483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15536110482817405747867655 23304165724226108621801483)
  ·
    refine ⟨34956248586339162932702225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23304165724226108621801483 34956248586339162932702225)
    ·
      refine ⟨26217186439754372199526669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34956248586339162932702225 26217186439754372199526669)
      ·
        refine ⟨9831444914907889574822501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26217186439754372199526669 9831444914907889574822501)
        ·
          refine ⟨1843395921545229295279219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9831444914907889574822501 1843395921545229295279219)
          ·
            refine ⟨2765093882317843942918829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1843395921545229295279219 2765093882317843942918829)
            ·
              refine ⟨1036910205869191478594561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2765093882317843942918829 1036910205869191478594561)
              ·
                refine ⟨777682654401893608945921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1036910205869191478594561 777682654401893608945921)
                ·
                  refine ⟨583261990801420206709441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 777682654401893608945921 583261990801420206709441)
                  ·
                    refine ⟨437446493101065155032081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 583261990801420206709441 437446493101065155032081)
                    ·
                      refine ⟨328084869825798866274061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 437446493101065155032081 328084869825798866274061)
                      ·
                        rfl

theorem cell23_638943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 2, 2, 2, 2].length) (baseStart_638943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_638943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_638943 prefixEnd_638943 := by exact prefixLift 638943
  have htrace : WordTrace (prefixWord ++ tailWord_638943) baseStart_638943 baseEnd_638943 := by
    simpa [prefixWord, tailWord_638943, baseEnd_638943] using wordTrace_append hprefix tailTrace_638943
  have hstable : (prefixWord ++ tailWord_638943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638943).length < 2 ^ (prefixWord ++ tailWord_638943).sum := by decide
  have hdescent : baseEnd_638943 < baseStart_638943 := by decide
  rcases family_descends (prefixWord ++ tailWord_638943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639036 : List Nat := [2, 2, 2, 2, 2, 1, 4, 1, 2, 2, 3]
def baseStart_639036 : Nat := 118140960795 + 639036 * 2 ^ 59
def prefixEnd_639036 : Nat := 4983230072969 + 3 ^ 40 * 639036 * 2
def baseEnd_639036 : Nat := 328132623526667002411133

theorem tailTrace_639036 : CollatzResearch.WordTrace tailWord_639036 prefixEnd_639036 328132623526667002411133 := by
  unfold tailWord_639036
  simp only [CollatzResearch.WordTrace]
  refine ⟨11653778856444592752468481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15538371808592790336624641 11653778856444592752468481)
  ·
    refine ⟨8740334142333444564351361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11653778856444592752468481 8740334142333444564351361)
    ·
      refine ⟨6555250606750083423263521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8740334142333444564351361 6555250606750083423263521)
      ·
        refine ⟨4916437955062562567447641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6555250606750083423263521 4916437955062562567447641)
        ·
          refine ⟨3687328466296921925585731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4916437955062562567447641 3687328466296921925585731)
          ·
            refine ⟨5530992699445382888378597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3687328466296921925585731 5530992699445382888378597)
            ·
              refine ⟨1037061131146009291570987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5530992699445382888378597 1037061131146009291570987)
              ·
                refine ⟨1555591696719013937356481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1037061131146009291570987 1555591696719013937356481)
                ·
                  refine ⟨1166693772539260453017361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1555591696719013937356481 1166693772539260453017361)
                  ·
                    refine ⟨875020329404445339763021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1166693772539260453017361 875020329404445339763021)
                    ·
                      refine ⟨328132623526667002411133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 875020329404445339763021 328132623526667002411133)
                      ·
                        rfl

theorem cell23_639036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_639036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_639036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_639036 prefixEnd_639036 := by exact prefixLift 639036
  have htrace : WordTrace (prefixWord ++ tailWord_639036) baseStart_639036 baseEnd_639036 := by
    simpa [prefixWord, tailWord_639036, baseEnd_639036] using wordTrace_append hprefix tailTrace_639036
  have hstable : (prefixWord ++ tailWord_639036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639036).length < 2 ^ (prefixWord ++ tailWord_639036).sum := by decide
  have hdescent : baseEnd_639036 < baseStart_639036 := by decide
  rcases family_descends (prefixWord ++ tailWord_639036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639046 : List Nat := [6, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6]
def baseStart_639046 : Nat := 118140960795 + 639046 * 2 ^ 59
def prefixEnd_639046 : Nat := 4983230072969 + 3 ^ 40 * 639046 * 2
def baseEnd_639046 : Nat := 328137758333211963286087

theorem tailTrace_639046 : CollatzResearch.WordTrace tailWord_639046 prefixEnd_639046 328137758333211963286087 := by
  unfold tailWord_639046
  simp only [CollatzResearch.WordTrace]
  refine ⟨728372576339154912900031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15538614961901971475200661 728372576339154912900031)
  ·
    refine ⟨1092558864508732369350047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 728372576339154912900031 1092558864508732369350047)
    ·
      refine ⟨1638838296763098554025071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1092558864508732369350047 1638838296763098554025071)
      ·
        refine ⟨2458257445144647831037607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1638838296763098554025071 2458257445144647831037607)
        ·
          refine ⟨3687386167716971746556411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2458257445144647831037607 3687386167716971746556411)
          ·
            refine ⟨5531079251575457619834617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3687386167716971746556411 5531079251575457619834617)
            ·
              refine ⟨4148309438681593214875963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5531079251575457619834617 4148309438681593214875963)
              ·
                refine ⟨6222464158022389822313945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4148309438681593214875963 6222464158022389822313945)
                ·
                  refine ⟨4666848118516792366735459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6222464158022389822313945 4666848118516792366735459)
                  ·
                    refine ⟨7000272177775188550103189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4666848118516792366735459 7000272177775188550103189)
                    ·
                      refine ⟨328137758333211963286087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7000272177775188550103189 328137758333211963286087)
                      ·
                        rfl

theorem cell23_639046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_639046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_639046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_639046 prefixEnd_639046 := by exact prefixLift 639046
  have htrace : WordTrace (prefixWord ++ tailWord_639046) baseStart_639046 baseEnd_639046 := by
    simpa [prefixWord, tailWord_639046, baseEnd_639046] using wordTrace_append hprefix tailTrace_639046
  have hstable : (prefixWord ++ tailWord_639046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639046).length < 2 ^ (prefixWord ++ tailWord_639046).sum := by decide
  have hdescent : baseEnd_639046 < baseStart_639046 := by decide
  rcases family_descends (prefixWord ++ tailWord_639046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639066 : List Nat := [3, 1, 1, 2, 1, 1, 4, 3, 3, 1, 3]
def baseStart_639066 : Nat := 118140960795 + 639066 * 2 ^ 59
def prefixEnd_639066 : Nat := 4983230072969 + 3 ^ 40 * 639066 * 2
def baseEnd_639066 : Nat := 328148027946301885035995

theorem tailTrace_639066 : CollatzResearch.WordTrace tailWord_639066 prefixEnd_639066 328148027946301885035995 := by
  unfold tailWord_639066
  simp only [CollatzResearch.WordTrace]
  refine ⟨5827162975695125157132263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15539101268520333752352701 5827162975695125157132263)
  ·
    refine ⟨8740744463542687735698395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5827162975695125157132263 8740744463542687735698395)
    ·
      refine ⟨13111116695314031603547593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8740744463542687735698395 13111116695314031603547593)
      ·
        refine ⟨9833337521485523702660695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13111116695314031603547593 9833337521485523702660695)
        ·
          refine ⟨14750006282228285553991043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9833337521485523702660695 14750006282228285553991043)
          ·
            refine ⟨22125009423342428330986565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14750006282228285553991043 22125009423342428330986565)
            ·
              refine ⟨4148439266876705312059981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22125009423342428330986565 4148439266876705312059981)
              ·
                refine ⟨1555664725078764492022493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4148439266876705312059981 1555664725078764492022493)
                ·
                  refine ⟨583374271904536684508435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1555664725078764492022493 583374271904536684508435)
                  ·
                    refine ⟨875061407856805026762653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 583374271904536684508435 875061407856805026762653)
                    ·
                      refine ⟨328148027946301885035995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 875061407856805026762653 328148027946301885035995)
                      ·
                        rfl

theorem cell23_639066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 3, 1, 3].length) (baseStart_639066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_639066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_639066 prefixEnd_639066 := by exact prefixLift 639066
  have htrace : WordTrace (prefixWord ++ tailWord_639066) baseStart_639066 baseEnd_639066 := by
    simpa [prefixWord, tailWord_639066, baseEnd_639066] using wordTrace_append hprefix tailTrace_639066
  have hstable : (prefixWord ++ tailWord_639066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639066).length < 2 ^ (prefixWord ++ tailWord_639066).sum := by decide
  have hdescent : baseEnd_639066 < baseStart_639066 := by decide
  rcases family_descends (prefixWord ++ tailWord_639066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639076 : List Nat := [2, 3, 1, 1, 2, 1, 2, 2, 4, 3, 2]
def baseStart_639076 : Nat := 118140960795 + 639076 * 2 ^ 59
def prefixEnd_639076 : Nat := 4983230072969 + 3 ^ 40 * 639076 * 2
def baseEnd_639076 : Nat := 328153162752846845910949

theorem tailTrace_639076 : CollatzResearch.WordTrace tailWord_639076 prefixEnd_639076 328153162752846845910949 := by
  unfold tailWord_639076
  simp only [CollatzResearch.WordTrace]
  refine ⟨11654508316372136168196541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15539344421829514890928721 11654508316372136168196541)
  ·
    refine ⟨4370440618639551063073703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11654508316372136168196541 4370440618639551063073703)
    ·
      refine ⟨6555660927959326594610555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4370440618639551063073703 6555660927959326594610555)
      ·
        refine ⟨9833491391938989891915833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6555660927959326594610555 9833491391938989891915833)
        ·
          refine ⟨7375118543954242418936875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9833491391938989891915833 7375118543954242418936875)
          ·
            refine ⟨11062677815931363628405313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7375118543954242418936875 11062677815931363628405313)
            ·
              refine ⟨8297008361948522721303985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11062677815931363628405313 8297008361948522721303985)
              ·
                refine ⟨6222756271461392040977989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8297008361948522721303985 6222756271461392040977989)
                ·
                  refine ⟨1166766800899011007683373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6222756271461392040977989 1166766800899011007683373)
                  ·
                    refine ⟨437537550337129127881265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1166766800899011007683373 437537550337129127881265)
                    ·
                      refine ⟨328153162752846845910949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 437537550337129127881265 328153162752846845910949)
                      ·
                        rfl

theorem cell23_639076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 4, 3, 2].length) (baseStart_639076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_639076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_639076 prefixEnd_639076 := by exact prefixLift 639076
  have htrace : WordTrace (prefixWord ++ tailWord_639076) baseStart_639076 baseEnd_639076 := by
    simpa [prefixWord, tailWord_639076, baseEnd_639076] using wordTrace_append hprefix tailTrace_639076
  have hstable : (prefixWord ++ tailWord_639076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639076).length < 2 ^ (prefixWord ++ tailWord_639076).sum := by decide
  have hdescent : baseEnd_639076 < baseStart_639076 := by decide
  rcases family_descends (prefixWord ++ tailWord_639076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639086 : List Nat := [4, 1, 2, 2, 1, 1, 2, 4, 1, 5]
def baseStart_639086 : Nat := 118140960795 + 639086 * 2 ^ 59
def prefixEnd_639086 : Nat := 4983230072969 + 3 ^ 40 * 639086 * 2
def baseEnd_639086 : Nat := 109386099186463935595301

theorem tailTrace_639086 : CollatzResearch.WordTrace tailWord_639086 prefixEnd_639086 109386099186463935595301 := by
  unfold tailWord_639086
  simp only [CollatzResearch.WordTrace]
  refine ⟨2913672670338505505532139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15539587575138696029504741 2913672670338505505532139)
  ·
    refine ⟨4370509005507758258298209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2913672670338505505532139 4370509005507758258298209)
    ·
      refine ⟨3277881754130818693723657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4370509005507758258298209 3277881754130818693723657)
      ·
        refine ⟨2458411315598114020292743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3277881754130818693723657 2458411315598114020292743)
        ·
          refine ⟨3687616973397171030439115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2458411315598114020292743 3687616973397171030439115)
          ·
            refine ⟨5531425460095756545658673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3687616973397171030439115 5531425460095756545658673)
            ·
              refine ⟨4148569095071817409244005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5531425460095756545658673 4148569095071817409244005)
              ·
                refine ⟨777856705325965764233251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4148569095071817409244005 777856705325965764233251)
                ·
                  refine ⟨1166785057988948646349877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 777856705325965764233251 1166785057988948646349877)
                  ·
                    refine ⟨109386099186463935595301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1166785057988948646349877 109386099186463935595301)
                    ·
                      rfl

theorem cell23_639086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_639086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_639086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_639086 prefixEnd_639086 := by exact prefixLift 639086
  have htrace : WordTrace (prefixWord ++ tailWord_639086) baseStart_639086 baseEnd_639086 := by
    simpa [prefixWord, tailWord_639086, baseEnd_639086] using wordTrace_append hprefix tailTrace_639086
  have hstable : (prefixWord ++ tailWord_639086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639086).length < 2 ^ (prefixWord ++ tailWord_639086).sum := by decide
  have hdescent : baseEnd_639086 < baseStart_639086 := by decide
  rcases family_descends (prefixWord ++ tailWord_639086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639089 : List Nat := [1, 2, 2, 2, 1, 1, 3, 3, 3, 1, 4]
def baseStart_639089 : Nat := 118140960795 + 639089 * 2 ^ 59
def prefixEnd_639089 : Nat := 4983230072969 + 3 ^ 40 * 639089 * 2
def baseEnd_639089 : Nat := 328159838001355295048389

theorem tailTrace_639089 : CollatzResearch.WordTrace tailWord_639089 prefixEnd_639089 328159838001355295048389 := by
  unfold tailWord_639089
  simp only [CollatzResearch.WordTrace]
  refine ⟨23309490781697175556616321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15539660521131450371077547 23309490781697175556616321)
  ·
    refine ⟨17482118086272881667462241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23309490781697175556616321 17482118086272881667462241)
    ·
      refine ⟨13111588564704661250596681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17482118086272881667462241 13111588564704661250596681)
      ·
        refine ⟨9833691423528495937947511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13111588564704661250596681 9833691423528495937947511)
        ·
          refine ⟨14750537135292743906921267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9833691423528495937947511 14750537135292743906921267)
          ·
            refine ⟨22125805702939115860381901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14750537135292743906921267 22125805702939115860381901)
            ·
              refine ⟨8297177138602168447643213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22125805702939115860381901 8297177138602168447643213)
              ·
                refine ⟨3111441426975813167866205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8297177138602168447643213 3111441426975813167866205)
                ·
                  refine ⟨1166790535115929937949827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3111441426975813167866205 1166790535115929937949827)
                  ·
                    refine ⟨1750185802673894906924741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1166790535115929937949827 1750185802673894906924741)
                    ·
                      refine ⟨328159838001355295048389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1750185802673894906924741 328159838001355295048389)
                      ·
                        rfl

theorem cell23_639089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_639089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_639089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_639089 prefixEnd_639089 := by exact prefixLift 639089
  have htrace : WordTrace (prefixWord ++ tailWord_639089) baseStart_639089 baseEnd_639089 := by
    simpa [prefixWord, tailWord_639089, baseEnd_639089] using wordTrace_append hprefix tailTrace_639089
  have hstable : (prefixWord ++ tailWord_639089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639089).length < 2 ^ (prefixWord ++ tailWord_639089).sum := by decide
  have hdescent : baseEnd_639089 < baseStart_639089 := by decide
  rcases family_descends (prefixWord ++ tailWord_639089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639100 : List Nat := [2, 2, 2, 1, 1, 5, 2, 3, 1, 1, 3]
def baseStart_639100 : Nat := 118140960795 + 639100 * 2 ^ 59
def prefixEnd_639100 : Nat := 4983230072969 + 3 ^ 40 * 639100 * 2
def baseEnd_639100 : Nat := 328165486288554752010839

theorem tailTrace_639100 : CollatzResearch.WordTrace tailWord_639100 prefixEnd_639100 328165486288554752010839 := by
  unfold tailWord_639100
  simp only [CollatzResearch.WordTrace]
  refine ⟨11654945992328662217633377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15539927989771549623511169 11654945992328662217633377)
  ·
    refine ⟨8741209494246496663225033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11654945992328662217633377 8741209494246496663225033)
    ·
      refine ⟨6555907120684872497418775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8741209494246496663225033 6555907120684872497418775)
      ·
        refine ⟨9833860681027308746128163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6555907120684872497418775 9833860681027308746128163)
        ·
          refine ⟨14750791021540963119192245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9833860681027308746128163 14750791021540963119192245)
          ·
            refine ⟨1382886658269465292424273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14750791021540963119192245 1382886658269465292424273)
            ·
              refine ⟨1037164993702098969318205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1382886658269465292424273 1037164993702098969318205)
              ·
                refine ⟨388936872638287113494327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1037164993702098969318205 388936872638287113494327)
                ·
                  refine ⟨583405308957430670241491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 388936872638287113494327 583405308957430670241491)
                  ·
                    refine ⟨875107963436146005362237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 583405308957430670241491 875107963436146005362237)
                    ·
                      refine ⟨328165486288554752010839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 875107963436146005362237 328165486288554752010839)
                      ·
                        rfl

theorem cell23_639100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 3, 1, 1, 3].length) (baseStart_639100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_639100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_639100 prefixEnd_639100 := by exact prefixLift 639100
  have htrace : WordTrace (prefixWord ++ tailWord_639100) baseStart_639100 baseEnd_639100 := by
    simpa [prefixWord, tailWord_639100, baseEnd_639100] using wordTrace_append hprefix tailTrace_639100
  have hstable : (prefixWord ++ tailWord_639100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639100).length < 2 ^ (prefixWord ++ tailWord_639100).sum := by decide
  have hdescent : baseEnd_639100 < baseStart_639100 := by decide
  rcases family_descends (prefixWord ++ tailWord_639100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639136 : List Nat := [2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 4]
def baseStart_639136 : Nat := 118140960795 + 639136 * 2 ^ 59
def prefixEnd_639136 : Nat := 4983230072969 + 3 ^ 40 * 639136 * 2
def baseEnd_639136 : Nat := 328183971592116611160673

theorem tailTrace_639136 : CollatzResearch.WordTrace tailWord_639136 prefixEnd_639136 328183971592116611160673 := by
  unfold tailWord_639136
  simp only [CollatzResearch.WordTrace]
  refine ⟨11655602506263451291788631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15540803341684601722384841 11655602506263451291788631)
  ·
    refine ⟨17483403759395176937682947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11655602506263451291788631 17483403759395176937682947)
    ·
      refine ⟨26225105639092765406524421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17483403759395176937682947 26225105639092765406524421)
      ·
        refine ⟨4917207307329893513723329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26225105639092765406524421 4917207307329893513723329)
        ·
          refine ⟨3687905480497420135292497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4917207307329893513723329 3687905480497420135292497)
          ·
            refine ⟨2765929110373065101469373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3687905480497420135292497 2765929110373065101469373)
            ·
              refine ⟨1037223416389899413051015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2765929110373065101469373 1037223416389899413051015)
              ·
                refine ⟨1555835124584849119576523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1037223416389899413051015 1555835124584849119576523)
                ·
                  refine ⟨2333752686877273679364785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1555835124584849119576523 2333752686877273679364785)
                  ·
                    refine ⟨1750314515157955259523589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2333752686877273679364785 1750314515157955259523589)
                    ·
                      refine ⟨328183971592116611160673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1750314515157955259523589 328183971592116611160673)
                      ·
                        rfl

theorem cell23_639136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_639136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_639136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_639136 prefixEnd_639136 := by exact prefixLift 639136
  have htrace : WordTrace (prefixWord ++ tailWord_639136) baseStart_639136 baseEnd_639136 := by
    simpa [prefixWord, tailWord_639136, baseEnd_639136] using wordTrace_append hprefix tailTrace_639136
  have hstable : (prefixWord ++ tailWord_639136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639136).length < 2 ^ (prefixWord ++ tailWord_639136).sum := by decide
  have hdescent : baseEnd_639136 < baseStart_639136 := by decide
  rcases family_descends (prefixWord ++ tailWord_639136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639179 : List Nat := [1, 1, 1, 1, 3, 2, 4, 1, 2, 3, 4]
def baseStart_639179 : Nat := 118140960795 + 639179 * 2 ^ 59
def prefixEnd_639179 : Nat := 4983230072969 + 3 ^ 40 * 639179 * 2
def baseEnd_639179 : Nat := 328206051260259942922975

theorem tailTrace_639179 : CollatzResearch.WordTrace tailWord_639179 prefixEnd_639179 328206051260259942922975 := by
  unfold tailWord_639179
  simp only [CollatzResearch.WordTrace]
  refine ⟨23312773351371120927392591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15541848900914080618261727 23312773351371120927392591)
  ·
    refine ⟨34969160027056681391088887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23312773351371120927392591 34969160027056681391088887)
    ·
      refine ⟨52453740040585022086633331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34969160027056681391088887 52453740040585022086633331)
      ·
        refine ⟨78680610060877533129949997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52453740040585022086633331 78680610060877533129949997)
        ·
          refine ⟨29505228772829074923731249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78680610060877533129949997 29505228772829074923731249)
          ·
            refine ⟨22128921579621806192798437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29505228772829074923731249 22128921579621806192798437)
            ·
              refine ⟨4149172796179088661149707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22128921579621806192798437 4149172796179088661149707)
              ·
                refine ⟨6223759194268632991724561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4149172796179088661149707 6223759194268632991724561)
                ·
                  refine ⟨4667819395701474743793421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6223759194268632991724561 4667819395701474743793421)
                  ·
                    refine ⟨1750432273388053028922533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4667819395701474743793421 1750432273388053028922533)
                    ·
                      refine ⟨328206051260259942922975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1750432273388053028922533 328206051260259942922975)
                      ·
                        rfl

theorem cell23_639179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 3, 4].length) (baseStart_639179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_639179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_639179 prefixEnd_639179 := by exact prefixLift 639179
  have htrace : WordTrace (prefixWord ++ tailWord_639179) baseStart_639179 baseEnd_639179 := by
    simpa [prefixWord, tailWord_639179, baseEnd_639179] using wordTrace_append hprefix tailTrace_639179
  have hstable : (prefixWord ++ tailWord_639179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639179).length < 2 ^ (prefixWord ++ tailWord_639179).sum := by decide
  have hdescent : baseEnd_639179 < baseStart_639179 := by decide
  rcases family_descends (prefixWord ++ tailWord_639179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639209 : List Nat := [1, 2, 1, 1, 1, 2, 2, 4, 1, 4, 4]
def baseStart_639209 : Nat := 118140960795 + 639209 * 2 ^ 59
def prefixEnd_639209 : Nat := 4983230072969 + 3 ^ 40 * 639209 * 2
def baseEnd_639209 : Nat := 328221455679894825547837

theorem tailTrace_639209 : CollatzResearch.WordTrace tailWord_639209 prefixEnd_639209 328221455679894825547837 := by
  unfold tailWord_639209
  simp only [CollatzResearch.WordTrace]
  refine ⟨23313867541262436050984681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15542578360841624033989787 23313867541262436050984681)
  ·
    refine ⟨17485400655946827038238511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23313867541262436050984681 17485400655946827038238511)
    ·
      refine ⟨26228100983920240557357767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17485400655946827038238511 26228100983920240557357767)
      ·
        refine ⟨39342151475880360836036651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26228100983920240557357767 39342151475880360836036651)
        ·
          refine ⟨59013227213820541254054977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39342151475880360836036651 59013227213820541254054977)
          ·
            refine ⟨44259920410365405940541233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59013227213820541254054977 44259920410365405940541233)
            ·
              refine ⟨33194940307774054455405925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44259920410365405940541233 33194940307774054455405925)
              ·
                refine ⟨6224051307707635210388611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33194940307774054455405925 6224051307707635210388611)
                ·
                  refine ⟨9336076961561452815582917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6224051307707635210388611 9336076961561452815582917)
                  ·
                    refine ⟨1750514430292772402921797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9336076961561452815582917 1750514430292772402921797)
                    ·
                      refine ⟨328221455679894825547837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1750514430292772402921797 328221455679894825547837)
                      ·
                        rfl

theorem cell23_639209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 4, 4].length) (baseStart_639209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_639209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_639209 prefixEnd_639209 := by exact prefixLift 639209
  have htrace : WordTrace (prefixWord ++ tailWord_639209) baseStart_639209 baseEnd_639209 := by
    simpa [prefixWord, tailWord_639209, baseEnd_639209] using wordTrace_append hprefix tailTrace_639209
  have hstable : (prefixWord ++ tailWord_639209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639209).length < 2 ^ (prefixWord ++ tailWord_639209).sum := by decide
  have hdescent : baseEnd_639209 < baseStart_639209 := by decide
  rcases family_descends (prefixWord ++ tailWord_639209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639229 : List Nat := [1, 4, 1, 1, 1, 1, 1, 3, 1, 2, 7]
def baseStart_639229 : Nat := 118140960795 + 639229 * 2 ^ 59
def prefixEnd_639229 : Nat := 4983230072969 + 3 ^ 40 * 639229 * 2
def baseEnd_639229 : Nat := 328231725292984747297745

theorem tailTrace_639229 : CollatzResearch.WordTrace tailWord_639229 prefixEnd_639229 328231725292984747297745 := by
  unfold tailWord_639229
  simp only [CollatzResearch.WordTrace]
  refine ⟨23314597001189979466712741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15543064667459986311141827 23314597001189979466712741)
  ·
    refine ⟨4371486937723121150008639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23314597001189979466712741 4371486937723121150008639)
    ·
      refine ⟨6557230406584681725012959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4371486937723121150008639 6557230406584681725012959)
      ·
        refine ⟨9835845609877022587519439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6557230406584681725012959 9835845609877022587519439)
        ·
          refine ⟨14753768414815533881279159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9835845609877022587519439 14753768414815533881279159)
          ·
            refine ⟨22130652622223300821918739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14753768414815533881279159 22130652622223300821918739)
            ·
              refine ⟨33195978933334951232878109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22130652622223300821918739 33195978933334951232878109)
              ·
                refine ⟨12448492100000606712329291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33195978933334951232878109 12448492100000606712329291)
                ·
                  refine ⟨18672738150000910068493937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12448492100000606712329291 18672738150000910068493937)
                  ·
                    refine ⟨14004553612500682551370453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18672738150000910068493937 14004553612500682551370453)
                    ·
                      refine ⟨328231725292984747297745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 14004553612500682551370453 328231725292984747297745)
                      ·
                        rfl

theorem cell23_639229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_639229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_639229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_639229 prefixEnd_639229 := by exact prefixLift 639229
  have htrace : WordTrace (prefixWord ++ tailWord_639229) baseStart_639229 baseEnd_639229 := by
    simpa [prefixWord, tailWord_639229, baseEnd_639229] using wordTrace_append hprefix tailTrace_639229
  have hstable : (prefixWord ++ tailWord_639229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639229).length < 2 ^ (prefixWord ++ tailWord_639229).sum := by decide
  have hdescent : baseEnd_639229 < baseStart_639229 := by decide
  rcases family_descends (prefixWord ++ tailWord_639229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639259 : List Nat := [1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 7]
def baseStart_639259 : Nat := 118140960795 + 639259 * 2 ^ 59
def prefixEnd_639259 : Nat := 4983230072969 + 3 ^ 40 * 639259 * 2
def baseEnd_639259 : Nat := 328247129712619629922607

theorem tailTrace_639259 : CollatzResearch.WordTrace tailWord_639259 prefixEnd_639259 328247129712619629922607 := by
  unfold tailWord_639259
  simp only [CollatzResearch.WordTrace]
  refine ⟨23315691191081294590304831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15543794127387529726869887 23315691191081294590304831)
  ·
    refine ⟨34973536786621941885457247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23315691191081294590304831 34973536786621941885457247)
    ·
      refine ⟨52460305179932912828185871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34973536786621941885457247 52460305179932912828185871)
      ·
        refine ⟨78690457769899369242278807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52460305179932912828185871 78690457769899369242278807)
        ·
          refine ⟨118035686654849053863418211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78690457769899369242278807 118035686654849053863418211)
          ·
            refine ⟨177053529982273580795127317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118035686654849053863418211 177053529982273580795127317)
            ·
              refine ⟨8299384217919074099771593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 177053529982273580795127317 8299384217919074099771593)
              ·
                refine ⟨6224538163439305574828695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8299384217919074099771593 6224538163439305574828695)
                ·
                  refine ⟨9336807245158958362243043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6224538163439305574828695 9336807245158958362243043)
                  ·
                    refine ⟨14005210867738437543364565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9336807245158958362243043 14005210867738437543364565)
                    ·
                      refine ⟨328247129712619629922607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 14005210867738437543364565 328247129712619629922607)
                      ·
                        rfl

theorem cell23_639259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 7].length) (baseStart_639259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_639259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_639259 prefixEnd_639259 := by exact prefixLift 639259
  have htrace : WordTrace (prefixWord ++ tailWord_639259) baseStart_639259 baseEnd_639259 := by
    simpa [prefixWord, tailWord_639259, baseEnd_639259] using wordTrace_append hprefix tailTrace_639259
  have hstable : (prefixWord ++ tailWord_639259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639259).length < 2 ^ (prefixWord ++ tailWord_639259).sum := by decide
  have hdescent : baseEnd_639259 < baseStart_639259 := by decide
  rcases family_descends (prefixWord ++ tailWord_639259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639303 : List Nat := [1, 1, 4, 1, 2, 2, 1, 3, 2, 4, 2]
def baseStart_639303 : Nat := 118140960795 + 639303 * 2 ^ 59
def prefixEnd_639303 : Nat := 4983230072969 + 3 ^ 40 * 639303 * 2
def baseEnd_639303 : Nat := 328269722861417457772405

theorem tailTrace_639303 : CollatzResearch.WordTrace tailWord_639303 prefixEnd_639303 328269722861417457772405 := by
  unfold tailWord_639303
  simp only [CollatzResearch.WordTrace]
  refine ⟨23317296002921890104906563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15544864001947926736604375 23317296002921890104906563)
  ·
    refine ⟨34975944004382835157359845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23317296002921890104906563 34975944004382835157359845)
    ·
      refine ⟨6557989500821781592004971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34975944004382835157359845 6557989500821781592004971)
      ·
        refine ⟨9836984251232672388007457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6557989500821781592004971 9836984251232672388007457)
        ·
          refine ⟨7377738188424504291005593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9836984251232672388007457 7377738188424504291005593)
          ·
            refine ⟨5533303641318378218254195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7377738188424504291005593 5533303641318378218254195)
            ·
              refine ⟨8299955461977567327381293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5533303641318378218254195 8299955461977567327381293)
              ·
                refine ⟨3112483298241587747767985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8299955461977567327381293 3112483298241587747767985)
                ·
                  refine ⟨2334362473681190810825989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3112483298241587747767985 2334362473681190810825989)
                  ·
                    refine ⟨437692963815223277029873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2334362473681190810825989 437692963815223277029873)
                    ·
                      refine ⟨328269722861417457772405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 437692963815223277029873 328269722861417457772405)
                      ·
                        rfl

theorem cell23_639303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 4, 2].length) (baseStart_639303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_639303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_639303 prefixEnd_639303 := by exact prefixLift 639303
  have htrace : WordTrace (prefixWord ++ tailWord_639303) baseStart_639303 baseEnd_639303 := by
    simpa [prefixWord, tailWord_639303, baseEnd_639303] using wordTrace_append hprefix tailTrace_639303
  have hstable : (prefixWord ++ tailWord_639303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639303).length < 2 ^ (prefixWord ++ tailWord_639303).sum := by decide
  have hdescent : baseEnd_639303 < baseStart_639303 := by decide
  rcases family_descends (prefixWord ++ tailWord_639303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639313 : List Nat := [1, 2, 2, 1, 4, 2, 2, 2, 3, 4]
def baseStart_639313 : Nat := 118140960795 + 639313 * 2 ^ 59
def prefixEnd_639313 : Nat := 4983230072969 + 3 ^ 40 * 639313 * 2
def baseEnd_639313 : Nat := 109424952555987472882453

theorem tailTrace_639313 : CollatzResearch.WordTrace tailWord_639313 prefixEnd_639313 109424952555987472882453 := by
  unfold tailWord_639313
  simp only [CollatzResearch.WordTrace]
  refine ⟨23317660732885661812770593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15545107155257107875180395 23317660732885661812770593)
  ·
    refine ⟨17488245549664246359577945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23317660732885661812770593 17488245549664246359577945)
    ·
      refine ⟨13116184162248184769683459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17488245549664246359577945 13116184162248184769683459)
      ·
        refine ⟨19674276243372277154525189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13116184162248184769683459 19674276243372277154525189)
        ·
          refine ⟨3688926795632301966473473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19674276243372277154525189 3688926795632301966473473)
          ·
            refine ⟨2766695096724226474855105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3688926795632301966473473 2766695096724226474855105)
            ·
              refine ⟨2075021322543169856141329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2766695096724226474855105 2075021322543169856141329)
              ·
                refine ⟨1556265991907377392105997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2075021322543169856141329 1556265991907377392105997)
                ·
                  refine ⟨583599746965266522039749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1556265991907377392105997 583599746965266522039749)
                  ·
                    refine ⟨109424952555987472882453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 583599746965266522039749 109424952555987472882453)
                    ·
                      rfl

theorem cell23_639313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 3, 4].length) (baseStart_639313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_639313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_639313 prefixEnd_639313 := by exact prefixLift 639313
  have htrace : WordTrace (prefixWord ++ tailWord_639313) baseStart_639313 baseEnd_639313 := by
    simpa [prefixWord, tailWord_639313, baseEnd_639313] using wordTrace_append hprefix tailTrace_639313
  have hstable : (prefixWord ++ tailWord_639313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639313).length < 2 ^ (prefixWord ++ tailWord_639313).sum := by decide
  have hdescent : baseEnd_639313 < baseStart_639313 := by decide
  rcases family_descends (prefixWord ++ tailWord_639313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639340 : List Nat := [2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 3]
def baseStart_639340 : Nat := 118140960795 + 639340 * 2 ^ 59
def prefixEnd_639340 : Nat := 4983230072969 + 3 ^ 40 * 639340 * 2
def baseEnd_639340 : Nat := 328288721645633813009735

theorem tailTrace_639340 : CollatzResearch.WordTrace tailWord_639340 prefixEnd_639340 328288721645633813009735 := by
  unfold tailWord_639340
  simp only [CollatzResearch.WordTrace]
  refine ⟨11659322751893922712001737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15545763669191896949335649 11659322751893922712001737)
  ·
    refine ⟨8744492063920442034001303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11659322751893922712001737 8744492063920442034001303)
    ·
      refine ⟨13116738095880663051001955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8744492063920442034001303 13116738095880663051001955)
      ·
        refine ⟨19675107143820994576502933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13116738095880663051001955 19675107143820994576502933)
        ·
          refine ⟨922270647366609120773575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 19675107143820994576502933 922270647366609120773575)
          ·
            refine ⟨1383405971049913681160363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 922270647366609120773575 1383405971049913681160363)
            ·
              refine ⟨2075108956574870521740545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1383405971049913681160363 2075108956574870521740545)
              ·
                refine ⟨1556331717431152891305409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2075108956574870521740545 1556331717431152891305409)
                ·
                  refine ⟨1167248788073364668479057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1556331717431152891305409 1167248788073364668479057)
                  ·
                    refine ⟨875436591055023501359293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1167248788073364668479057 875436591055023501359293)
                    ·
                      refine ⟨328288721645633813009735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 875436591055023501359293 328288721645633813009735)
                      ·
                        rfl

theorem cell23_639340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 3].length) (baseStart_639340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_639340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_639340 prefixEnd_639340 := by exact prefixLift 639340
  have htrace : WordTrace (prefixWord ++ tailWord_639340) baseStart_639340 baseEnd_639340 := by
    simpa [prefixWord, tailWord_639340, baseEnd_639340] using wordTrace_append hprefix tailTrace_639340
  have hstable : (prefixWord ++ tailWord_639340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639340).length < 2 ^ (prefixWord ++ tailWord_639340).sum := by decide
  have hdescent : baseEnd_639340 < baseStart_639340 := by decide
  rcases family_descends (prefixWord ++ tailWord_639340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639420 : List Nat := [2, 2, 2, 4, 1, 2, 2, 1, 1, 6]
def baseStart_639420 : Nat := 118140960795 + 639420 * 2 ^ 59
def prefixEnd_639420 : Nat := 4983230072969 + 3 ^ 40 * 639420 * 2
def baseEnd_639420 : Nat := 109443266699331166669789

theorem tailTrace_639420 : CollatzResearch.WordTrace tailWord_639420 prefixEnd_639420 109443266699331166669789 := by
  unfold tailWord_639420
  simp only [CollatzResearch.WordTrace]
  refine ⟨11660781671749009543457857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15547708895665346057943809 11660781671749009543457857)
  ·
    refine ⟨8745586253811757157593393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11660781671749009543457857 8745586253811757157593393)
    ·
      refine ⟨6559189690358817868195045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8745586253811757157593393 6559189690358817868195045)
      ·
        refine ⟨1229848066942278350286571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6559189690358817868195045 1229848066942278350286571)
        ·
          refine ⟨1844772100413417525429857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1229848066942278350286571 1844772100413417525429857)
          ·
            refine ⟨1383579075310063144072393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1844772100413417525429857 1383579075310063144072393)
            ·
              refine ⟨1037684306482547358054295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1383579075310063144072393 1037684306482547358054295)
              ·
                refine ⟨1556526459723821037081443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1037684306482547358054295 1556526459723821037081443)
                ·
                  refine ⟨2334789689585731555622165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1556526459723821037081443 2334789689585731555622165)
                  ·
                    refine ⟨109443266699331166669789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2334789689585731555622165 109443266699331166669789)
                    ·
                      rfl

theorem cell23_639420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 1, 6].length) (baseStart_639420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_639420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_639420 prefixEnd_639420 := by exact prefixLift 639420
  have htrace : WordTrace (prefixWord ++ tailWord_639420) baseStart_639420 baseEnd_639420 := by
    simpa [prefixWord, tailWord_639420, baseEnd_639420] using wordTrace_append hprefix tailTrace_639420
  have hstable : (prefixWord ++ tailWord_639420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639420).length < 2 ^ (prefixWord ++ tailWord_639420).sum := by decide
  have hdescent : baseEnd_639420 < baseStart_639420 := by decide
  rcases family_descends (prefixWord ++ tailWord_639420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639444 : List Nat := [2, 4, 1, 2, 2, 3, 2, 1, 1, 1, 4]
def baseStart_639444 : Nat := 118140960795 + 639444 * 2 ^ 59
def prefixEnd_639444 : Nat := 4983230072969 + 3 ^ 40 * 639444 * 2
def baseEnd_639444 : Nat := 328342123633701406109257

theorem tailTrace_639444 : CollatzResearch.WordTrace tailWord_639444 prefixEnd_639444 328342123633701406109257 := by
  unfold tailWord_639444
  simp only [CollatzResearch.WordTrace]
  refine ⟨11661219347705535592894693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15548292463607380790526257 11661219347705535592894693)
  ·
    refine ⟨2186478627694787923667755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11661219347705535592894693 2186478627694787923667755)
    ·
      refine ⟨3279717941542181885501633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2186478627694787923667755 3279717941542181885501633)
      ·
        refine ⟨2459788456156636414126225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3279717941542181885501633 2459788456156636414126225)
        ·
          refine ⟨1844841342117477310594669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2459788456156636414126225 1844841342117477310594669)
          ·
            refine ⟨691815503294053991473001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1844841342117477310594669 691815503294053991473001)
            ·
              refine ⟨518861627470540493604751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 691815503294053991473001 518861627470540493604751)
              ·
                refine ⟨778292441205810740407127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 518861627470540493604751 778292441205810740407127)
                ·
                  refine ⟨1167438661808716110610691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 778292441205810740407127 1167438661808716110610691)
                  ·
                    refine ⟨1751157992713074165916037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1167438661808716110610691 1751157992713074165916037)
                    ·
                      refine ⟨328342123633701406109257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1751157992713074165916037 328342123633701406109257)
                      ·
                        rfl

theorem cell23_639444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_639444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_639444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_639444 prefixEnd_639444 := by exact prefixLift 639444
  have htrace : WordTrace (prefixWord ++ tailWord_639444) baseStart_639444 baseEnd_639444 := by
    simpa [prefixWord, tailWord_639444, baseEnd_639444] using wordTrace_append hprefix tailTrace_639444
  have hstable : (prefixWord ++ tailWord_639444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639444).length < 2 ^ (prefixWord ++ tailWord_639444).sum := by decide
  have hdescent : baseEnd_639444 < baseStart_639444 := by decide
  rcases family_descends (prefixWord ++ tailWord_639444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639474 : List Nat := [3, 2, 1, 4, 3, 1, 1, 1, 1, 2, 4]
def baseStart_639474 : Nat := 118140960795 + 639474 * 2 ^ 59
def prefixEnd_639474 : Nat := 4983230072969 + 3 ^ 40 * 639474 * 2
def baseEnd_639474 : Nat := 328357528053336288734119

theorem tailTrace_639474 : CollatzResearch.WordTrace tailWord_639474 prefixEnd_639474 328357528053336288734119 := by
  unfold tailWord_639474
  simp only [CollatzResearch.WordTrace]
  refine ⟨5830883221325596577345369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15549021923534924206254317 5830883221325596577345369)
  ·
    refine ⟨4373162415994197433009027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5830883221325596577345369 4373162415994197433009027)
    ·
      refine ⟨6559743623991296149513541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4373162415994197433009027 6559743623991296149513541)
      ·
        refine ⟨1229951929498368028033789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6559743623991296149513541 1229951929498368028033789)
        ·
          refine ⟨461231973561888010512671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1229951929498368028033789 461231973561888010512671)
          ·
            refine ⟨691847960342832015769007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 461231973561888010512671 691847960342832015769007)
            ·
              refine ⟨1037771940514248023653511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 691847960342832015769007 1037771940514248023653511)
              ·
                refine ⟨1556657910771372035480267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1037771940514248023653511 1556657910771372035480267)
                ·
                  refine ⟨2334986866157058053220401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1556657910771372035480267 2334986866157058053220401)
                  ·
                    refine ⟨1751240149617793539915301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2334986866157058053220401 1751240149617793539915301)
                    ·
                      refine ⟨328357528053336288734119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1751240149617793539915301 328357528053336288734119)
                      ·
                        rfl

theorem cell23_639474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_639474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_639474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_639474 prefixEnd_639474 := by exact prefixLift 639474
  have htrace : WordTrace (prefixWord ++ tailWord_639474) baseStart_639474 baseEnd_639474 := by
    simpa [prefixWord, tailWord_639474, baseEnd_639474] using wordTrace_append hprefix tailTrace_639474
  have hstable : (prefixWord ++ tailWord_639474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639474).length < 2 ^ (prefixWord ++ tailWord_639474).sum := by decide
  have hdescent : baseEnd_639474 < baseStart_639474 := by decide
  rcases family_descends (prefixWord ++ tailWord_639474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639487 : List Nat := [1, 1, 2, 2, 1, 2, 6, 2, 1, 3, 2]
def baseStart_639487 : Nat := 118140960795 + 639487 * 2 ^ 59
def prefixEnd_639487 : Nat := 4983230072969 + 3 ^ 40 * 639487 * 2
def baseEnd_639487 : Nat := 328364203301844737871559

theorem tailTrace_639487 : CollatzResearch.WordTrace tailWord_639487 prefixEnd_639487 328364203301844737871559 := by
  unfold tailWord_639487
  simp only [CollatzResearch.WordTrace]
  refine ⟨23324007034255289529604715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15549338022836859686403143 23324007034255289529604715)
  ·
    refine ⟨34986010551382934294407073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23324007034255289529604715 34986010551382934294407073)
    ·
      refine ⟨26239507913537200720805305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34986010551382934294407073 26239507913537200720805305)
      ·
        refine ⟨19679630935152900540603979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26239507913537200720805305 19679630935152900540603979)
        ·
          refine ⟨29519446402729350810905969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19679630935152900540603979 29519446402729350810905969)
          ·
            refine ⟨22139584802047013108179477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29519446402729350810905969 22139584802047013108179477)
            ·
              refine ⟨1037793037595953739445913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22139584802047013108179477 1037793037595953739445913)
              ·
                refine ⟨778344778196965304584435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1037793037595953739445913 778344778196965304584435)
                ·
                  refine ⟨1167517167295447956876653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 778344778196965304584435 1167517167295447956876653)
                  ·
                    refine ⟨437818937735792983828745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1167517167295447956876653 437818937735792983828745)
                    ·
                      refine ⟨328364203301844737871559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 437818937735792983828745 328364203301844737871559)
                      ·
                        rfl

theorem cell23_639487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 2, 1, 3, 2].length) (baseStart_639487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_639487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_639487 prefixEnd_639487 := by exact prefixLift 639487
  have htrace : WordTrace (prefixWord ++ tailWord_639487) baseStart_639487 baseEnd_639487 := by
    simpa [prefixWord, tailWord_639487, baseEnd_639487] using wordTrace_append hprefix tailTrace_639487
  have hstable : (prefixWord ++ tailWord_639487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639487).length < 2 ^ (prefixWord ++ tailWord_639487).sum := by decide
  have hdescent : baseEnd_639487 < baseStart_639487 := by decide
  rcases family_descends (prefixWord ++ tailWord_639487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639560 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 4, 5, 2]
def baseStart_639560 : Nat := 118140960795 + 639560 * 2 ^ 59
def prefixEnd_639560 : Nat := 4983230072969 + 3 ^ 40 * 639560 * 2
def baseEnd_639560 : Nat := 328401687389622952258723

theorem tailTrace_639560 : CollatzResearch.WordTrace tailWord_639560 prefixEnd_639560 328401687389622952258723 := by
  unfold tailWord_639560
  simp only [CollatzResearch.WordTrace]
  refine ⟨11663334781495411498506067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15551113041993881998008089 11663334781495411498506067)
  ·
    refine ⟨17495002172243117247759101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11663334781495411498506067 17495002172243117247759101)
    ·
      refine ⟨6560625814591168967909663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17495002172243117247759101 6560625814591168967909663)
      ·
        refine ⟨9840938721886753451864495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6560625814591168967909663 9840938721886753451864495)
        ·
          refine ⟨14761408082830130177796743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9840938721886753451864495 14761408082830130177796743)
          ·
            refine ⟨22142112124245195266695115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14761408082830130177796743 22142112124245195266695115)
            ·
              refine ⟨33213168186367792900042673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22142112124245195266695115 33213168186367792900042673)
              ·
                refine ⟨24909876139775844675032005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33213168186367792900042673 24909876139775844675032005)
                ·
                  refine ⟨4670601776207970876568501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24909876139775844675032005 4670601776207970876568501)
                  ·
                    refine ⟨437868916519497269678297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4670601776207970876568501 437868916519497269678297)
                    ·
                      refine ⟨328401687389622952258723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 437868916519497269678297 328401687389622952258723)
                      ·
                        rfl

theorem cell23_639560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 4, 5, 2].length) (baseStart_639560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_639560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_639560 prefixEnd_639560 := by exact prefixLift 639560
  have htrace : WordTrace (prefixWord ++ tailWord_639560) baseStart_639560 baseEnd_639560 := by
    simpa [prefixWord, tailWord_639560, baseEnd_639560] using wordTrace_append hprefix tailTrace_639560
  have hstable : (prefixWord ++ tailWord_639560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639560).length < 2 ^ (prefixWord ++ tailWord_639560).sum := by decide
  have hdescent : baseEnd_639560 < baseStart_639560 := by decide
  rcases family_descends (prefixWord ++ tailWord_639560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639563 : List Nat := [1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 5]
def baseStart_639563 : Nat := 118140960795 + 639563 * 2 ^ 59
def prefixEnd_639563 : Nat := 4983230072969 + 3 ^ 40 * 639563 * 2
def baseEnd_639563 : Nat := 328403227831586440521209

theorem tailTrace_639563 : CollatzResearch.WordTrace tailWord_639563 prefixEnd_639563 328403227831586440521209 := by
  unfold tailWord_639563
  simp only [CollatzResearch.WordTrace]
  refine ⟨23326778981979954509371343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15551185987986636339580895 23326778981979954509371343)
  ·
    refine ⟨34990168472969931764057015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23326778981979954509371343 34990168472969931764057015)
    ·
      refine ⟨52485252709454897646085523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34990168472969931764057015 52485252709454897646085523)
      ·
        refine ⟨78727879064182346469128285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52485252709454897646085523 78727879064182346469128285)
        ·
          refine ⟨29522954649068379925923107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78727879064182346469128285 29522954649068379925923107)
          ·
            refine ⟨44284431973602569888884661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29522954649068379925923107 44284431973602569888884661)
            ·
              refine ⟨4151665497525240927082937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44284431973602569888884661 4151665497525240927082937)
              ·
                refine ⟨3113749123143930695312203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4151665497525240927082937 3113749123143930695312203)
                ·
                  refine ⟨4670623684715896042968305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3113749123143930695312203 4670623684715896042968305)
                  ·
                    refine ⟨3502967763536922032226229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4670623684715896042968305 3502967763536922032226229)
                    ·
                      refine ⟨328403227831586440521209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3502967763536922032226229 328403227831586440521209)
                      ·
                        rfl

theorem cell23_639563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 2, 5].length) (baseStart_639563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_639563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_639563 prefixEnd_639563 := by exact prefixLift 639563
  have htrace : WordTrace (prefixWord ++ tailWord_639563) baseStart_639563 baseEnd_639563 := by
    simpa [prefixWord, tailWord_639563, baseEnd_639563] using wordTrace_append hprefix tailTrace_639563
  have hstable : (prefixWord ++ tailWord_639563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639563).length < 2 ^ (prefixWord ++ tailWord_639563).sum := by decide
  have hdescent : baseEnd_639563 < baseStart_639563 := by decide
  rcases family_descends (prefixWord ++ tailWord_639563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639570 : List Nat := [3, 2, 2, 1, 2, 1, 1, 4, 2, 5]
def baseStart_639570 : Nat := 118140960795 + 639570 * 2 ^ 59
def prefixEnd_639570 : Nat := 4983230072969 + 3 ^ 40 * 639570 * 2
def baseEnd_639570 : Nat := 109468940732055971044559

theorem tailTrace_639570 : CollatzResearch.WordTrace tailWord_639570 prefixEnd_639570 109468940732055971044559 := by
  unfold tailWord_639570
  simp only [CollatzResearch.WordTrace]
  refine ⟨5831758573238648676219041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15551356195303063136584109 5831758573238648676219041)
  ·
    refine ⟨4373818929928986507164281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5831758573238648676219041 4373818929928986507164281)
    ·
      refine ⟨3280364197446739880373211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4373818929928986507164281 3280364197446739880373211)
      ·
        refine ⟨4920546296170109820559817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3280364197446739880373211 4920546296170109820559817)
        ·
          refine ⟨3690409722127582365419863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4920546296170109820559817 3690409722127582365419863)
          ·
            refine ⟨5535614583191373548129795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3690409722127582365419863 5535614583191373548129795)
            ·
              refine ⟨8303421874787060322194693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5535614583191373548129795 8303421874787060322194693)
              ·
                refine ⟨1556891601522573810411505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8303421874787060322194693 1556891601522573810411505)
                ·
                  refine ⟨1167668701141930357808629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1556891601522573810411505 1167668701141930357808629)
                  ·
                    refine ⟨109468940732055971044559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1167668701141930357808629 109468940732055971044559)
                    ·
                      rfl

theorem cell23_639570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_639570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_639570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_639570 prefixEnd_639570 := by exact prefixLift 639570
  have htrace : WordTrace (prefixWord ++ tailWord_639570) baseStart_639570 baseEnd_639570 := by
    simpa [prefixWord, tailWord_639570, baseEnd_639570] using wordTrace_append hprefix tailTrace_639570
  have hstable : (prefixWord ++ tailWord_639570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639570).length < 2 ^ (prefixWord ++ tailWord_639570).sum := by decide
  have hdescent : baseEnd_639570 < baseStart_639570 := by decide
  rcases family_descends (prefixWord ++ tailWord_639570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639603 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 1, 6, 4]
def baseStart_639603 : Nat := 118140960795 + 639603 * 2 ^ 59
def prefixEnd_639603 : Nat := 4983230072969 + 3 ^ 40 * 639603 * 2
def baseEnd_639603 : Nat := 328423767057766284021025

theorem tailTrace_639603 : CollatzResearch.WordTrace tailWord_639603 prefixEnd_639603 328423767057766284021025 := by
  unfold tailWord_639603
  simp only [CollatzResearch.WordTrace]
  refine ⟨23328237901835041340827463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15552158601223360893884975 23328237901835041340827463)
  ·
    refine ⟨34992356852752562011241195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23328237901835041340827463 34992356852752562011241195)
    ·
      refine ⟨52488535279128843016861793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34992356852752562011241195 52488535279128843016861793)
      ·
        refine ⟨39366401459346632262646345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52488535279128843016861793 39366401459346632262646345)
        ·
          refine ⟨29524801094509974196984759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39366401459346632262646345 29524801094509974196984759)
          ·
            refine ⟨44287201641764961295477139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29524801094509974196984759 44287201641764961295477139)
            ·
              refine ⟨66430802462647441943215709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44287201641764961295477139 66430802462647441943215709)
              ·
                refine ⟨24911550923492790728705891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66430802462647441943215709 24911550923492790728705891)
                ·
                  refine ⟨37367326385239186093058837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24911550923492790728705891 37367326385239186093058837)
                  ·
                    refine ⟨1751593424308086848112133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 37367326385239186093058837 1751593424308086848112133)
                    ·
                      refine ⟨328423767057766284021025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1751593424308086848112133 328423767057766284021025)
                      ·
                        rfl

theorem cell23_639603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 6, 4].length) (baseStart_639603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_639603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_639603 prefixEnd_639603 := by exact prefixLift 639603
  have htrace : WordTrace (prefixWord ++ tailWord_639603) baseStart_639603 baseEnd_639603 := by
    simpa [prefixWord, tailWord_639603, baseEnd_639603] using wordTrace_append hprefix tailTrace_639603
  have hstable : (prefixWord ++ tailWord_639603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639603).length < 2 ^ (prefixWord ++ tailWord_639603).sum := by decide
  have hdescent : baseEnd_639603 < baseStart_639603 := by decide
  rcases family_descends (prefixWord ++ tailWord_639603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639620 : List Nat := [2, 3, 2, 1, 3, 1, 1, 1, 2, 1, 6]
def baseStart_639620 : Nat := 118140960795 + 639620 * 2 ^ 59
def prefixEnd_639620 : Nat := 4983230072969 + 3 ^ 40 * 639620 * 2
def baseEnd_639620 : Nat := 328432496228892717508447

theorem tailTrace_639620 : CollatzResearch.WordTrace tailWord_639620 prefixEnd_639620 328432496228892717508447 := by
  unfold tailWord_639620
  simp only [CollatzResearch.WordTrace]
  refine ⟨11664428971386726622098157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15552571961848968829464209 11664428971386726622098157)
  ·
    refine ⟨4374160864270022483286809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11664428971386726622098157 4374160864270022483286809)
    ·
      refine ⟨3280620648202516862465107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4374160864270022483286809 3280620648202516862465107)
      ·
        refine ⟨4920930972303775293697661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3280620648202516862465107 4920930972303775293697661)
        ·
          refine ⟨1845349114613915735136623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4920930972303775293697661 1845349114613915735136623)
          ·
            refine ⟨2768023671920873602704935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1845349114613915735136623 2768023671920873602704935)
            ·
              refine ⟨4152035507881310404057403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2768023671920873602704935 4152035507881310404057403)
              ·
                refine ⟨6228053261821965606086105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4152035507881310404057403 6228053261821965606086105)
                ·
                  refine ⟨4671039946366474204564579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6228053261821965606086105 4671039946366474204564579)
                  ·
                    refine ⟨7006559919549711306846869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4671039946366474204564579 7006559919549711306846869)
                    ·
                      refine ⟨328432496228892717508447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7006559919549711306846869 328432496228892717508447)
                      ·
                        rfl

theorem cell23_639620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_639620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_639620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_639620 prefixEnd_639620 := by exact prefixLift 639620
  have htrace : WordTrace (prefixWord ++ tailWord_639620) baseStart_639620 baseEnd_639620 := by
    simpa [prefixWord, tailWord_639620, baseEnd_639620] using wordTrace_append hprefix tailTrace_639620
  have hstable : (prefixWord ++ tailWord_639620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639620).length < 2 ^ (prefixWord ++ tailWord_639620).sum := by decide
  have hdescent : baseEnd_639620 < baseStart_639620 := by decide
  rcases family_descends (prefixWord ++ tailWord_639620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639630 : List Nat := [4, 1, 1, 3, 1, 1, 3, 1, 8]
def baseStart_639630 : Nat := 118140960795 + 639630 * 2 ^ 59
def prefixEnd_639630 : Nat := 4983230072969 + 3 ^ 40 * 639630 * 2
def baseEnd_639630 : Nat := 36493070115048630931489

theorem tailTrace_639630 : CollatzResearch.WordTrace tailWord_639630 prefixEnd_639630 36493070115048630931489 := by
  unfold tailWord_639630
  simp only [CollatzResearch.WordTrace]
  refine ⟨2916152834092153119007543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15552815115158149968040229 2916152834092153119007543)
  ·
    refine ⟨4374229251138229678511315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2916152834092153119007543 4374229251138229678511315)
    ·
      refine ⟨6561343876707344517766973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4374229251138229678511315 6561343876707344517766973)
      ·
        refine ⟨2460503953765254194162615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6561343876707344517766973 2460503953765254194162615)
        ·
          refine ⟨3690755930647881291243923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2460503953765254194162615 3690755930647881291243923)
          ·
            refine ⟨5536133895971821936865885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3690755930647881291243923 5536133895971821936865885)
            ·
              refine ⟨2076050210989433226324707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5536133895971821936865885 2076050210989433226324707)
              ·
                refine ⟨3114075316484149839487061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2076050210989433226324707 3114075316484149839487061)
                ·
                  refine ⟨36493070115048630931489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3114075316484149839487061 36493070115048630931489)
                  ·
                    rfl

theorem cell23_639630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 8].length) (baseStart_639630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_639630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_639630 prefixEnd_639630 := by exact prefixLift 639630
  have htrace : WordTrace (prefixWord ++ tailWord_639630) baseStart_639630 baseEnd_639630 := by
    simpa [prefixWord, tailWord_639630, baseEnd_639630] using wordTrace_append hprefix tailTrace_639630
  have hstable : (prefixWord ++ tailWord_639630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639630).length < 2 ^ (prefixWord ++ tailWord_639630).sum := by decide
  have hdescent : baseEnd_639630 < baseStart_639630 := by decide
  rcases family_descends (prefixWord ++ tailWord_639630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639634 : List Nat := [3, 2, 3, 1, 2, 2, 2, 1, 3, 4]
def baseStart_639634 : Nat := 118140960795 + 639634 * 2 ^ 59
def prefixEnd_639634 : Nat := 4983230072969 + 3 ^ 40 * 639634 * 2
def baseEnd_639634 : Nat := 109479894986018554244461

theorem tailTrace_639634 : CollatzResearch.WordTrace tailWord_639634 prefixEnd_639634 109479894986018554244461 := by
  unfold tailWord_639634
  simp only [CollatzResearch.WordTrace]
  refine ⟨5832342141180683408801489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15552912376481822423470637 5832342141180683408801489)
  ·
    refine ⟨4374256605885512556601117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5832342141180683408801489 4374256605885512556601117)
    ·
      refine ⟨1640346227207067208725419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4374256605885512556601117 1640346227207067208725419)
      ·
        refine ⟨2460519340810600813088129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1640346227207067208725419 2460519340810600813088129)
        ·
          refine ⟨1845389505607950609816097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2460519340810600813088129 1845389505607950609816097)
          ·
            refine ⟨1384042129205962957362073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1845389505607950609816097 1384042129205962957362073)
            ·
              refine ⟨1038031596904472218021555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1384042129205962957362073 1038031596904472218021555)
              ·
                refine ⟨1557047395356708327032333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1038031596904472218021555 1557047395356708327032333)
                ·
                  refine ⟨583892773258765622637125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1557047395356708327032333 583892773258765622637125)
                  ·
                    refine ⟨109479894986018554244461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 583892773258765622637125 109479894986018554244461)
                    ·
                      rfl

theorem cell23_639634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_639634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_639634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_639634 prefixEnd_639634 := by exact prefixLift 639634
  have htrace : WordTrace (prefixWord ++ tailWord_639634) baseStart_639634 baseEnd_639634 := by
    simpa [prefixWord, tailWord_639634, baseEnd_639634] using wordTrace_append hprefix tailTrace_639634
  have hstable : (prefixWord ++ tailWord_639634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639634).length < 2 ^ (prefixWord ++ tailWord_639634).sum := by decide
  have hdescent : baseEnd_639634 < baseStart_639634 := by decide
  rcases family_descends (prefixWord ++ tailWord_639634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639667 : List Nat := [1, 1, 1, 2, 3, 4, 2, 1, 1, 5, 2]
def baseStart_639667 : Nat := 118140960795 + 639667 * 2 ^ 59
def prefixEnd_639667 : Nat := 4983230072969 + 3 ^ 40 * 639667 * 2
def baseEnd_639667 : Nat := 328456629819654033620731

theorem tailTrace_639667 : CollatzResearch.WordTrace tailWord_639667 prefixEnd_639667 328456629819654033620731 := by
  unfold tailWord_639667
  simp only [CollatzResearch.WordTrace]
  refine ⟨23330572173603180271157255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15553714782402120180771503 23330572173603180271157255)
  ·
    refine ⟨34995858260404770406735883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23330572173603180271157255 34995858260404770406735883)
    ·
      refine ⟨52493787390607155610103825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34995858260404770406735883 52493787390607155610103825)
      ·
        refine ⟨39370340542955366707577869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52493787390607155610103825 39370340542955366707577869)
        ·
          refine ⟨14763877703608262515341701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39370340542955366707577869 14763877703608262515341701)
          ·
            refine ⟨2768227069426549221626569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14763877703608262515341701 2768227069426549221626569)
            ·
              refine ⟨2076170302069911916219927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2768227069426549221626569 2076170302069911916219927)
              ·
                refine ⟨3114255453104867874329891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2076170302069911916219927 3114255453104867874329891)
                ·
                  refine ⟨4671383179657301811494837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3114255453104867874329891 4671383179657301811494837)
                  ·
                    refine ⟨437942173092872044827641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4671383179657301811494837 437942173092872044827641)
                    ·
                      refine ⟨328456629819654033620731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 437942173092872044827641 328456629819654033620731)
                      ·
                        rfl

theorem cell23_639667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 5, 2].length) (baseStart_639667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_639667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_639667 prefixEnd_639667 := by exact prefixLift 639667
  have htrace : WordTrace (prefixWord ++ tailWord_639667) baseStart_639667 baseEnd_639667 := by
    simpa [prefixWord, tailWord_639667, baseEnd_639667] using wordTrace_append hprefix tailTrace_639667
  have hstable : (prefixWord ++ tailWord_639667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639667).length < 2 ^ (prefixWord ++ tailWord_639667).sum := by decide
  have hdescent : baseEnd_639667 < baseStart_639667 := by decide
  rcases family_descends (prefixWord ++ tailWord_639667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639677 : List Nat := [1, 4, 1, 2, 1, 3, 2, 3, 1, 5]
def baseStart_639677 : Nat := 118140960795 + 639677 * 2 ^ 59
def prefixEnd_639677 : Nat := 4983230072969 + 3 ^ 40 * 639677 * 2
def baseEnd_639677 : Nat := 109487254875399664831895

theorem tailTrace_639677 : CollatzResearch.WordTrace tailWord_639677 prefixEnd_639677 109487254875399664831895 := by
  unfold tailWord_639677
  simp only [CollatzResearch.WordTrace]
  refine ⟨23330936903566951979021285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15553957935711301319347523 23330936903566951979021285)
  ·
    refine ⟨4374550669418803496066491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23330936903566951979021285 4374550669418803496066491)
    ·
      refine ⟨6561826004128205244099737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4374550669418803496066491 6561826004128205244099737)
      ·
        refine ⟨4921369503096153933074803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6561826004128205244099737 4921369503096153933074803)
        ·
          refine ⟨7382054254644230899612205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4921369503096153933074803 7382054254644230899612205)
          ·
            refine ⟨2768270345491586587354577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7382054254644230899612205 2768270345491586587354577)
            ·
              refine ⟨2076202759118689940515933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2768270345491586587354577 2076202759118689940515933)
              ·
                refine ⟨778576034669508727693475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2076202759118689940515933 778576034669508727693475)
                ·
                  refine ⟨1167864052004263091540213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 778576034669508727693475 1167864052004263091540213)
                  ·
                    refine ⟨109487254875399664831895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1167864052004263091540213 109487254875399664831895)
                    ·
                      rfl

theorem cell23_639677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 3, 1, 5].length) (baseStart_639677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_639677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_639677 prefixEnd_639677 := by exact prefixLift 639677
  have htrace : WordTrace (prefixWord ++ tailWord_639677) baseStart_639677 baseEnd_639677 := by
    simpa [prefixWord, tailWord_639677, baseEnd_639677] using wordTrace_append hprefix tailTrace_639677
  have hstable : (prefixWord ++ tailWord_639677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639677).length < 2 ^ (prefixWord ++ tailWord_639677).sum := by decide
  have hdescent : baseEnd_639677 < baseStart_639677 := by decide
  rcases family_descends (prefixWord ++ tailWord_639677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639684 : List Nat := [2, 3, 3, 1, 1, 2, 1, 1, 4, 3, 2]
def baseStart_639684 : Nat := 118140960795 + 639684 * 2 ^ 59
def prefixEnd_639684 : Nat := 4983230072969 + 3 ^ 40 * 639684 * 2
def baseEnd_639684 : Nat := 328465358990780467108153

theorem tailTrace_639684 : CollatzResearch.WordTrace tailWord_639684 prefixEnd_639684 328465358990780467108153 := by
  unfold tailWord_639684
  simp only [CollatzResearch.WordTrace]
  refine ⟨11665596107270796087263053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15554128143027728116350737 11665596107270796087263053)
  ·
    refine ⟨4374598540226548532723645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11665596107270796087263053 4374598540226548532723645)
    ·
      refine ⟨1640474452584955699771367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4374598540226548532723645 1640474452584955699771367)
      ·
        refine ⟨2460711678877433549657051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1640474452584955699771367 2460711678877433549657051)
        ·
          refine ⟨3691067518316150324485577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2460711678877433549657051 3691067518316150324485577)
          ·
            refine ⟨2768300638737112743364183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3691067518316150324485577 2768300638737112743364183)
            ·
              refine ⟨4152450958105669115046275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2768300638737112743364183 4152450958105669115046275)
              ·
                refine ⟨6228676437158503672569413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4152450958105669115046275 6228676437158503672569413)
                ·
                  refine ⟨1167876831967219438606765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6228676437158503672569413 1167876831967219438606765)
                  ·
                    refine ⟨437953811987707289477537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1167876831967219438606765 437953811987707289477537)
                    ·
                      refine ⟨328465358990780467108153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 437953811987707289477537 328465358990780467108153)
                      ·
                        rfl

theorem cell23_639684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_639684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_639684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_639684 prefixEnd_639684 := by exact prefixLift 639684
  have htrace : WordTrace (prefixWord ++ tailWord_639684) baseStart_639684 baseEnd_639684 := by
    simpa [prefixWord, tailWord_639684, baseEnd_639684] using wordTrace_append hprefix tailTrace_639684
  have hstable : (prefixWord ++ tailWord_639684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639684).length < 2 ^ (prefixWord ++ tailWord_639684).sum := by decide
  have hdescent : baseEnd_639684 < baseStart_639684 := by decide
  rcases family_descends (prefixWord ++ tailWord_639684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639727 : List Nat := [1, 1, 2, 1, 5, 3, 1, 2, 1, 2, 4]
def baseStart_639727 : Nat := 118140960795 + 639727 * 2 ^ 59
def prefixEnd_639727 : Nat := 4983230072969 + 3 ^ 40 * 639727 * 2
def baseEnd_639727 : Nat := 328487438658923798870455

theorem tailTrace_639727 : CollatzResearch.WordTrace tailWord_639727 prefixEnd_639727 328487438658923798870455 := by
  unfold tailWord_639727
  simp only [CollatzResearch.WordTrace]
  refine ⟨23332760553385810518341435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15555173702257207012227623 23332760553385810518341435)
  ·
    refine ⟨34999140830078715777512153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23332760553385810518341435 34999140830078715777512153)
    ·
      refine ⟨26249355622559036833134115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34999140830078715777512153 26249355622559036833134115)
      ·
        refine ⟨39374033433838555249701173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26249355622559036833134115 39374033433838555249701173)
        ·
          refine ⟨3691315634422364554659485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39374033433838555249701173 3691315634422364554659485)
          ·
            refine ⟨1384243362908386707997307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3691315634422364554659485 1384243362908386707997307)
            ·
              refine ⟨2076365044362580061995961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1384243362908386707997307 2076365044362580061995961)
              ·
                refine ⟨1557273783271935046496971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2076365044362580061995961 1557273783271935046496971)
                ·
                  refine ⟨2335910674907902569745457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1557273783271935046496971 2335910674907902569745457)
                  ·
                    refine ⟨1751933006180926927309093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2335910674907902569745457 1751933006180926927309093)
                    ·
                      refine ⟨328487438658923798870455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1751933006180926927309093 328487438658923798870455)
                      ·
                        rfl

theorem cell23_639727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 2, 4].length) (baseStart_639727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_639727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_639727 prefixEnd_639727 := by exact prefixLift 639727
  have htrace : WordTrace (prefixWord ++ tailWord_639727) baseStart_639727 baseEnd_639727 := by
    simpa [prefixWord, tailWord_639727, baseEnd_639727] using wordTrace_append hprefix tailTrace_639727
  have hstable : (prefixWord ++ tailWord_639727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639727).length < 2 ^ (prefixWord ++ tailWord_639727).sum := by decide
  have hdescent : baseEnd_639727 < baseStart_639727 := by decide
  rcases family_descends (prefixWord ++ tailWord_639727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639731 : List Nat := [1, 1, 1, 2, 2, 3, 1, 7, 1, 2, 2]
def baseStart_639731 : Nat := 118140960795 + 639731 * 2 ^ 59
def prefixEnd_639731 : Nat := 4983230072969 + 3 ^ 40 * 639731 * 2
def baseEnd_639731 : Nat := 328489492581541783220437

theorem tailTrace_639731 : CollatzResearch.WordTrace tailWord_639731 prefixEnd_639731 328489492581541783220437 := by
  unfold tailWord_639731
  simp only [CollatzResearch.WordTrace]
  refine ⟨23332906445371319201487047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15555270963580879467658031 23332906445371319201487047)
  ·
    refine ⟨34999359668056978802230571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23332906445371319201487047 34999359668056978802230571)
    ·
      refine ⟨52499039502085468203345857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34999359668056978802230571 52499039502085468203345857)
      ·
        refine ⟨39374279626564101152509393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52499039502085468203345857 39374279626564101152509393)
        ·
          refine ⟨29530709719923075864382045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39374279626564101152509393 29530709719923075864382045)
          ·
            refine ⟨11074016144971153449143267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29530709719923075864382045 11074016144971153449143267)
            ·
              refine ⟨16611024217456730173714901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11074016144971153449143267 16611024217456730173714901)
              ·
                refine ⟨389320880096642113446443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 16611024217456730173714901 389320880096642113446443)
                ·
                  refine ⟨583981320144963170169665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 389320880096642113446443 583981320144963170169665)
                  ·
                    refine ⟨437985990108722377627249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 583981320144963170169665 437985990108722377627249)
                    ·
                      refine ⟨328489492581541783220437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 437985990108722377627249 328489492581541783220437)
                      ·
                        rfl

theorem cell23_639731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 7, 1, 2, 2].length) (baseStart_639731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_639731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_639731 prefixEnd_639731 := by exact prefixLift 639731
  have htrace : WordTrace (prefixWord ++ tailWord_639731) baseStart_639731 baseEnd_639731 := by
    simpa [prefixWord, tailWord_639731, baseEnd_639731] using wordTrace_append hprefix tailTrace_639731
  have hstable : (prefixWord ++ tailWord_639731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639731).length < 2 ^ (prefixWord ++ tailWord_639731).sum := by decide
  have hdescent : baseEnd_639731 < baseStart_639731 := by decide
  rcases family_descends (prefixWord ++ tailWord_639731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639748 : List Nat := [2, 3, 2, 2, 1, 1, 3, 4, 1, 2, 2]
def baseStart_639748 : Nat := 118140960795 + 639748 * 2 ^ 59
def prefixEnd_639748 : Nat := 4983230072969 + 3 ^ 40 * 639748 * 2
def baseEnd_639748 : Nat := 328498221752668216707859

theorem tailTrace_639748 : CollatzResearch.WordTrace tailWord_639748 prefixEnd_639748 328498221752668216707859 := by
  unfold tailWord_639748
  simp only [CollatzResearch.WordTrace]
  refine ⟨11666763243154865552427949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15555684324206487403237265 11666763243154865552427949)
  ·
    refine ⟨4375036216183074582160481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11666763243154865552427949 4375036216183074582160481)
    ·
      refine ⟨3281277162137305936620361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4375036216183074582160481 3281277162137305936620361)
      ·
        refine ⟨2460957871602979452465271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3281277162137305936620361 2460957871602979452465271)
        ·
          refine ⟨3691436807404469178697907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2460957871602979452465271 3691436807404469178697907)
          ·
            refine ⟨5537155211106703768046861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3691436807404469178697907 5537155211106703768046861)
            ·
              refine ⟨2076433204165013913017573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5537155211106703768046861 2076433204165013913017573)
              ·
                refine ⟨389331225780940108690795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2076433204165013913017573 389331225780940108690795)
                ·
                  refine ⟨583996838671410163036193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 389331225780940108690795 583996838671410163036193)
                  ·
                    refine ⟨437997629003557622277145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 583996838671410163036193 437997629003557622277145)
                    ·
                      refine ⟨328498221752668216707859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 437997629003557622277145 328498221752668216707859)
                      ·
                        rfl

theorem cell23_639748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_639748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_639748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_639748 prefixEnd_639748 := by exact prefixLift 639748
  have htrace : WordTrace (prefixWord ++ tailWord_639748) baseStart_639748 baseEnd_639748 := by
    simpa [prefixWord, tailWord_639748, baseEnd_639748] using wordTrace_append hprefix tailTrace_639748
  have hstable : (prefixWord ++ tailWord_639748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639748).length < 2 ^ (prefixWord ++ tailWord_639748).sum := by decide
  have hdescent : baseEnd_639748 < baseStart_639748 := by decide
  rcases family_descends (prefixWord ++ tailWord_639748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639797 : List Nat := [1, 3, 3, 1, 3, 1, 1, 2, 2, 6]
def baseStart_639797 : Nat := 118140960795 + 639797 * 2 ^ 59
def prefixEnd_639797 : Nat := 4983230072969 + 3 ^ 40 * 639797 * 2
def baseEnd_639797 : Nat := 109507794101579508331711

theorem tailTrace_639797 : CollatzResearch.WordTrace tailWord_639797 prefixEnd_639797 109507794101579508331711 := by
  unfold tailWord_639797
  simp only [CollatzResearch.WordTrace]
  refine ⟨23335313663132212473389645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15556875775421474982259763 23335313663132212473389645)
  ·
    refine ⟨8750742623674579677521117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23335313663132212473389645 8750742623674579677521117)
    ·
      refine ⟨3281528483877967379070419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8750742623674579677521117 3281528483877967379070419)
      ·
        refine ⟨4922292725816951068605629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3281528483877967379070419 4922292725816951068605629)
        ·
          refine ⟨1845859772181356650727111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4922292725816951068605629 1845859772181356650727111)
          ·
            refine ⟨2768789658272034976090667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1845859772181356650727111 2768789658272034976090667)
            ·
              refine ⟨4153184487408052464136001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2768789658272034976090667 4153184487408052464136001)
              ·
                refine ⟨3114888365556039348102001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4153184487408052464136001 3114888365556039348102001)
                ·
                  refine ⟨2336166274167029511076501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3114888365556039348102001 2336166274167029511076501)
                  ·
                    refine ⟨109507794101579508331711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2336166274167029511076501 109507794101579508331711)
                    ·
                      rfl

theorem cell23_639797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_639797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_639797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_639797 prefixEnd_639797 := by exact prefixLift 639797
  have htrace : WordTrace (prefixWord ++ tailWord_639797) baseStart_639797 baseEnd_639797 := by
    simpa [prefixWord, tailWord_639797, baseEnd_639797] using wordTrace_append hprefix tailTrace_639797
  have hstable : (prefixWord ++ tailWord_639797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639797).length < 2 ^ (prefixWord ++ tailWord_639797).sum := by decide
  have hdescent : baseEnd_639797 < baseStart_639797 := by decide
  rcases family_descends (prefixWord ++ tailWord_639797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639798 : List Nat := [5, 1, 2, 2, 2, 1, 1, 1, 4, 1, 3]
def baseStart_639798 : Nat := 118140960795 + 639798 * 2 ^ 59
def prefixEnd_639798 : Nat := 4983230072969 + 3 ^ 40 * 639798 * 2
def baseEnd_639798 : Nat := 328523895785393021082629

theorem tailTrace_639798 : CollatzResearch.WordTrace tailWord_639798 prefixEnd_639798 328523895785393021082629 := by
  unfold tailWord_639798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1458459383508036852761003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15556900090752393096117365 1458459383508036852761003)
  ·
    refine ⟨2187689075262055279141505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1458459383508036852761003 2187689075262055279141505)
    ·
      refine ⟨1640766806446541459356129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2187689075262055279141505 1640766806446541459356129)
      ·
        refine ⟨1230575104834906094517097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1640766806446541459356129 1230575104834906094517097)
        ·
          refine ⟨922931328626179570887823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1230575104834906094517097 922931328626179570887823)
          ·
            refine ⟨1384396992939269356331735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 922931328626179570887823 1384396992939269356331735)
            ·
              refine ⟨2076595489408904034497603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1384396992939269356331735 2076595489408904034497603)
              ·
                refine ⟨3114893234113356051746405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2076595489408904034497603 3114893234113356051746405)
                ·
                  refine ⟨584042481396254259702451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3114893234113356051746405 584042481396254259702451)
                  ·
                    refine ⟨876063722094381389553677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 584042481396254259702451 876063722094381389553677)
                    ·
                      refine ⟨328523895785393021082629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 876063722094381389553677 328523895785393021082629)
                      ·
                        rfl

theorem cell23_639798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_639798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_639798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_639798 prefixEnd_639798 := by exact prefixLift 639798
  have htrace : WordTrace (prefixWord ++ tailWord_639798) baseStart_639798 baseEnd_639798 := by
    simpa [prefixWord, tailWord_639798, baseEnd_639798] using wordTrace_append hprefix tailTrace_639798
  have hstable : (prefixWord ++ tailWord_639798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639798).length < 2 ^ (prefixWord ++ tailWord_639798).sum := by decide
  have hdescent : baseEnd_639798 < baseStart_639798 := by decide
  rcases family_descends (prefixWord ++ tailWord_639798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639817 : List Nat := [1, 2, 1, 1, 2, 5, 2, 1, 2, 2, 4]
def baseStart_639817 : Nat := 118140960795 + 639817 * 2 ^ 59
def prefixEnd_639817 : Nat := 4983230072969 + 3 ^ 40 * 639817 * 2
def baseEnd_639817 : Nat := 328533651917828446745041

theorem tailTrace_639817 : CollatzResearch.WordTrace tailWord_639817 prefixEnd_639817 328533651917828446745041 := by
  unfold tailWord_639817
  simp only [CollatzResearch.WordTrace]
  refine ⟨23336043123059755889117705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15557362082039837259411803 23336043123059755889117705)
  ·
    refine ⟨17502032342294816916838279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23336043123059755889117705 17502032342294816916838279)
    ·
      refine ⟨26253048513442225375257419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17502032342294816916838279 26253048513442225375257419)
      ·
        refine ⟨39379572770163338062886129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26253048513442225375257419 39379572770163338062886129)
        ·
          refine ⟨29534679577622503547164597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39379572770163338062886129 29534679577622503547164597)
          ·
            refine ⟨2768876210402109707546681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29534679577622503547164597 2768876210402109707546681)
            ·
              refine ⟨2076657157801582280660011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2768876210402109707546681 2076657157801582280660011)
              ·
                refine ⟨3114985736702373420990017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2076657157801582280660011 3114985736702373420990017)
                ·
                  refine ⟨2336239302526780065742513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3114985736702373420990017 2336239302526780065742513)
                  ·
                    refine ⟨1752179476895085049306885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2336239302526780065742513 1752179476895085049306885)
                    ·
                      refine ⟨328533651917828446745041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1752179476895085049306885 328533651917828446745041)
                      ·
                        rfl

theorem cell23_639817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 2, 4].length) (baseStart_639817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_639817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_639817 prefixEnd_639817 := by exact prefixLift 639817
  have htrace : WordTrace (prefixWord ++ tailWord_639817) baseStart_639817 baseEnd_639817 := by
    simpa [prefixWord, tailWord_639817, baseEnd_639817] using wordTrace_append hprefix tailTrace_639817
  have hstable : (prefixWord ++ tailWord_639817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639817).length < 2 ^ (prefixWord ++ tailWord_639817).sum := by decide
  have hdescent : baseEnd_639817 < baseStart_639817 := by decide
  rcases family_descends (prefixWord ++ tailWord_639817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639857 : List Nat := [1, 2, 2, 2, 1, 4, 1, 1, 4, 5]
def baseStart_639857 : Nat := 118140960795 + 639857 * 2 ^ 59
def prefixEnd_639857 : Nat := 4983230072969 + 3 ^ 40 * 639857 * 2
def baseEnd_639857 : Nat := 109518063714669430081619

theorem tailTrace_639857 : CollatzResearch.WordTrace tailWord_639857 prefixEnd_639857 109518063714669430081619 := by
  unfold tailWord_639857
  simp only [CollatzResearch.WordTrace]
  refine ⟨23337502042914842720573825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15558334695276561813715883 23337502042914842720573825)
  ·
    refine ⟨17503126532186132040430369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23337502042914842720573825 17503126532186132040430369)
    ·
      refine ⟨13127344899139599030322777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17503126532186132040430369 13127344899139599030322777)
      ·
        refine ⟨9845508674354699272742083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13127344899139599030322777 9845508674354699272742083)
        ·
          refine ⟨14768263011532048909113125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9845508674354699272742083 14768263011532048909113125)
          ·
            refine ⟨2769049314662259170458711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14768263011532048909113125 2769049314662259170458711)
            ·
              refine ⟨4153573971993388755688067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2769049314662259170458711 4153573971993388755688067)
              ·
                refine ⟨6230360957990083133532101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4153573971993388755688067 6230360957990083133532101)
                ·
                  refine ⟨1168192679623140587537269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6230360957990083133532101 1168192679623140587537269)
                  ·
                    refine ⟨109518063714669430081619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1168192679623140587537269 109518063714669430081619)
                    ·
                      rfl

theorem cell23_639857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 4, 5].length) (baseStart_639857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_639857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_639857 prefixEnd_639857 := by exact prefixLift 639857
  have htrace : WordTrace (prefixWord ++ tailWord_639857) baseStart_639857 baseEnd_639857 := by
    simpa [prefixWord, tailWord_639857, baseEnd_639857] using wordTrace_append hprefix tailTrace_639857
  have hstable : (prefixWord ++ tailWord_639857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639857).length < 2 ^ (prefixWord ++ tailWord_639857).sum := by decide
  have hdescent : baseEnd_639857 < baseStart_639857 := by decide
  rcases family_descends (prefixWord ++ tailWord_639857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639934 : List Nat := [4, 2, 1, 1, 1, 2, 1, 5, 6]
def baseStart_639934 : Nat := 118140960795 + 639934 * 2 ^ 59
def prefixEnd_639934 : Nat := 4983230072969 + 3 ^ 40 * 639934 * 2
def baseEnd_639934 : Nat := 36510414350489387664667

theorem tailTrace_639934 : CollatzResearch.WordTrace tailWord_639934 prefixEnd_639934 36510414350489387664667 := by
  unfold tailWord_639934
  simp only [CollatzResearch.WordTrace]
  refine ⟨2917538807954485608890857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15560206975757256580751237 2917538807954485608890857)
  ·
    refine ⟨2188154105965864206668143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2917538807954485608890857 2188154105965864206668143)
    ·
      refine ⟨3282231158948796310002215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2188154105965864206668143 3282231158948796310002215)
      ·
        refine ⟨4923346738423194465003323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3282231158948796310002215 4923346738423194465003323)
        ·
          refine ⟨7385020107634791697504985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4923346738423194465003323 7385020107634791697504985)
          ·
            refine ⟨5538765080726093773128739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7385020107634791697504985 5538765080726093773128739)
            ·
              refine ⟨8308147621089140659693109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5538765080726093773128739 8308147621089140659693109)
              ·
                refine ⟨778888839477106936846229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8308147621089140659693109 778888839477106936846229)
                ·
                  refine ⟨36510414350489387664667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 778888839477106936846229 36510414350489387664667)
                  ·
                    rfl

theorem cell23_639934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 5, 6].length) (baseStart_639934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_639934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_639934 prefixEnd_639934 := by exact prefixLift 639934
  have htrace : WordTrace (prefixWord ++ tailWord_639934) baseStart_639934 baseEnd_639934 := by
    simpa [prefixWord, tailWord_639934, baseEnd_639934] using wordTrace_append hprefix tailTrace_639934
  have hstable : (prefixWord ++ tailWord_639934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639934).length < 2 ^ (prefixWord ++ tailWord_639934).sum := by decide
  have hdescent : baseEnd_639934 < baseStart_639934 := by decide
  rcases family_descends (prefixWord ++ tailWord_639934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639971 : List Nat := [1, 1, 1, 6, 1, 1, 2, 1, 4, 3, 2]
def baseStart_639971 : Nat := 118140960795 + 639971 * 2 ^ 59
def prefixEnd_639971 : Nat := 4983230072969 + 3 ^ 40 * 639971 * 2
def baseEnd_639971 : Nat := 328612727938620844219333

theorem tailTrace_639971 : CollatzResearch.WordTrace tailWord_639971 prefixEnd_639971 328612727938620844219333 := by
  unfold tailWord_639971
  simp only [CollatzResearch.WordTrace]
  refine ⟨23341659964501840190223767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15561106643001226793482511 23341659964501840190223767)
  ·
    refine ⟨35012489946752760285335651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23341659964501840190223767 35012489946752760285335651)
    ·
      refine ⟨52518734920129140428003477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35012489946752760285335651 52518734920129140428003477)
      ·
        refine ⟨2461815699381053457562663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 52518734920129140428003477 2461815699381053457562663)
        ·
          refine ⟨3692723549071580186343995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2461815699381053457562663 3692723549071580186343995)
          ·
            refine ⟨5539085323607370279515993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3692723549071580186343995 5539085323607370279515993)
            ·
              refine ⟨4154313992705527709636995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5539085323607370279515993 4154313992705527709636995)
              ·
                refine ⟨6231470989058291564455493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4154313992705527709636995 6231470989058291564455493)
                ·
                  refine ⟨1168400810448429668335405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6231470989058291564455493 1168400810448429668335405)
                  ·
                    refine ⟨438150303918161125625777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1168400810448429668335405 438150303918161125625777)
                    ·
                      refine ⟨328612727938620844219333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 438150303918161125625777 328612727938620844219333)
                      ·
                        rfl

theorem cell23_639971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_639971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_639971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_639971 prefixEnd_639971 := by exact prefixLift 639971
  have htrace : WordTrace (prefixWord ++ tailWord_639971) baseStart_639971 baseEnd_639971 := by
    simpa [prefixWord, tailWord_639971, baseEnd_639971] using wordTrace_append hprefix tailTrace_639971
  have hstable : (prefixWord ++ tailWord_639971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639971).length < 2 ^ (prefixWord ++ tailWord_639971).sum := by decide
  have hdescent : baseEnd_639971 < baseStart_639971 := by decide
  rcases family_descends (prefixWord ++ tailWord_639971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_639978 : List Nat := [3, 1, 3, 1, 2, 3, 2, 1, 3, 1, 3]
def baseStart_639978 : Nat := 118140960795 + 639978 * 2 ^ 59
def prefixEnd_639978 : Nat := 4983230072969 + 3 ^ 40 * 639978 * 2
def baseEnd_639978 : Nat := 328616322303202316831801

theorem tailTrace_639978 : CollatzResearch.WordTrace tailWord_639978 prefixEnd_639978 328616322303202316831801 := by
  unfold tailWord_639978
  simp only [CollatzResearch.WordTrace]
  refine ⟨5835478818869120096432147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15561276850317653590485725 5835478818869120096432147)
  ·
    refine ⟨8753218228303680144648221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5835478818869120096432147 8753218228303680144648221)
    ·
      refine ⟨3282456835613880054243083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8753218228303680144648221 3282456835613880054243083)
      ·
        refine ⟨4923685253420820081364625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3282456835613880054243083 4923685253420820081364625)
        ·
          refine ⟨3692763940065615061023469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4923685253420820081364625 3692763940065615061023469)
          ·
            refine ⟨1384786477524605647883801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3692763940065615061023469 1384786477524605647883801)
            ·
              refine ⟨1038589858143454235912851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1384786477524605647883801 1038589858143454235912851)
              ·
                refine ⟨1557884787215181353869277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1038589858143454235912851 1557884787215181353869277)
                ·
                  refine ⟨584206795205693007700979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1557884787215181353869277 584206795205693007700979)
                  ·
                    refine ⟨876310192808539511551469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 584206795205693007700979 876310192808539511551469)
                    ·
                      refine ⟨328616322303202316831801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 876310192808539511551469 328616322303202316831801)
                      ·
                        rfl

theorem cell23_639978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_639978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_639978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_639978 prefixEnd_639978 := by exact prefixLift 639978
  have htrace : WordTrace (prefixWord ++ tailWord_639978) baseStart_639978 baseEnd_639978 := by
    simpa [prefixWord, tailWord_639978, baseEnd_639978] using wordTrace_append hprefix tailTrace_639978
  have hstable : (prefixWord ++ tailWord_639978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_639978).length < 2 ^ (prefixWord ++ tailWord_639978).sum := by decide
  have hdescent : baseEnd_639978 < baseStart_639978 := by decide
  rcases family_descends (prefixWord ++ tailWord_639978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640001 : List Nat := [1, 2, 4, 1, 2, 2, 1, 4, 1, 1, 4]
def baseStart_640001 : Nat := 118140960795 + 640001 * 2 ^ 59
def prefixEnd_640001 : Nat := 4983230072969 + 3 ^ 40 * 640001 * 2
def baseEnd_640001 : Nat := 328628132358255726844195

theorem tailTrace_640001 : CollatzResearch.WordTrace tailWord_640001 prefixEnd_640001 328628132358255726844195 := by
  unfold tailWord_640001
  simp only [CollatzResearch.WordTrace]
  refine ⟨23342754154393155313815857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15561836102928770209210571 23342754154393155313815857)
  ·
    refine ⟨17507065615794866485361893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23342754154393155313815857 17507065615794866485361893)
    ·
      refine ⟨3282574802961537466005355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17507065615794866485361893 3282574802961537466005355)
      ·
        refine ⟨4923862204442306199008033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3282574802961537466005355 4923862204442306199008033)
        ·
          refine ⟨3692896653331729649256025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4923862204442306199008033 3692896653331729649256025)
          ·
            refine ⟨2769672489998797236942019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3692896653331729649256025 2769672489998797236942019)
            ·
              refine ⟨4154508734998195855413029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2769672489998797236942019 4154508734998195855413029)
              ·
                refine ⟨778970387812161722889943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4154508734998195855413029 778970387812161722889943)
                ·
                  refine ⟨1168455581718242584334915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 778970387812161722889943 1168455581718242584334915)
                  ·
                    refine ⟨1752683372577363876502373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1168455581718242584334915 1752683372577363876502373)
                    ·
                      refine ⟨328628132358255726844195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1752683372577363876502373 328628132358255726844195)
                      ·
                        rfl

theorem cell23_640001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_640001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_640001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_640001 prefixEnd_640001 := by exact prefixLift 640001
  have htrace : WordTrace (prefixWord ++ tailWord_640001) baseStart_640001 baseEnd_640001 := by
    simpa [prefixWord, tailWord_640001, baseEnd_640001] using wordTrace_append hprefix tailTrace_640001
  have hstable : (prefixWord ++ tailWord_640001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640001).length < 2 ^ (prefixWord ++ tailWord_640001).sum := by decide
  have hdescent : baseEnd_640001 < baseStart_640001 := by decide
  rcases family_descends (prefixWord ++ tailWord_640001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640021 : List Nat := [1, 3, 2, 1, 4, 2, 2, 1, 1, 1, 5]
def baseStart_640021 : Nat := 118140960795 + 640021 * 2 ^ 59
def prefixEnd_640021 : Nat := 4983230072969 + 3 ^ 40 * 640021 * 2
def baseEnd_640021 : Nat := 328638401971345648594103

theorem tailTrace_640021 : CollatzResearch.WordTrace tailWord_640021 prefixEnd_640021 328638401971345648594103 := by
  unfold tailWord_640021
  simp only [CollatzResearch.WordTrace]
  refine ⟨23343483614320698729543917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15562322409547132486362611 23343483614320698729543917)
  ·
    refine ⟨8753806355370262023578969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23343483614320698729543917 8753806355370262023578969)
    ·
      refine ⟨6565354766527696517684227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8753806355370262023578969 6565354766527696517684227)
      ·
        refine ⟨9848032149791544776526341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6565354766527696517684227 9848032149791544776526341)
        ·
          refine ⟨1846506028085914645598689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9848032149791544776526341 1846506028085914645598689)
          ·
            refine ⟨1384879521064435984199017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1846506028085914645598689 1384879521064435984199017)
            ·
              refine ⟨1038659640798326988149263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1384879521064435984199017 1038659640798326988149263)
              ·
                refine ⟨1557989461197490482223895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1038659640798326988149263 1557989461197490482223895)
                ·
                  refine ⟨2336984191796235723335843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1557989461197490482223895 2336984191796235723335843)
                  ·
                    refine ⟨3505476287694353585003765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2336984191796235723335843 3505476287694353585003765)
                    ·
                      refine ⟨328638401971345648594103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3505476287694353585003765 328638401971345648594103)
                      ·
                        rfl

theorem cell23_640021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 1, 5].length) (baseStart_640021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_640021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_640021 prefixEnd_640021 := by exact prefixLift 640021
  have htrace : WordTrace (prefixWord ++ tailWord_640021) baseStart_640021 baseEnd_640021 := by
    simpa [prefixWord, tailWord_640021, baseEnd_640021] using wordTrace_append hprefix tailTrace_640021
  have hstable : (prefixWord ++ tailWord_640021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640021).length < 2 ^ (prefixWord ++ tailWord_640021).sum := by decide
  have hdescent : baseEnd_640021 < baseStart_640021 := by decide
  rcases family_descends (prefixWord ++ tailWord_640021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640024 : List Nat := [2, 1, 2, 3, 2, 4, 9]
def baseStart_640024 : Nat := 118140960795 + 640024 * 2 ^ 59
def prefixEnd_640024 : Nat := 4983230072969 + 3 ^ 40 * 640024 * 2
def baseEnd_640024 : Nat := 4057283239670483171069

theorem tailTrace_640024 : CollatzResearch.WordTrace tailWord_640024 prefixEnd_640024 4057283239670483171069 := by
  unfold tailWord_640024
  simp only [CollatzResearch.WordTrace]
  refine ⟨11671796516654915120951563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15562395355539886827935417 11671796516654915120951563)
  ·
    refine ⟨17507694774982372681427345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11671796516654915120951563 17507694774982372681427345)
    ·
      refine ⟨13130771081236779511070509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17507694774982372681427345 13130771081236779511070509)
      ·
        refine ⟨4924039155463792316651441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13130771081236779511070509 4924039155463792316651441)
        ·
          refine ⟨3693029366597844237488581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4924039155463792316651441 3693029366597844237488581)
          ·
            refine ⟨692443006237095794529109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3693029366597844237488581 692443006237095794529109)
            ·
              refine ⟨4057283239670483171069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 692443006237095794529109 4057283239670483171069)
              ·
                rfl

theorem cell23_640024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 9].length) (baseStart_640024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_640024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_640024 prefixEnd_640024 := by exact prefixLift 640024
  have htrace : WordTrace (prefixWord ++ tailWord_640024) baseStart_640024 baseEnd_640024 := by
    simpa [prefixWord, tailWord_640024, baseEnd_640024] using wordTrace_append hprefix tailTrace_640024
  have hstable : (prefixWord ++ tailWord_640024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640024).length < 2 ^ (prefixWord ++ tailWord_640024).sum := by decide
  have hdescent : baseEnd_640024 < baseStart_640024 := by decide
  rcases family_descends (prefixWord ++ tailWord_640024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640035 : List Nat := [1, 1, 1, 4, 3, 4, 1, 1, 3, 2, 2]
def baseStart_640035 : Nat := 118140960795 + 640035 * 2 ^ 59
def prefixEnd_640035 : Nat := 4983230072969 + 3 ^ 40 * 640035 * 2
def baseEnd_640035 : Nat := 328645590700508593819039

theorem tailTrace_640035 : CollatzResearch.WordTrace tailWord_640035 prefixEnd_640035 328645590700508593819039 := by
  unfold tailWord_640035
  simp only [CollatzResearch.WordTrace]
  refine ⟨23343994236269979120553559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15562662824179986080369039 23343994236269979120553559)
  ·
    refine ⟨35015991354404968680830339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23343994236269979120553559 35015991354404968680830339)
    ·
      refine ⟨52523987031607453021245509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35015991354404968680830339 52523987031607453021245509)
      ·
        refine ⟨9848247568426397441483533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52523987031607453021245509 9848247568426397441483533)
        ·
          refine ⟨3693092838159899040556325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9848247568426397441483533 3693092838159899040556325)
          ·
            refine ⟨692454907154981070104311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3693092838159899040556325 692454907154981070104311)
            ·
              refine ⟨1038682360732471605156467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 692454907154981070104311 1038682360732471605156467)
              ·
                refine ⟨1558023541098707407734701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1038682360732471605156467 1558023541098707407734701)
                ·
                  refine ⟨584258827912015277900513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1558023541098707407734701 584258827912015277900513)
                  ·
                    refine ⟨438194120934011458425385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 584258827912015277900513 438194120934011458425385)
                    ·
                      refine ⟨328645590700508593819039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 438194120934011458425385 328645590700508593819039)
                      ·
                        rfl

theorem cell23_640035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 3, 2, 2].length) (baseStart_640035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_640035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_640035 prefixEnd_640035 := by exact prefixLift 640035
  have htrace : WordTrace (prefixWord ++ tailWord_640035) baseStart_640035 baseEnd_640035 := by
    simpa [prefixWord, tailWord_640035, baseEnd_640035] using wordTrace_append hprefix tailTrace_640035
  have hstable : (prefixWord ++ tailWord_640035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640035).length < 2 ^ (prefixWord ++ tailWord_640035).sum := by decide
  have hdescent : baseEnd_640035 < baseStart_640035 := by decide
  rcases family_descends (prefixWord ++ tailWord_640035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640086 : List Nat := [5, 2, 2, 1, 2, 1, 1, 4, 1, 2, 2]
def baseStart_640086 : Nat := 118140960795 + 640086 * 2 ^ 59
def prefixEnd_640086 : Nat := 4983230072969 + 3 ^ 40 * 640086 * 2
def baseEnd_640086 : Nat := 328671778213887894281305

theorem tailTrace_640086 : CollatzResearch.WordTrace tailWord_640086 prefixEnd_640086 328671778213887894281305 := by
  unfold tailWord_640086
  simp only [CollatzResearch.WordTrace]
  refine ⟨1459115897442825926916257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15563902906056809887106741 1459115897442825926916257)
  ·
    refine ⟨1094336923082119445187193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1459115897442825926916257 1094336923082119445187193)
    ·
      refine ⟨820752692311589583890395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1094336923082119445187193 820752692311589583890395)
      ·
        refine ⟨1231129038467384375835593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 820752692311589583890395 1231129038467384375835593)
        ·
          refine ⟨923346778850538281876695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1231129038467384375835593 923346778850538281876695)
          ·
            refine ⟨1385020168275807422815043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 923346778850538281876695 1385020168275807422815043)
            ·
              refine ⟨2077530252413711134222565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1385020168275807422815043 2077530252413711134222565)
              ·
                refine ⟨389536922327570837666731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2077530252413711134222565 389536922327570837666731)
                ·
                  refine ⟨584305383491356256500097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 389536922327570837666731 584305383491356256500097)
                  ·
                    refine ⟨438229037618517192375073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 584305383491356256500097 438229037618517192375073)
                    ·
                      refine ⟨328671778213887894281305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 438229037618517192375073 328671778213887894281305)
                      ·
                        rfl

theorem cell23_640086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_640086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_640086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_640086 prefixEnd_640086 := by exact prefixLift 640086
  have htrace : WordTrace (prefixWord ++ tailWord_640086) baseStart_640086 baseEnd_640086 := by
    simpa [prefixWord, tailWord_640086, baseEnd_640086] using wordTrace_append hprefix tailTrace_640086
  have hstable : (prefixWord ++ tailWord_640086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640086).length < 2 ^ (prefixWord ++ tailWord_640086).sum := by decide
  have hdescent : baseEnd_640086 < baseStart_640086 := by decide
  rcases family_descends (prefixWord ++ tailWord_640086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640108 : List Nat := [2, 2, 1, 1, 3, 2, 4, 1, 1, 4, 2]
def baseStart_640108 : Nat := 118140960795 + 640108 * 2 ^ 59
def prefixEnd_640108 : Nat := 4983230072969 + 3 ^ 40 * 640108 * 2
def baseEnd_640108 : Nat := 328683074788286808206203

theorem tailTrace_640108 : CollatzResearch.WordTrace tailWord_640108 prefixEnd_640108 328683074788286808206203 := by
  unfold tailWord_640108
  simp only [CollatzResearch.WordTrace]
  refine ⟨11673328382502756293980489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15564437843337008391973985 11673328382502756293980489)
  ·
    refine ⟨8754996286877067220485367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11673328382502756293980489 8754996286877067220485367)
    ·
      refine ⟨13132494430315600830728051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8754996286877067220485367 13132494430315600830728051)
      ·
        refine ⟨19698741645473401246092077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13132494430315600830728051 19698741645473401246092077)
        ·
          refine ⟨7387028117052525467284529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19698741645473401246092077 7387028117052525467284529)
          ·
            refine ⟨5540271087789394100463397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7387028117052525467284529 5540271087789394100463397)
            ·
              refine ⟨1038800828960511393836887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5540271087789394100463397 1038800828960511393836887)
              ·
                refine ⟨1558201243440767090755331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1038800828960511393836887 1558201243440767090755331)
                ·
                  refine ⟨2337301865161150636132997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1558201243440767090755331 2337301865161150636132997)
                  ·
                    refine ⟨438244099717715744274937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2337301865161150636132997 438244099717715744274937)
                    ·
                      refine ⟨328683074788286808206203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 438244099717715744274937 328683074788286808206203)
                      ·
                        rfl

theorem cell23_640108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 4, 2].length) (baseStart_640108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_640108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_640108 prefixEnd_640108 := by exact prefixLift 640108
  have htrace : WordTrace (prefixWord ++ tailWord_640108) baseStart_640108 baseEnd_640108 := by
    simpa [prefixWord, tailWord_640108, baseEnd_640108] using wordTrace_append hprefix tailTrace_640108
  have hstable : (prefixWord ++ tailWord_640108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640108).length < 2 ^ (prefixWord ++ tailWord_640108).sum := by decide
  have hdescent : baseEnd_640108 < baseStart_640108 := by decide
  rcases family_descends (prefixWord ++ tailWord_640108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640142 : List Nat := [4, 1, 1, 3, 2, 1, 3, 2, 2, 2, 2]
def baseStart_640142 : Nat := 118140960795 + 640142 * 2 ^ 59
def prefixEnd_640142 : Nat := 4983230072969 + 3 ^ 40 * 640142 * 2
def baseEnd_640142 : Nat := 328700533130539675181047

theorem tailTrace_640142 : CollatzResearch.WordTrace tailWord_640142 prefixEnd_640142 328700533130539675181047 := by
  unfold tailWord_640142
  simp only [CollatzResearch.WordTrace]
  refine ⟨2918487105860292049337335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15565264564588224263132453 2918487105860292049337335)
  ·
    refine ⟨4377730658790438074006003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2918487105860292049337335 4377730658790438074006003)
    ·
      refine ⟨6566595988185657111009005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4377730658790438074006003 6566595988185657111009005)
      ·
        refine ⟨2462473495569621416628377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6566595988185657111009005 2462473495569621416628377)
        ·
          refine ⟨1846855121677216062471283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2462473495569621416628377 1846855121677216062471283)
          ·
            refine ⟨2770282682515824093706925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1846855121677216062471283 2770282682515824093706925)
            ·
              refine ⟨1038856005943434035140097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2770282682515824093706925 1038856005943434035140097)
              ·
                refine ⟨779142004457575526355073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1038856005943434035140097 779142004457575526355073)
                ·
                  refine ⟨584356503343181644766305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 779142004457575526355073 584356503343181644766305)
                  ·
                    refine ⟨438267377507386233574729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 584356503343181644766305 438267377507386233574729)
                    ·
                      refine ⟨328700533130539675181047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 438267377507386233574729 328700533130539675181047)
                      ·
                        rfl

theorem cell23_640142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_640142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_640142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_640142 prefixEnd_640142 := by exact prefixLift 640142
  have htrace : WordTrace (prefixWord ++ tailWord_640142) baseStart_640142 baseEnd_640142 := by
    simpa [prefixWord, tailWord_640142, baseEnd_640142] using wordTrace_append hprefix tailTrace_640142
  have hstable : (prefixWord ++ tailWord_640142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640142).length < 2 ^ (prefixWord ++ tailWord_640142).sum := by decide
  have hdescent : baseEnd_640142 < baseStart_640142 := by decide
  rcases family_descends (prefixWord ++ tailWord_640142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640159 : List Nat := [1, 1, 2, 6, 2, 1, 3, 1, 2, 2, 2]
def baseStart_640159 : Nat := 118140960795 + 640159 * 2 ^ 59
def prefixEnd_640159 : Nat := 4983230072969 + 3 ^ 40 * 640159 * 2
def baseEnd_640159 : Nat := 328709262301666108668469

theorem tailTrace_640159 : CollatzResearch.WordTrace tailWord_640159 prefixEnd_640159 328709262301666108668469 := by
  unfold tailWord_640159
  simp only [CollatzResearch.WordTrace]
  refine ⟨23348516887820748298067531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15565677925213832198711687 23348516887820748298067531)
  ·
    refine ⟨35022775331731122447101297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23348516887820748298067531 35022775331731122447101297)
    ·
      refine ⟨26267081498798341835325973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35022775331731122447101297 26267081498798341835325973)
      ·
        refine ⟨1231269445256172273530905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 26267081498798341835325973 1231269445256172273530905)
        ·
          refine ⟨923452083942129205148179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1231269445256172273530905 923452083942129205148179)
          ·
            refine ⟨1385178125913193807722269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 923452083942129205148179 1385178125913193807722269)
            ·
              refine ⟨519441797217447677895851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1385178125913193807722269 519441797217447677895851)
              ·
                refine ⟨779162695826171516843777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 519441797217447677895851 779162695826171516843777)
                ·
                  refine ⟨584372021869628637632833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 779162695826171516843777 584372021869628637632833)
                  ·
                    refine ⟨438279016402221478224625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 584372021869628637632833 438279016402221478224625)
                    ·
                      refine ⟨328709262301666108668469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 438279016402221478224625 328709262301666108668469)
                      ·
                        rfl

theorem cell23_640159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_640159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_640159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_640159 prefixEnd_640159 := by exact prefixLift 640159
  have htrace : WordTrace (prefixWord ++ tailWord_640159) baseStart_640159 baseEnd_640159 := by
    simpa [prefixWord, tailWord_640159, baseEnd_640159] using wordTrace_append hprefix tailTrace_640159
  have hstable : (prefixWord ++ tailWord_640159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640159).length < 2 ^ (prefixWord ++ tailWord_640159).sum := by decide
  have hdescent : baseEnd_640159 < baseStart_640159 := by decide
  rcases family_descends (prefixWord ++ tailWord_640159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640191 : List Nat := [1, 1, 2, 2, 2, 2, 2, 2, 5, 4]
def baseStart_640191 : Nat := 118140960795 + 640191 * 2 ^ 59
def prefixEnd_640191 : Nat := 4983230072969 + 3 ^ 40 * 640191 * 2
def baseEnd_640191 : Nat := 109575231227536661156107

theorem tailTrace_640191 : CollatzResearch.WordTrace tailWord_640191 prefixEnd_640191 109575231227536661156107 := by
  unfold tailWord_640191
  simp only [CollatzResearch.WordTrace]
  refine ⟨23349684023704817763232427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15566456015803211842154951 23349684023704817763232427)
  ·
    refine ⟨35024526035557226644848641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23349684023704817763232427 35024526035557226644848641)
    ·
      refine ⟨26268394526667919983636481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35024526035557226644848641 26268394526667919983636481)
      ·
        refine ⟨19701295895000939987727361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26268394526667919983636481 19701295895000939987727361)
        ·
          refine ⟨14775971921250704990795521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19701295895000939987727361 14775971921250704990795521)
          ·
            refine ⟨11081978940938028743096641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14775971921250704990795521 11081978940938028743096641)
            ·
              refine ⟨8311484205703521557322481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11081978940938028743096641 8311484205703521557322481)
              ·
                refine ⟨6233613154277641167991861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8311484205703521557322481 6233613154277641167991861)
                ·
                  refine ⟨584401233213528859499237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6233613154277641167991861 584401233213528859499237)
                  ·
                    refine ⟨109575231227536661156107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 584401233213528859499237 109575231227536661156107)
                    ·
                      rfl

theorem cell23_640191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 5, 4].length) (baseStart_640191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_640191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_640191 prefixEnd_640191 := by exact prefixLift 640191
  have htrace : WordTrace (prefixWord ++ tailWord_640191) baseStart_640191 baseEnd_640191 := by
    simpa [prefixWord, tailWord_640191, baseEnd_640191] using wordTrace_append hprefix tailTrace_640191
  have hstable : (prefixWord ++ tailWord_640191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640191).length < 2 ^ (prefixWord ++ tailWord_640191).sum := by decide
  have hdescent : baseEnd_640191 < baseStart_640191 := by decide
  rcases family_descends (prefixWord ++ tailWord_640191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640286 : List Nat := [4, 3, 2, 1, 3, 1, 1, 1, 2, 2, 3]
def baseStart_640286 : Nat := 118140960795 + 640286 * 2 ^ 59
def prefixEnd_640286 : Nat := 4983230072969 + 3 ^ 40 * 640286 * 2
def baseEnd_640286 : Nat := 328774474344787111780385

theorem tailTrace_640286 : CollatzResearch.WordTrace tailWord_640286 prefixEnd_640286 328774474344787111780385 := by
  unfold tailWord_640286
  simp only [CollatzResearch.WordTrace]
  refine ⟨2919143619795081123492589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15568765972240432658627141 2919143619795081123492589)
  ·
    refine ⟨1094678857423155421309721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2919143619795081123492589 1094678857423155421309721)
    ·
      refine ⟨821009143067366565982291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1094678857423155421309721 821009143067366565982291)
      ·
        refine ⟨1231513714601049848973437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 821009143067366565982291 1231513714601049848973437)
        ·
          refine ⟨461817642975393693365039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1231513714601049848973437 461817642975393693365039)
          ·
            refine ⟨692726464463090540047559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 461817642975393693365039 692726464463090540047559)
            ·
              refine ⟨1039089696694635810071339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 692726464463090540047559 1039089696694635810071339)
              ·
                refine ⟨1558634545041953715107009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1039089696694635810071339 1558634545041953715107009)
                ·
                  refine ⟨1168975908781465286330257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1558634545041953715107009 1168975908781465286330257)
                  ·
                    refine ⟨876731931586098964747693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1168975908781465286330257 876731931586098964747693)
                    ·
                      refine ⟨328774474344787111780385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 876731931586098964747693 328774474344787111780385)
                      ·
                        rfl

theorem cell23_640286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_640286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_640286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_640286 prefixEnd_640286 := by exact prefixLift 640286
  have htrace : WordTrace (prefixWord ++ tailWord_640286) baseStart_640286 baseEnd_640286 := by
    simpa [prefixWord, tailWord_640286, baseEnd_640286] using wordTrace_append hprefix tailTrace_640286
  have hstable : (prefixWord ++ tailWord_640286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640286).length < 2 ^ (prefixWord ++ tailWord_640286).sum := by decide
  have hdescent : baseEnd_640286 < baseStart_640286 := by decide
  rcases family_descends (prefixWord ++ tailWord_640286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640305 : List Nat := [1, 2, 2, 3, 3, 2, 1, 3, 1, 1, 4]
def baseStart_640305 : Nat := 118140960795 + 640305 * 2 ^ 59
def prefixEnd_640305 : Nat := 4983230072969 + 3 ^ 40 * 640305 * 2
def baseEnd_640305 : Nat := 328784230477222537442797

theorem tailTrace_640305 : CollatzResearch.WordTrace tailWord_640305 prefixEnd_640305 328784230477222537442797 := by
  unfold tailWord_640305
  simp only [CollatzResearch.WordTrace]
  refine ⟨23353841945291815232882369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15569227963527876821921579 23353841945291815232882369)
  ·
    refine ⟨17515381458968861424661777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23353841945291815232882369 17515381458968861424661777)
    ·
      refine ⟨13136536094226646068496333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17515381458968861424661777 13136536094226646068496333)
      ·
        refine ⟨4926201035334992275686125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13136536094226646068496333 4926201035334992275686125)
        ·
          refine ⟨1847325388250622103382297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4926201035334992275686125 1847325388250622103382297)
          ·
            refine ⟨1385494041187966577536723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1847325388250622103382297 1385494041187966577536723)
            ·
              refine ⟨2078241061781949866305085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1385494041187966577536723 2078241061781949866305085)
              ·
                refine ⟨779340398168231199864407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2078241061781949866305085 779340398168231199864407)
                ·
                  refine ⟨1169010597252346799796611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 779340398168231199864407 1169010597252346799796611)
                  ·
                    refine ⟨1753515895878520199694917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1169010597252346799796611 1753515895878520199694917)
                    ·
                      refine ⟨328784230477222537442797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1753515895878520199694917 328784230477222537442797)
                      ·
                        rfl

theorem cell23_640305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_640305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_640305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_640305 prefixEnd_640305 := by exact prefixLift 640305
  have htrace : WordTrace (prefixWord ++ tailWord_640305) baseStart_640305 baseEnd_640305 := by
    simpa [prefixWord, tailWord_640305, baseEnd_640305] using wordTrace_append hprefix tailTrace_640305
  have hstable : (prefixWord ++ tailWord_640305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640305).length < 2 ^ (prefixWord ++ tailWord_640305).sum := by decide
  have hdescent : baseEnd_640305 < baseStart_640305 := by decide
  rcases family_descends (prefixWord ++ tailWord_640305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640318 : List Nat := [4, 2, 1, 2, 1, 1, 2, 2, 1, 1, 6]
def baseStart_640318 : Nat := 118140960795 + 640318 * 2 ^ 59
def prefixEnd_640318 : Nat := 4983230072969 + 3 ^ 40 * 640318 * 2
def baseEnd_640318 : Nat := 328790905725730986580237

theorem tailTrace_640318 : CollatzResearch.WordTrace tailWord_640318 prefixEnd_640318 328790905725730986580237 := by
  unfold tailWord_640318
  simp only [CollatzResearch.WordTrace]
  refine ⟨2919289511780589806638201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15569544062829812302070405 2919289511780589806638201)
  ·
    refine ⟨2189467133835442354978651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2919289511780589806638201 2189467133835442354978651)
    ·
      refine ⟨3284200700753163532467977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2189467133835442354978651 3284200700753163532467977)
      ·
        refine ⟨2463150525564872649350983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3284200700753163532467977 2463150525564872649350983)
        ·
          refine ⟨3694725788347308974026475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2463150525564872649350983 3694725788347308974026475)
          ·
            refine ⟨5542088682520963461039713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3694725788347308974026475 5542088682520963461039713)
            ·
              refine ⟨4156566511890722595779785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5542088682520963461039713 4156566511890722595779785)
              ·
                refine ⟨3117424883918041946834839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4156566511890722595779785 3117424883918041946834839)
                ·
                  refine ⟨4676137325877062920252259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3117424883918041946834839 4676137325877062920252259)
                  ·
                    refine ⟨7014205988815594380378389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4676137325877062920252259 7014205988815594380378389)
                    ·
                      refine ⟨328790905725730986580237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7014205988815594380378389 328790905725730986580237)
                      ·
                        rfl

theorem cell23_640318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_640318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_640318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_640318 prefixEnd_640318 := by exact prefixLift 640318
  have htrace : WordTrace (prefixWord ++ tailWord_640318) baseStart_640318 baseEnd_640318 := by
    simpa [prefixWord, tailWord_640318, baseEnd_640318] using wordTrace_append hprefix tailTrace_640318
  have hstable : (prefixWord ++ tailWord_640318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640318).length < 2 ^ (prefixWord ++ tailWord_640318).sum := by decide
  have hdescent : baseEnd_640318 < baseStart_640318 := by decide
  rcases family_descends (prefixWord ++ tailWord_640318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640332 : List Nat := [2, 2, 1, 3, 2, 3, 3, 1, 2, 4]
def baseStart_640332 : Nat := 118140960795 + 640332 * 2 ^ 59
def prefixEnd_640332 : Nat := 4983230072969 + 3 ^ 40 * 640332 * 2
def baseEnd_640332 : Nat := 109599364818297977268391

theorem tailTrace_640332 : CollatzResearch.WordTrace tailWord_640332 prefixEnd_640332 109599364818297977268391 := by
  unfold tailWord_640332
  simp only [CollatzResearch.WordTrace]
  refine ⟨11677413358096999422057625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15569884477462665896076833 11677413358096999422057625)
  ·
    refine ⟨8758060018572749566543219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11677413358096999422057625 8758060018572749566543219)
    ·
      refine ⟨13137090027859124349814829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8758060018572749566543219 13137090027859124349814829)
      ·
        refine ⟨4926408760447171631180561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13137090027859124349814829 4926408760447171631180561)
        ·
          refine ⟨3694806570335378723385421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4926408760447171631180561 3694806570335378723385421)
          ·
            refine ⟨1385552463875767021269533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3694806570335378723385421 1385552463875767021269533)
            ·
              refine ⟨519582173953412632976075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1385552463875767021269533 519582173953412632976075)
              ·
                refine ⟨779373260930118949464113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 519582173953412632976075 779373260930118949464113)
                ·
                  refine ⟨584529945697589212098085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 779373260930118949464113 584529945697589212098085)
                  ·
                    refine ⟨109599364818297977268391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 584529945697589212098085 109599364818297977268391)
                    ·
                      rfl

theorem cell23_640332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 1, 2, 4].length) (baseStart_640332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_640332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_640332 prefixEnd_640332 := by exact prefixLift 640332
  have htrace : WordTrace (prefixWord ++ tailWord_640332) baseStart_640332 baseEnd_640332 := by
    simpa [prefixWord, tailWord_640332, baseEnd_640332] using wordTrace_append hprefix tailTrace_640332
  have hstable : (prefixWord ++ tailWord_640332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640332).length < 2 ^ (prefixWord ++ tailWord_640332).sum := by decide
  have hdescent : baseEnd_640332 < baseStart_640332 := by decide
  rcases family_descends (prefixWord ++ tailWord_640332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640355 : List Nat := [1, 1, 1, 5, 2, 2, 1, 2, 4, 1, 3]
def baseStart_640355 : Nat := 118140960795 + 640355 * 2 ^ 59
def prefixEnd_640355 : Nat := 4983230072969 + 3 ^ 40 * 640355 * 2
def baseEnd_640355 : Nat := 328809904509947341817567

theorem tailTrace_640355 : CollatzResearch.WordTrace tailWord_640355 prefixEnd_640355 328809904509947341817567 := by
  unfold tailWord_640355
  simp only [CollatzResearch.WordTrace]
  refine ⟨23355665595110673772202519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15570443730073782514801679 23355665595110673772202519)
  ·
    refine ⟨35033498392666010658303779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23355665595110673772202519 35033498392666010658303779)
    ·
      refine ⟨52550247588999015987455669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35033498392666010658303779 52550247588999015987455669)
      ·
        refine ⟨4926585711468657748823969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52550247588999015987455669 4926585711468657748823969)
        ·
          refine ⟨3694939283601493311617977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4926585711468657748823969 3694939283601493311617977)
          ·
            refine ⟨2771204462701119983713483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3694939283601493311617977 2771204462701119983713483)
            ·
              refine ⟨4156806694051679975570225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2771204462701119983713483 4156806694051679975570225)
              ·
                refine ⟨3117605020538759981677669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4156806694051679975570225 3117605020538759981677669)
                ·
                  refine ⟨584550941351017496564563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3117605020538759981677669 584550941351017496564563)
                  ·
                    refine ⟨876826412026526244846845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 584550941351017496564563 876826412026526244846845)
                    ·
                      refine ⟨328809904509947341817567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 876826412026526244846845 328809904509947341817567)
                      ·
                        rfl

theorem cell23_640355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_640355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_640355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_640355 prefixEnd_640355 := by exact prefixLift 640355
  have htrace : WordTrace (prefixWord ++ tailWord_640355) baseStart_640355 baseEnd_640355 := by
    simpa [prefixWord, tailWord_640355, baseEnd_640355] using wordTrace_append hprefix tailTrace_640355
  have hstable : (prefixWord ++ tailWord_640355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640355).length < 2 ^ (prefixWord ++ tailWord_640355).sum := by decide
  have hdescent : baseEnd_640355 < baseStart_640355 := by decide
  rcases family_descends (prefixWord ++ tailWord_640355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640356 : List Nat := [2, 3, 1, 1, 3, 4, 1, 3, 1, 2, 2]
def baseStart_640356 : Nat := 118140960795 + 640356 * 2 ^ 59
def prefixEnd_640356 : Nat := 4983230072969 + 3 ^ 40 * 640356 * 2
def baseEnd_640356 : Nat := 328810417990601837905063

theorem tailTrace_640356 : CollatzResearch.WordTrace tailWord_640356 prefixEnd_640356 328810417990601837905063 := by
  unfold tailWord_640356
  simp only [CollatzResearch.WordTrace]
  refine ⟨11677851034053525471494461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15570468045404700628659281 11677851034053525471494461)
  ·
    refine ⟨4379194137770072051810423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11677851034053525471494461 4379194137770072051810423)
    ·
      refine ⟨6568791206655108077715635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4379194137770072051810423 6568791206655108077715635)
      ·
        refine ⟨9853186809982662116573453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6568791206655108077715635 9853186809982662116573453)
        ·
          refine ⟨3694945053743498293715045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9853186809982662116573453 3694945053743498293715045)
          ·
            refine ⟨692802197576905930071571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3694945053743498293715045 692802197576905930071571)
            ·
              refine ⟨1039203296365358895107357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 692802197576905930071571 1039203296365358895107357)
              ·
                refine ⟨389701236137009585665259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1039203296365358895107357 389701236137009585665259)
                ·
                  refine ⟨584551854205514378497889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 389701236137009585665259 584551854205514378497889)
                  ·
                    refine ⟨438413890654135783873417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 584551854205514378497889 438413890654135783873417)
                    ·
                      refine ⟨328810417990601837905063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 438413890654135783873417 328810417990601837905063)
                      ·
                        rfl

theorem cell23_640356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 3, 1, 2, 2].length) (baseStart_640356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_640356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_640356 prefixEnd_640356 := by exact prefixLift 640356
  have htrace : WordTrace (prefixWord ++ tailWord_640356) baseStart_640356 baseEnd_640356 := by
    simpa [prefixWord, tailWord_640356, baseEnd_640356] using wordTrace_append hprefix tailTrace_640356
  have hstable : (prefixWord ++ tailWord_640356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640356).length < 2 ^ (prefixWord ++ tailWord_640356).sum := by decide
  have hdescent : baseEnd_640356 < baseStart_640356 := by decide
  rcases family_descends (prefixWord ++ tailWord_640356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640373 : List Nat := [1, 3, 4, 1, 3, 1, 3, 2, 1, 2, 2]
def baseStart_640373 : Nat := 118140960795 + 640373 * 2 ^ 59
def prefixEnd_640373 : Nat := 4983230072969 + 3 ^ 40 * 640373 * 2
def baseEnd_640373 : Nat := 328819147161728271392485

theorem tailTrace_640373 : CollatzResearch.WordTrace tailWord_640373 prefixEnd_640373 328819147161728271392485 := by
  unfold tailWord_640373
  simp only [CollatzResearch.WordTrace]
  refine ⟨23356322109045462846357773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15570881406030308564238515 23356322109045462846357773)
  ·
    refine ⟨8758620790892048567384165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23356322109045462846357773 8758620790892048567384165)
    ·
      refine ⟨1642241398292259106384531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8758620790892048567384165 1642241398292259106384531)
      ·
        refine ⟨2463362097438388659576797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1642241398292259106384531 2463362097438388659576797)
        ·
          refine ⟨923760786539395747341299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2463362097438388659576797 923760786539395747341299)
          ·
            refine ⟨1385641179809093621011949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 923760786539395747341299 1385641179809093621011949)
            ·
              refine ⟨519615442428410107879481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1385641179809093621011949 519615442428410107879481)
              ·
                refine ⟨389711581821307580909611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 519615442428410107879481 389711581821307580909611)
                ·
                  refine ⟨584567372731961371364417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 389711581821307580909611 584567372731961371364417)
                  ·
                    refine ⟨438425529548971028523313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 584567372731961371364417 438425529548971028523313)
                    ·
                      refine ⟨328819147161728271392485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 438425529548971028523313 328819147161728271392485)
                      ·
                        rfl

theorem cell23_640373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_640373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_640373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_640373 prefixEnd_640373 := by exact prefixLift 640373
  have htrace : WordTrace (prefixWord ++ tailWord_640373) baseStart_640373 baseEnd_640373 := by
    simpa [prefixWord, tailWord_640373, baseEnd_640373] using wordTrace_append hprefix tailTrace_640373
  have hstable : (prefixWord ++ tailWord_640373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640373).length < 2 ^ (prefixWord ++ tailWord_640373).sum := by decide
  have hdescent : baseEnd_640373 < baseStart_640373 := by decide
  rcases family_descends (prefixWord ++ tailWord_640373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640395 : List Nat := [1, 1, 1, 1, 4, 3, 2, 3, 1, 4, 2]
def baseStart_640395 : Nat := 118140960795 + 640395 * 2 ^ 59
def prefixEnd_640395 : Nat := 4983230072969 + 3 ^ 40 * 640395 * 2
def baseEnd_640395 : Nat := 328830443736127185317383

theorem tailTrace_640395 : CollatzResearch.WordTrace tailWord_640395 prefixEnd_640395 328830443736127185317383 := by
  unfold tailWord_640395
  simp only [CollatzResearch.WordTrace]
  refine ⟨23357124514965760603658639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15571416343310507069105759 23357124514965760603658639)
  ·
    refine ⟨35035686772448640905487959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23357124514965760603658639 35035686772448640905487959)
    ·
      refine ⟨52553530158672961358231939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35035686772448640905487959 52553530158672961358231939)
      ·
        refine ⟨78830295238009442037347909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52553530158672961358231939 78830295238009442037347909)
        ·
          refine ⟨14780680357126770382002733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78830295238009442037347909 14780680357126770382002733)
          ·
            refine ⟨5542755133922538893251025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14780680357126770382002733 5542755133922538893251025)
            ·
              refine ⟨4157066350441904169938269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5542755133922538893251025 4157066350441904169938269)
              ·
                refine ⟨1558899881415714063726851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4157066350441904169938269 1558899881415714063726851)
                ·
                  refine ⟨2338349822123571095590277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1558899881415714063726851 2338349822123571095590277)
                  ·
                    refine ⟨438440591648169580423177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2338349822123571095590277 438440591648169580423177)
                    ·
                      refine ⟨328830443736127185317383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 438440591648169580423177 328830443736127185317383)
                      ·
                        rfl

theorem cell23_640395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 4, 2].length) (baseStart_640395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_640395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_640395 prefixEnd_640395 := by exact prefixLift 640395
  have htrace : WordTrace (prefixWord ++ tailWord_640395) baseStart_640395 baseEnd_640395 := by
    simpa [prefixWord, tailWord_640395, baseEnd_640395] using wordTrace_append hprefix tailTrace_640395
  have hstable : (prefixWord ++ tailWord_640395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640395).length < 2 ^ (prefixWord ++ tailWord_640395).sum := by decide
  have hdescent : baseEnd_640395 < baseStart_640395 := by decide
  rcases family_descends (prefixWord ++ tailWord_640395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640445 : List Nat := [1, 4, 1, 2, 2, 1, 3, 1, 2, 3, 3]
def baseStart_640445 : Nat := 118140960795 + 640445 * 2 ^ 59
def prefixEnd_640445 : Nat := 4983230072969 + 3 ^ 40 * 640445 * 2
def baseEnd_640445 : Nat := 328856117768851989692153

theorem tailTrace_640445 : CollatzResearch.WordTrace tailWord_640445 prefixEnd_640445 328856117768851989692153 := by
  unfold tailWord_640445
  simp only [CollatzResearch.WordTrace]
  refine ⟨23358948164784619142978789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15572632109856412761985859 23358948164784619142978789)
  ·
    refine ⟨4379802780897116089308523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23358948164784619142978789 4379802780897116089308523)
    ·
      refine ⟨6569704171345674133962785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4379802780897116089308523 6569704171345674133962785)
      ·
        refine ⟨4927278128509255600472089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6569704171345674133962785 4927278128509255600472089)
        ·
          refine ⟨3695458596381941700354067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4927278128509255600472089 3695458596381941700354067)
          ·
            refine ⟨5543187894572912550531101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3695458596381941700354067 5543187894572912550531101)
            ·
              refine ⟨2078695460464842206449163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5543187894572912550531101 2078695460464842206449163)
              ·
                refine ⟨3118043190697263309673745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2078695460464842206449163 3118043190697263309673745)
                ·
                  refine ⟨2338532393022947482255309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3118043190697263309673745 2338532393022947482255309)
                  ·
                    refine ⟨876949647383605305845741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2338532393022947482255309 876949647383605305845741)
                    ·
                      refine ⟨328856117768851989692153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 876949647383605305845741 328856117768851989692153)
                      ·
                        rfl

theorem cell23_640445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_640445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_640445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_640445 prefixEnd_640445 := by exact prefixLift 640445
  have htrace : WordTrace (prefixWord ++ tailWord_640445) baseStart_640445 baseEnd_640445 := by
    simpa [prefixWord, tailWord_640445, baseEnd_640445] using wordTrace_append hprefix tailTrace_640445
  have hstable : (prefixWord ++ tailWord_640445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640445).length < 2 ^ (prefixWord ++ tailWord_640445).sum := by decide
  have hdescent : baseEnd_640445 < baseStart_640445 := by decide
  rcases family_descends (prefixWord ++ tailWord_640445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640448 : List Nat := [2, 1, 1, 2, 3, 1, 2, 2, 4, 5]
def baseStart_640448 : Nat := 118140960795 + 640448 * 2 ^ 59
def prefixEnd_640448 : Nat := 4983230072969 + 3 ^ 40 * 640448 * 2
def baseEnd_640448 : Nat := 109619219403605159318213

theorem tailTrace_640448 : CollatzResearch.WordTrace tailWord_640448 prefixEnd_640448 109619219403605159318213 := by
  unfold tailWord_640448
  simp only [CollatzResearch.WordTrace]
  refine ⟨11679528791886875327668999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15572705055849167103558665 11679528791886875327668999)
  ·
    refine ⟨17519293187830312991503499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11679528791886875327668999 17519293187830312991503499)
    ·
      refine ⟨26278939781745469487255249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17519293187830312991503499 26278939781745469487255249)
      ·
        refine ⟨19709204836309102115441437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26278939781745469487255249 19709204836309102115441437)
        ·
          refine ⟨7390951813615913293290539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19709204836309102115441437 7390951813615913293290539)
          ·
            refine ⟨11086427720423869939935809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7390951813615913293290539 11086427720423869939935809)
            ·
              refine ⟨8314820790317902454951857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11086427720423869939935809 8314820790317902454951857)
              ·
                refine ⟨6236115592738426841213893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8314820790317902454951857 6236115592738426841213893)
                ·
                  refine ⟨1169271673638455032727605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6236115592738426841213893 1169271673638455032727605)
                  ·
                    refine ⟨109619219403605159318213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1169271673638455032727605 109619219403605159318213)
                    ·
                      rfl

theorem cell23_640448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 4, 5].length) (baseStart_640448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_640448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_640448 prefixEnd_640448 := by exact prefixLift 640448
  have htrace : WordTrace (prefixWord ++ tailWord_640448) baseStart_640448 baseEnd_640448 := by
    simpa [prefixWord, tailWord_640448, baseEnd_640448] using wordTrace_append hprefix tailTrace_640448
  have hstable : (prefixWord ++ tailWord_640448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640448).length < 2 ^ (prefixWord ++ tailWord_640448).sum := by decide
  have hdescent : baseEnd_640448 < baseStart_640448 := by decide
  rcases family_descends (prefixWord ++ tailWord_640448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640455 : List Nat := [1, 1, 4, 1, 1, 3, 1, 2, 2, 5, 2]
def baseStart_640455 : Nat := 118140960795 + 640455 * 2 ^ 59
def prefixEnd_640455 : Nat := 4983230072969 + 3 ^ 40 * 640455 * 2
def baseEnd_640455 : Nat := 328861252575396950567107

theorem tailTrace_640455 : CollatzResearch.WordTrace tailWord_640455 prefixEnd_640455 328861252575396950567107 := by
  unfold tailWord_640455
  simp only [CollatzResearch.WordTrace]
  refine ⟨23359312894748390850842819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15572875263165593900561879 23359312894748390850842819)
  ·
    refine ⟨35038969342122586276264229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23359312894748390850842819 35038969342122586276264229)
    ·
      refine ⟨6569806751647984926799543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35038969342122586276264229 6569806751647984926799543)
      ·
        refine ⟨9854710127471977390199315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6569806751647984926799543 9854710127471977390199315)
        ·
          refine ⟨14782065191207966085298973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9854710127471977390199315 14782065191207966085298973)
          ·
            refine ⟨5543274446702987281987115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14782065191207966085298973 5543274446702987281987115)
            ·
              refine ⟨8314911670054480922980673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5543274446702987281987115 8314911670054480922980673)
              ·
                refine ⟨6236183752540860692235505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8314911670054480922980673 6236183752540860692235505)
                ·
                  refine ⟨4677137814405645519176629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6236183752540860692235505 4677137814405645519176629)
                  ·
                    refine ⟨438481670100529267422809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4677137814405645519176629 438481670100529267422809)
                    ·
                      refine ⟨328861252575396950567107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 438481670100529267422809 328861252575396950567107)
                      ·
                        rfl

theorem cell23_640455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 5, 2].length) (baseStart_640455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_640455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_640455 prefixEnd_640455 := by exact prefixLift 640455
  have htrace : WordTrace (prefixWord ++ tailWord_640455) baseStart_640455 baseEnd_640455 := by
    simpa [prefixWord, tailWord_640455, baseEnd_640455] using wordTrace_append hprefix tailTrace_640455
  have hstable : (prefixWord ++ tailWord_640455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640455).length < 2 ^ (prefixWord ++ tailWord_640455).sum := by decide
  have hdescent : baseEnd_640455 < baseStart_640455 := by decide
  rcases family_descends (prefixWord ++ tailWord_640455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640495 : List Nat := [1, 1, 2, 1, 4, 1, 3, 3, 3, 4]
def baseStart_640495 : Nat := 118140960795 + 640495 * 2 ^ 59
def prefixEnd_640495 : Nat := 4983230072969 + 3 ^ 40 * 640495 * 2
def baseEnd_640495 : Nat := 109627263933858931355641

theorem tailTrace_640495 : CollatzResearch.WordTrace tailWord_640495 prefixEnd_640495 109627263933858931355641 := by
  unfold tailWord_640495
  simp only [CollatzResearch.WordTrace]
  refine ⟨23360771814603477682298939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15573847876402318454865959 23360771814603477682298939)
  ·
    refine ⟨35041157721905216523448409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23360771814603477682298939 35041157721905216523448409)
    ·
      refine ⟨26280868291428912392586307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35041157721905216523448409 26280868291428912392586307)
      ·
        refine ⟨39421302437143368588879461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26280868291428912392586307 39421302437143368588879461)
        ·
          refine ⟨7391494206964381610414899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39421302437143368588879461 7391494206964381610414899)
          ·
            refine ⟨11087241310446572415622349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7391494206964381610414899 11087241310446572415622349)
            ·
              refine ⟨4157715491417464655858381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11087241310446572415622349 4157715491417464655858381)
              ·
                refine ⟨1559143309281549245946893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4157715491417464655858381 1559143309281549245946893)
                ·
                  refine ⟨584678740980580967230085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1559143309281549245946893 584678740980580967230085)
                  ·
                    refine ⟨109627263933858931355641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 584678740980580967230085 109627263933858931355641)
                    ·
                      rfl

theorem cell23_640495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 3, 4].length) (baseStart_640495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_640495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_640495 prefixEnd_640495 := by exact prefixLift 640495
  have htrace : WordTrace (prefixWord ++ tailWord_640495) baseStart_640495 baseEnd_640495 := by
    simpa [prefixWord, tailWord_640495, baseEnd_640495] using wordTrace_append hprefix tailTrace_640495
  have hstable : (prefixWord ++ tailWord_640495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640495).length < 2 ^ (prefixWord ++ tailWord_640495).sum := by decide
  have hdescent : baseEnd_640495 < baseStart_640495 := by decide
  rcases family_descends (prefixWord ++ tailWord_640495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640562 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2]
def baseStart_640562 : Nat := 118140960795 + 640562 * 2 ^ 59
def prefixEnd_640562 : Nat := 4983230072969 + 3 ^ 40 * 640562 * 2
def baseEnd_640562 : Nat := 328916195005428031929115

theorem tailTrace_640562 : CollatzResearch.WordTrace tailWord_640562 prefixEnd_640562 328916195005428031929115 := by
  unfold tailWord_640562
  simp only [CollatzResearch.WordTrace]
  refine ⟨5840803876340187031246985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15575477003573832083325293 5840803876340187031246985)
  ·
    refine ⟨4380602907255140273435239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5840803876340187031246985 4380602907255140273435239)
    ·
      refine ⟨6570904360882710410152859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4380602907255140273435239 6570904360882710410152859)
      ·
        refine ⟨9856356541324065615229289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6570904360882710410152859 9856356541324065615229289)
        ·
          refine ⟨7392267405993049211421967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9856356541324065615229289 7392267405993049211421967)
          ·
            refine ⟨11088401108989573817132951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7392267405993049211421967 11088401108989573817132951)
            ·
              refine ⟨16632601663484360725699427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11088401108989573817132951 16632601663484360725699427)
              ·
                refine ⟨24948902495226541088549141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16632601663484360725699427 24948902495226541088549141)
                ·
                  refine ⟨1169479804463744113525741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 24948902495226541088549141 1169479804463744113525741)
                  ·
                    refine ⟨438554926673904042572153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1169479804463744113525741 438554926673904042572153)
                    ·
                      refine ⟨328916195005428031929115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 438554926673904042572153 328916195005428031929115)
                      ·
                        rfl

theorem cell23_640562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2].length) (baseStart_640562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_640562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_640562 prefixEnd_640562 := by exact prefixLift 640562
  have htrace : WordTrace (prefixWord ++ tailWord_640562) baseStart_640562 baseEnd_640562 := by
    simpa [prefixWord, tailWord_640562, baseEnd_640562] using wordTrace_append hprefix tailTrace_640562
  have hstable : (prefixWord ++ tailWord_640562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640562).length < 2 ^ (prefixWord ++ tailWord_640562).sum := by decide
  have hdescent : baseEnd_640562 < baseStart_640562 := by decide
  rcases family_descends (prefixWord ++ tailWord_640562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640572 : List Nat := [2, 2, 2, 2, 4, 1, 1, 1, 3, 5]
def baseStart_640572 : Nat := 118140960795 + 640572 * 2 ^ 59
def prefixEnd_640572 : Nat := 4983230072969 + 3 ^ 40 * 640572 * 2
def baseEnd_640572 : Nat := 109640443270657664268023

theorem tailTrace_640572 : CollatzResearch.WordTrace tailWord_640572 prefixEnd_640572 109640443270657664268023 := by
  unfold tailWord_640572
  simp only [CollatzResearch.WordTrace]
  refine ⟨11681790117662259916425985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15575720156883013221901313 11681790117662259916425985)
  ·
    refine ⟨8761342588246694937319489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11681790117662259916425985 8761342588246694937319489)
    ·
      refine ⟨6571006941185021202989617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8761342588246694937319489 6571006941185021202989617)
      ·
        refine ⟨4928255205888765902242213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6571006941185021202989617 4928255205888765902242213)
        ·
          refine ⟨924047851104143606670415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4928255205888765902242213 924047851104143606670415)
          ·
            refine ⟨1386071776656215410005623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 924047851104143606670415 1386071776656215410005623)
            ·
              refine ⟨2079107664984323115008435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1386071776656215410005623 2079107664984323115008435)
              ·
                refine ⟨3118661497476484672512653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2079107664984323115008435 3118661497476484672512653)
                ·
                  refine ⟨1169498061553681752192245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3118661497476484672512653 1169498061553681752192245)
                  ·
                    refine ⟨109640443270657664268023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1169498061553681752192245 109640443270657664268023)
                    ·
                      rfl

theorem cell23_640572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 3, 5].length) (baseStart_640572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_640572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_640572 prefixEnd_640572 := by exact prefixLift 640572
  have htrace : WordTrace (prefixWord ++ tailWord_640572) baseStart_640572 baseEnd_640572 := by
    simpa [prefixWord, tailWord_640572, baseEnd_640572] using wordTrace_append hprefix tailTrace_640572
  have hstable : (prefixWord ++ tailWord_640572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640572).length < 2 ^ (prefixWord ++ tailWord_640572).sum := by decide
  have hdescent : baseEnd_640572 < baseStart_640572 := by decide
  rcases family_descends (prefixWord ++ tailWord_640572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640585 : List Nat := [1, 2, 1, 1, 2, 2, 1, 3, 6, 4]
def baseStart_640585 : Nat := 118140960795 + 640585 * 2 ^ 59
def prefixEnd_640585 : Nat := 4983230072969 + 3 ^ 40 * 640585 * 2
def baseEnd_640585 : Nat := 109642668353493813980503

theorem tailTrace_640585 : CollatzResearch.WordTrace tailWord_640585 prefixEnd_640585 109642668353493813980503 := by
  unfold tailWord_640585
  simp only [CollatzResearch.WordTrace]
  refine ⟨23364054384277423053075209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15576036256184948702050139 23364054384277423053075209)
  ·
    refine ⟨17523040788208067289806407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23364054384277423053075209 17523040788208067289806407)
    ·
      refine ⟨26284561182312100934709611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17523040788208067289806407 26284561182312100934709611)
      ·
        refine ⟨39426841773468151402064417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26284561182312100934709611 39426841773468151402064417)
        ·
          refine ⟨29570131330101113551548313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39426841773468151402064417 29570131330101113551548313)
          ·
            refine ⟨22177598497575835163661235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29570131330101113551548313 22177598497575835163661235)
            ·
              refine ⟨33266397746363752745491853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22177598497575835163661235 33266397746363752745491853)
              ·
                refine ⟨12474899154886407279559445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33266397746363752745491853 12474899154886407279559445)
                ·
                  refine ⟨584760897885300341229349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 12474899154886407279559445 584760897885300341229349)
                  ·
                    refine ⟨109642668353493813980503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 584760897885300341229349 109642668353493813980503)
                    ·
                      rfl

theorem cell23_640585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 6, 4].length) (baseStart_640585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_640585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_640585 prefixEnd_640585 := by exact prefixLift 640585
  have htrace : WordTrace (prefixWord ++ tailWord_640585) baseStart_640585 baseEnd_640585 := by
    simpa [prefixWord, tailWord_640585, baseEnd_640585] using wordTrace_append hprefix tailTrace_640585
  have hstable : (prefixWord ++ tailWord_640585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640585).length < 2 ^ (prefixWord ++ tailWord_640585).sum := by decide
  have hdescent : baseEnd_640585 < baseStart_640585 := by decide
  rcases family_descends (prefixWord ++ tailWord_640585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640609 : List Nat := [1, 2, 3, 1, 1, 3, 2, 3, 3, 2, 2]
def baseStart_640609 : Nat := 118140960795 + 640609 * 2 ^ 59
def prefixEnd_640609 : Nat := 4983230072969 + 3 ^ 40 * 640609 * 2
def baseEnd_640609 : Nat := 328940328596189348041399

theorem tailTrace_640609 : CollatzResearch.WordTrace tailWord_640609 prefixEnd_640609 328940328596189348041399 := by
  unfold tailWord_640609
  simp only [CollatzResearch.WordTrace]
  refine ⟨23364929736190475151948881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15576619824126983434632587 23364929736190475151948881)
  ·
    refine ⟨17523697302142856363961661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23364929736190475151948881 17523697302142856363961661)
    ·
      refine ⟨6571386488303571136485623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17523697302142856363961661 6571386488303571136485623)
      ·
        refine ⟨9857079732455356704728435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6571386488303571136485623 9857079732455356704728435)
        ·
          refine ⟨14785619598683035057092653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9857079732455356704728435 14785619598683035057092653)
          ·
            refine ⟨5544607349506138146409745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14785619598683035057092653 5544607349506138146409745)
            ·
              refine ⟨4158455512129603609807309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5544607349506138146409745 4158455512129603609807309)
              ·
                refine ⟨1559420817048601353677741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4158455512129603609807309 1559420817048601353677741)
                ·
                  refine ⟨584782806393225507629153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1559420817048601353677741 584782806393225507629153)
                  ·
                    refine ⟨438587104794919130721865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 584782806393225507629153 438587104794919130721865)
                    ·
                      refine ⟨328940328596189348041399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 438587104794919130721865 328940328596189348041399)
                      ·
                        rfl

theorem cell23_640609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 3, 2, 2].length) (baseStart_640609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_640609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_640609 prefixEnd_640609 := by exact prefixLift 640609
  have htrace : WordTrace (prefixWord ++ tailWord_640609) baseStart_640609 baseEnd_640609 := by
    simpa [prefixWord, tailWord_640609, baseEnd_640609] using wordTrace_append hprefix tailTrace_640609
  have hstable : (prefixWord ++ tailWord_640609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640609).length < 2 ^ (prefixWord ++ tailWord_640609).sum := by decide
  have hdescent : baseEnd_640609 < baseStart_640609 := by decide
  rcases family_descends (prefixWord ++ tailWord_640609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640612 : List Nat := [2, 3, 1, 1, 2, 3, 1, 2, 3, 2, 3]
def baseStart_640612 : Nat := 118140960795 + 640612 * 2 ^ 59
def prefixEnd_640612 : Nat := 4983230072969 + 3 ^ 40 * 640612 * 2
def baseEnd_640612 : Nat := 328941869038152836303885

theorem tailTrace_640612 : CollatzResearch.WordTrace tailWord_640612 prefixEnd_640612 328941869038152836303885 := by
  unfold tailWord_640612
  simp only [CollatzResearch.WordTrace]
  refine ⟨11682519577589803332154045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15576692770119737776205393 11682519577589803332154045)
  ·
    refine ⟨4380944841596176249557767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11682519577589803332154045 4380944841596176249557767)
    ·
      refine ⟨6571417262394264374336651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4380944841596176249557767 6571417262394264374336651)
      ·
        refine ⟨9857125893591396561504977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6571417262394264374336651 9857125893591396561504977)
        ·
          refine ⟨7392844420193547421128733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9857125893591396561504977 7392844420193547421128733)
          ·
            refine ⟨2772316657572580282923275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7392844420193547421128733 2772316657572580282923275)
            ·
              refine ⟨4158474986358870424384913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2772316657572580282923275 4158474986358870424384913)
              ·
                refine ⟨3118856239769152818288685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4158474986358870424384913 3118856239769152818288685)
                ·
                  refine ⟨1169571089913432306858257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3118856239769152818288685 1169571089913432306858257)
                  ·
                    refine ⟨877178317435074230143693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1169571089913432306858257 877178317435074230143693)
                    ·
                      refine ⟨328941869038152836303885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 877178317435074230143693 328941869038152836303885)
                      ·
                        rfl

theorem cell23_640612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 3, 2, 3].length) (baseStart_640612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_640612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_640612 prefixEnd_640612 := by exact prefixLift 640612
  have htrace : WordTrace (prefixWord ++ tailWord_640612) baseStart_640612 baseEnd_640612 := by
    simpa [prefixWord, tailWord_640612, baseEnd_640612] using wordTrace_append hprefix tailTrace_640612
  have hstable : (prefixWord ++ tailWord_640612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640612).length < 2 ^ (prefixWord ++ tailWord_640612).sum := by decide
  have hdescent : baseEnd_640612 < baseStart_640612 := by decide
  rcases family_descends (prefixWord ++ tailWord_640612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640615 : List Nat := [1, 1, 5, 1, 1, 1, 5, 8]
def baseStart_640615 : Nat := 118140960795 + 640615 * 2 ^ 59
def prefixEnd_640615 : Nat := 4983230072969 + 3 ^ 40 * 640615 * 2
def baseEnd_640615 : Nat := 12183089240004308317273

theorem tailTrace_640615 : CollatzResearch.WordTrace tailWord_640615 prefixEnd_640615 12183089240004308317273 := by
  unfold tailWord_640615
  simp only [CollatzResearch.WordTrace]
  refine ⟨23365148574168738176667299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15576765716112492117778199 23365148574168738176667299)
  ·
    refine ⟨35047722861253107265000949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23365148574168738176667299 35047722861253107265000949)
    ·
      refine ⟨3285724018242478806093839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35047722861253107265000949 3285724018242478806093839)
      ·
        refine ⟨4928586027363718209140759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3285724018242478806093839 4928586027363718209140759)
        ·
          refine ⟨7392879041045577313711139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4928586027363718209140759 7392879041045577313711139)
          ·
            refine ⟨11089318561568365970566709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7392879041045577313711139 11089318561568365970566709)
            ·
              refine ⟨1039623615147034309740629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11089318561568365970566709 1039623615147034309740629)
              ·
                refine ⟨12183089240004308317273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1039623615147034309740629 12183089240004308317273)
                ·
                  rfl

theorem cell23_640615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 8].length) (baseStart_640615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_640615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_640615 prefixEnd_640615 := by exact prefixLift 640615
  have htrace : WordTrace (prefixWord ++ tailWord_640615) baseStart_640615 baseEnd_640615 := by
    simpa [prefixWord, tailWord_640615, baseEnd_640615] using wordTrace_append hprefix tailTrace_640615
  have hstable : (prefixWord ++ tailWord_640615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640615).length < 2 ^ (prefixWord ++ tailWord_640615).sum := by decide
  have hdescent : baseEnd_640615 < baseStart_640615 := by decide
  rcases family_descends (prefixWord ++ tailWord_640615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640626 : List Nat := [3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 2]
def baseStart_640626 : Nat := 118140960795 + 640626 * 2 ^ 59
def prefixEnd_640626 : Nat := 4983230072969 + 3 ^ 40 * 640626 * 2
def baseEnd_640626 : Nat := 328949057767315781528821

theorem tailTrace_640626 : CollatzResearch.WordTrace tailWord_640626 prefixEnd_640626 328949057767315781528821 := by
  unfold tailWord_640626
  simp only [CollatzResearch.WordTrace]
  refine ⟨5841387444282221763829433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15577033184752591370211821 5841387444282221763829433)
  ·
    refine ⟨4381040583211666322872075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5841387444282221763829433 4381040583211666322872075)
    ·
      refine ⟨6571560874817499484308113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4381040583211666322872075 6571560874817499484308113)
      ·
        refine ⟨4928670656113124613231085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6571560874817499484308113 4928670656113124613231085)
        ·
          refine ⟨1848251496042421729961657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4928670656113124613231085 1848251496042421729961657)
          ·
            refine ⟨1386188622031816297471243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1848251496042421729961657 1386188622031816297471243)
            ·
              refine ⟨2079282933047724446206865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1386188622031816297471243 2079282933047724446206865)
              ·
                refine ⟨1559462199785793334655149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2079282933047724446206865 1559462199785793334655149)
                ·
                  refine ⟨584798324919672500495681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1559462199785793334655149 584798324919672500495681)
                  ·
                    refine ⟨438598743689754375371761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 584798324919672500495681 438598743689754375371761)
                    ·
                      refine ⟨328949057767315781528821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 438598743689754375371761 328949057767315781528821)
                      ·
                        rfl

theorem cell23_640626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 2].length) (baseStart_640626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_640626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_640626 prefixEnd_640626 := by exact prefixLift 640626
  have htrace : WordTrace (prefixWord ++ tailWord_640626) baseStart_640626 baseEnd_640626 := by
    simpa [prefixWord, tailWord_640626, baseEnd_640626] using wordTrace_append hprefix tailTrace_640626
  have hstable : (prefixWord ++ tailWord_640626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640626).length < 2 ^ (prefixWord ++ tailWord_640626).sum := by decide
  have hdescent : baseEnd_640626 < baseStart_640626 := by decide
  rcases family_descends (prefixWord ++ tailWord_640626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640629 : List Nat := [1, 3, 4, 2, 1, 1, 2, 1, 3, 2, 3]
def baseStart_640629 : Nat := 118140960795 + 640629 * 2 ^ 59
def prefixEnd_640629 : Nat := 4983230072969 + 3 ^ 40 * 640629 * 2
def baseEnd_640629 : Nat := 328950598209279269791307

theorem tailTrace_640629 : CollatzResearch.WordTrace tailWord_640629 prefixEnd_640629 328950598209279269791307 := by
  unfold tailWord_640629
  simp only [CollatzResearch.WordTrace]
  refine ⟨23365659196118018567676941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15577106130745345711784627 23365659196118018567676941)
  ·
    refine ⟨8762122198544256962878853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23365659196118018567676941 8762122198544256962878853)
    ·
      refine ⟨1642897912227048180539785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8762122198544256962878853 1642897912227048180539785)
      ·
        refine ⟨1232173434170286135404839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1642897912227048180539785 1232173434170286135404839)
        ·
          refine ⟨1848260151255429203107259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1232173434170286135404839 1848260151255429203107259)
          ·
            refine ⟨2772390226883143804660889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1848260151255429203107259 2772390226883143804660889)
            ·
              refine ⟨2079292670162357853495667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2772390226883143804660889 2079292670162357853495667)
              ·
                refine ⟨3118939005243536780243501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2079292670162357853495667 3118939005243536780243501)
                ·
                  refine ⟨1169602126966326292591313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3118939005243536780243501 1169602126966326292591313)
                  ·
                    refine ⟨877201595224744719443485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1169602126966326292591313 877201595224744719443485)
                    ·
                      refine ⟨328950598209279269791307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 877201595224744719443485 328950598209279269791307)
                      ·
                        rfl

theorem cell23_640629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_640629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_640629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_640629 prefixEnd_640629 := by exact prefixLift 640629
  have htrace : WordTrace (prefixWord ++ tailWord_640629) baseStart_640629 baseEnd_640629 := by
    simpa [prefixWord, tailWord_640629, baseEnd_640629] using wordTrace_append hprefix tailTrace_640629
  have hstable : (prefixWord ++ tailWord_640629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640629).length < 2 ^ (prefixWord ++ tailWord_640629).sum := by decide
  have hdescent : baseEnd_640629 < baseStart_640629 := by decide
  rcases family_descends (prefixWord ++ tailWord_640629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640665 : List Nat := [1, 2, 1, 2, 1, 2, 2, 3, 2, 3, 4]
def baseStart_640665 : Nat := 118140960795 + 640665 * 2 ^ 59
def prefixEnd_640665 : Nat := 4983230072969 + 3 ^ 40 * 640665 * 2
def baseEnd_640665 : Nat := 328969083512841128941141

theorem tailTrace_640665 : CollatzResearch.WordTrace tailWord_640665 prefixEnd_640665 328969083512841128941141 := by
  unfold tailWord_640665
  simp only [CollatzResearch.WordTrace]
  refine ⟨23366972223987596715987449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15577981482658397810658299 23366972223987596715987449)
  ·
    refine ⟨17525229167990697536990587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23366972223987596715987449 17525229167990697536990587)
    ·
      refine ⟨26287843751986046305485881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17525229167990697536990587 26287843751986046305485881)
      ·
        refine ⟨19715882813989534729114411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26287843751986046305485881 19715882813989534729114411)
        ·
          refine ⟨29573824220984302093671617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19715882813989534729114411 29573824220984302093671617)
          ·
            refine ⟨22180368165738226570253713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29573824220984302093671617 22180368165738226570253713)
            ·
              refine ⟨16635276124303669927690285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22180368165738226570253713 16635276124303669927690285)
              ·
                refine ⟨6238228546613876222883857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16635276124303669927690285 6238228546613876222883857)
                ·
                  refine ⟨4678671409960407167162893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6238228546613876222883857 4678671409960407167162893)
                  ·
                    refine ⟨1754501778735152687686085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4678671409960407167162893 1754501778735152687686085)
                    ·
                      refine ⟨328969083512841128941141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1754501778735152687686085 328969083512841128941141)
                      ·
                        rfl

theorem cell23_640665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 3, 4].length) (baseStart_640665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_640665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_640665 prefixEnd_640665 := by exact prefixLift 640665
  have htrace : WordTrace (prefixWord ++ tailWord_640665) baseStart_640665 baseEnd_640665 := by
    simpa [prefixWord, tailWord_640665, baseEnd_640665] using wordTrace_append hprefix tailTrace_640665
  have hstable : (prefixWord ++ tailWord_640665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640665).length < 2 ^ (prefixWord ++ tailWord_640665).sum := by decide
  have hdescent : baseEnd_640665 < baseStart_640665 := by decide
  rcases family_descends (prefixWord ++ tailWord_640665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640675 : List Nat := [1, 1, 1, 4, 1, 1, 3, 3, 2, 6]
def baseStart_640675 : Nat := 118140960795 + 640675 * 2 ^ 59
def prefixEnd_640675 : Nat := 4983230072969 + 3 ^ 40 * 640675 * 2
def baseEnd_640675 : Nat := 109658072773128696605365

theorem tailTrace_640675 : CollatzResearch.WordTrace tailWord_640675 prefixEnd_640675 109658072773128696605365 := by
  unfold tailWord_640675
  simp only [CollatzResearch.WordTrace]
  refine ⟨23367336953951368423851479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15578224635967578949234319 23367336953951368423851479)
  ·
    refine ⟨35051005430927052635777219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23367336953951368423851479 35051005430927052635777219)
    ·
      refine ⟨52576508146390578953665829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35051005430927052635777219 52576508146390578953665829)
      ·
        refine ⟨9858095277448233553812343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52576508146390578953665829 9858095277448233553812343)
        ·
          refine ⟨14787142916172350330718515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9858095277448233553812343 14787142916172350330718515)
          ·
            refine ⟨22180714374258525496077773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14787142916172350330718515 22180714374258525496077773)
            ·
              refine ⟨8317767890346947061029165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22180714374258525496077773 8317767890346947061029165)
              ·
                refine ⟨3119162958880105147885937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8317767890346947061029165 3119162958880105147885937)
                ·
                  refine ⟨2339372219160078860914453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3119162958880105147885937 2339372219160078860914453)
                  ·
                    refine ⟨109658072773128696605365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2339372219160078860914453 109658072773128696605365)
                    ·
                      rfl

theorem cell23_640675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 6].length) (baseStart_640675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_640675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_640675 prefixEnd_640675 := by exact prefixLift 640675
  have htrace : WordTrace (prefixWord ++ tailWord_640675) baseStart_640675 baseEnd_640675 := by
    simpa [prefixWord, tailWord_640675, baseEnd_640675] using wordTrace_append hprefix tailTrace_640675
  have hstable : (prefixWord ++ tailWord_640675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640675).length < 2 ^ (prefixWord ++ tailWord_640675).sum := by decide
  have hdescent : baseEnd_640675 < baseStart_640675 := by decide
  rcases family_descends (prefixWord ++ tailWord_640675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640680 : List Nat := [2, 1, 7, 1, 1, 1, 2, 2, 1, 2, 3]
def baseStart_640680 : Nat := 118140960795 + 640680 * 2 ^ 59
def prefixEnd_640680 : Nat := 4983230072969 + 3 ^ 40 * 640680 * 2
def baseEnd_640680 : Nat := 328976785722658570253573

theorem tailTrace_640680 : CollatzResearch.WordTrace tailWord_640680 prefixEnd_640680 328976785722658570253573 := by
  unfold tailWord_640680
  simp only [CollatzResearch.WordTrace]
  refine ⟨11683759659466627138891747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15578346212622169518522329 11683759659466627138891747)
  ·
    refine ⟨17525639489199940708337621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11683759659466627138891747 17525639489199940708337621)
    ·
      refine ⟨410757175528123610351663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 17525639489199940708337621 410757175528123610351663)
      ·
        refine ⟨616135763292185415527495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 410757175528123610351663 616135763292185415527495)
        ·
          refine ⟨924203644938278123291243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 616135763292185415527495 924203644938278123291243)
          ·
            refine ⟨1386305467407417184936865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 924203644938278123291243 1386305467407417184936865)
            ·
              refine ⟨1039729100555562888702649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1386305467407417184936865 1039729100555562888702649)
              ·
                refine ⟨779796825416672166526987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1039729100555562888702649 779796825416672166526987)
                ·
                  refine ⟨1169695238125008249790481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 779796825416672166526987 1169695238125008249790481)
                  ·
                    refine ⟨877271428593756187342861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1169695238125008249790481 877271428593756187342861)
                    ·
                      refine ⟨328976785722658570253573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 877271428593756187342861 328976785722658570253573)
                      ·
                        rfl

theorem cell23_640680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_640680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_640680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_640680 prefixEnd_640680 := by exact prefixLift 640680
  have htrace : WordTrace (prefixWord ++ tailWord_640680) baseStart_640680 baseEnd_640680 := by
    simpa [prefixWord, tailWord_640680, baseEnd_640680] using wordTrace_append hprefix tailTrace_640680
  have hstable : (prefixWord ++ tailWord_640680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640680).length < 2 ^ (prefixWord ++ tailWord_640680).sum := by decide
  have hdescent : baseEnd_640680 < baseStart_640680 := by decide
  rcases family_descends (prefixWord ++ tailWord_640680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640702 : List Nat := [4, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5]
def baseStart_640702 : Nat := 118140960795 + 640702 * 2 ^ 59
def prefixEnd_640702 : Nat := 4983230072969 + 3 ^ 40 * 640702 * 2
def baseEnd_640702 : Nat := 328988082297057484178471

theorem tailTrace_640702 : CollatzResearch.WordTrace tailWord_640702 prefixEnd_640702 328988082297057484178471 := by
  unfold tailWord_640702
  simp only [CollatzResearch.WordTrace]
  refine ⟨2921040215606694004385545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15578881149902368023389573 2921040215606694004385545)
  ·
    refine ⟨2190780161705020503289159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2921040215606694004385545 2190780161705020503289159)
    ·
      refine ⟨3286170242557530754933739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2190780161705020503289159 3286170242557530754933739)
      ·
        refine ⟨4929255363836296132400609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3286170242557530754933739 4929255363836296132400609)
        ·
          refine ⟨3696941522877222099300457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4929255363836296132400609 3696941522877222099300457)
          ·
            refine ⟨2772706142157916574475343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3696941522877222099300457 2772706142157916574475343)
            ·
              refine ⟨4159059213236874861713015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2772706142157916574475343 4159059213236874861713015)
              ·
                refine ⟨6238588819855312292569523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4159059213236874861713015 6238588819855312292569523)
                ·
                  refine ⟨9357883229782968438854285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6238588819855312292569523 9357883229782968438854285)
                  ·
                    refine ⟨3509206211168613164570357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9357883229782968438854285 3509206211168613164570357)
                    ·
                      refine ⟨328988082297057484178471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3509206211168613164570357 328988082297057484178471)
                      ·
                        rfl

theorem cell23_640702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_640702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_640702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_640702 prefixEnd_640702 := by exact prefixLift 640702
  have htrace : WordTrace (prefixWord ++ tailWord_640702) baseStart_640702 baseEnd_640702 := by
    simpa [prefixWord, tailWord_640702, baseEnd_640702] using wordTrace_append hprefix tailTrace_640702
  have hstable : (prefixWord ++ tailWord_640702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640702).length < 2 ^ (prefixWord ++ tailWord_640702).sum := by decide
  have hdescent : baseEnd_640702 < baseStart_640702 := by decide
  rcases family_descends (prefixWord ++ tailWord_640702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640745 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 3, 1, 7]
def baseStart_640745 : Nat := 118140960795 + 640745 * 2 ^ 59
def prefixEnd_640745 : Nat := 4983230072969 + 3 ^ 40 * 640745 * 2
def baseEnd_640745 : Nat := 329010161965200815940773

theorem tailTrace_640745 : CollatzResearch.WordTrace tailWord_640745 prefixEnd_640745 329010161965200815940773 := by
  unfold tailWord_640745
  simp only [CollatzResearch.WordTrace]
  refine ⟨23369890063697770378899689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15579926709131846919266459 23369890063697770378899689)
  ·
    refine ⟨17527417547773327784174767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23369890063697770378899689 17527417547773327784174767)
    ·
      refine ⟨26291126321659991676262151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17527417547773327784174767 26291126321659991676262151)
      ·
        refine ⟨39436689482489987514393227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26291126321659991676262151 39436689482489987514393227)
        ·
          refine ⟨59155034223734981271589841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39436689482489987514393227 59155034223734981271589841)
          ·
            refine ⟨44366275667801235953692381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59155034223734981271589841 44366275667801235953692381)
            ·
              refine ⟨16637353375425463482634643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44366275667801235953692381 16637353375425463482634643)
              ·
                refine ⟨24956030063138195223951965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16637353375425463482634643 24956030063138195223951965)
                ·
                  refine ⟨9358511273676823208981987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24956030063138195223951965 9358511273676823208981987)
                  ·
                    refine ⟨14037766910515234813472981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9358511273676823208981987 14037766910515234813472981)
                    ·
                      refine ⟨329010161965200815940773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 14037766910515234813472981 329010161965200815940773)
                      ·
                        rfl

theorem cell23_640745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 1, 7].length) (baseStart_640745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_640745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_640745 prefixEnd_640745 := by exact prefixLift 640745
  have htrace : WordTrace (prefixWord ++ tailWord_640745) baseStart_640745 baseEnd_640745 := by
    simpa [prefixWord, tailWord_640745, baseEnd_640745] using wordTrace_append hprefix tailTrace_640745
  have hstable : (prefixWord ++ tailWord_640745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640745).length < 2 ^ (prefixWord ++ tailWord_640745).sum := by decide
  have hdescent : baseEnd_640745 < baseStart_640745 := by decide
  rcases family_descends (prefixWord ++ tailWord_640745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640789 : List Nat := [1, 3, 2, 1, 2, 3, 1, 1, 1, 6, 2]
def baseStart_640789 : Nat := 118140960795 + 640789 * 2 ^ 59
def prefixEnd_640789 : Nat := 4983230072969 + 3 ^ 40 * 640789 * 2
def baseEnd_640789 : Nat := 329032755113998643790571

theorem tailTrace_640789 : CollatzResearch.WordTrace tailWord_640789 prefixEnd_640789 329032755113998643790571 := by
  unfold tailWord_640789
  simp only [CollatzResearch.WordTrace]
  refine ⟨23371494875538365893501421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15580996583692243929000947 23371494875538365893501421)
  ·
    refine ⟨8764310578326887210063033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23371494875538365893501421 8764310578326887210063033)
    ·
      refine ⟨6573232933745165407547275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8764310578326887210063033 6573232933745165407547275)
      ·
        refine ⟨9859849400617748111320913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6573232933745165407547275 9859849400617748111320913)
        ·
          refine ⟨7394887050463311083490685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9859849400617748111320913 7394887050463311083490685)
          ·
            refine ⟨2773082643923741656309007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7394887050463311083490685 2773082643923741656309007)
            ·
              refine ⟨4159623965885612484463511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2773082643923741656309007 4159623965885612484463511)
              ·
                refine ⟨6239435948828418726695267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4159623965885612484463511 6239435948828418726695267)
                ·
                  refine ⟨9359153923242628090042901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6239435948828418726695267 9359153923242628090042901)
                  ·
                    refine ⟨438710340151998191720761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9359153923242628090042901 438710340151998191720761)
                    ·
                      refine ⟨329032755113998643790571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 438710340151998191720761 329032755113998643790571)
                      ·
                        rfl

theorem cell23_640789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 6, 2].length) (baseStart_640789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_640789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_640789 prefixEnd_640789 := by exact prefixLift 640789
  have htrace : WordTrace (prefixWord ++ tailWord_640789) baseStart_640789 baseEnd_640789 := by
    simpa [prefixWord, tailWord_640789, baseEnd_640789] using wordTrace_append hprefix tailTrace_640789
  have hstable : (prefixWord ++ tailWord_640789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640789).length < 2 ^ (prefixWord ++ tailWord_640789).sum := by decide
  have hdescent : baseEnd_640789 < baseStart_640789 := by decide
  rcases family_descends (prefixWord ++ tailWord_640789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640799 : List Nat := [1, 1, 2, 4, 2, 1, 3, 2, 3, 4]
def baseStart_640799 : Nat := 118140960795 + 640799 * 2 ^ 59
def prefixEnd_640799 : Nat := 4983230072969 + 3 ^ 40 * 640799 * 2
def baseEnd_640799 : Nat := 109679296640181201555175

theorem tailTrace_640799 : CollatzResearch.WordTrace tailWord_640799 prefixEnd_640799 109679296640181201555175 := by
  unfold tailWord_640799
  simp only [CollatzResearch.WordTrace]
  refine ⟨23371859605502137601365451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15581239737001425067576967 23371859605502137601365451)
  ·
    refine ⟨35057789408253206402048177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23371859605502137601365451 35057789408253206402048177)
    ·
      refine ⟨26293342056189904801536133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35057789408253206402048177 26293342056189904801536133)
      ·
        refine ⟨4930001635535607150288025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26293342056189904801536133 4930001635535607150288025)
        ·
          refine ⟨3697501226651705362716019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4930001635535607150288025 3697501226651705362716019)
          ·
            refine ⟨5546251839977558044074029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3697501226651705362716019 5546251839977558044074029)
            ·
              refine ⟨2079844439991584266527761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5546251839977558044074029 2079844439991584266527761)
              ·
                refine ⟨1559883329993688199895821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2079844439991584266527761 1559883329993688199895821)
                ·
                  refine ⟨584956248747633074960933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1559883329993688199895821 584956248747633074960933)
                  ·
                    refine ⟨109679296640181201555175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 584956248747633074960933 109679296640181201555175)
                    ·
                      rfl

theorem cell23_640799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 3, 4].length) (baseStart_640799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_640799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_640799 prefixEnd_640799 := by exact prefixLift 640799
  have htrace : WordTrace (prefixWord ++ tailWord_640799) baseStart_640799 baseEnd_640799 := by
    simpa [prefixWord, tailWord_640799, baseEnd_640799] using wordTrace_append hprefix tailTrace_640799
  have hstable : (prefixWord ++ tailWord_640799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640799).length < 2 ^ (prefixWord ++ tailWord_640799).sum := by decide
  have hdescent : baseEnd_640799 < baseStart_640799 := by decide
  rcases family_descends (prefixWord ++ tailWord_640799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640829 : List Nat := [1, 4, 1, 4, 1, 2, 1, 1, 8]
def baseStart_640829 : Nat := 118140960795 + 640829 * 2 ^ 59
def prefixEnd_640829 : Nat := 4983230072969 + 3 ^ 40 * 640829 * 2
def baseEnd_640829 : Nat := 36561477148908720810043

theorem tailTrace_640829 : CollatzResearch.WordTrace tailWord_640829 prefixEnd_640829 36561477148908720810043 := by
  unfold tailWord_640829
  simp only [CollatzResearch.WordTrace]
  refine ⟨23372953795393452724957541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15581969196928968483305027 23372953795393452724957541)
  ·
    refine ⟨4382428836636272385929539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23372953795393452724957541 4382428836636272385929539)
    ·
      refine ⟨6573643254954408578894309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4382428836636272385929539 6573643254954408578894309)
      ·
        refine ⟨1232558110303951608542683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6573643254954408578894309 1232558110303951608542683)
        ·
          refine ⟨1848837165455927412814025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1232558110303951608542683 1848837165455927412814025)
          ·
            refine ⟨1386627874091945559610519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1848837165455927412814025 1386627874091945559610519)
            ·
              refine ⟨2079941811137918339415779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1386627874091945559610519 2079941811137918339415779)
              ·
                refine ⟨3119912716706877509123669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2079941811137918339415779 3119912716706877509123669)
                ·
                  refine ⟨36561477148908720810043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3119912716706877509123669 36561477148908720810043)
                  ·
                    rfl

theorem cell23_640829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 8].length) (baseStart_640829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_640829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_640829 prefixEnd_640829 := by exact prefixLift 640829
  have htrace : WordTrace (prefixWord ++ tailWord_640829) baseStart_640829 baseEnd_640829 := by
    simpa [prefixWord, tailWord_640829, baseEnd_640829] using wordTrace_append hprefix tailTrace_640829
  have hstable : (prefixWord ++ tailWord_640829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640829).length < 2 ^ (prefixWord ++ tailWord_640829).sum := by decide
  have hdescent : baseEnd_640829 < baseStart_640829 := by decide
  rcases family_descends (prefixWord ++ tailWord_640829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640889 : List Nat := [1, 2, 1, 3, 2, 2, 1, 3, 4, 4]
def baseStart_640889 : Nat := 118140960795 + 640889 * 2 ^ 59
def prefixEnd_640889 : Nat := 4983230072969 + 3 ^ 40 * 640889 * 2
def baseEnd_640889 : Nat := 109694701059816084180037

theorem tailTrace_640889 : CollatzResearch.WordTrace tailWord_640889 prefixEnd_640889 109694701059816084180037 := by
  unfold tailWord_640889
  simp only [CollatzResearch.WordTrace]
  refine ⟨23375142175176082972141721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15583428116784055314761147 23375142175176082972141721)
  ·
    refine ⟨17531356631382062229106291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23375142175176082972141721 17531356631382062229106291)
    ·
      refine ⟨26297034947073093343659437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17531356631382062229106291 26297034947073093343659437)
      ·
        refine ⟨9861388105152410003872289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26297034947073093343659437 9861388105152410003872289)
        ·
          refine ⟨7396041078864307502904217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9861388105152410003872289 7396041078864307502904217)
          ·
            refine ⟨5547030809148230627178163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7396041078864307502904217 5547030809148230627178163)
            ·
              refine ⟨8320546213722345940767245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5547030809148230627178163 8320546213722345940767245)
              ·
                refine ⟨3120204830145879727787717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8320546213722345940767245 3120204830145879727787717)
                ·
                  refine ⟨585038405652352448960197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3120204830145879727787717 585038405652352448960197)
                  ·
                    refine ⟨109694701059816084180037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 585038405652352448960197 109694701059816084180037)
                    ·
                      rfl

theorem cell23_640889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 4, 4].length) (baseStart_640889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_640889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_640889 prefixEnd_640889 := by exact prefixLift 640889
  have htrace : WordTrace (prefixWord ++ tailWord_640889) baseStart_640889 baseEnd_640889 := by
    simpa [prefixWord, tailWord_640889, baseEnd_640889] using wordTrace_append hprefix tailTrace_640889
  have hstable : (prefixWord ++ tailWord_640889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640889).length < 2 ^ (prefixWord ++ tailWord_640889).sum := by decide
  have hdescent : baseEnd_640889 < baseStart_640889 := by decide
  rcases family_descends (prefixWord ++ tailWord_640889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640899 : List Nat := [1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 5]
def baseStart_640899 : Nat := 118140960795 + 640899 * 2 ^ 59
def prefixEnd_640899 : Nat := 4983230072969 + 3 ^ 40 * 640899 * 2
def baseEnd_640899 : Nat := 329089237985993213415065

theorem tailTrace_640899 : CollatzResearch.WordTrace tailWord_640899 prefixEnd_640899 329089237985993213415065 := by
  unfold tailWord_640899
  simp only [CollatzResearch.WordTrace]
  refine ⟨23375506905139854680005751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15583671270093236453337167 23375506905139854680005751)
  ·
    refine ⟨35063260357709782020008627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23375506905139854680005751 35063260357709782020008627)
    ·
      refine ⟨52594890536564673030012941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35063260357709782020008627 52594890536564673030012941)
      ·
        refine ⟨19723083951211752386254853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52594890536564673030012941 19723083951211752386254853)
        ·
          refine ⟨3698078240852203572422785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19723083951211752386254853 3698078240852203572422785)
          ·
            refine ⟨2773558680639152679317089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3698078240852203572422785 2773558680639152679317089)
            ·
              refine ⟨2080169010479364509487817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2773558680639152679317089 2080169010479364509487817)
              ·
                refine ⟨1560126757859523382115863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2080169010479364509487817 1560126757859523382115863)
                ·
                  refine ⟨2340190136789285073173795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1560126757859523382115863 2340190136789285073173795)
                  ·
                    refine ⟨3510285205183927609760693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2340190136789285073173795 3510285205183927609760693)
                    ·
                      refine ⟨329089237985993213415065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3510285205183927609760693 329089237985993213415065)
                      ·
                        rfl

theorem cell23_640899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 5].length) (baseStart_640899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_640899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_640899 prefixEnd_640899 := by exact prefixLift 640899
  have htrace : WordTrace (prefixWord ++ tailWord_640899) baseStart_640899 baseEnd_640899 := by
    simpa [prefixWord, tailWord_640899, baseEnd_640899] using wordTrace_append hprefix tailTrace_640899
  have hstable : (prefixWord ++ tailWord_640899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640899).length < 2 ^ (prefixWord ++ tailWord_640899).sum := by decide
  have hdescent : baseEnd_640899 < baseStart_640899 := by decide
  rcases family_descends (prefixWord ++ tailWord_640899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640910 : List Nat := [4, 1, 1, 5, 1, 2, 1, 2, 1, 5]
def baseStart_640910 : Nat := 118140960795 + 640910 * 2 ^ 59
def prefixEnd_640910 : Nat := 4983230072969 + 3 ^ 40 * 640910 * 2
def baseEnd_640910 : Nat := 109698295424397556792505

theorem tailTrace_640910 : CollatzResearch.WordTrace tailWord_640910 prefixEnd_640910 109698295424397556792505 := by
  unfold tailWord_640910
  simp only [CollatzResearch.WordTrace]
  refine ⟨2921988513512500444832023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15583938738733335705770789 2921988513512500444832023)
  ·
    refine ⟨4382982770268750667248035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2921988513512500444832023 4382982770268750667248035)
    ·
      refine ⟨6574474155403126000872053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4382982770268750667248035 6574474155403126000872053)
      ·
        refine ⟨616356952069043062581755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6574474155403126000872053 616356952069043062581755)
        ·
          refine ⟨924535428103564593872633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 616356952069043062581755 924535428103564593872633)
          ·
            refine ⟨693401571077673445404475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 924535428103564593872633 693401571077673445404475)
            ·
              refine ⟨1040102356616510168106713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 693401571077673445404475 1040102356616510168106713)
              ·
                refine ⟨780076767462382626080035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1040102356616510168106713 780076767462382626080035)
                ·
                  refine ⟨1170115151193573939120053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 780076767462382626080035 1170115151193573939120053)
                  ·
                    refine ⟨109698295424397556792505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1170115151193573939120053 109698295424397556792505)
                    ·
                      rfl

theorem cell23_640910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 2, 1, 5].length) (baseStart_640910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_640910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_640910 prefixEnd_640910 := by exact prefixLift 640910
  have htrace : WordTrace (prefixWord ++ tailWord_640910) baseStart_640910 baseEnd_640910 := by
    simpa [prefixWord, tailWord_640910, baseEnd_640910] using wordTrace_append hprefix tailTrace_640910
  have hstable : (prefixWord ++ tailWord_640910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640910).length < 2 ^ (prefixWord ++ tailWord_640910).sum := by decide
  have hdescent : baseEnd_640910 < baseStart_640910 := by decide
  rcases family_descends (prefixWord ++ tailWord_640910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640930 : List Nat := [3, 3, 1, 2, 3, 1, 3, 1, 1, 1, 4]
def baseStart_640930 : Nat := 118140960795 + 640930 * 2 ^ 59
def prefixEnd_640930 : Nat := 4983230072969 + 3 ^ 40 * 640930 * 2
def baseEnd_640930 : Nat := 329105155886282592127423

theorem tailTrace_640930 : CollatzResearch.WordTrace tailWord_640930 prefixEnd_640930 329105155886282592127423 := by
  unfold tailWord_640930
  simp only [CollatzResearch.WordTrace]
  refine ⟨5844159392006886743596061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15584425045351697982922829 5844159392006886743596061)
  ·
    refine ⟨2191559772002582528848523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5844159392006886743596061 2191559772002582528848523)
    ·
      refine ⟨3287339658003873793272785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2191559772002582528848523 3287339658003873793272785)
      ·
        refine ⟨2465504743502905344954589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3287339658003873793272785 2465504743502905344954589)
        ·
          refine ⟨924564278813589504357971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2465504743502905344954589 924564278813589504357971)
          ·
            refine ⟨1386846418220384256536957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 924564278813589504357971 1386846418220384256536957)
            ·
              refine ⟨520067406832644096201359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1386846418220384256536957 520067406832644096201359)
              ·
                refine ⟨780101110248966144302039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 520067406832644096201359 780101110248966144302039)
                ·
                  refine ⟨1170151665373449216453059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 780101110248966144302039 1170151665373449216453059)
                  ·
                    refine ⟨1755227498060173824679589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1170151665373449216453059 1755227498060173824679589)
                    ·
                      refine ⟨329105155886282592127423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1755227498060173824679589 329105155886282592127423)
                      ·
                        rfl

theorem cell23_640930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_640930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_640930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_640930 prefixEnd_640930 := by exact prefixLift 640930
  have htrace : WordTrace (prefixWord ++ tailWord_640930) baseStart_640930 baseEnd_640930 := by
    simpa [prefixWord, tailWord_640930, baseEnd_640930] using wordTrace_append hprefix tailTrace_640930
  have hstable : (prefixWord ++ tailWord_640930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640930).length < 2 ^ (prefixWord ++ tailWord_640930).sum := by decide
  have hdescent : baseEnd_640930 < baseStart_640930 := by decide
  rcases family_descends (prefixWord ++ tailWord_640930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640936 : List Nat := [2, 1, 6, 2, 1, 11]
def baseStart_640936 : Nat := 118140960795 + 640936 * 2 ^ 59
def prefixEnd_640936 : Nat := 4983230072969 + 3 ^ 40 * 640936 * 2
def baseEnd_640936 : Nat := 1354354883828022916265

theorem tailTrace_640936 : CollatzResearch.WordTrace tailWord_640936 prefixEnd_640936 1354354883828022916265 := by
  unfold tailWord_640936
  simp only [CollatzResearch.WordTrace]
  refine ⟨11688428203002904999551331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15584570937337206666068441 11688428203002904999551331)
  ·
    refine ⟨17532642304504357499326997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11688428203002904999551331 17532642304504357499326997)
    ·
      refine ⟨821842608023641757780953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 17532642304504357499326997 821842608023641757780953)
      ·
        refine ⟨616381956017731318335715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 821842608023641757780953 616381956017731318335715)
        ·
          refine ⟨924572934026596977503573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 616381956017731318335715 924572934026596977503573)
          ·
            refine ⟨1354354883828022916265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 924572934026596977503573 1354354883828022916265)
            ·
              rfl

theorem cell23_640936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 11].length) (baseStart_640936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_640936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_640936 prefixEnd_640936 := by exact prefixLift 640936
  have htrace : WordTrace (prefixWord ++ tailWord_640936) baseStart_640936 baseEnd_640936 := by
    simpa [prefixWord, tailWord_640936, baseEnd_640936] using wordTrace_append hprefix tailTrace_640936
  have hstable : (prefixWord ++ tailWord_640936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640936).length < 2 ^ (prefixWord ++ tailWord_640936).sum := by decide
  have hdescent : baseEnd_640936 < baseStart_640936 := by decide
  rcases family_descends (prefixWord ++ tailWord_640936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640946 : List Nat := [3, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3]
def baseStart_640946 : Nat := 118140960795 + 640946 * 2 ^ 59
def prefixEnd_640946 : Nat := 4983230072969 + 3 ^ 40 * 640946 * 2
def baseEnd_640946 : Nat := 329113371576754529527349

theorem tailTrace_640946 : CollatzResearch.WordTrace tailWord_640946 prefixEnd_640946 329113371576754529527349 := by
  unfold tailWord_640946
  simp only [CollatzResearch.WordTrace]
  refine ⟨5844305283992395426741673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15584814090646387804644461 5844305283992395426741673)
  ·
    refine ⟨4383228962994296570056255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5844305283992395426741673 4383228962994296570056255)
    ·
      refine ⟨6574843444491444855084383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4383228962994296570056255 6574843444491444855084383)
      ·
        refine ⟨9862265166737167282626575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6574843444491444855084383 9862265166737167282626575)
        ·
          refine ⟨14793397750105750923939863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9862265166737167282626575 14793397750105750923939863)
          ·
            refine ⟨22190096625158626385909795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14793397750105750923939863 22190096625158626385909795)
            ·
              refine ⟨33285144937737939578864693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22190096625158626385909795 33285144937737939578864693)
              ·
                refine ⟨3120482337912931835518565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33285144937737939578864693 3120482337912931835518565)
                ·
                  refine ⟨585090438358674719159731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3120482337912931835518565 585090438358674719159731)
                  ·
                    refine ⟨877635657538012078739597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 585090438358674719159731 877635657538012078739597)
                    ·
                      refine ⟨329113371576754529527349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 877635657538012078739597 329113371576754529527349)
                      ·
                        rfl

theorem cell23_640946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3].length) (baseStart_640946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_640946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_640946 prefixEnd_640946 := by exact prefixLift 640946
  have htrace : WordTrace (prefixWord ++ tailWord_640946) baseStart_640946 baseEnd_640946 := by
    simpa [prefixWord, tailWord_640946, baseEnd_640946] using wordTrace_append hprefix tailTrace_640946
  have hstable : (prefixWord ++ tailWord_640946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640946).length < 2 ^ (prefixWord ++ tailWord_640946).sum := by decide
  have hdescent : baseEnd_640946 < baseStart_640946 := by decide
  rcases family_descends (prefixWord ++ tailWord_640946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_640949 : List Nat := [1, 3, 3, 2, 1, 2, 1, 1, 2, 7]
def baseStart_640949 : Nat := 118140960795 + 640949 * 2 ^ 59
def prefixEnd_640949 : Nat := 4983230072969 + 3 ^ 40 * 640949 * 2
def baseEnd_640949 : Nat := 109704970672906005929945

theorem tailTrace_640949 : CollatzResearch.WordTrace tailWord_640949 prefixEnd_640949 109704970672906005929945 := by
  unfold tailWord_640949
  simp only [CollatzResearch.WordTrace]
  refine ⟨23377330554958713219325901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15584887036639142146217267 23377330554958713219325901)
  ·
    refine ⟨8766498958109517457247213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23377330554958713219325901 8766498958109517457247213)
    ·
      refine ⟨3287437109291069046467705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8766498958109517457247213 3287437109291069046467705)
      ·
        refine ⟨2465577831968301784850779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3287437109291069046467705 2465577831968301784850779)
        ·
          refine ⟨3698366747952452677276169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2465577831968301784850779 3698366747952452677276169)
          ·
            refine ⟨2773775060964339507957127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3698366747952452677276169 2773775060964339507957127)
            ·
              refine ⟨4160662591446509261935691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2773775060964339507957127 4160662591446509261935691)
              ·
                refine ⟨6240993887169763892903537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4160662591446509261935691 6240993887169763892903537)
                ·
                  refine ⟨4680745415377322919677653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6240993887169763892903537 4680745415377322919677653)
                  ·
                    refine ⟨109704970672906005929945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4680745415377322919677653 109704970672906005929945)
                    ·
                      rfl

theorem cell23_640949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_640949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_640949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_640949 prefixEnd_640949 := by exact prefixLift 640949
  have htrace : WordTrace (prefixWord ++ tailWord_640949) baseStart_640949 baseEnd_640949 := by
    simpa [prefixWord, tailWord_640949, baseEnd_640949] using wordTrace_append hprefix tailTrace_640949
  have hstable : (prefixWord ++ tailWord_640949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_640949).length < 2 ^ (prefixWord ++ tailWord_640949).sum := by decide
  have hdescent : baseEnd_640949 < baseStart_640949 := by decide
  rcases family_descends (prefixWord ++ tailWord_640949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641049 : List Nat := [1, 2, 1, 2, 1, 1, 3, 4, 1, 2, 5]
def baseStart_641049 : Nat := 118140960795 + 641049 * 2 ^ 59
def prefixEnd_641049 : Nat := 4983230072969 + 3 ^ 40 * 641049 * 2
def baseEnd_641049 : Nat := 329166260084167626539375

theorem tailTrace_641049 : CollatzResearch.WordTrace tailWord_641049 prefixEnd_641049 329166260084167626539375 := by
  unfold tailWord_641049
  simp only [CollatzResearch.WordTrace]
  refine ⟨23380977854596430297966201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15587318569730953531977467 23380977854596430297966201)
  ·
    refine ⟨17535733390947322723474651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23380977854596430297966201 17535733390947322723474651)
    ·
      refine ⟨26303600086420984085211977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17535733390947322723474651 26303600086420984085211977)
      ·
        refine ⟨19727700064815738063908983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26303600086420984085211977 19727700064815738063908983)
        ·
          refine ⟨29591550097223607095863475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19727700064815738063908983 29591550097223607095863475)
          ·
            refine ⟨44387325145835410643795213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29591550097223607095863475 44387325145835410643795213)
            ·
              refine ⟨16645246929688278991423205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44387325145835410643795213 16645246929688278991423205)
              ·
                refine ⟨3120983799316552310891851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16645246929688278991423205 3120983799316552310891851)
                ·
                  refine ⟨4681475698974828466337777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3120983799316552310891851 4681475698974828466337777)
                  ·
                    refine ⟨3511106774231121349753333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4681475698974828466337777 3511106774231121349753333)
                    ·
                      refine ⟨329166260084167626539375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3511106774231121349753333 329166260084167626539375)
                      ·
                        rfl

theorem cell23_641049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 2, 5].length) (baseStart_641049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_641049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_641049 prefixEnd_641049 := by exact prefixLift 641049
  have htrace : WordTrace (prefixWord ++ tailWord_641049) baseStart_641049 baseEnd_641049 := by
    simpa [prefixWord, tailWord_641049, baseEnd_641049] using wordTrace_append hprefix tailTrace_641049
  have hstable : (prefixWord ++ tailWord_641049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641049).length < 2 ^ (prefixWord ++ tailWord_641049).sum := by decide
  have hdescent : baseEnd_641049 < baseStart_641049 := by decide
  rcases family_descends (prefixWord ++ tailWord_641049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641060 : List Nat := [2, 3, 1, 4, 3, 1, 1, 1, 7]
def baseStart_641060 : Nat := 118140960795 + 641060 * 2 ^ 59
def prefixEnd_641060 : Nat := 4983230072969 + 3 ^ 40 * 641060 * 2
def baseEnd_641060 : Nat := 36574656485707453722425

theorem tailTrace_641060 : CollatzResearch.WordTrace tailWord_641060 prefixEnd_641060 36574656485707453722425 := by
  unfold tailWord_641060
  simp only [CollatzResearch.WordTrace]
  refine ⟨11690689528778289588308317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15587586038371052784411089 11690689528778289588308317)
  ·
    refine ⟨4384008573291858595615619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11690689528778289588308317 4384008573291858595615619)
    ·
      refine ⟨6576012859937787893423429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4384008573291858595615619 6576012859937787893423429)
      ·
        refine ⟨1233002411238335230016893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6576012859937787893423429 1233002411238335230016893)
        ·
          refine ⟨462375904214375711256335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1233002411238335230016893 462375904214375711256335)
          ·
            refine ⟨693563856321563566884503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 462375904214375711256335 693563856321563566884503)
            ·
              refine ⟨1040345784482345350326755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 693563856321563566884503 1040345784482345350326755)
              ·
                refine ⟨1560518676723518025490133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1040345784482345350326755 1560518676723518025490133)
                ·
                  refine ⟨36574656485707453722425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1560518676723518025490133 36574656485707453722425)
                  ·
                    rfl

theorem cell23_641060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 7].length) (baseStart_641060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_641060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_641060 prefixEnd_641060 := by exact prefixLift 641060
  have htrace : WordTrace (prefixWord ++ tailWord_641060) baseStart_641060 baseEnd_641060 := by
    simpa [prefixWord, tailWord_641060, baseEnd_641060] using wordTrace_append hprefix tailTrace_641060
  have hstable : (prefixWord ++ tailWord_641060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641060).length < 2 ^ (prefixWord ++ tailWord_641060).sum := by decide
  have hdescent : baseEnd_641060 < baseStart_641060 := by decide
  rcases family_descends (prefixWord ++ tailWord_641060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641066 : List Nat := [3, 1, 4, 1, 2, 1, 1, 1, 1, 1, 7]
def baseStart_641066 : Nat := 118140960795 + 641066 * 2 ^ 59
def prefixEnd_641066 : Nat := 4983230072969 + 3 ^ 40 * 641066 * 2
def baseEnd_641066 : Nat := 329174989255294060026797

theorem tailTrace_641066 : CollatzResearch.WordTrace tailWord_641066 prefixEnd_641066 329174989255294060026797 := by
  unfold tailWord_641066
  simp only [CollatzResearch.WordTrace]
  refine ⟨5845399473883710550333763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15587731930356561467556701 5845399473883710550333763)
  ·
    refine ⟨8768099210825565825500645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5845399473883710550333763 8768099210825565825500645)
    ·
      refine ⟨1644018602029793592281371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8768099210825565825500645 1644018602029793592281371)
      ·
        refine ⟨2466027903044690388422057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1644018602029793592281371 2466027903044690388422057)
        ·
          refine ⟨1849520927283517791316543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2466027903044690388422057 1849520927283517791316543)
          ·
            refine ⟨2774281390925276686974815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1849520927283517791316543 2774281390925276686974815)
            ·
              refine ⟨4161422086387915030462223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2774281390925276686974815 4161422086387915030462223)
              ·
                refine ⟨6242133129581872545693335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4161422086387915030462223 6242133129581872545693335)
                ·
                  refine ⟨9363199694372808818540003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6242133129581872545693335 9363199694372808818540003)
                  ·
                    refine ⟨14044799541559213227810005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9363199694372808818540003 14044799541559213227810005)
                    ·
                      refine ⟨329174989255294060026797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 14044799541559213227810005 329174989255294060026797)
                      ·
                        rfl

theorem cell23_641066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_641066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_641066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_641066 prefixEnd_641066 := by exact prefixLift 641066
  have htrace : WordTrace (prefixWord ++ tailWord_641066) baseStart_641066 baseEnd_641066 := by
    simpa [prefixWord, tailWord_641066, baseEnd_641066] using wordTrace_append hprefix tailTrace_641066
  have hstable : (prefixWord ++ tailWord_641066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641066).length < 2 ^ (prefixWord ++ tailWord_641066).sum := by decide
  have hdescent : baseEnd_641066 < baseStart_641066 := by decide
  rcases family_descends (prefixWord ++ tailWord_641066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641120 : List Nat := [2, 1, 1, 3, 2, 4, 1, 4, 1, 4]
def baseStart_641120 : Nat := 118140960795 + 641120 * 2 ^ 59
def prefixEnd_641120 : Nat := 4983230072969 + 3 ^ 40 * 641120 * 2
def baseEnd_641120 : Nat := 109734239070212282917183

theorem tailTrace_641120 : CollatzResearch.WordTrace tailWord_641120 prefixEnd_641120 109734239070212282917183 := by
  unfold tailWord_641120
  simp only [CollatzResearch.WordTrace]
  refine ⟨11691783718669604711900407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15589044958226139615867209 11691783718669604711900407)
  ·
    refine ⟨17537675578004407067850611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11691783718669604711900407 17537675578004407067850611)
    ·
      refine ⟨26306513367006610601775917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17537675578004407067850611 26306513367006610601775917)
      ·
        refine ⟨9864942512627478975665969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26306513367006610601775917 9864942512627478975665969)
        ·
          refine ⟨7398706884470609231749477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9864942512627478975665969 7398706884470609231749477)
          ·
            refine ⟨1387257540838239230953027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7398706884470609231749477 1387257540838239230953027)
            ·
              refine ⟨2080886311257358846429541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1387257540838239230953027 2080886311257358846429541)
              ·
                refine ⟨390166183360754783705539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2080886311257358846429541 390166183360754783705539)
                ·
                  refine ⟨585249275041132175558309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 390166183360754783705539 585249275041132175558309)
                  ·
                    refine ⟨109734239070212282917183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 585249275041132175558309 109734239070212282917183)
                    ·
                      rfl

theorem cell23_641120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 4, 1, 4].length) (baseStart_641120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_641120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_641120 prefixEnd_641120 := by exact prefixLift 641120
  have htrace : WordTrace (prefixWord ++ tailWord_641120) baseStart_641120 baseEnd_641120 := by
    simpa [prefixWord, tailWord_641120, baseEnd_641120] using wordTrace_append hprefix tailTrace_641120
  have hstable : (prefixWord ++ tailWord_641120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641120).length < 2 ^ (prefixWord ++ tailWord_641120).sum := by decide
  have hdescent : baseEnd_641120 < baseStart_641120 := by decide
  rcases family_descends (prefixWord ++ tailWord_641120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641143 : List Nat := [1, 1, 3, 1, 1, 5, 1, 1, 5, 1, 3]
def baseStart_641143 : Nat := 118140960795 + 641143 * 2 ^ 59
def prefixEnd_641143 : Nat := 4983230072969 + 3 ^ 40 * 641143 * 2
def baseEnd_641143 : Nat := 329214527265690258763943

theorem tailTrace_641143 : CollatzResearch.WordTrace tailWord_641143 prefixEnd_641143 329214527265690258763943 := by
  unfold tailWord_641143
  simp only [CollatzResearch.WordTrace]
  refine ⟨23384406316255884351888083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15589604210837256234592055 23384406316255884351888083)
  ·
    refine ⟨35076609474383826527832125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23384406316255884351888083 35076609474383826527832125)
    ·
      refine ⟨13153728552893934947937047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35076609474383826527832125 13153728552893934947937047)
      ·
        refine ⟨19730592829340902421905571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13153728552893934947937047 19730592829340902421905571)
        ·
          refine ⟨29595889244011353632858357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19730592829340902421905571 29595889244011353632858357)
          ·
            refine ⟨2774614616626064403080471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29595889244011353632858357 2774614616626064403080471)
            ·
              refine ⟨4161921924939096604620707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2774614616626064403080471 4161921924939096604620707)
              ·
                refine ⟨6242882887408644906931061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4161921924939096604620707 6242882887408644906931061)
                ·
                  refine ⟨585270270694560460024787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6242882887408644906931061 585270270694560460024787)
                  ·
                    refine ⟨877905406041840690037181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 585270270694560460024787 877905406041840690037181)
                    ·
                      refine ⟨329214527265690258763943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 877905406041840690037181 329214527265690258763943)
                      ·
                        rfl

theorem cell23_641143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 5, 1, 3].length) (baseStart_641143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_641143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_641143 prefixEnd_641143 := by exact prefixLift 641143
  have htrace : WordTrace (prefixWord ++ tailWord_641143) baseStart_641143 baseEnd_641143 := by
    simpa [prefixWord, tailWord_641143, baseEnd_641143] using wordTrace_append hprefix tailTrace_641143
  have hstable : (prefixWord ++ tailWord_641143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641143).length < 2 ^ (prefixWord ++ tailWord_641143).sum := by decide
  have hdescent : baseEnd_641143 < baseStart_641143 := by decide
  rcases family_descends (prefixWord ++ tailWord_641143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641170 : List Nat := [3, 2, 3, 1, 1, 1, 2, 1, 4, 3, 2]
def baseStart_641170 : Nat := 118140960795 + 641170 * 2 ^ 59
def prefixEnd_641170 : Nat := 4983230072969 + 3 ^ 40 * 641170 * 2
def baseEnd_641170 : Nat := 329228391243361653126319

theorem tailTrace_641170 : CollatzResearch.WordTrace tailWord_641170 prefixEnd_641170 329228391243361653126319 := by
  unfold tailWord_641170
  simp only [CollatzResearch.WordTrace]
  refine ⟨5846347771789516990780241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15590260724772045308747309 5846347771789516990780241)
  ·
    refine ⟨4384760828842137743085181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5846347771789516990780241 4384760828842137743085181)
    ·
      refine ⟨1644285310815801653656943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4384760828842137743085181 1644285310815801653656943)
      ·
        refine ⟨2466427966223702480485415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1644285310815801653656943 2466427966223702480485415)
        ·
          refine ⟨3699641949335553720728123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2466427966223702480485415 3699641949335553720728123)
          ·
            refine ⟨5549462924003330581092185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3699641949335553720728123 5549462924003330581092185)
            ·
              refine ⟨4162097193002497935819139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5549462924003330581092185 4162097193002497935819139)
              ·
                refine ⟨6243145789503746903728709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4162097193002497935819139 6243145789503746903728709)
                ·
                  refine ⟨1170589835531952544449133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6243145789503746903728709 1170589835531952544449133)
                  ·
                    refine ⟨438971188324482204168425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1170589835531952544449133 438971188324482204168425)
                    ·
                      refine ⟨329228391243361653126319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 438971188324482204168425 329228391243361653126319)
                      ·
                        rfl

theorem cell23_641170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_641170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_641170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_641170 prefixEnd_641170 := by exact prefixLift 641170
  have htrace : WordTrace (prefixWord ++ tailWord_641170) baseStart_641170 baseEnd_641170 := by
    simpa [prefixWord, tailWord_641170, baseEnd_641170] using wordTrace_append hprefix tailTrace_641170
  have hstable : (prefixWord ++ tailWord_641170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641170).length < 2 ^ (prefixWord ++ tailWord_641170).sum := by decide
  have hdescent : baseEnd_641170 < baseStart_641170 := by decide
  rcases family_descends (prefixWord ++ tailWord_641170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641220 : List Nat := [2, 3, 3, 1, 2, 2, 2, 1, 1, 1, 5]
def baseStart_641220 : Nat := 118140960795 + 641220 * 2 ^ 59
def prefixEnd_641220 : Nat := 4983230072969 + 3 ^ 40 * 641220 * 2
def baseEnd_641220 : Nat := 329254065276086457501089

theorem tailTrace_641220 : CollatzResearch.WordTrace tailWord_641220 prefixEnd_641220 329254065276086457501089 := by
  unfold tailWord_641220
  simp only [CollatzResearch.WordTrace]
  refine ⟨11693607368488463251220557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15591476491317951001627409 11693607368488463251220557)
  ·
    refine ⟨4385102763183173719207709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11693607368488463251220557 4385102763183173719207709)
    ·
      refine ⟨1644413536193690144702891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4385102763183173719207709 1644413536193690144702891)
      ·
        refine ⟨2466620304290535217054337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1644413536193690144702891 2466620304290535217054337)
        ·
          refine ⟨1849965228217901412790753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2466620304290535217054337 1849965228217901412790753)
          ·
            refine ⟨1387473921163426059593065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1849965228217901412790753 1387473921163426059593065)
            ·
              refine ⟨1040605440872569544694799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1387473921163426059593065 1040605440872569544694799)
              ·
                refine ⟨1560908161308854317042199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1040605440872569544694799 1560908161308854317042199)
                ·
                  refine ⟨2341362241963281475563299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1560908161308854317042199 2341362241963281475563299)
                  ·
                    refine ⟨3512043362944922213344949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2341362241963281475563299 3512043362944922213344949)
                    ·
                      refine ⟨329254065276086457501089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3512043362944922213344949 329254065276086457501089)
                      ·
                        rfl

theorem cell23_641220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_641220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_641220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_641220 prefixEnd_641220 := by exact prefixLift 641220
  have htrace : WordTrace (prefixWord ++ tailWord_641220) baseStart_641220 baseEnd_641220 := by
    simpa [prefixWord, tailWord_641220, baseEnd_641220] using wordTrace_append hprefix tailTrace_641220
  have hstable : (prefixWord ++ tailWord_641220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641220).length < 2 ^ (prefixWord ++ tailWord_641220).sum := by decide
  have hdescent : baseEnd_641220 < baseStart_641220 := by decide
  rcases family_descends (prefixWord ++ tailWord_641220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641234 : List Nat := [3, 2, 2, 2, 1, 4, 1, 1, 3, 2, 2]
def baseStart_641234 : Nat := 118140960795 + 641234 * 2 ^ 59
def prefixEnd_641234 : Nat := 4983230072969 + 3 ^ 40 * 641234 * 2
def baseEnd_641234 : Nat := 329261254005249402726025

theorem tailTrace_641234 : CollatzResearch.WordTrace tailWord_641234 prefixEnd_641234 329261254005249402726025 := by
  unfold tailWord_641234
  simp only [CollatzResearch.WordTrace]
  refine ⟨5846931339731551723362689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15591816905950804595633837 5846931339731551723362689)
  ·
    refine ⟨4385198504798663792522017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5846931339731551723362689 4385198504798663792522017)
    ·
      refine ⟨3288898878598997844391513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4385198504798663792522017 3288898878598997844391513)
      ·
        refine ⟨2466674158949248383293635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3288898878598997844391513 2466674158949248383293635)
        ·
          refine ⟨3700011238423872574940453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2466674158949248383293635 3700011238423872574940453)
          ·
            refine ⟨693752107204476107801335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3700011238423872574940453 693752107204476107801335)
            ·
              refine ⟨1040628160806714161702003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 693752107204476107801335 1040628160806714161702003)
              ·
                refine ⟨1560942241210071242553005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1040628160806714161702003 1560942241210071242553005)
                ·
                  refine ⟨585353340453776715957377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1560942241210071242553005 585353340453776715957377)
                  ·
                    refine ⟨439015005340332536968033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 585353340453776715957377 439015005340332536968033)
                    ·
                      refine ⟨329261254005249402726025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 439015005340332536968033 329261254005249402726025)
                      ·
                        rfl

theorem cell23_641234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_641234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_641234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_641234 prefixEnd_641234 := by exact prefixLift 641234
  have htrace : WordTrace (prefixWord ++ tailWord_641234) baseStart_641234 baseEnd_641234 := by
    simpa [prefixWord, tailWord_641234, baseEnd_641234] using wordTrace_append hprefix tailTrace_641234
  have hstable : (prefixWord ++ tailWord_641234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641234).length < 2 ^ (prefixWord ++ tailWord_641234).sum := by decide
  have hdescent : baseEnd_641234 < baseStart_641234 := by decide
  rcases family_descends (prefixWord ++ tailWord_641234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641244 : List Nat := [2, 2, 5, 2, 1, 1, 1, 3, 2, 4]
def baseStart_641244 : Nat := 118140960795 + 641244 * 2 ^ 59
def prefixEnd_641244 : Nat := 4983230072969 + 3 ^ 40 * 641244 * 2
def baseEnd_641244 : Nat := 109755462937264787866993

theorem tailTrace_641244 : CollatzResearch.WordTrace tailWord_641244 prefixEnd_641244 109755462937264787866993 := by
  unfold tailWord_641244
  simp only [CollatzResearch.WordTrace]
  refine ⟨11694045044444989300657393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15592060059259985734209857 11694045044444989300657393)
  ·
    refine ⟨8770533783333741975493045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11694045044444989300657393 8770533783333741975493045)
    ·
      refine ⟨822237542187538310202473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8770533783333741975493045 822237542187538310202473)
      ·
        refine ⟨616678156640653732651855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 822237542187538310202473 616678156640653732651855)
        ·
          refine ⟨925017234960980598977783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 616678156640653732651855 925017234960980598977783)
          ·
            refine ⟨1387525852441470898466675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 925017234960980598977783 1387525852441470898466675)
            ·
              refine ⟨2081288778662206347700013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1387525852441470898466675 2081288778662206347700013)
              ·
                refine ⟨780483291998327380387505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2081288778662206347700013 780483291998327380387505)
                ·
                  refine ⟨585362468998745535290629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 780483291998327380387505 585362468998745535290629)
                  ·
                    refine ⟨109755462937264787866993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 585362468998745535290629 109755462937264787866993)
                    ·
                      rfl

theorem cell23_641244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_641244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_641244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_641244 prefixEnd_641244 := by exact prefixLift 641244
  have htrace : WordTrace (prefixWord ++ tailWord_641244) baseStart_641244 baseEnd_641244 := by
    simpa [prefixWord, tailWord_641244, baseEnd_641244] using wordTrace_append hprefix tailTrace_641244
  have hstable : (prefixWord ++ tailWord_641244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641244).length < 2 ^ (prefixWord ++ tailWord_641244).sum := by decide
  have hdescent : baseEnd_641244 < baseStart_641244 := by decide
  rcases family_descends (prefixWord ++ tailWord_641244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641260 : List Nat := [2, 2, 1, 1, 2, 3, 3, 1, 3, 3, 2]
def baseStart_641260 : Nat := 118140960795 + 641260 * 2 ^ 59
def prefixEnd_641260 : Nat := 4983230072969 + 3 ^ 40 * 641260 * 2
def baseEnd_641260 : Nat := 329274604502266301000905

theorem tailTrace_641260 : CollatzResearch.WordTrace tailWord_641260 prefixEnd_641260 329274604502266301000905 := by
  unfold tailWord_641260
  simp only [CollatzResearch.WordTrace]
  refine ⟨11694336828416006666948617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15592449104554675555931489 11694336828416006666948617)
  ·
    refine ⟨8770752621312005000211463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11694336828416006666948617 8770752621312005000211463)
    ·
      refine ⟨13156128931968007500317195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8770752621312005000211463 13156128931968007500317195)
      ·
        refine ⟨19734193397952011250475793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13156128931968007500317195 19734193397952011250475793)
        ·
          refine ⟨14800645048464008437856845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19734193397952011250475793 14800645048464008437856845)
          ·
            refine ⟨5550241893174003164196317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14800645048464008437856845 5550241893174003164196317)
            ·
              refine ⟨2081340709940251186573619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5550241893174003164196317 2081340709940251186573619)
              ·
                refine ⟨3122011064910376779860429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2081340709940251186573619 3122011064910376779860429)
                ·
                  refine ⟨1170754149341391292447661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3122011064910376779860429 1170754149341391292447661)
                  ·
                    refine ⟨439032806003021734667873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1170754149341391292447661 439032806003021734667873)
                    ·
                      refine ⟨329274604502266301000905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 439032806003021734667873 329274604502266301000905)
                      ·
                        rfl

theorem cell23_641260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 3, 2].length) (baseStart_641260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_641260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_641260 prefixEnd_641260 := by exact prefixLift 641260
  have htrace : WordTrace (prefixWord ++ tailWord_641260) baseStart_641260 baseEnd_641260 := by
    simpa [prefixWord, tailWord_641260, baseEnd_641260] using wordTrace_append hprefix tailTrace_641260
  have hstable : (prefixWord ++ tailWord_641260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641260).length < 2 ^ (prefixWord ++ tailWord_641260).sum := by decide
  have hdescent : baseEnd_641260 < baseStart_641260 := by decide
  rcases family_descends (prefixWord ++ tailWord_641260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641284 : List Nat := [2, 3, 2, 2, 3, 1, 2, 2, 2, 1, 3]
def baseStart_641284 : Nat := 118140960795 + 641284 * 2 ^ 59
def prefixEnd_641284 : Nat := 4983230072969 + 3 ^ 40 * 641284 * 2
def baseEnd_641284 : Nat := 329286928037974207100795

theorem tailTrace_641284 : CollatzResearch.WordTrace tailWord_641284 prefixEnd_641284 329286928037974207100795 := by
  unfold tailWord_641284
  simp only [CollatzResearch.WordTrace]
  refine ⟨11694774504372532716385453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15593032672496710288513937 11694774504372532716385453)
  ·
    refine ⟨4385540439139699768644545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11694774504372532716385453 4385540439139699768644545)
    ·
      refine ⟨3289155329354774826483409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4385540439139699768644545 3289155329354774826483409)
      ·
        refine ⟨2466866497016081119862557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3289155329354774826483409 2466866497016081119862557)
        ·
          refine ⟨925074936381030419948459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2466866497016081119862557 925074936381030419948459)
          ·
            refine ⟨1387612404571545629922689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 925074936381030419948459 1387612404571545629922689)
            ·
              refine ⟨1040709303428659222442017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1387612404571545629922689 1040709303428659222442017)
              ·
                refine ⟨780531977571494416831513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1040709303428659222442017 780531977571494416831513)
                ·
                  refine ⟨585398983178620812623635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 780531977571494416831513 585398983178620812623635)
                  ·
                    refine ⟨878098474767931218935453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 585398983178620812623635 878098474767931218935453)
                    ·
                      refine ⟨329286928037974207100795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 878098474767931218935453 329286928037974207100795)
                      ·
                        rfl

theorem cell23_641284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_641284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_641284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_641284 prefixEnd_641284 := by exact prefixLift 641284
  have htrace : WordTrace (prefixWord ++ tailWord_641284) baseStart_641284 baseEnd_641284 := by
    simpa [prefixWord, tailWord_641284, baseEnd_641284] using wordTrace_append hprefix tailTrace_641284
  have hstable : (prefixWord ++ tailWord_641284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641284).length < 2 ^ (prefixWord ++ tailWord_641284).sum := by decide
  have hdescent : baseEnd_641284 < baseStart_641284 := by decide
  rcases family_descends (prefixWord ++ tailWord_641284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641303 : List Nat := [1, 1, 3, 4, 1, 2, 1, 1, 1, 4, 4]
def baseStart_641303 : Nat := 118140960795 + 641303 * 2 ^ 59
def prefixEnd_641303 : Nat := 4983230072969 + 3 ^ 40 * 641303 * 2
def baseEnd_641303 : Nat := 329296684170409632763207

theorem tailTrace_641303 : CollatzResearch.WordTrace tailWord_641303 prefixEnd_641303 329296684170409632763207 := by
  unfold tailWord_641303
  simp only [CollatzResearch.WordTrace]
  refine ⟨23390241995676231677712563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15593494663784154451808375 23390241995676231677712563)
  ·
    refine ⟨35085362993514347516568845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23390241995676231677712563 35085362993514347516568845)
    ·
      refine ⟨13157011122567880318713317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35085362993514347516568845 13157011122567880318713317)
      ·
        refine ⟨2466939585481477559758747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13157011122567880318713317 2466939585481477559758747)
        ·
          refine ⟨3700409378222216339638121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2466939585481477559758747 3700409378222216339638121)
          ·
            refine ⟨2775307033666662254728591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3700409378222216339638121 2775307033666662254728591)
            ·
              refine ⟨4162960550499993382092887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2775307033666662254728591 4162960550499993382092887)
              ·
                refine ⟨6244440825749990073139331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4162960550499993382092887 6244440825749990073139331)
                ·
                  refine ⟨9366661238624985109708997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6244440825749990073139331 9366661238624985109708997)
                  ·
                    refine ⟨1756248982242184708070437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9366661238624985109708997 1756248982242184708070437)
                    ·
                      refine ⟨329296684170409632763207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1756248982242184708070437 329296684170409632763207)
                      ·
                        rfl

theorem cell23_641303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_641303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_641303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_641303 prefixEnd_641303 := by exact prefixLift 641303
  have htrace : WordTrace (prefixWord ++ tailWord_641303) baseStart_641303 baseEnd_641303 := by
    simpa [prefixWord, tailWord_641303, baseEnd_641303] using wordTrace_append hprefix tailTrace_641303
  have hstable : (prefixWord ++ tailWord_641303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641303).length < 2 ^ (prefixWord ++ tailWord_641303).sum := by decide
  have hdescent : baseEnd_641303 < baseStart_641303 := by decide
  rcases family_descends (prefixWord ++ tailWord_641303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641307 : List Nat := [1, 1, 1, 1, 1, 1, 8, 3, 2, 2, 2]
def baseStart_641307 : Nat := 118140960795 + 641307 * 2 ^ 59
def prefixEnd_641307 : Nat := 4983230072969 + 3 ^ 40 * 641307 * 2
def baseEnd_641307 : Nat := 329298738093027617113189

theorem tailTrace_641307 : CollatzResearch.WordTrace tailWord_641307 prefixEnd_641307 329298738093027617113189 := by
  unfold tailWord_641307
  simp only [CollatzResearch.WordTrace]
  refine ⟨23390387887661740360858175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15593591925107826907238783 23390387887661740360858175)
  ·
    refine ⟨35085581831492610541287263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23390387887661740360858175 35085581831492610541287263)
    ·
      refine ⟨52628372747238915811930895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35085581831492610541287263 52628372747238915811930895)
      ·
        refine ⟨78942559120858373717896343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52628372747238915811930895 78942559120858373717896343)
        ·
          refine ⟨118413838681287560576844515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78942559120858373717896343 118413838681287560576844515)
          ·
            refine ⟨177620758021931340865266773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118413838681287560576844515 177620758021931340865266773)
            ·
              refine ⟨2081493258069507900764845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 177620758021931340865266773 2081493258069507900764845)
              ·
                refine ⟨780559971776065462786817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2081493258069507900764845 780559971776065462786817)
                ·
                  refine ⟨585419978832049097090113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 780559971776065462786817 585419978832049097090113)
                  ·
                    refine ⟨439064984124036822817585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 585419978832049097090113 439064984124036822817585)
                    ·
                      refine ⟨329298738093027617113189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 439064984124036822817585 329298738093027617113189)
                      ·
                        rfl

theorem cell23_641307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 3, 2, 2, 2].length) (baseStart_641307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_641307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_641307 prefixEnd_641307 := by exact prefixLift 641307
  have htrace : WordTrace (prefixWord ++ tailWord_641307) baseStart_641307 baseEnd_641307 := by
    simpa [prefixWord, tailWord_641307, baseEnd_641307] using wordTrace_append hprefix tailTrace_641307
  have hstable : (prefixWord ++ tailWord_641307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641307).length < 2 ^ (prefixWord ++ tailWord_641307).sum := by decide
  have hdescent : baseEnd_641307 < baseStart_641307 := by decide
  rcases family_descends (prefixWord ++ tailWord_641307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641343 : List Nat := [1, 1, 2, 2, 4, 1, 2, 1, 4, 5]
def baseStart_641343 : Nat := 118140960795 + 641343 * 2 ^ 59
def prefixEnd_641343 : Nat := 4983230072969 + 3 ^ 40 * 641343 * 2
def baseEnd_641343 : Nat := 109772407798863158754341

theorem tailTrace_641343 : CollatzResearch.WordTrace tailWord_641343 prefixEnd_641343 109772407798863158754341 := by
  unfold tailWord_641343
  simp only [CollatzResearch.WordTrace]
  refine ⟨23391700915531318509168683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15594467277020879006112455 23391700915531318509168683)
  ·
    refine ⟨35087551373296977763753025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23391700915531318509168683 35087551373296977763753025)
    ·
      refine ⟨26315663529972733322814769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35087551373296977763753025 26315663529972733322814769)
      ·
        refine ⟨19736747647479549992111077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26315663529972733322814769 19736747647479549992111077)
        ·
          refine ⟨3700640183902415623520827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19736747647479549992111077 3700640183902415623520827)
          ·
            refine ⟨5550960275853623435281241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3700640183902415623520827 5550960275853623435281241)
            ·
              refine ⟨4163220206890217576460931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5550960275853623435281241 4163220206890217576460931)
              ·
                refine ⟨6244830310335326364691397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4163220206890217576460931 6244830310335326364691397)
                ·
                  refine ⟨1170905683187873693379637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6244830310335326364691397 1170905683187873693379637)
                  ·
                    refine ⟨109772407798863158754341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1170905683187873693379637 109772407798863158754341)
                    ·
                      rfl

theorem cell23_641343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 4, 5].length) (baseStart_641343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_641343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_641343 prefixEnd_641343 := by exact prefixLift 641343
  have htrace : WordTrace (prefixWord ++ tailWord_641343) baseStart_641343 baseEnd_641343 := by
    simpa [prefixWord, tailWord_641343, baseEnd_641343] using wordTrace_append hprefix tailTrace_641343
  have hstable : (prefixWord ++ tailWord_641343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641343).length < 2 ^ (prefixWord ++ tailWord_641343).sum := by decide
  have hdescent : baseEnd_641343 < baseStart_641343 := by decide
  rcases family_descends (prefixWord ++ tailWord_641343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641363 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 6, 1, 4]
def baseStart_641363 : Nat := 118140960795 + 641363 * 2 ^ 59
def prefixEnd_641363 : Nat := 4983230072969 + 3 ^ 40 * 641363 * 2
def baseEnd_641363 : Nat := 329327493009679398012931

theorem tailTrace_641363 : CollatzResearch.WordTrace tailWord_641363 prefixEnd_641363 329327493009679398012931 := by
  unfold tailWord_641363
  simp only [CollatzResearch.WordTrace]
  refine ⟨23392430375458861924896743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15594953583639241283264495 23392430375458861924896743)
  ·
    refine ⟨35088645563188292887345115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23392430375458861924896743 35088645563188292887345115)
    ·
      refine ⟨52632968344782439331017673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35088645563188292887345115 52632968344782439331017673)
      ·
        refine ⟨39474726258586829498263255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52632968344782439331017673 39474726258586829498263255)
        ·
          refine ⟨59212089387880244247394883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39474726258586829498263255 59212089387880244247394883)
          ·
            refine ⟨88818134081820366371092325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59212089387880244247394883 88818134081820366371092325)
            ·
              refine ⟨16653400140341318694579811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88818134081820366371092325 16653400140341318694579811)
              ·
                refine ⟨24980100210511978041869717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16653400140341318694579811 24980100210511978041869717)
                ·
                  refine ⟨1170942197367748970712643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 24980100210511978041869717 1170942197367748970712643)
                  ·
                    refine ⟨1756413296051623456068965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1170942197367748970712643 1756413296051623456068965)
                    ·
                      refine ⟨329327493009679398012931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1756413296051623456068965 329327493009679398012931)
                      ·
                        rfl

theorem cell23_641363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 6, 1, 4].length) (baseStart_641363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_641363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_641363 prefixEnd_641363 := by exact prefixLift 641363
  have htrace : WordTrace (prefixWord ++ tailWord_641363) baseStart_641363 baseEnd_641363 := by
    simpa [prefixWord, tailWord_641363, baseEnd_641363] using wordTrace_append hprefix tailTrace_641363
  have hstable : (prefixWord ++ tailWord_641363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641363).length < 2 ^ (prefixWord ++ tailWord_641363).sum := by decide
  have hdescent : baseEnd_641363 < baseStart_641363 := by decide
  rcases family_descends (prefixWord ++ tailWord_641363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641380 : List Nat := [2, 3, 1, 1, 3, 1, 2, 3, 2, 1, 4]
def baseStart_641380 : Nat := 118140960795 + 641380 * 2 ^ 59
def prefixEnd_641380 : Nat := 4983230072969 + 3 ^ 40 * 641380 * 2
def baseEnd_641380 : Nat := 329336222180805831500353

theorem tailTrace_641380 : CollatzResearch.WordTrace tailWord_641380 prefixEnd_641380 329336222180805831500353 := by
  unfold tailWord_641380
  simp only [CollatzResearch.WordTrace]
  refine ⟨11696525208198636914132797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15595366944264849218843729 11696525208198636914132797)
  ·
    refine ⟨4386196953074488842799799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11696525208198636914132797 4386196953074488842799799)
    ·
      refine ⟨6579295429611733264199699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4386196953074488842799799 6579295429611733264199699)
      ·
        refine ⟨9868943144417599896299549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6579295429611733264199699 9868943144417599896299549)
        ·
          refine ⟨3700853679156599961112331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9868943144417599896299549 3700853679156599961112331)
          ·
            refine ⟨5551280518734899941668497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3700853679156599961112331 5551280518734899941668497)
            ·
              refine ⟨4163460389051174956251373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5551280518734899941668497 4163460389051174956251373)
              ·
                refine ⟨1561297645894190608594265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4163460389051174956251373 1561297645894190608594265)
                ·
                  refine ⟨1170973234420642956445699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1561297645894190608594265 1170973234420642956445699)
                  ·
                    refine ⟨1756459851630964434668549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1170973234420642956445699 1756459851630964434668549)
                    ·
                      refine ⟨329336222180805831500353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1756459851630964434668549 329336222180805831500353)
                      ·
                        rfl

theorem cell23_641380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_641380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_641380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_641380 prefixEnd_641380 := by exact prefixLift 641380
  have htrace : WordTrace (prefixWord ++ tailWord_641380) baseStart_641380 baseEnd_641380 := by
    simpa [prefixWord, tailWord_641380, baseEnd_641380] using wordTrace_append hprefix tailTrace_641380
  have hstable : (prefixWord ++ tailWord_641380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641380).length < 2 ^ (prefixWord ++ tailWord_641380).sum := by decide
  have hdescent : baseEnd_641380 < baseStart_641380 := by decide
  rcases family_descends (prefixWord ++ tailWord_641380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641397 : List Nat := [1, 3, 4, 1, 2, 2, 1, 2, 2, 1, 4]
def baseStart_641397 : Nat := 118140960795 + 641397 * 2 ^ 59
def prefixEnd_641397 : Nat := 4983230072969 + 3 ^ 40 * 641397 * 2
def baseEnd_641397 : Nat := 329344951351932264987775

theorem tailTrace_641397 : CollatzResearch.WordTrace tailWord_641397 prefixEnd_641397 329344951351932264987775 := by
  unfold tailWord_641397
  simp only [CollatzResearch.WordTrace]
  refine ⟨23393670457335685731634445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15595780304890457154422963 23393670457335685731634445)
  ·
    refine ⟨8772626421500882149362917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23393670457335685731634445 8772626421500882149362917)
    ·
      refine ⟨1644867454031415403005547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8772626421500882149362917 1644867454031415403005547)
      ·
        refine ⟨2467301181047123104508321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1644867454031415403005547 2467301181047123104508321)
        ·
          refine ⟨1850475885785342328381241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2467301181047123104508321 1850475885785342328381241)
          ·
            refine ⟨1387856914339006746285931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1850475885785342328381241 1387856914339006746285931)
            ·
              refine ⟨2081785371508510119428897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1387856914339006746285931 2081785371508510119428897)
              ·
                refine ⟨1561339028631382589571673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2081785371508510119428897 1561339028631382589571673)
                ·
                  refine ⟨1171004271473536942178755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1561339028631382589571673 1171004271473536942178755)
                  ·
                    refine ⟨1756506407210305413268133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1171004271473536942178755 1756506407210305413268133)
                    ·
                      refine ⟨329344951351932264987775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1756506407210305413268133 329344951351932264987775)
                      ·
                        rfl

theorem cell23_641397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_641397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_641397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_641397 prefixEnd_641397 := by exact prefixLift 641397
  have htrace : WordTrace (prefixWord ++ tailWord_641397) baseStart_641397 baseEnd_641397 := by
    simpa [prefixWord, tailWord_641397, baseEnd_641397] using wordTrace_append hprefix tailTrace_641397
  have hstable : (prefixWord ++ tailWord_641397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641397).length < 2 ^ (prefixWord ++ tailWord_641397).sum := by decide
  have hdescent : baseEnd_641397 < baseStart_641397 := by decide
  rcases family_descends (prefixWord ++ tailWord_641397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641403 : List Nat := [1, 1, 1, 1, 1, 7, 2, 1, 8]
def baseStart_641403 : Nat := 118140960795 + 641403 * 2 ^ 59
def prefixEnd_641403 : Nat := 4983230072969 + 3 ^ 40 * 641403 * 2
def baseEnd_641403 : Nat := 36594225803984360168083

theorem tailTrace_641403 : CollatzResearch.WordTrace tailWord_641403 prefixEnd_641403 36594225803984360168083 := by
  unfold tailWord_641403
  simp only [CollatzResearch.WordTrace]
  refine ⟨23393889295313948756352863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15595926196875965837568575 23393889295313948756352863)
  ·
    refine ⟨35090833942970923134529295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23393889295313948756352863 35090833942970923134529295)
    ·
      refine ⟨52636250914456384701793943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35090833942970923134529295 52636250914456384701793943)
      ·
        refine ⟨78954376371684577052690915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52636250914456384701793943 78954376371684577052690915)
        ·
          refine ⟨118431564557526865579036373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78954376371684577052690915 118431564557526865579036373)
          ·
            refine ⟨2775739794317035912008665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 118431564557526865579036373 2775739794317035912008665)
            ·
              refine ⟨2081804845737776934006499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2775739794317035912008665 2081804845737776934006499)
              ·
                refine ⟨3122707268606665401009749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2081804845737776934006499 3122707268606665401009749)
                ·
                  refine ⟨36594225803984360168083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3122707268606665401009749 36594225803984360168083)
                  ·
                    rfl

theorem cell23_641403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 8].length) (baseStart_641403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_641403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_641403 prefixEnd_641403 := by exact prefixLift 641403
  have htrace : WordTrace (prefixWord ++ tailWord_641403) baseStart_641403 baseEnd_641403 := by
    simpa [prefixWord, tailWord_641403, baseEnd_641403] using wordTrace_append hprefix tailTrace_641403
  have hstable : (prefixWord ++ tailWord_641403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641403).length < 2 ^ (prefixWord ++ tailWord_641403).sum := by decide
  have hdescent : baseEnd_641403 < baseStart_641403 := by decide
  rcases family_descends (prefixWord ++ tailWord_641403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641420 : List Nat := [2, 2, 1, 2, 1, 5, 1, 3, 6]
def baseStart_641420 : Nat := 118140960795 + 641420 * 2 ^ 59
def prefixEnd_641420 : Nat := 4983230072969 + 3 ^ 40 * 641420 * 2
def baseEnd_641420 : Nat := 36595195711887297222241

theorem tailTrace_641420 : CollatzResearch.WordTrace tailWord_641420 prefixEnd_641420 36595195711887297222241 := by
  unfold tailWord_641420
  simp only [CollatzResearch.WordTrace]
  refine ⟨11697254668126180329860857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15596339557501573773147809 11697254668126180329860857)
  ·
    refine ⟨8772941001094635247395643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11697254668126180329860857 8772941001094635247395643)
    ·
      refine ⟨13159411501641952871093465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8772941001094635247395643 13159411501641952871093465)
      ·
        refine ⟨9869558626231464653320099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13159411501641952871093465 9869558626231464653320099)
        ·
          refine ⟨14804337939347196979980149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9869558626231464653320099 14804337939347196979980149)
          ·
            refine ⟨1387906681813799716873139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14804337939347196979980149 1387906681813799716873139)
            ·
              refine ⟨2081860022720699575309709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1387906681813799716873139 2081860022720699575309709)
              ·
                refine ⟨780697508520262340741141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2081860022720699575309709 780697508520262340741141)
                ·
                  refine ⟨36595195711887297222241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 780697508520262340741141 36595195711887297222241)
                  ·
                    rfl

theorem cell23_641420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 3, 6].length) (baseStart_641420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_641420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_641420 prefixEnd_641420 := by exact prefixLift 641420
  have htrace : WordTrace (prefixWord ++ tailWord_641420) baseStart_641420 baseEnd_641420 := by
    simpa [prefixWord, tailWord_641420, baseEnd_641420] using wordTrace_append hprefix tailTrace_641420
  have hstable : (prefixWord ++ tailWord_641420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641420).length < 2 ^ (prefixWord ++ tailWord_641420).sum := by decide
  have hdescent : baseEnd_641420 < baseStart_641420 := by decide
  rcases family_descends (prefixWord ++ tailWord_641420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641480 : List Nat := [2, 1, 3, 1, 3, 2, 1, 3, 1, 6]
def baseStart_641480 : Nat := 118140960795 + 641480 * 2 ^ 59
def prefixEnd_641480 : Nat := 4983230072969 + 3 ^ 40 * 641480 * 2
def baseEnd_641480 : Nat := 109795856748751813416631

theorem tailTrace_641480 : CollatzResearch.WordTrace tailWord_641480 prefixEnd_641480 109795856748751813416631 := by
  unfold tailWord_641480
  simp only [CollatzResearch.WordTrace]
  refine ⟨11698348858017495453452947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15597798477356660604603929 11698348858017495453452947)
  ·
    refine ⟨17547523287026243180179421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11698348858017495453452947 17547523287026243180179421)
    ·
      refine ⟨6580321232634841192567283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17547523287026243180179421 6580321232634841192567283)
      ·
        refine ⟨9870481848952261788850925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6580321232634841192567283 9870481848952261788850925)
        ·
          refine ⟨3701430693357098170819097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9870481848952261788850925 3701430693357098170819097)
          ·
            refine ⟨2776073020017823628114323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3701430693357098170819097 2776073020017823628114323)
            ·
              refine ⟨4164109530026735442171485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2776073020017823628114323 4164109530026735442171485)
              ·
                refine ⟨1561541073760025790814307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4164109530026735442171485 1561541073760025790814307)
                ·
                  refine ⟨2342311610640038686221461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1561541073760025790814307 2342311610640038686221461)
                  ·
                    refine ⟨109795856748751813416631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2342311610640038686221461 109795856748751813416631)
                    ·
                      rfl

theorem cell23_641480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 1, 6].length) (baseStart_641480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_641480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_641480 prefixEnd_641480 := by exact prefixLift 641480
  have htrace : WordTrace (prefixWord ++ tailWord_641480) baseStart_641480 baseEnd_641480 := by
    simpa [prefixWord, tailWord_641480, baseEnd_641480] using wordTrace_append hprefix tailTrace_641480
  have hstable : (prefixWord ++ tailWord_641480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641480).length < 2 ^ (prefixWord ++ tailWord_641480).sum := by decide
  have hdescent : baseEnd_641480 < baseStart_641480 := by decide
  rcases family_descends (prefixWord ++ tailWord_641480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641514 : List Nat := [3, 1, 3, 1, 3, 1, 3, 2, 2, 4]
def baseStart_641514 : Nat := 118140960795 + 641514 * 2 ^ 59
def prefixEnd_641514 : Nat := 4983230072969 + 3 ^ 40 * 641514 * 2
def baseEnd_641514 : Nat := 109801676196169435741579

theorem tailTrace_641514 : CollatzResearch.WordTrace tailWord_641514 prefixEnd_641514 109801676196169435741579 := by
  unfold tailWord_641514
  simp only [CollatzResearch.WordTrace]
  refine ⟨5849484449477953678410899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15598625198607876475762397 5849484449477953678410899)
  ·
    refine ⟨8774226674216930517616349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5849484449477953678410899 8774226674216930517616349)
    ·
      refine ⟨3290335002831348944106131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8774226674216930517616349 3290335002831348944106131)
      ·
        refine ⟨4935502504247023416159197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3290335002831348944106131 4935502504247023416159197)
        ·
          refine ⟨1850813439092633781059699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4935502504247023416159197 1850813439092633781059699)
          ·
            refine ⟨2776220158638950671589549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1850813439092633781059699 2776220158638950671589549)
            ·
              refine ⟨1041082559489606501846081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2776220158638950671589549 1041082559489606501846081)
              ·
                refine ⟨780811919617204876384561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1041082559489606501846081 780811919617204876384561)
                ·
                  refine ⟨585608939712903657288421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 780811919617204876384561 585608939712903657288421)
                  ·
                    refine ⟨109801676196169435741579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 585608939712903657288421 109801676196169435741579)
                    ·
                      rfl

theorem cell23_641514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_641514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_641514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_641514 prefixEnd_641514 := by exact prefixLift 641514
  have htrace : WordTrace (prefixWord ++ tailWord_641514) baseStart_641514 baseEnd_641514 := by
    simpa [prefixWord, tailWord_641514, baseEnd_641514] using wordTrace_append hprefix tailTrace_641514
  have hstable : (prefixWord ++ tailWord_641514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641514).length < 2 ^ (prefixWord ++ tailWord_641514).sum := by decide
  have hdescent : baseEnd_641514 < baseStart_641514 := by decide
  rcases family_descends (prefixWord ++ tailWord_641514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641521 : List Nat := [1, 2, 2, 2, 3, 1, 1, 6, 1, 2, 2]
def baseStart_641521 : Nat := 118140960795 + 641521 * 2 ^ 59
def prefixEnd_641521 : Nat := 4983230072969 + 3 ^ 40 * 641521 * 2
def baseEnd_641521 : Nat := 329408622953089779837205

theorem tailTrace_641521 : CollatzResearch.WordTrace tailWord_641521 prefixEnd_641521 329408622953089779837205 := by
  unfold tailWord_641521
  simp only [CollatzResearch.WordTrace]
  refine ⟨23398193108886454909148417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15598795405924303272765611 23398193108886454909148417)
  ·
    refine ⟨17548644831664841181861313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23398193108886454909148417 17548644831664841181861313)
    ·
      refine ⟨13161483623748630886395985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17548644831664841181861313 13161483623748630886395985)
      ·
        refine ⟨9871112717811473164796989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13161483623748630886395985 9871112717811473164796989)
        ·
          refine ⟨3701667269179302436798871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9871112717811473164796989 3701667269179302436798871)
          ·
            refine ⟨5552500903768953655198307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3701667269179302436798871 5552500903768953655198307)
            ·
              refine ⟨8328751355653430482797461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5552500903768953655198307 8328751355653430482797461)
              ·
                refine ⟨390410219796254553881131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8328751355653430482797461 390410219796254553881131)
                ·
                  refine ⟨585615329694381830821697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 390410219796254553881131 585615329694381830821697)
                  ·
                    refine ⟨439211497270786373116273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 585615329694381830821697 439211497270786373116273)
                    ·
                      refine ⟨329408622953089779837205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 439211497270786373116273 329408622953089779837205)
                      ·
                        rfl

theorem cell23_641521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 6, 1, 2, 2].length) (baseStart_641521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_641521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_641521 prefixEnd_641521 := by exact prefixLift 641521
  have htrace : WordTrace (prefixWord ++ tailWord_641521) baseStart_641521 baseEnd_641521 := by
    simpa [prefixWord, tailWord_641521, baseEnd_641521] using wordTrace_append hprefix tailTrace_641521
  have hstable : (prefixWord ++ tailWord_641521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641521).length < 2 ^ (prefixWord ++ tailWord_641521).sum := by decide
  have hdescent : baseEnd_641521 < baseStart_641521 := by decide
  rcases family_descends (prefixWord ++ tailWord_641521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641572 : List Nat := [2, 3, 1, 5, 1, 1, 3, 2, 1, 2, 2]
def baseStart_641572 : Nat := 118140960795 + 641572 * 2 ^ 59
def prefixEnd_641572 : Nat := 4983230072969 + 3 ^ 40 * 641572 * 2
def baseEnd_641572 : Nat := 329434810466469080299471

theorem tailTrace_641572 : CollatzResearch.WordTrace tailWord_641572 prefixEnd_641572 329434810466469080299471 := by
  unfold tailWord_641572
  simp only [CollatzResearch.WordTrace]
  refine ⟨11700026615850845309627485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15600035487801127079503313 11700026615850845309627485)
  ·
    refine ⟨4387509980944066991110307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11700026615850845309627485 4387509980944066991110307)
    ·
      refine ⟨6581264971416100486665461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4387509980944066991110307 6581264971416100486665461)
      ·
        refine ⟨616993591070259420624887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6581264971416100486665461 616993591070259420624887)
        ·
          refine ⟨925490386605389130937331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 616993591070259420624887 925490386605389130937331)
          ·
            refine ⟨1388235579908083696405997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 925490386605389130937331 1388235579908083696405997)
            ·
              refine ⟨520588342465531386152249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1388235579908083696405997 520588342465531386152249)
              ·
                refine ⟨390441256849148539614187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 520588342465531386152249 390441256849148539614187)
                ·
                  refine ⟨585661885273722809421281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 390441256849148539614187 585661885273722809421281)
                  ·
                    refine ⟨439246413955292107065961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 585661885273722809421281 439246413955292107065961)
                    ·
                      refine ⟨329434810466469080299471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 439246413955292107065961 329434810466469080299471)
                      ·
                        rfl

theorem cell23_641572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_641572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_641572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_641572 prefixEnd_641572 := by exact prefixLift 641572
  have htrace : WordTrace (prefixWord ++ tailWord_641572) baseStart_641572 baseEnd_641572 := by
    simpa [prefixWord, tailWord_641572, baseEnd_641572] using wordTrace_append hprefix tailTrace_641572
  have hstable : (prefixWord ++ tailWord_641572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641572).length < 2 ^ (prefixWord ++ tailWord_641572).sum := by decide
  have hdescent : baseEnd_641572 < baseStart_641572 := by decide
  rcases family_descends (prefixWord ++ tailWord_641572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641597 : List Nat := [1, 4, 1, 3, 2, 1, 1, 2, 2, 1, 5]
def baseStart_641597 : Nat := 118140960795 + 641597 * 2 ^ 59
def prefixEnd_641597 : Nat := 4983230072969 + 3 ^ 40 * 641597 * 2
def baseEnd_641597 : Nat := 329447647482831482486855

theorem tailTrace_641597 : CollatzResearch.WordTrace tailWord_641597 prefixEnd_641597 329447647482831482486855 := by
  unfold tailWord_641597
  simp only [CollatzResearch.WordTrace]
  refine ⟨23400965056611119888915045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15600643371074079925943363 23400965056611119888915045)
  ·
    refine ⟨4387680948114584979171571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23400965056611119888915045 4387680948114584979171571)
    ·
      refine ⟨6581521422171877468757357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4387680948114584979171571 6581521422171877468757357)
      ·
        refine ⟨2468070533314454050784009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6581521422171877468757357 2468070533314454050784009)
        ·
          refine ⟨1851052899985840538088007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2468070533314454050784009 1851052899985840538088007)
          ·
            refine ⟨2776579349978760807132011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1851052899985840538088007 2776579349978760807132011)
            ·
              refine ⟨4164869024968141210698017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2776579349978760807132011 4164869024968141210698017)
              ·
                refine ⟨3123651768726105908023513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4164869024968141210698017 3123651768726105908023513)
                ·
                  refine ⟨2342738826544579431017635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3123651768726105908023513 2342738826544579431017635)
                  ·
                    refine ⟨3514108239816869146526453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2342738826544579431017635 3514108239816869146526453)
                    ·
                      refine ⟨329447647482831482486855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3514108239816869146526453 329447647482831482486855)
                      ·
                        rfl

theorem cell23_641597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_641597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_641597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_641597 prefixEnd_641597 := by exact prefixLift 641597
  have htrace : WordTrace (prefixWord ++ tailWord_641597) baseStart_641597 baseEnd_641597 := by
    simpa [prefixWord, tailWord_641597, baseEnd_641597] using wordTrace_append hprefix tailTrace_641597
  have hstable : (prefixWord ++ tailWord_641597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641597).length < 2 ^ (prefixWord ++ tailWord_641597).sum := by decide
  have hdescent : baseEnd_641597 < baseStart_641597 := by decide
  rcases family_descends (prefixWord ++ tailWord_641597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641598 : List Nat := [4, 2, 1, 4, 1, 1, 1, 1, 3, 3, 2]
def baseStart_641598 : Nat := 118140960795 + 641598 * 2 ^ 59
def prefixEnd_641598 : Nat := 4983230072969 + 3 ^ 40 * 641598 * 2
def baseEnd_641598 : Nat := 329448160963485978574351

theorem tailTrace_641598 : CollatzResearch.WordTrace tailWord_641598 prefixEnd_641598 329448160963485978574351 := by
  unfold tailWord_641598
  simp only [CollatzResearch.WordTrace]
  refine ⟨2925125191200937132462681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15600667686404998039800965 2925125191200937132462681)
  ·
    refine ⟨2193843893400702849347011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2925125191200937132462681 2193843893400702849347011)
    ·
      refine ⟨3290765840101054274020517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2193843893400702849347011 3290765840101054274020517)
      ·
        refine ⟨617018595018947676378847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3290765840101054274020517 617018595018947676378847)
        ·
          refine ⟨925527892528421514568271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 617018595018947676378847 925527892528421514568271)
          ·
            refine ⟨1388291838792632271852407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 925527892528421514568271 1388291838792632271852407)
            ·
              refine ⟨2082437758188948407778611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1388291838792632271852407 2082437758188948407778611)
              ·
                refine ⟨3123656637283422611667917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2082437758188948407778611 3123656637283422611667917)
                ·
                  refine ⟨1171371238981283479375469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3123656637283422611667917 1171371238981283479375469)
                  ·
                    refine ⟨439264214617981304765801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1171371238981283479375469 439264214617981304765801)
                    ·
                      refine ⟨329448160963485978574351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 439264214617981304765801 329448160963485978574351)
                      ·
                        rfl

theorem cell23_641598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_641598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_641598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_641598 prefixEnd_641598 := by exact prefixLift 641598
  have htrace : WordTrace (prefixWord ++ tailWord_641598) baseStart_641598 baseEnd_641598 := by
    simpa [prefixWord, tailWord_641598, baseEnd_641598] using wordTrace_append hprefix tailTrace_641598
  have hstable : (prefixWord ++ tailWord_641598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641598).length < 2 ^ (prefixWord ++ tailWord_641598).sum := by decide
  have hdescent : baseEnd_641598 < baseStart_641598 := by decide
  rcases family_descends (prefixWord ++ tailWord_641598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641600 : List Nat := [2, 1, 1, 2, 2, 2, 2, 4, 7]
def baseStart_641600 : Nat := 118140960795 + 641600 * 2 ^ 59
def prefixEnd_641600 : Nat := 4983230072969 + 3 ^ 40 * 641600 * 2
def baseEnd_641600 : Nat := 36605465324977218972149

theorem tailTrace_641600 : CollatzResearch.WordTrace tailWord_641600 prefixEnd_641600 36605465324977218972149 := by
  unfold tailWord_641600
  simp only [CollatzResearch.WordTrace]
  refine ⟨11700537237800125700637127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15600716317066834267516169 11700537237800125700637127)
  ·
    refine ⟨17550805856700188550955691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11700537237800125700637127 17550805856700188550955691)
    ·
      refine ⟨26326208785050282826433537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17550805856700188550955691 26326208785050282826433537)
      ·
        refine ⟨19744656588787712119825153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26326208785050282826433537 19744656588787712119825153)
        ·
          refine ⟨14808492441590784089868865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19744656588787712119825153 14808492441590784089868865)
          ·
            refine ⟨11106369331193088067401649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14808492441590784089868865 11106369331193088067401649)
            ·
              refine ⟨8329776998394816050551237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11106369331193088067401649 8329776998394816050551237)
              ·
                refine ⟨1561833187199028009478357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8329776998394816050551237 1561833187199028009478357)
                ·
                  refine ⟨36605465324977218972149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1561833187199028009478357 36605465324977218972149)
                  ·
                    rfl

theorem cell23_641600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 7].length) (baseStart_641600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_641600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_641600 prefixEnd_641600 := by exact prefixLift 641600
  have htrace : WordTrace (prefixWord ++ tailWord_641600) baseStart_641600 baseEnd_641600 := by
    simpa [prefixWord, tailWord_641600, baseEnd_641600] using wordTrace_append hprefix tailTrace_641600
  have hstable : (prefixWord ++ tailWord_641600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641600).length < 2 ^ (prefixWord ++ tailWord_641600).sum := by decide
  have hdescent : baseEnd_641600 < baseStart_641600 := by decide
  rcases family_descends (prefixWord ++ tailWord_641600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641664 : List Nat := [2, 1, 1, 2, 1, 7, 1, 1, 2, 5]
def baseStart_641664 : Nat := 118140960795 + 641664 * 2 ^ 59
def prefixEnd_641664 : Nat := 4983230072969 + 3 ^ 40 * 641664 * 2
def baseEnd_641664 : Nat := 109827350228894240116349

theorem tailTrace_641664 : CollatzResearch.WordTrace tailWord_641664 prefixEnd_641664 109827350228894240116349 := by
  unfold tailWord_641664
  simp only [CollatzResearch.WordTrace]
  refine ⟨11701704373684195165802023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15602272498245593554402697 11701704373684195165802023)
  ·
    refine ⟨17552556560526292748703035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11701704373684195165802023 17552556560526292748703035)
    ·
      refine ⟨26328834840789439123054553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17552556560526292748703035 26328834840789439123054553)
      ·
        refine ⟨19746626130592079342290915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26328834840789439123054553 19746626130592079342290915)
        ·
          refine ⟨29619939195888119013436373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19746626130592079342290915 29619939195888119013436373)
          ·
            refine ⟨694217324903627789377415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 29619939195888119013436373 694217324903627789377415)
            ·
              refine ⟨1041325987355441684066123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 694217324903627789377415 1041325987355441684066123)
              ·
                refine ⟨1561988981033162526099185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1041325987355441684066123 1561988981033162526099185)
                ·
                  refine ⟨1171491735774871894574389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1561988981033162526099185 1171491735774871894574389)
                  ·
                    refine ⟨109827350228894240116349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1171491735774871894574389 109827350228894240116349)
                    ·
                      rfl

theorem cell23_641664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 2, 5].length) (baseStart_641664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_641664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_641664 prefixEnd_641664 := by exact prefixLift 641664
  have htrace : WordTrace (prefixWord ++ tailWord_641664) baseStart_641664 baseEnd_641664 := by
    simpa [prefixWord, tailWord_641664, baseEnd_641664] using wordTrace_append hprefix tailTrace_641664
  have hstable : (prefixWord ++ tailWord_641664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641664).length < 2 ^ (prefixWord ++ tailWord_641664).sum := by decide
  have hdescent : baseEnd_641664 < baseStart_641664 := by decide
  rcases family_descends (prefixWord ++ tailWord_641664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641666 : List Nat := [3, 4, 3, 1, 2, 1, 2, 1, 1, 3, 2]
def baseStart_641666 : Nat := 118140960795 + 641666 * 2 ^ 59
def prefixEnd_641666 : Nat := 4983230072969 + 3 ^ 40 * 641666 * 2
def baseEnd_641666 : Nat := 329483077647991712524039

theorem tailTrace_641666 : CollatzResearch.WordTrace tailWord_641666 prefixEnd_641666 329483077647991712524039 := by
  unfold tailWord_641666
  simp only [CollatzResearch.WordTrace]
  refine ⟨5850870423340286168294213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15602321128907429782117901 5850870423340286168294213)
  ·
    refine ⟨1097038204376303656555165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5850870423340286168294213 1097038204376303656555165)
    ·
      refine ⟨411389326641113871208187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1097038204376303656555165 411389326641113871208187)
      ·
        refine ⟨617083989961670806812281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 411389326641113871208187 617083989961670806812281)
        ·
          refine ⟨462812992471253105109211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 617083989961670806812281 462812992471253105109211)
          ·
            refine ⟨694219488706879657663817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 462812992471253105109211 694219488706879657663817)
            ·
              refine ⟨520664616530159743247863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 694219488706879657663817 520664616530159743247863)
              ·
                refine ⟨780996924795239614871795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 520664616530159743247863 780996924795239614871795)
                ·
                  refine ⟨1171495387192859422307693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 780996924795239614871795 1171495387192859422307693)
                  ·
                    refine ⟨439310770197322283365385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1171495387192859422307693 439310770197322283365385)
                    ·
                      refine ⟨329483077647991712524039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 439310770197322283365385 329483077647991712524039)
                      ·
                        rfl

theorem cell23_641666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_641666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_641666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_641666 prefixEnd_641666 := by exact prefixLift 641666
  have htrace : WordTrace (prefixWord ++ tailWord_641666) baseStart_641666 baseEnd_641666 := by
    simpa [prefixWord, tailWord_641666, baseEnd_641666] using wordTrace_append hprefix tailTrace_641666
  have hstable : (prefixWord ++ tailWord_641666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641666).length < 2 ^ (prefixWord ++ tailWord_641666).sum := by decide
  have hdescent : baseEnd_641666 < baseStart_641666 := by decide
  rcases family_descends (prefixWord ++ tailWord_641666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641728 : List Nat := [2, 1, 1, 2, 4, 4, 1, 3, 1, 4]
def baseStart_641728 : Nat := 118140960795 + 641728 * 2 ^ 59
def prefixEnd_641728 : Nat := 4983230072969 + 3 ^ 40 * 641728 * 2
def baseEnd_641728 : Nat := 109838304482856823316251

theorem tailTrace_641728 : CollatzResearch.WordTrace tailWord_641728 prefixEnd_641728 109838304482856823316251 := by
  unfold tailWord_641728
  simp only [CollatzResearch.WordTrace]
  refine ⟨11702871509568264630966919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15603828679424352841289225 11702871509568264630966919)
  ·
    refine ⟨17554307264352396946450379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11702871509568264630966919 17554307264352396946450379)
    ·
      refine ⟨26331460896528595419675569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17554307264352396946450379 26331460896528595419675569)
      ·
        refine ⟨19748595672396446564756677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26331460896528595419675569 19748595672396446564756677)
        ·
          refine ⟨3702861688574333730891877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19748595672396446564756677 3702861688574333730891877)
          ·
            refine ⟨694286566607687574542227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3702861688574333730891877 694286566607687574542227)
            ·
              refine ⟨1041429849911531361813341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 694286566607687574542227 1041429849911531361813341)
              ·
                refine ⟨390536193716824260680003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1041429849911531361813341 390536193716824260680003)
                ·
                  refine ⟨585804290575236391020005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 390536193716824260680003 585804290575236391020005)
                  ·
                    refine ⟨109838304482856823316251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 585804290575236391020005 109838304482856823316251)
                    ·
                      rfl

theorem cell23_641728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 3, 1, 4].length) (baseStart_641728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_641728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_641728 prefixEnd_641728 := by exact prefixLift 641728
  have htrace : WordTrace (prefixWord ++ tailWord_641728) baseStart_641728 baseEnd_641728 := by
    simpa [prefixWord, tailWord_641728, baseEnd_641728] using wordTrace_append hprefix tailTrace_641728
  have hstable : (prefixWord ++ tailWord_641728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641728).length < 2 ^ (prefixWord ++ tailWord_641728).sum := by decide
  have hdescent : baseEnd_641728 < baseStart_641728 := by decide
  rcases family_descends (prefixWord ++ tailWord_641728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641751 : List Nat := [1, 1, 3, 2, 1, 4, 3, 1, 3, 1, 3]
def baseStart_641751 : Nat := 118140960795 + 641751 * 2 ^ 59
def prefixEnd_641751 : Nat := 4983230072969 + 3 ^ 40 * 641751 * 2
def baseEnd_641751 : Nat := 329526723503623879961147

theorem tailTrace_641751 : CollatzResearch.WordTrace tailWord_641751 prefixEnd_641751 329526723503623879961147 := by
  unfold tailWord_641751
  simp only [CollatzResearch.WordTrace]
  refine ⟨23406581898053204190021107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15604387932035469460014071 23406581898053204190021107)
  ·
    refine ⟨35109872847079806285031661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23406581898053204190021107 35109872847079806285031661)
    ·
      refine ⟨13166202317654927356886873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35109872847079806285031661 13166202317654927356886873)
      ·
        refine ⟨9874651738241195517665155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13166202317654927356886873 9874651738241195517665155)
        ·
          refine ⟨14811977607361793276497733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9874651738241195517665155 14811977607361793276497733)
          ·
            refine ⟨2777245801380336239343325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14811977607361793276497733 2777245801380336239343325)
            ·
              refine ⟨1041467175517626089753747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2777245801380336239343325 1041467175517626089753747)
              ·
                refine ⟨1562200763276439134630621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1041467175517626089753747 1562200763276439134630621)
                ·
                  refine ⟨585825286228664675486483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1562200763276439134630621 585825286228664675486483)
                  ·
                    refine ⟨878737929342997013229725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 585825286228664675486483 878737929342997013229725)
                    ·
                      refine ⟨329526723503623879961147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 878737929342997013229725 329526723503623879961147)
                      ·
                        rfl

theorem cell23_641751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 3, 1, 3].length) (baseStart_641751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_641751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_641751 prefixEnd_641751 := by exact prefixLift 641751
  have htrace : WordTrace (prefixWord ++ tailWord_641751) baseStart_641751 baseEnd_641751 := by
    simpa [prefixWord, tailWord_641751, baseEnd_641751] using wordTrace_append hprefix tailTrace_641751
  have hstable : (prefixWord ++ tailWord_641751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641751).length < 2 ^ (prefixWord ++ tailWord_641751).sum := by decide
  have hdescent : baseEnd_641751 < baseStart_641751 := by decide
  rcases family_descends (prefixWord ++ tailWord_641751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641778 : List Nat := [3, 2, 1, 3, 1, 3, 2, 1, 2, 3, 2]
def baseStart_641778 : Nat := 118140960795 + 641778 * 2 ^ 59
def prefixEnd_641778 : Nat := 4983230072969 + 3 ^ 40 * 641778 * 2
def baseEnd_641778 : Nat := 329540587481295274323523

theorem tailTrace_641778 : CollatzResearch.WordTrace tailWord_641778 prefixEnd_641778 329540587481295274323523 := by
  unfold tailWord_641778
  simp only [CollatzResearch.WordTrace]
  refine ⟨5851891667238846950313497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15605044445970258534169325 5851891667238846950313497)
  ·
    refine ⟨4388918750429135212735123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5851891667238846950313497 4388918750429135212735123)
    ·
      refine ⟨6583378125643702819102685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4388918750429135212735123 6583378125643702819102685)
      ·
        refine ⟨2468766797116388557163507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6583378125643702819102685 2468766797116388557163507)
        ·
          refine ⟨3703150195674582835745261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2468766797116388557163507 3703150195674582835745261)
          ·
            refine ⟨1388681323377968563404473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3703150195674582835745261 1388681323377968563404473)
            ·
              refine ⟨1041510992533476422553355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1388681323377968563404473 1041510992533476422553355)
              ·
                refine ⟨1562266488800214633830033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1041510992533476422553355 1562266488800214633830033)
                ·
                  refine ⟨1171699866600160975372525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1562266488800214633830033 1171699866600160975372525)
                  ·
                    refine ⟨439387449975060365764697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1171699866600160975372525 439387449975060365764697)
                    ·
                      refine ⟨329540587481295274323523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 439387449975060365764697 329540587481295274323523)
                      ·
                        rfl

theorem cell23_641778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_641778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_641778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_641778 prefixEnd_641778 := by exact prefixLift 641778
  have htrace : WordTrace (prefixWord ++ tailWord_641778) baseStart_641778 baseEnd_641778 := by
    simpa [prefixWord, tailWord_641778, baseEnd_641778] using wordTrace_append hprefix tailTrace_641778
  have hstable : (prefixWord ++ tailWord_641778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641778).length < 2 ^ (prefixWord ++ tailWord_641778).sum := by decide
  have hdescent : baseEnd_641778 < baseStart_641778 := by decide
  rcases family_descends (prefixWord ++ tailWord_641778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641827 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 4, 7]
def baseStart_641827 : Nat := 118140960795 + 641827 * 2 ^ 59
def prefixEnd_641827 : Nat := 4983230072969 + 3 ^ 40 * 641827 * 2
def baseEnd_641827 : Nat := 109855249344455194203599

theorem tailTrace_641827 : CollatzResearch.WordTrace tailWord_641827 prefixEnd_641827 109855249344455194203599 := by
  unfold tailWord_641827
  simp only [CollatzResearch.WordTrace]
  refine ⟨23409353845777869169787735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15606235897185246113191823 23409353845777869169787735)
  ·
    refine ⟨35114030768666803754681603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23409353845777869169787735 35114030768666803754681603)
    ·
      refine ⟨52671046153000205632022405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35114030768666803754681603 52671046153000205632022405)
      ·
        refine ⟨9875821153687538556004201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52671046153000205632022405 9875821153687538556004201)
        ·
          refine ⟨7406865865265653917003151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9875821153687538556004201 7406865865265653917003151)
          ·
            refine ⟨11110298797898480875504727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7406865865265653917003151 11110298797898480875504727)
            ·
              refine ⟨16665448196847721313257091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11110298797898480875504727 16665448196847721313257091)
              ·
                refine ⟨24998172295271581969885637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16665448196847721313257091 24998172295271581969885637)
                ·
                  refine ⟨4687157305363421619353557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24998172295271581969885637 4687157305363421619353557)
                  ·
                    refine ⟨109855249344455194203599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4687157305363421619353557 109855249344455194203599)
                    ·
                      rfl

theorem cell23_641827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 7].length) (baseStart_641827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_641827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_641827 prefixEnd_641827 := by exact prefixLift 641827
  have htrace : WordTrace (prefixWord ++ tailWord_641827) baseStart_641827 baseEnd_641827 := by
    simpa [prefixWord, tailWord_641827, baseEnd_641827] using wordTrace_append hprefix tailTrace_641827
  have hstable : (prefixWord ++ tailWord_641827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641827).length < 2 ^ (prefixWord ++ tailWord_641827).sum := by decide
  have hdescent : baseEnd_641827 < baseStart_641827 := by decide
  rcases family_descends (prefixWord ++ tailWord_641827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641841 : List Nat := [1, 2, 2, 3, 2, 1, 2, 2, 4, 1, 3]
def baseStart_641841 : Nat := 118140960795 + 641841 * 2 ^ 59
def prefixEnd_641841 : Nat := 4983230072969 + 3 ^ 40 * 641841 * 2
def baseEnd_641841 : Nat := 329572936762528527835733

theorem tailTrace_641841 : CollatzResearch.WordTrace tailWord_641841 prefixEnd_641841 329572936762528527835733 := by
  unfold tailWord_641841
  simp only [CollatzResearch.WordTrace]
  refine ⟨23409864467727149560797377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15606576311818099707198251 23409864467727149560797377)
  ·
    refine ⟨17557398350795362170598033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23409864467727149560797377 17557398350795362170598033)
    ·
      refine ⟨13168048763096521627948525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17557398350795362170598033 13168048763096521627948525)
      ·
        refine ⟨4938018286161195610480697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13168048763096521627948525 4938018286161195610480697)
        ·
          refine ⟨3703513714620896707860523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4938018286161195610480697 3703513714620896707860523)
          ·
            refine ⟨5555270571931345061790785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3703513714620896707860523 5555270571931345061790785)
            ·
              refine ⟨4166452928948508796343089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5555270571931345061790785 4166452928948508796343089)
              ·
                refine ⟨3124839696711381597257317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4166452928948508796343089 3124839696711381597257317)
                ·
                  refine ⟨585907443133384049485747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3124839696711381597257317 585907443133384049485747)
                  ·
                    refine ⟨878861164700076074228621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 585907443133384049485747 878861164700076074228621)
                    ·
                      refine ⟨329572936762528527835733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 878861164700076074228621 329572936762528527835733)
                      ·
                        rfl

theorem cell23_641841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_641841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_641841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_641841 prefixEnd_641841 := by exact prefixLift 641841
  have htrace : WordTrace (prefixWord ++ tailWord_641841) baseStart_641841 baseEnd_641841 := by
    simpa [prefixWord, tailWord_641841, baseEnd_641841] using wordTrace_append hprefix tailTrace_641841
  have hstable : (prefixWord ++ tailWord_641841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641841).length < 2 ^ (prefixWord ++ tailWord_641841).sum := by decide
  have hdescent : baseEnd_641841 < baseStart_641841 := by decide
  rcases family_descends (prefixWord ++ tailWord_641841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641845 : List Nat := [1, 3, 3, 1, 3, 3, 2, 1, 1, 2, 3]
def baseStart_641845 : Nat := 118140960795 + 641845 * 2 ^ 59
def prefixEnd_641845 : Nat := 4983230072969 + 3 ^ 40 * 641845 * 2
def baseEnd_641845 : Nat := 329574990685146512185715

theorem tailTrace_641845 : CollatzResearch.WordTrace tailWord_641845 prefixEnd_641845 329574990685146512185715 := by
  unfold tailWord_641845
  simp only [CollatzResearch.WordTrace]
  refine ⟨23410010359712658243942989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15606673573141772162628659 23410010359712658243942989)
  ·
    refine ⟨8778753884892246841478621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23410010359712658243942989 8778753884892246841478621)
    ·
      refine ⟨3292032706834592565554483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8778753884892246841478621 3292032706834592565554483)
      ·
        refine ⟨4938049060251888848331725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3292032706834592565554483 4938049060251888848331725)
        ·
          refine ⟨1851768397594458318124397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4938049060251888848331725 1851768397594458318124397)
          ·
            refine ⟨694413149097921869296649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1851768397594458318124397 694413149097921869296649)
            ·
              refine ⟨520809861823441401972487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 694413149097921869296649 520809861823441401972487)
              ·
                refine ⟨781214792735162102958731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 520809861823441401972487 781214792735162102958731)
                ·
                  refine ⟨1171822189102743154438097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 781214792735162102958731 1171822189102743154438097)
                  ·
                    refine ⟨878866641827057365828573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1171822189102743154438097 878866641827057365828573)
                    ·
                      refine ⟨329574990685146512185715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 878866641827057365828573 329574990685146512185715)
                      ·
                        rfl

theorem cell23_641845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 1, 1, 2, 3].length) (baseStart_641845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_641845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_641845 prefixEnd_641845 := by exact prefixLift 641845
  have htrace : WordTrace (prefixWord ++ tailWord_641845) baseStart_641845 baseEnd_641845 := by
    simpa [prefixWord, tailWord_641845, baseEnd_641845] using wordTrace_append hprefix tailTrace_641845
  have hstable : (prefixWord ++ tailWord_641845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641845).length < 2 ^ (prefixWord ++ tailWord_641845).sum := by decide
  have hdescent : baseEnd_641845 < baseStart_641845 := by decide
  rcases family_descends (prefixWord ++ tailWord_641845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641874 : List Nat := [3, 2, 2, 1, 1, 2, 1, 3, 2, 6]
def baseStart_641874 : Nat := 118140960795 + 641874 * 2 ^ 59
def prefixEnd_641874 : Nat := 4983230072969 + 3 ^ 40 * 641874 * 2
def baseEnd_641874 : Nat := 109863293874708966241027

theorem tailTrace_641874 : CollatzResearch.WordTrace tailWord_641874 prefixEnd_641874 109863293874708966241027 := by
  unfold tailWord_641874
  simp only [CollatzResearch.WordTrace]
  refine ⟨5852767019151899049187169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15607378717738397464499117 5852767019151899049187169)
  ·
    refine ⟨4389575264363924286890377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5852767019151899049187169 4389575264363924286890377)
    ·
      refine ⟨3292181448272943215167783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4389575264363924286890377 3292181448272943215167783)
      ·
        refine ⟨4938272172409414822751675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3292181448272943215167783 4938272172409414822751675)
        ·
          refine ⟨7407408258614122234127513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4938272172409414822751675 7407408258614122234127513)
          ·
            refine ⟨5555556193960591675595635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7407408258614122234127513 5555556193960591675595635)
            ·
              refine ⟨8333334290940887513393453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5555556193960591675595635 8333334290940887513393453)
              ·
                refine ⟨3125000359102832817522545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8333334290940887513393453 3125000359102832817522545)
                ·
                  refine ⟨2343750269327124613141909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3125000359102832817522545 2343750269327124613141909)
                  ·
                    refine ⟨109863293874708966241027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2343750269327124613141909 109863293874708966241027)
                    ·
                      rfl

theorem cell23_641874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_641874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_641874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_641874 prefixEnd_641874 := by exact prefixLift 641874
  have htrace : WordTrace (prefixWord ++ tailWord_641874) baseStart_641874 baseEnd_641874 := by
    simpa [prefixWord, tailWord_641874, baseEnd_641874] using wordTrace_append hprefix tailTrace_641874
  have hstable : (prefixWord ++ tailWord_641874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641874).length < 2 ^ (prefixWord ++ tailWord_641874).sum := by decide
  have hdescent : baseEnd_641874 < baseStart_641874 := by decide
  rcases family_descends (prefixWord ++ tailWord_641874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641951 : List Nat := [1, 1, 2, 5, 2, 1, 1, 3, 2, 5]
def baseStart_641951 : Nat := 118140960795 + 641951 * 2 ^ 59
def prefixEnd_641951 : Nat := 4983230072969 + 3 ^ 40 * 641951 * 2
def baseEnd_641951 : Nat := 109876473211507699153409

theorem tailTrace_641951 : CollatzResearch.WordTrace tailWord_641951 prefixEnd_641951 109876473211507699153409 := by
  unfold tailWord_641951
  simp only [CollatzResearch.WordTrace]
  refine ⟨23413876497328638347301707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15609250998219092231534471 23413876497328638347301707)
  ·
    refine ⟨35120814745992957520952561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23413876497328638347301707 35120814745992957520952561)
    ·
      refine ⟨26340611059494718140714421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35120814745992957520952561 26340611059494718140714421)
      ·
        refine ⟨2469432286827629825691977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26340611059494718140714421 2469432286827629825691977)
        ·
          refine ⟨1852074215120722369268983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2469432286827629825691977 1852074215120722369268983)
          ·
            refine ⟨2778111322681083553903475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1852074215120722369268983 2778111322681083553903475)
            ·
              refine ⟨4167166984021625330855213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2778111322681083553903475 4167166984021625330855213)
              ·
                refine ⟨1562687619008109499070705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4167166984021625330855213 1562687619008109499070705)
                ·
                  refine ⟨1172015714256082124303029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1562687619008109499070705 1172015714256082124303029)
                  ·
                    refine ⟨109876473211507699153409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1172015714256082124303029 109876473211507699153409)
                    ·
                      rfl

theorem cell23_641951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 2, 5].length) (baseStart_641951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_641951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_641951 prefixEnd_641951 := by exact prefixLift 641951
  have htrace : WordTrace (prefixWord ++ tailWord_641951) baseStart_641951 baseEnd_641951 := by
    simpa [prefixWord, tailWord_641951, baseEnd_641951] using wordTrace_append hprefix tailTrace_641951
  have hstable : (prefixWord ++ tailWord_641951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641951).length < 2 ^ (prefixWord ++ tailWord_641951).sum := by decide
  have hdescent : baseEnd_641951 < baseStart_641951 := by decide
  rcases family_descends (prefixWord ++ tailWord_641951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641972 : List Nat := [2, 5, 2, 1, 1, 1, 4, 2, 5]
def baseStart_641972 : Nat := 118140960795 + 641972 * 2 ^ 59
def prefixEnd_641972 : Nat := 4983230072969 + 3 ^ 40 * 641972 * 2
def baseEnd_641972 : Nat := 36626689192029723921959

theorem tailTrace_641972 : CollatzResearch.WordTrace tailWord_641972 prefixEnd_641972 36626689192029723921959 := by
  unfold tailWord_641972
  simp only [CollatzResearch.WordTrace]
  refine ⟨11707321215126279466908085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15609761620168372622544113 11707321215126279466908085)
  ·
    refine ⟨1097561363918088700022633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11707321215126279466908085 1097561363918088700022633)
    ·
      refine ⟨823171022938566525016975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1097561363918088700022633 823171022938566525016975)
      ·
        refine ⟨1234756534407849787525463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 823171022938566525016975 1234756534407849787525463)
        ·
          refine ⟨1852134801611774681288195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1234756534407849787525463 1852134801611774681288195)
          ·
            refine ⟨2778202202417662021932293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1852134801611774681288195 2778202202417662021932293)
            ·
              refine ⟨520912912953311629112305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2778202202417662021932293 520912912953311629112305)
              ·
                refine ⟨390684684714983721834229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 520912912953311629112305 390684684714983721834229)
                ·
                  refine ⟨36626689192029723921959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 390684684714983721834229 36626689192029723921959)
                  ·
                    rfl

theorem cell23_641972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_641972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_641972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_641972 prefixEnd_641972 := by exact prefixLift 641972
  have htrace : WordTrace (prefixWord ++ tailWord_641972) baseStart_641972 baseEnd_641972 := by
    simpa [prefixWord, tailWord_641972, baseEnd_641972] using wordTrace_append hprefix tailTrace_641972
  have hstable : (prefixWord ++ tailWord_641972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641972).length < 2 ^ (prefixWord ++ tailWord_641972).sum := by decide
  have hdescent : baseEnd_641972 < baseStart_641972 := by decide
  rcases family_descends (prefixWord ++ tailWord_641972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641991 : List Nat := [1, 1, 4, 1, 1, 2, 2, 2, 4, 2, 3]
def baseStart_641991 : Nat := 118140960795 + 641991 * 2 ^ 59
def prefixEnd_641991 : Nat := 4983230072969 + 3 ^ 40 * 641991 * 2
def baseEnd_641991 : Nat := 329649958860702940960043

theorem tailTrace_641991 : CollatzResearch.WordTrace tailWord_641991 prefixEnd_641991 329649958860702940960043 := by
  unfold tailWord_641991
  simp only [CollatzResearch.WordTrace]
  refine ⟨23415335417183725178757827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15610223611455816785838551 23415335417183725178757827)
  ·
    refine ⟨35123003125775587768136741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23415335417183725178757827 35123003125775587768136741)
    ·
      refine ⟨6585563086082922706525639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35123003125775587768136741 6585563086082922706525639)
      ·
        refine ⟨9878344629124384059788459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6585563086082922706525639 9878344629124384059788459)
        ·
          refine ⟨14817516943686576089682689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9878344629124384059788459 14817516943686576089682689)
          ·
            refine ⟨11113137707764932067262017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14817516943686576089682689 11113137707764932067262017)
            ·
              refine ⟨8334853280823699050446513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11113137707764932067262017 8334853280823699050446513)
              ·
                refine ⟨6251139960617774287834885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8334853280823699050446513 6251139960617774287834885)
                ·
                  refine ⟨1172088742615832678969041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6251139960617774287834885 1172088742615832678969041)
                  ·
                    refine ⟨879066556961874509226781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1172088742615832678969041 879066556961874509226781)
                    ·
                      refine ⟨329649958860702940960043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 879066556961874509226781 329649958860702940960043)
                      ·
                        rfl

theorem cell23_641991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 4, 2, 3].length) (baseStart_641991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_641991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_641991 prefixEnd_641991 := by exact prefixLift 641991
  have htrace : WordTrace (prefixWord ++ tailWord_641991) baseStart_641991 baseEnd_641991 := by
    simpa [prefixWord, tailWord_641991, baseEnd_641991] using wordTrace_append hprefix tailTrace_641991
  have hstable : (prefixWord ++ tailWord_641991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641991).length < 2 ^ (prefixWord ++ tailWord_641991).sum := by decide
  have hdescent : baseEnd_641991 < baseStart_641991 := by decide
  rcases family_descends (prefixWord ++ tailWord_641991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641994 : List Nat := [3, 1, 2, 1, 2, 1, 1, 2, 10]
def baseStart_641994 : Nat := 118140960795 + 641994 * 2 ^ 59
def prefixEnd_641994 : Nat := 4983230072969 + 3 ^ 40 * 641994 * 2
def baseEnd_641994 : Nat := 36627944366962936580281

theorem tailTrace_641994 : CollatzResearch.WordTrace tailWord_641994 prefixEnd_641994 36627944366962936580281 := by
  unfold tailWord_641994
  simp only [CollatzResearch.WordTrace]
  refine ⟨5853861209043214172779259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15610296557448571127411357 5853861209043214172779259)
  ·
    refine ⟨8780791813564821259168889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5853861209043214172779259 8780791813564821259168889)
    ·
      refine ⟨6585593860173615944376667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8780791813564821259168889 6585593860173615944376667)
      ·
        refine ⟨9878390790260423916565001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6585593860173615944376667 9878390790260423916565001)
        ·
          refine ⟨7408793092695317937423751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9878390790260423916565001 7408793092695317937423751)
          ·
            refine ⟨11113189639042976906135627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7408793092695317937423751 11113189639042976906135627)
            ·
              refine ⟨16669784458564465359203441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11113189639042976906135627 16669784458564465359203441)
              ·
                refine ⟨12502338343923349019402581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16669784458564465359203441 12502338343923349019402581)
                ·
                  refine ⟨36627944366962936580281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 12502338343923349019402581 36627944366962936580281)
                  ·
                    rfl

theorem cell23_641994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 10].length) (baseStart_641994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_641994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_641994 prefixEnd_641994 := by exact prefixLift 641994
  have htrace : WordTrace (prefixWord ++ tailWord_641994) baseStart_641994 baseEnd_641994 := by
    simpa [prefixWord, tailWord_641994, baseEnd_641994] using wordTrace_append hprefix tailTrace_641994
  have hstable : (prefixWord ++ tailWord_641994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641994).length < 2 ^ (prefixWord ++ tailWord_641994).sum := by decide
  have hdescent : baseEnd_641994 < baseStart_641994 := by decide
  rcases family_descends (prefixWord ++ tailWord_641994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_641998 : List Nat := [4, 1, 1, 1, 2, 4, 1, 2, 3, 4]
def baseStart_641998 : Nat := 118140960795 + 641998 * 2 ^ 59
def prefixEnd_641998 : Nat := 4983230072969 + 3 ^ 40 * 641998 * 2
def baseEnd_641998 : Nat := 109884517741761471190837

theorem tailTrace_641998 : CollatzResearch.WordTrace tailWord_641998 prefixEnd_641998 109884517741761471190837 := by
  unfold tailWord_641998
  simp only [CollatzResearch.WordTrace]
  refine ⟨2926948841019795671782831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15610393818772243582841765 2926948841019795671782831)
  ·
    refine ⟨4390423261529693507674247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2926948841019795671782831 4390423261529693507674247)
    ·
      refine ⟨6585634892294540261511371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4390423261529693507674247 6585634892294540261511371)
      ·
        refine ⟨9878452338441810392267057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6585634892294540261511371 9878452338441810392267057)
        ·
          refine ⟨7408839253831357794200293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9878452338441810392267057 7408839253831357794200293)
          ·
            refine ⟨1389157360093379586412555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7408839253831357794200293 1389157360093379586412555)
            ·
              refine ⟨2083736040140069379618833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1389157360093379586412555 2083736040140069379618833)
              ·
                refine ⟨1562802030105052034714125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2083736040140069379618833 1562802030105052034714125)
                ·
                  refine ⟨586050761289394513017797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1562802030105052034714125 586050761289394513017797)
                  ·
                    refine ⟨109884517741761471190837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 586050761289394513017797 109884517741761471190837)
                    ·
                      rfl

theorem cell23_641998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 3, 4].length) (baseStart_641998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_641998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_641998 prefixEnd_641998 := by exact prefixLift 641998
  have htrace : WordTrace (prefixWord ++ tailWord_641998) baseStart_641998 baseEnd_641998 := by
    simpa [prefixWord, tailWord_641998, baseEnd_641998] using wordTrace_append hprefix tailTrace_641998
  have hstable : (prefixWord ++ tailWord_641998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_641998).length < 2 ^ (prefixWord ++ tailWord_641998).sum := by decide
  have hdescent : baseEnd_641998 < baseStart_641998 := by decide
  rcases family_descends (prefixWord ++ tailWord_641998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642005 : List Nat := [1, 3, 2, 3, 3, 2, 1, 1, 2, 1, 4]
def baseStart_642005 : Nat := 118140960795 + 642005 * 2 ^ 59
def prefixEnd_642005 : Nat := 4983230072969 + 3 ^ 40 * 642005 * 2
def baseEnd_642005 : Nat := 329657147589865886184979

theorem tailTrace_642005 : CollatzResearch.WordTrace tailWord_642005 prefixEnd_642005 329657147589865886184979 := by
  unfold tailWord_642005
  simp only [CollatzResearch.WordTrace]
  refine ⟨23415846039133005569767469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15610564026088670379844979 23415846039133005569767469)
  ·
    refine ⟨8780942264674877088662801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23415846039133005569767469 8780942264674877088662801)
    ·
      refine ⟨6585706698506157816497101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8780942264674877088662801 6585706698506157816497101)
      ·
        refine ⟨2469640011939809181186413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6585706698506157816497101 2469640011939809181186413)
        ·
          refine ⟨926115004477428442944905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2469640011939809181186413 926115004477428442944905)
          ·
            refine ⟨694586253358071332208679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 926115004477428442944905 694586253358071332208679)
            ·
              refine ⟨1041879380037106998313019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 694586253358071332208679 1041879380037106998313019)
              ·
                refine ⟨1562819070055660497469529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1041879380037106998313019 1562819070055660497469529)
                ·
                  refine ⟨1172114302541745373102147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1562819070055660497469529 1172114302541745373102147)
                  ·
                    refine ⟨1758171453812618059653221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1172114302541745373102147 1758171453812618059653221)
                    ·
                      refine ⟨329657147589865886184979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1758171453812618059653221 329657147589865886184979)
                      ·
                        rfl

theorem cell23_642005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_642005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_642005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_642005 prefixEnd_642005 := by exact prefixLift 642005
  have htrace : WordTrace (prefixWord ++ tailWord_642005) baseStart_642005 baseEnd_642005 := by
    simpa [prefixWord, tailWord_642005, baseEnd_642005] using wordTrace_append hprefix tailTrace_642005
  have hstable : (prefixWord ++ tailWord_642005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642005).length < 2 ^ (prefixWord ++ tailWord_642005).sum := by decide
  have hdescent : baseEnd_642005 < baseStart_642005 := by decide
  rcases family_descends (prefixWord ++ tailWord_642005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642008 : List Nat := [2, 1, 2, 2, 2, 3, 3, 1, 2, 2, 3]
def baseStart_642008 : Nat := 118140960795 + 642008 * 2 ^ 59
def prefixEnd_642008 : Nat := 4983230072969 + 3 ^ 40 * 642008 * 2
def baseEnd_642008 : Nat := 329658688031829374447465

theorem tailTrace_642008 : CollatzResearch.WordTrace tailWord_642008 prefixEnd_642008 329658688031829374447465 := by
  unfold tailWord_642008
  simp only [CollatzResearch.WordTrace]
  refine ⟨11707977729061068541063339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15610636972081424721417785 11707977729061068541063339)
  ·
    refine ⟨17561966593591602811595009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11707977729061068541063339 17561966593591602811595009)
    ·
      refine ⟨13171474945193702108696257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17561966593591602811595009 13171474945193702108696257)
      ·
        refine ⟨9878606208895276581522193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13171474945193702108696257 9878606208895276581522193)
        ·
          refine ⟨7408954656671457436141645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9878606208895276581522193 7408954656671457436141645)
          ·
            refine ⟨2778357996251796538553117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7408954656671457436141645 2778357996251796538553117)
            ·
              refine ⟨1041884248594423701957419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2778357996251796538553117 1041884248594423701957419)
              ·
                refine ⟨1562826372891635552936129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1041884248594423701957419 1562826372891635552936129)
                ·
                  refine ⟨1172119779668726664702097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1562826372891635552936129 1172119779668726664702097)
                  ·
                    refine ⟨879089834751544998526573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1172119779668726664702097 879089834751544998526573)
                    ·
                      refine ⟨329658688031829374447465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 879089834751544998526573 329658688031829374447465)
                      ·
                        rfl

theorem cell23_642008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 2, 2, 3].length) (baseStart_642008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_642008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_642008 prefixEnd_642008 := by exact prefixLift 642008
  have htrace : WordTrace (prefixWord ++ tailWord_642008) baseStart_642008 baseEnd_642008 := by
    simpa [prefixWord, tailWord_642008, baseEnd_642008] using wordTrace_append hprefix tailTrace_642008
  have hstable : (prefixWord ++ tailWord_642008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642008).length < 2 ^ (prefixWord ++ tailWord_642008).sum := by decide
  have hdescent : baseEnd_642008 < baseStart_642008 := by decide
  rcases family_descends (prefixWord ++ tailWord_642008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642018 : List Nat := [3, 3, 3, 1, 1, 1, 1, 1, 2, 1, 6]
def baseStart_642018 : Nat := 118140960795 + 642018 * 2 ^ 59
def prefixEnd_642018 : Nat := 4983230072969 + 3 ^ 40 * 642018 * 2
def baseEnd_642018 : Nat := 329663822838374335322419

theorem tailTrace_642018 : CollatzResearch.WordTrace tailWord_642018 prefixEnd_642018 329663822838374335322419 := by
  unfold tailWord_642018
  simp only [CollatzResearch.WordTrace]
  refine ⟨5854080047021477197497677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15610880125390605859993805 5854080047021477197497677)
  ·
    refine ⟨2195280017633053949061629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5854080047021477197497677 2195280017633053949061629)
    ·
      refine ⟨823230006612395230898111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2195280017633053949061629 823230006612395230898111)
      ·
        refine ⟨1234845009918592846347167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 823230006612395230898111 1234845009918592846347167)
        ·
          refine ⟨1852267514877889269520751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1234845009918592846347167 1852267514877889269520751)
          ·
            refine ⟨2778401272316833904281127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1852267514877889269520751 2778401272316833904281127)
            ·
              refine ⟨4167601908475250856421691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2778401272316833904281127 4167601908475250856421691)
              ·
                refine ⟨6251402862712876284632537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4167601908475250856421691 6251402862712876284632537)
                ·
                  refine ⟨4688552147034657213474403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6251402862712876284632537 4688552147034657213474403)
                  ·
                    refine ⟨7032828220551985820211605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4688552147034657213474403 7032828220551985820211605)
                    ·
                      refine ⟨329663822838374335322419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7032828220551985820211605 329663822838374335322419)
                      ·
                        rfl

theorem cell23_642018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_642018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_642018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_642018 prefixEnd_642018 := by exact prefixLift 642018
  have htrace : WordTrace (prefixWord ++ tailWord_642018) baseStart_642018 baseEnd_642018 := by
    simpa [prefixWord, tailWord_642018, baseEnd_642018] using wordTrace_append hprefix tailTrace_642018
  have hstable : (prefixWord ++ tailWord_642018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642018).length < 2 ^ (prefixWord ++ tailWord_642018).sum := by decide
  have hdescent : baseEnd_642018 < baseStart_642018 := by decide
  rcases family_descends (prefixWord ++ tailWord_642018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642058 : List Nat := [3, 1, 2, 2, 3, 1, 1, 4, 1, 5]
def baseStart_642058 : Nat := 118140960795 + 642058 * 2 ^ 59
def prefixEnd_642058 : Nat := 4983230072969 + 3 ^ 40 * 642058 * 2
def baseEnd_642058 : Nat := 109894787354851392940745

theorem tailTrace_642058 : CollatzResearch.WordTrace tailWord_642058 prefixEnd_642058 109894787354851392940745 := by
  unfold tailWord_642058
  simp only [CollatzResearch.WordTrace]
  refine ⟨5854444776985248905361707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15611852738627330414297885 5854444776985248905361707)
  ·
    refine ⟨8781667165477873358042561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5854444776985248905361707 8781667165477873358042561)
    ·
      refine ⟨6586250374108405018531921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8781667165477873358042561 6586250374108405018531921)
      ·
        refine ⟨4939687780581303763898941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6586250374108405018531921 4939687780581303763898941)
        ·
          refine ⟨1852382917717988911462103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4939687780581303763898941 1852382917717988911462103)
          ·
            refine ⟨2778574376576983367193155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1852382917717988911462103 2778574376576983367193155)
            ·
              refine ⟨4167861564865475050789733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2778574376576983367193155 4167861564865475050789733)
              ·
                refine ⟨781474043412276572023075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4167861564865475050789733 781474043412276572023075)
                ·
                  refine ⟨1172211065118414858034613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 781474043412276572023075 1172211065118414858034613)
                  ·
                    refine ⟨109894787354851392940745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1172211065118414858034613 109894787354851392940745)
                    ·
                      rfl

theorem cell23_642058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 4, 1, 5].length) (baseStart_642058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_642058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_642058 prefixEnd_642058 := by exact prefixLift 642058
  have htrace : WordTrace (prefixWord ++ tailWord_642058) baseStart_642058 baseEnd_642058 := by
    simpa [prefixWord, tailWord_642058, baseEnd_642058] using wordTrace_append hprefix tailTrace_642058
  have hstable : (prefixWord ++ tailWord_642058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642058).length < 2 ^ (prefixWord ++ tailWord_642058).sum := by decide
  have hdescent : baseEnd_642058 < baseStart_642058 := by decide
  rcases family_descends (prefixWord ++ tailWord_642058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642072 : List Nat := [2, 1, 2, 3, 2, 2, 3, 3, 1, 1, 3]
def baseStart_642072 : Nat := 118140960795 + 642072 * 2 ^ 59
def prefixEnd_642072 : Nat := 4983230072969 + 3 ^ 40 * 642072 * 2
def baseEnd_642072 : Nat := 329691550793717124047171

theorem tailTrace_642072 : CollatzResearch.WordTrace tailWord_642072 prefixEnd_642072 329691550793717124047171 := by
  unfold tailWord_642072
  simp only [CollatzResearch.WordTrace]
  refine ⟨11709144864945138006228235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15612193153260184008304313 11709144864945138006228235)
  ·
    refine ⟨17563717297417707009342353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11709144864945138006228235 17563717297417707009342353)
    ·
      refine ⟨13172787973063280257006765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17563717297417707009342353 13172787973063280257006765)
      ·
        refine ⟨4939795489898730096377537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13172787973063280257006765 4939795489898730096377537)
        ·
          refine ⟨3704846617424047572283153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4939795489898730096377537 3704846617424047572283153)
          ·
            refine ⟨2778634963068035679212365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3704846617424047572283153 2778634963068035679212365)
            ·
              refine ⟨1041988111150513379704637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2778634963068035679212365 1041988111150513379704637)
              ·
                refine ⟨390745541681442517389239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1041988111150513379704637 390745541681442517389239)
                ·
                  refine ⟨586118312522163776083859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 390745541681442517389239 586118312522163776083859)
                  ·
                    refine ⟨879177468783245664125789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 586118312522163776083859 879177468783245664125789)
                    ·
                      refine ⟨329691550793717124047171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 879177468783245664125789 329691550793717124047171)
                      ·
                        rfl

theorem cell23_642072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 3, 1, 1, 3].length) (baseStart_642072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_642072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_642072 prefixEnd_642072 := by exact prefixLift 642072
  have htrace : WordTrace (prefixWord ++ tailWord_642072) baseStart_642072 baseEnd_642072 := by
    simpa [prefixWord, tailWord_642072, baseEnd_642072] using wordTrace_append hprefix tailTrace_642072
  have hstable : (prefixWord ++ tailWord_642072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642072).length < 2 ^ (prefixWord ++ tailWord_642072).sum := by decide
  have hdescent : baseEnd_642072 < baseStart_642072 := by decide
  rcases family_descends (prefixWord ++ tailWord_642072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642098 : List Nat := [3, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3]
def baseStart_642098 : Nat := 118140960795 + 642098 * 2 ^ 59
def prefixEnd_642098 : Nat := 4983230072969 + 3 ^ 40 * 642098 * 2
def baseEnd_642098 : Nat := 329704901290734022322051

theorem tailTrace_642098 : CollatzResearch.WordTrace tailWord_642098 prefixEnd_642098 329704901290734022322051 := by
  unfold tailWord_642098
  simp only [CollatzResearch.WordTrace]
  refine ⟨5854809506949020613225737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15612825351864054968601965 5854809506949020613225737)
  ·
    refine ⟨4391107130211765459919303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5854809506949020613225737 4391107130211765459919303)
    ·
      refine ⟨6586660695317648189878955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4391107130211765459919303 6586660695317648189878955)
      ·
        refine ⟨9879991042976472284818433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6586660695317648189878955 9879991042976472284818433)
        ·
          refine ⟨7409993282232354213613825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9879991042976472284818433 7409993282232354213613825)
          ·
            refine ⟨5557494961674265660210369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7409993282232354213613825 5557494961674265660210369)
            ·
              refine ⟨4168121221255699245157777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5557494961674265660210369 4168121221255699245157777)
              ·
                refine ⟨3126090915941774433868333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4168121221255699245157777 3126090915941774433868333)
                ·
                  refine ⟨1172284093478165412700625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3126090915941774433868333 1172284093478165412700625)
                  ·
                    refine ⟨879213070108624059525469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1172284093478165412700625 879213070108624059525469)
                    ·
                      refine ⟨329704901290734022322051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 879213070108624059525469 329704901290734022322051)
                      ·
                        rfl

theorem cell23_642098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3].length) (baseStart_642098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_642098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_642098 prefixEnd_642098 := by exact prefixLift 642098
  have htrace : WordTrace (prefixWord ++ tailWord_642098) baseStart_642098 baseEnd_642098 := by
    simpa [prefixWord, tailWord_642098, baseEnd_642098] using wordTrace_append hprefix tailTrace_642098
  have hstable : (prefixWord ++ tailWord_642098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642098).length < 2 ^ (prefixWord ++ tailWord_642098).sum := by decide
  have hdescent : baseEnd_642098 < baseStart_642098 := by decide
  rcases family_descends (prefixWord ++ tailWord_642098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642105 : List Nat := [1, 2, 1, 5, 2, 2, 1, 3, 2, 4]
def baseStart_642105 : Nat := 118140960795 + 642105 * 2 ^ 59
def prefixEnd_642105 : Nat := 4983230072969 + 3 ^ 40 * 642105 * 2
def baseEnd_642105 : Nat := 109902831885105164978173

theorem tailTrace_642105 : CollatzResearch.WordTrace tailWord_642105 prefixEnd_642105 109902831885105164978173 := by
  unfold tailWord_642105
  simp only [CollatzResearch.WordTrace]
  refine ⟨23419493338770722648407769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15612995559180481765605179 23419493338770722648407769)
  ·
    refine ⟨17564620004078041986305827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23419493338770722648407769 17564620004078041986305827)
    ·
      refine ⟨26346930006117062979458741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17564620004078041986305827 26346930006117062979458741)
      ·
        refine ⟨2470024688073474654324257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26346930006117062979458741 2470024688073474654324257)
        ·
          refine ⟨1852518516055105990743193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2470024688073474654324257 1852518516055105990743193)
          ·
            refine ⟨1389388887041329493057395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1852518516055105990743193 1389388887041329493057395)
            ·
              refine ⟨2084083330561994239586093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1389388887041329493057395 2084083330561994239586093)
              ·
                refine ⟨781531248960747839844785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2084083330561994239586093 781531248960747839844785)
                ·
                  refine ⟨586148436720560879883589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 781531248960747839844785 586148436720560879883589)
                  ·
                    refine ⟨109902831885105164978173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 586148436720560879883589 109902831885105164978173)
                    ·
                      rfl

theorem cell23_642105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 3, 2, 4].length) (baseStart_642105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_642105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_642105 prefixEnd_642105 := by exact prefixLift 642105
  have htrace : WordTrace (prefixWord ++ tailWord_642105) baseStart_642105 baseEnd_642105 := by
    simpa [prefixWord, tailWord_642105, baseEnd_642105] using wordTrace_append hprefix tailTrace_642105
  have hstable : (prefixWord ++ tailWord_642105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642105).length < 2 ^ (prefixWord ++ tailWord_642105).sum := by decide
  have hdescent : baseEnd_642105 < baseStart_642105 := by decide
  rcases family_descends (prefixWord ++ tailWord_642105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642125 : List Nat := [1, 6, 1, 1, 1, 3, 1, 2, 1, 2, 4]
def baseStart_642125 : Nat := 118140960795 + 642125 * 2 ^ 59
def prefixEnd_642125 : Nat := 4983230072969 + 3 ^ 40 * 642125 * 2
def baseEnd_642125 : Nat := 329718765268405416684427

theorem tailTrace_642125 : CollatzResearch.WordTrace tailWord_642125 prefixEnd_642125 329718765268405416684427 := by
  unfold tailWord_642125
  simp only [CollatzResearch.WordTrace]
  refine ⟨23420222798698266064135829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15613481865798844042757219 23420222798698266064135829)
  ·
    refine ⟨1097822943688981221756367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 23420222798698266064135829 1097822943688981221756367)
    ·
      refine ⟨1646734415533471832634551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1097822943688981221756367 1646734415533471832634551)
      ·
        refine ⟨2470101623300207748951827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1646734415533471832634551 2470101623300207748951827)
        ·
          refine ⟨3705152434950311623427741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2470101623300207748951827 3705152434950311623427741)
          ·
            refine ⟨1389432163106366858785403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3705152434950311623427741 1389432163106366858785403)
            ·
              refine ⟨2084148244659550288178105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1389432163106366858785403 2084148244659550288178105)
              ·
                refine ⟨1563111183494662716133579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2084148244659550288178105 1563111183494662716133579)
                ·
                  refine ⟨2344666775241994074200369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1563111183494662716133579 2344666775241994074200369)
                  ·
                    refine ⟨1758500081431495555650277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2344666775241994074200369 1758500081431495555650277)
                    ·
                      refine ⟨329718765268405416684427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1758500081431495555650277 329718765268405416684427)
                      ·
                        rfl

theorem cell23_642125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_642125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_642125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_642125 prefixEnd_642125 := by exact prefixLift 642125
  have htrace : WordTrace (prefixWord ++ tailWord_642125) baseStart_642125 baseEnd_642125 := by
    simpa [prefixWord, tailWord_642125, baseEnd_642125] using wordTrace_append hprefix tailTrace_642125
  have hstable : (prefixWord ++ tailWord_642125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642125).length < 2 ^ (prefixWord ++ tailWord_642125).sum := by decide
  have hdescent : baseEnd_642125 < baseStart_642125 := by decide
  rcases family_descends (prefixWord ++ tailWord_642125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642128 : List Nat := [2, 1, 1, 1, 1, 3, 1, 3, 6, 1, 3]
def baseStart_642128 : Nat := 118140960795 + 642128 * 2 ^ 59
def prefixEnd_642128 : Nat := 4983230072969 + 3 ^ 40 * 642128 * 2
def baseEnd_642128 : Nat := 329720305710368904946913

theorem tailTrace_642128 : CollatzResearch.WordTrace tailWord_642128 prefixEnd_642128 329720305710368904946913 := by
  unfold tailWord_642128
  simp only [CollatzResearch.WordTrace]
  refine ⟨11710166108843698788247519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15613554811791598384330025 11710166108843698788247519)
  ·
    refine ⟨17565249163265548182371279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11710166108843698788247519 17565249163265548182371279)
    ·
      refine ⟨26347873744898322273556919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17565249163265548182371279 26347873744898322273556919)
      ·
        refine ⟨39521810617347483410335379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26347873744898322273556919 39521810617347483410335379)
        ·
          refine ⟨59282715926021225115503069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39521810617347483410335379 59282715926021225115503069)
          ·
            refine ⟨22231018472257959418313651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59282715926021225115503069 22231018472257959418313651)
            ·
              refine ⟨33346527708386939127470477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22231018472257959418313651 33346527708386939127470477)
              ·
                refine ⟨12504947890645102172801429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33346527708386939127470477 12504947890645102172801429)
                ·
                  refine ⟨586169432373989164350067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 12504947890645102172801429 586169432373989164350067)
                  ·
                    refine ⟨879254148560983746525101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 586169432373989164350067 879254148560983746525101)
                    ·
                      refine ⟨329720305710368904946913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 879254148560983746525101 329720305710368904946913)
                      ·
                        rfl

theorem cell23_642128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 6, 1, 3].length) (baseStart_642128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_642128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_642128 prefixEnd_642128 := by exact prefixLift 642128
  have htrace : WordTrace (prefixWord ++ tailWord_642128) baseStart_642128 baseEnd_642128 := by
    simpa [prefixWord, tailWord_642128, baseEnd_642128] using wordTrace_append hprefix tailTrace_642128
  have hstable : (prefixWord ++ tailWord_642128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642128).length < 2 ^ (prefixWord ++ tailWord_642128).sum := by decide
  have hdescent : baseEnd_642128 < baseStart_642128 := by decide
  rcases family_descends (prefixWord ++ tailWord_642128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642145 : List Nat := [1, 2, 3, 1, 1, 2, 3, 4, 2, 1, 3]
def baseStart_642145 : Nat := 118140960795 + 642145 * 2 ^ 59
def prefixEnd_642145 : Nat := 4983230072969 + 3 ^ 40 * 642145 * 2
def baseEnd_642145 : Nat := 329729034881495338434335

theorem tailTrace_642145 : CollatzResearch.WordTrace tailWord_642145 prefixEnd_642145 329729034881495338434335 := by
  unfold tailWord_642145
  simp only [CollatzResearch.WordTrace]
  refine ⟨23420952258625809479863889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15613968172417206319909259 23420952258625809479863889)
  ·
    refine ⟨17565714193969357109897917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23420952258625809479863889 17565714193969357109897917)
    ·
      refine ⟨6587142822738508916211719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17565714193969357109897917 6587142822738508916211719)
      ·
        refine ⟨9880714234107763374317579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6587142822738508916211719 9880714234107763374317579)
        ·
          refine ⟨14821071351161645061476369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9880714234107763374317579 14821071351161645061476369)
          ·
            refine ⟨11115803513371233796107277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14821071351161645061476369 11115803513371233796107277)
            ·
              refine ⟨4168426317514212673540229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11115803513371233796107277 4168426317514212673540229)
              ·
                refine ⟨781579934533914876288793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4168426317514212673540229 781579934533914876288793)
                ·
                  refine ⟨586184950900436157216595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 781579934533914876288793 586184950900436157216595)
                  ·
                    refine ⟨879277426350654235824893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 586184950900436157216595 879277426350654235824893)
                    ·
                      refine ⟨329729034881495338434335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 879277426350654235824893 329729034881495338434335)
                      ·
                        rfl

theorem cell23_642145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 4, 2, 1, 3].length) (baseStart_642145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_642145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_642145 prefixEnd_642145 := by exact prefixLift 642145
  have htrace : WordTrace (prefixWord ++ tailWord_642145) baseStart_642145 baseEnd_642145 := by
    simpa [prefixWord, tailWord_642145, baseEnd_642145] using wordTrace_append hprefix tailTrace_642145
  have hstable : (prefixWord ++ tailWord_642145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642145).length < 2 ^ (prefixWord ++ tailWord_642145).sum := by decide
  have hdescent : baseEnd_642145 < baseStart_642145 := by decide
  rcases family_descends (prefixWord ++ tailWord_642145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642146 : List Nat := [3, 3, 2, 2, 1, 2, 1, 4, 1, 2, 2]
def baseStart_642146 : Nat := 118140960795 + 642146 * 2 ^ 59
def prefixEnd_642146 : Nat := 4983230072969 + 3 ^ 40 * 642146 * 2
def baseEnd_642146 : Nat := 329729548362149834521831

theorem tailTrace_642146 : CollatzResearch.WordTrace tailWord_642146 prefixEnd_642146 329729548362149834521831 := by
  unfold tailWord_642146
  simp only [CollatzResearch.WordTrace]
  refine ⟨5855247182905546662662573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15613992487748124433766861 5855247182905546662662573)
  ·
    refine ⟨2195717693589579998498465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5855247182905546662662573 2195717693589579998498465)
    ·
      refine ⟨1646788270192184998873849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2195717693589579998498465 1646788270192184998873849)
      ·
        refine ⟨1235091202644138749155387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1646788270192184998873849 1235091202644138749155387)
        ·
          refine ⟨1852636803966208123733081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1235091202644138749155387 1852636803966208123733081)
          ·
            refine ⟨1389477602974656092799811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1852636803966208123733081 1389477602974656092799811)
            ·
              refine ⟨2084216404461984139199717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1389477602974656092799811 2084216404461984139199717)
              ·
                refine ⟨390790575836622026099947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2084216404461984139199717 390790575836622026099947)
                ·
                  refine ⟨586185863754933039149921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 390790575836622026099947 586185863754933039149921)
                  ·
                    refine ⟨439639397816199779362441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 586185863754933039149921 439639397816199779362441)
                    ·
                      refine ⟨329729548362149834521831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 439639397816199779362441 329729548362149834521831)
                      ·
                        rfl

theorem cell23_642146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_642146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_642146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_642146 prefixEnd_642146 := by exact prefixLift 642146
  have htrace : WordTrace (prefixWord ++ tailWord_642146) baseStart_642146 baseEnd_642146 := by
    simpa [prefixWord, tailWord_642146, baseEnd_642146] using wordTrace_append hprefix tailTrace_642146
  have hstable : (prefixWord ++ tailWord_642146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642146).length < 2 ^ (prefixWord ++ tailWord_642146).sum := by decide
  have hdescent : baseEnd_642146 < baseStart_642146 := by decide
  rcases family_descends (prefixWord ++ tailWord_642146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642152 : List Nat := [2, 1, 4, 4, 2, 1, 1, 8]
def baseStart_642152 : Nat := 118140960795 + 642152 * 2 ^ 59
def prefixEnd_642152 : Nat := 4983230072969 + 3 ^ 40 * 642152 * 2
def baseEnd_642152 : Nat := 12212319601706548557289

theorem tailTrace_642152 : CollatzResearch.WordTrace tailWord_642152 prefixEnd_642152 12212319601706548557289 := by
  unfold tailWord_642152
  simp only [CollatzResearch.WordTrace]
  refine ⟨11710603784800224837684355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15614138379733633116912473 11710603784800224837684355)
  ·
    refine ⟨17565905677200337256526533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11710603784800224837684355 17565905677200337256526533)
    ·
      refine ⟨3293607314475063235598725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17565905677200337256526533 3293607314475063235598725)
      ·
        refine ⟨617551371464074356674761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3293607314475063235598725 617551371464074356674761)
        ·
          refine ⟨463163528598055767506071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 617551371464074356674761 463163528598055767506071)
          ·
            refine ⟨694745292897083651259107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 463163528598055767506071 694745292897083651259107)
            ·
              refine ⟨1042117939345625476888661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 694745292897083651259107 1042117939345625476888661)
              ·
                refine ⟨12212319601706548557289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1042117939345625476888661 12212319601706548557289)
                ·
                  rfl

theorem cell23_642152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 8].length) (baseStart_642152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_642152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_642152 prefixEnd_642152 := by exact prefixLift 642152
  have htrace : WordTrace (prefixWord ++ tailWord_642152) baseStart_642152 baseEnd_642152 := by
    simpa [prefixWord, tailWord_642152, baseEnd_642152] using wordTrace_append hprefix tailTrace_642152
  have hstable : (prefixWord ++ tailWord_642152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642152).length < 2 ^ (prefixWord ++ tailWord_642152).sum := by decide
  have hdescent : baseEnd_642152 < baseStart_642152 := by decide
  rcases family_descends (prefixWord ++ tailWord_642152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642171 : List Nat := [1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 5]
def baseStart_642171 : Nat := 118140960795 + 642171 * 2 ^ 59
def prefixEnd_642171 : Nat := 4983230072969 + 3 ^ 40 * 642171 * 2
def baseEnd_642171 : Nat := 329742385378512236709215

theorem tailTrace_642171 : CollatzResearch.WordTrace tailWord_642171 prefixEnd_642171 329742385378512236709215 := by
  unfold tailWord_642171
  simp only [CollatzResearch.WordTrace]
  refine ⟨23421900556531615920310367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15614600371021077280206911 23421900556531615920310367)
  ·
    refine ⟨35132850834797423880465551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23421900556531615920310367 35132850834797423880465551)
    ·
      refine ⟨52699276252196135820698327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35132850834797423880465551 52699276252196135820698327)
      ·
        refine ⟨79048914378294203731047491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52699276252196135820698327 79048914378294203731047491)
        ·
          refine ⟨118573371567441305596571237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79048914378294203731047491 118573371567441305596571237)
          ·
            refine ⟨22232507168895244799357107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118573371567441305596571237 22232507168895244799357107)
            ·
              refine ⟨33348760753342867199035661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22232507168895244799357107 33348760753342867199035661)
              ·
                refine ⟨12505785282503575199638373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33348760753342867199035661 12505785282503575199638373)
                ·
                  refine ⟨2344834740469420349932195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12505785282503575199638373 2344834740469420349932195)
                  ·
                    refine ⟨3517252110704130524898293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2344834740469420349932195 3517252110704130524898293)
                    ·
                      refine ⟨329742385378512236709215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3517252110704130524898293 329742385378512236709215)
                      ·
                        rfl

theorem cell23_642171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 5].length) (baseStart_642171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_642171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_642171 prefixEnd_642171 := by exact prefixLift 642171
  have htrace : WordTrace (prefixWord ++ tailWord_642171) baseStart_642171 baseEnd_642171 := by
    simpa [prefixWord, tailWord_642171, baseEnd_642171] using wordTrace_append hprefix tailTrace_642171
  have hstable : (prefixWord ++ tailWord_642171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642171).length < 2 ^ (prefixWord ++ tailWord_642171).sum := by decide
  have hdescent : baseEnd_642171 < baseStart_642171 := by decide
  rcases family_descends (prefixWord ++ tailWord_642171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642185 : List Nat := [1, 2, 1, 1, 4, 3, 2, 2, 1, 4, 2]
def baseStart_642185 : Nat := 118140960795 + 642185 * 2 ^ 59
def prefixEnd_642185 : Nat := 4983230072969 + 3 ^ 40 * 642185 * 2
def baseEnd_642185 : Nat := 329749574107675181934151

theorem tailTrace_642185 : CollatzResearch.WordTrace tailWord_642185 prefixEnd_642185 329749574107675181934151 := by
  unfold tailWord_642185
  simp only [CollatzResearch.WordTrace]
  refine ⟨23422411178480896311320009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15614940785653930874213339 23422411178480896311320009)
  ·
    refine ⟨17566808383860672233490007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23422411178480896311320009 17566808383860672233490007)
    ·
      refine ⟨26350212575791008350235011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17566808383860672233490007 26350212575791008350235011)
      ·
        refine ⟨39525318863686512525352517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26350212575791008350235011 39525318863686512525352517)
        ·
          refine ⟨7410997286941221098503597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39525318863686512525352517 7410997286941221098503597)
          ·
            refine ⟨2779123982602957911938849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7410997286941221098503597 2779123982602957911938849)
            ·
              refine ⟨2084342986952218433954137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2779123982602957911938849 2084342986952218433954137)
              ·
                refine ⟨1563257240214163825465603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2084342986952218433954137 1563257240214163825465603)
                ·
                  refine ⟨2344885860321245738198405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1563257240214163825465603 2344885860321245738198405)
                  ·
                    refine ⟨439666098810233575912201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2344885860321245738198405 439666098810233575912201)
                    ·
                      refine ⟨329749574107675181934151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 439666098810233575912201 329749574107675181934151)
                      ·
                        rfl

theorem cell23_642185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 4, 2].length) (baseStart_642185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_642185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_642185 prefixEnd_642185 := by exact prefixLift 642185
  have htrace : WordTrace (prefixWord ++ tailWord_642185) baseStart_642185 baseEnd_642185 := by
    simpa [prefixWord, tailWord_642185, baseEnd_642185] using wordTrace_append hprefix tailTrace_642185
  have hstable : (prefixWord ++ tailWord_642185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642185).length < 2 ^ (prefixWord ++ tailWord_642185).sum := by decide
  have hdescent : baseEnd_642185 < baseStart_642185 := by decide
  rcases family_descends (prefixWord ++ tailWord_642185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642208 : List Nat := [2, 1, 1, 4, 2, 1, 4, 1, 7]
def baseStart_642208 : Nat := 118140960795 + 642208 * 2 ^ 59
def prefixEnd_642208 : Nat := 4983230072969 + 3 ^ 40 * 642208 * 2
def baseEnd_642208 : Nat := 36640153795858732438505

theorem tailTrace_642208 : CollatzResearch.WordTrace tailWord_642208 prefixEnd_642208 36640153795858732438505 := by
  unfold tailWord_642208
  simp only [CollatzResearch.WordTrace]
  refine ⟨11711625028698785619703639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15615500038265047492938185 11711625028698785619703639)
  ·
    refine ⟨17567437543048178429555459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11711625028698785619703639 17567437543048178429555459)
    ·
      refine ⟨26351156314572267644333189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17567437543048178429555459 26351156314572267644333189)
      ·
        refine ⟨4940841808982300183312473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26351156314572267644333189 4940841808982300183312473)
        ·
          refine ⟨3705631356736725137484355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4940841808982300183312473 3705631356736725137484355)
          ·
            refine ⟨5558447035105087706226533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3705631356736725137484355 5558447035105087706226533)
            ·
              refine ⟨1042208819082203944917475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5558447035105087706226533 1042208819082203944917475)
              ·
                refine ⟨1563313228623305917376213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1042208819082203944917475 1563313228623305917376213)
                ·
                  refine ⟨36640153795858732438505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1563313228623305917376213 36640153795858732438505)
                  ·
                    rfl

theorem cell23_642208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 7].length) (baseStart_642208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_642208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_642208 prefixEnd_642208 := by exact prefixLift 642208
  have htrace : WordTrace (prefixWord ++ tailWord_642208) baseStart_642208 baseEnd_642208 := by
    simpa [prefixWord, tailWord_642208, baseEnd_642208] using wordTrace_append hprefix tailTrace_642208
  have hstable : (prefixWord ++ tailWord_642208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642208).length < 2 ^ (prefixWord ++ tailWord_642208).sum := by decide
  have hdescent : baseEnd_642208 < baseStart_642208 := by decide
  rcases family_descends (prefixWord ++ tailWord_642208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642215 : List Nat := [1, 1, 6, 2, 1, 1, 2, 1, 2, 2, 4]
def baseStart_642215 : Nat := 118140960795 + 642215 * 2 ^ 59
def prefixEnd_642215 : Nat := 4983230072969 + 3 ^ 40 * 642215 * 2
def baseEnd_642215 : Nat := 329764978527310064559013

theorem tailTrace_642215 : CollatzResearch.WordTrace tailWord_642215 prefixEnd_642215 329764978527310064559013 := by
  unfold tailWord_642215
  simp only [CollatzResearch.WordTrace]
  refine ⟨23423505368372211434912099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15615670245581474289941399 23423505368372211434912099)
  ·
    refine ⟨35135258052558317152368149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23423505368372211434912099 35135258052558317152368149)
    ·
      refine ⟨1646965221213671116517257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 35135258052558317152368149 1646965221213671116517257)
      ·
        refine ⟨1235223915910253337387943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1646965221213671116517257 1235223915910253337387943)
        ·
          refine ⟨1852835873865380006081915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1235223915910253337387943 1852835873865380006081915)
          ·
            refine ⟨2779253810798070009122873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1852835873865380006081915 2779253810798070009122873)
            ·
              refine ⟨2084440358098552506842155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2779253810798070009122873 2084440358098552506842155)
              ·
                refine ⟨3126660537147828760263233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2084440358098552506842155 3126660537147828760263233)
                ·
                  refine ⟨2344995402860871570197425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3126660537147828760263233 2344995402860871570197425)
                  ·
                    refine ⟨1758746552145653677648069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2344995402860871570197425 1758746552145653677648069)
                    ·
                      refine ⟨329764978527310064559013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1758746552145653677648069 329764978527310064559013)
                      ·
                        rfl

theorem cell23_642215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_642215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_642215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_642215 prefixEnd_642215 := by exact prefixLift 642215
  have htrace : WordTrace (prefixWord ++ tailWord_642215) baseStart_642215 baseEnd_642215 := by
    simpa [prefixWord, tailWord_642215, baseEnd_642215] using wordTrace_append hprefix tailTrace_642215
  have hstable : (prefixWord ++ tailWord_642215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642215).length < 2 ^ (prefixWord ++ tailWord_642215).sum := by decide
  have hdescent : baseEnd_642215 < baseStart_642215 := by decide
  rcases family_descends (prefixWord ++ tailWord_642215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642315 : List Nat := [1, 1, 1, 1, 5, 4, 2, 2, 6]
def baseStart_642315 : Nat := 118140960795 + 642315 * 2 ^ 59
def prefixEnd_642315 : Nat := 4983230072969 + 3 ^ 40 * 642315 * 2
def baseEnd_642315 : Nat := 36646258510306630367617

theorem tailTrace_642315 : CollatzResearch.WordTrace tailWord_642315 prefixEnd_642315 36646258510306630367617 := by
  unfold tailWord_642315
  simp only [CollatzResearch.WordTrace]
  refine ⟨23427152668009928513552399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15618101778673285675701599 23427152668009928513552399)
  ·
    refine ⟨35140729002014892770328599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23427152668009928513552399 35140729002014892770328599)
    ·
      refine ⟨52711093503022339155492899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35140729002014892770328599 52711093503022339155492899)
      ·
        refine ⟨79066640254533508733239349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52711093503022339155492899 79066640254533508733239349)
        ·
          refine ⟨7412497523862516443741189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 79066640254533508733239349 7412497523862516443741189)
          ·
            refine ⟨1389843285724221833201473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7412497523862516443741189 1389843285724221833201473)
            ·
              refine ⟨1042382464293166374901105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1389843285724221833201473 1042382464293166374901105)
              ·
                refine ⟨781786848219874781175829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1042382464293166374901105 781786848219874781175829)
                ·
                  refine ⟨36646258510306630367617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 781786848219874781175829 36646258510306630367617)
                  ·
                    rfl

theorem cell23_642315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 2, 6].length) (baseStart_642315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_642315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_642315 prefixEnd_642315 := by exact prefixLift 642315
  have htrace : WordTrace (prefixWord ++ tailWord_642315) baseStart_642315 baseEnd_642315 := by
    simpa [prefixWord, tailWord_642315, baseEnd_642315] using wordTrace_append hprefix tailTrace_642315
  have hstable : (prefixWord ++ tailWord_642315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642315).length < 2 ^ (prefixWord ++ tailWord_642315).sum := by decide
  have hdescent : baseEnd_642315 < baseStart_642315 := by decide
  rcases family_descends (prefixWord ++ tailWord_642315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642385 : List Nat := [1, 2, 2, 1, 4, 1, 3, 2, 1, 1, 5]
def baseStart_642385 : Nat := 118140960795 + 642385 * 2 ^ 59
def prefixEnd_642385 : Nat := 4983230072969 + 3 ^ 40 * 642385 * 2
def baseEnd_642385 : Nat := 329852270238574399433231

theorem tailTrace_642385 : CollatzResearch.WordTrace tailWord_642385 prefixEnd_642385 329852270238574399433231 := by
  unfold tailWord_642385
  simp only [CollatzResearch.WordTrace]
  refine ⟨23429705777756330468600609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15619803851837553645733739 23429705777756330468600609)
  ·
    refine ⟨17572279333317247851450457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23429705777756330468600609 17572279333317247851450457)
    ·
      refine ⟨13179209499987935888587843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17572279333317247851450457 13179209499987935888587843)
      ·
        refine ⟨19768814249981903832881765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13179209499987935888587843 19768814249981903832881765)
        ·
          refine ⟨3706652671871606968665331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19768814249981903832881765 3706652671871606968665331)
          ·
            refine ⟨5559979007807410452997997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3706652671871606968665331 5559979007807410452997997)
            ·
              refine ⟨2084992127927778919874249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5559979007807410452997997 2084992127927778919874249)
              ·
                refine ⟨1563744095945834189905687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2084992127927778919874249 1563744095945834189905687)
                ·
                  refine ⟨2345616143918751284858531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1563744095945834189905687 2345616143918751284858531)
                  ·
                    refine ⟨3518424215878126927287797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2345616143918751284858531 3518424215878126927287797)
                    ·
                      refine ⟨329852270238574399433231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3518424215878126927287797 329852270238574399433231)
                      ·
                        rfl

theorem cell23_642385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 1, 5].length) (baseStart_642385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_642385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_642385 prefixEnd_642385 := by exact prefixLift 642385
  have htrace : WordTrace (prefixWord ++ tailWord_642385) baseStart_642385 baseEnd_642385 := by
    simpa [prefixWord, tailWord_642385, baseEnd_642385] using wordTrace_append hprefix tailTrace_642385
  have hstable : (prefixWord ++ tailWord_642385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642385).length < 2 ^ (prefixWord ++ tailWord_642385).sum := by decide
  have hdescent : baseEnd_642385 < baseStart_642385 := by decide
  rcases family_descends (prefixWord ++ tailWord_642385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642410 : List Nat := [3, 1, 3, 3, 3, 1, 1, 3, 1, 1, 3]
def baseStart_642410 : Nat := 118140960795 + 642410 * 2 ^ 59
def prefixEnd_642410 : Nat := 4983230072969 + 3 ^ 40 * 642410 * 2
def baseEnd_642410 : Nat := 329865107254936801620617

theorem tailTrace_642410 : CollatzResearch.WordTrace tailWord_642410 prefixEnd_642410 329865107254936801620617 := by
  unfold tailWord_642410
  simp only [CollatzResearch.WordTrace]
  refine ⟨5857654400666439934565171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15620411735110506492173789 5857654400666439934565171)
  ·
    refine ⟨8786481600999659901847757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5857654400666439934565171 8786481600999659901847757)
    ·
      refine ⟨3294930600374872463192909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8786481600999659901847757 3294930600374872463192909)
      ·
        refine ⟨1235598975140577173697341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3294930600374872463192909 1235598975140577173697341)
        ·
          refine ⟨463349615677716440136503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1235598975140577173697341 463349615677716440136503)
          ·
            refine ⟨695024423516574660204755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 463349615677716440136503 695024423516574660204755)
            ·
              refine ⟨1042536635274861990307133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 695024423516574660204755 1042536635274861990307133)
              ·
                refine ⟨390951238228073246365175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1042536635274861990307133 390951238228073246365175)
                ·
                  refine ⟨586426857342109869547763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 390951238228073246365175 586426857342109869547763)
                  ·
                    refine ⟨879640286013164804321645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 586426857342109869547763 879640286013164804321645)
                    ·
                      refine ⟨329865107254936801620617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 879640286013164804321645 329865107254936801620617)
                      ·
                        rfl

theorem cell23_642410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_642410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_642410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_642410 prefixEnd_642410 := by exact prefixLift 642410
  have htrace : WordTrace (prefixWord ++ tailWord_642410) baseStart_642410 baseEnd_642410 := by
    simpa [prefixWord, tailWord_642410, baseEnd_642410] using wordTrace_append hprefix tailTrace_642410
  have hstable : (prefixWord ++ tailWord_642410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642410).length < 2 ^ (prefixWord ++ tailWord_642410).sum := by decide
  have hdescent : baseEnd_642410 < baseStart_642410 := by decide
  rcases family_descends (prefixWord ++ tailWord_642410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642415 : List Nat := [1, 1, 2, 1, 3, 1, 4, 1, 3, 3, 3]
def baseStart_642415 : Nat := 118140960795 + 642415 * 2 ^ 59
def prefixEnd_642415 : Nat := 4983230072969 + 3 ^ 40 * 642415 * 2
def baseEnd_642415 : Nat := 329867674658209282058093

theorem tailTrace_642415 : CollatzResearch.WordTrace tailWord_642415 prefixEnd_642415 329867674658209282058093 := by
  unfold tailWord_642415
  simp only [CollatzResearch.WordTrace]
  refine ⟨23430799967647645592192699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15620533311765097061461799 23430799967647645592192699)
  ·
    refine ⟨35146199951471468388289049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23430799967647645592192699 35146199951471468388289049)
    ·
      refine ⟨26359649963603601291216787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35146199951471468388289049 26359649963603601291216787)
      ·
        refine ⟨39539474945405401936825181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26359649963603601291216787 39539474945405401936825181)
        ·
          refine ⟨14827303104527025726309443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39539474945405401936825181 14827303104527025726309443)
          ·
            refine ⟨22240954656790538589464165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14827303104527025726309443 22240954656790538589464165)
            ·
              refine ⟨4170178998148225985524531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22240954656790538589464165 4170178998148225985524531)
              ·
                refine ⟨6255268497222338978286797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4170178998148225985524531 6255268497222338978286797)
                ·
                  refine ⟨2345725686458377116857549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6255268497222338978286797 2345725686458377116857549)
                  ·
                    refine ⟨879647132421891418821581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2345725686458377116857549 879647132421891418821581)
                    ·
                      refine ⟨329867674658209282058093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 879647132421891418821581 329867674658209282058093)
                      ·
                        rfl

theorem cell23_642415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 3, 3].length) (baseStart_642415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_642415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_642415 prefixEnd_642415 := by exact prefixLift 642415
  have htrace : WordTrace (prefixWord ++ tailWord_642415) baseStart_642415 baseEnd_642415 := by
    simpa [prefixWord, tailWord_642415, baseEnd_642415] using wordTrace_append hprefix tailTrace_642415
  have hstable : (prefixWord ++ tailWord_642415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642415).length < 2 ^ (prefixWord ++ tailWord_642415).sum := by decide
  have hdescent : baseEnd_642415 < baseStart_642415 := by decide
  rcases family_descends (prefixWord ++ tailWord_642415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642433 : List Nat := [1, 2, 4, 3, 2, 2, 1, 1, 3, 2, 2]
def baseStart_642433 : Nat := 118140960795 + 642433 * 2 ^ 59
def prefixEnd_642433 : Nat := 4983230072969 + 3 ^ 40 * 642433 * 2
def baseEnd_642433 : Nat := 329876917309990211633011

theorem tailTrace_642433 : CollatzResearch.WordTrace tailWord_642433 prefixEnd_642433 329876917309990211633011 := by
  unfold tailWord_642433
  simp only [CollatzResearch.WordTrace]
  refine ⟨23431456481582434666347953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15620970987721623110898635 23431456481582434666347953)
  ·
    refine ⟨17573592361186825999760965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23431456481582434666347953 17573592361186825999760965)
    ·
      refine ⟨3295048567722529874955181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17573592361186825999760965 3295048567722529874955181)
      ·
        refine ⟨1235643212895948703108193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3295048567722529874955181 1235643212895948703108193)
        ·
          refine ⟨926732409671961527331145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1235643212895948703108193 926732409671961527331145)
          ·
            refine ⟨695049307253971145498359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 926732409671961527331145 695049307253971145498359)
            ·
              refine ⟨1042573960880956718247539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 695049307253971145498359 1042573960880956718247539)
              ·
                refine ⟨1563860941321435077371309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1042573960880956718247539 1563860941321435077371309)
                ·
                  refine ⟨586447852995538154014241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1563860941321435077371309 586447852995538154014241)
                  ·
                    refine ⟨439835889746653615510681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 586447852995538154014241 439835889746653615510681)
                    ·
                      refine ⟨329876917309990211633011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 439835889746653615510681 329876917309990211633011)
                      ·
                        rfl

theorem cell23_642433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_642433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_642433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_642433 prefixEnd_642433 := by exact prefixLift 642433
  have htrace : WordTrace (prefixWord ++ tailWord_642433) baseStart_642433 baseEnd_642433 := by
    simpa [prefixWord, tailWord_642433, baseEnd_642433] using wordTrace_append hprefix tailTrace_642433
  have hstable : (prefixWord ++ tailWord_642433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642433).length < 2 ^ (prefixWord ++ tailWord_642433).sum := by decide
  have hdescent : baseEnd_642433 < baseStart_642433 := by decide
  rcases family_descends (prefixWord ++ tailWord_642433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642506 : List Nat := [3, 1, 2, 1, 2, 3, 2, 3, 2, 2, 2]
def baseStart_642506 : Nat := 118140960795 + 642506 * 2 ^ 59
def prefixEnd_642506 : Nat := 4983230072969 + 3 ^ 40 * 642506 * 2
def baseEnd_642506 : Nat := 329914401397768426020175

theorem tailTrace_642506 : CollatzResearch.WordTrace tailWord_642506 prefixEnd_642506 329914401397768426020175 := by
  unfold tailWord_642506
  simp only [CollatzResearch.WordTrace]
  refine ⟨5858529752579492033438843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15622746006878645422503581 5858529752579492033438843)
  ·
    refine ⟨8787794628869238050158265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5858529752579492033438843 8787794628869238050158265)
    ·
      refine ⟨6590845971651928537618699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8787794628869238050158265 6590845971651928537618699)
      ·
        refine ⟨9886268957477892806428049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6590845971651928537618699 9886268957477892806428049)
        ·
          refine ⟨7414701718108419604821037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9886268957477892806428049 7414701718108419604821037)
          ·
            refine ⟨2780513144290657351807889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7414701718108419604821037 2780513144290657351807889)
            ·
              refine ⟨2085384858217993013855917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2780513144290657351807889 2085384858217993013855917)
              ·
                refine ⟨782019321831747380195969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2085384858217993013855917 782019321831747380195969)
                ·
                  refine ⟨586514491373810535146977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 782019321831747380195969 586514491373810535146977)
                  ·
                    refine ⟨439885868530357901360233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 586514491373810535146977 439885868530357901360233)
                    ·
                      refine ⟨329914401397768426020175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 439885868530357901360233 329914401397768426020175)
                      ·
                        rfl

theorem cell23_642506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 3, 2, 2, 2].length) (baseStart_642506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_642506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_642506 prefixEnd_642506 := by exact prefixLift 642506
  have htrace : WordTrace (prefixWord ++ tailWord_642506) baseStart_642506 baseEnd_642506 := by
    simpa [prefixWord, tailWord_642506, baseEnd_642506] using wordTrace_append hprefix tailTrace_642506
  have hstable : (prefixWord ++ tailWord_642506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642506).length < 2 ^ (prefixWord ++ tailWord_642506).sum := by decide
  have hdescent : baseEnd_642506 < baseStart_642506 := by decide
  rcases family_descends (prefixWord ++ tailWord_642506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642529 : List Nat := [1, 2, 3, 1, 2, 4, 2, 3, 5]
def baseStart_642529 : Nat := 118140960795 + 642529 * 2 ^ 59
def prefixEnd_642529 : Nat := 4983230072969 + 3 ^ 40 * 642529 * 2
def baseEnd_642529 : Nat := 36658467939202426225841

theorem tailTrace_642529 : CollatzResearch.WordTrace tailWord_642529 prefixEnd_642529 36658467939202426225841 := by
  unfold tailWord_642529
  simp only [CollatzResearch.WordTrace]
  refine ⟨23434957889234643061842641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15623305259489762041228427 23434957889234643061842641)
  ·
    refine ⟨17576218416925982296381981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23434957889234643061842641 17576218416925982296381981)
    ·
      refine ⟨6591081906347243361143243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17576218416925982296381981 6591081906347243361143243)
      ·
        refine ⟨9886622859520865041714865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6591081906347243361143243 9886622859520865041714865)
        ·
          refine ⟨7414967144640648781286149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9886622859520865041714865 7414967144640648781286149)
          ·
            refine ⟨1390306339620121646491153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7414967144640648781286149 1390306339620121646491153)
            ·
              refine ⟨1042729754715091234868365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1390306339620121646491153 1042729754715091234868365)
              ·
                refine ⟨391023658018159213075637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1042729754715091234868365 391023658018159213075637)
                ·
                  refine ⟨36658467939202426225841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 391023658018159213075637 36658467939202426225841)
                  ·
                    rfl

theorem cell23_642529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 3, 5].length) (baseStart_642529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_642529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_642529 prefixEnd_642529 := by exact prefixLift 642529
  have htrace : WordTrace (prefixWord ++ tailWord_642529) baseStart_642529 baseEnd_642529 := by
    simpa [prefixWord, tailWord_642529, baseEnd_642529] using wordTrace_append hprefix tailTrace_642529
  have hstable : (prefixWord ++ tailWord_642529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642529).length < 2 ^ (prefixWord ++ tailWord_642529).sum := by decide
  have hdescent : baseEnd_642529 < baseStart_642529 := by decide
  rcases family_descends (prefixWord ++ tailWord_642529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642542 : List Nat := [4, 1, 2, 1, 2, 1, 2, 1, 4, 5]
def baseStart_642542 : Nat := 118140960795 + 642542 * 2 ^ 59
def prefixEnd_642542 : Nat := 4983230072969 + 3 ^ 40 * 642542 * 2
def baseEnd_642542 : Nat := 109977628900443428390003

theorem tailTrace_642542 : CollatzResearch.WordTrace tailWord_642542 prefixEnd_642542 109977628900443428390003 := by
  unfold tailWord_642542
  simp only [CollatzResearch.WordTrace]
  refine ⟨2929429004773443285258235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15623621358791697521377253 2929429004773443285258235)
  ·
    refine ⟨4394143507160164927887353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2929429004773443285258235 4394143507160164927887353)
    ·
      refine ⟨3295607630370123695915515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4394143507160164927887353 3295607630370123695915515)
      ·
        refine ⟨4943411445555185543873273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3295607630370123695915515 4943411445555185543873273)
        ·
          refine ⟨3707558584166389157904955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4943411445555185543873273 3707558584166389157904955)
          ·
            refine ⟨5561337876249583736857433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3707558584166389157904955 5561337876249583736857433)
            ·
              refine ⟨4171003407187187802643075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5561337876249583736857433 4171003407187187802643075)
              ·
                refine ⟨6256505110780781703964613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4171003407187187802643075 6256505110780781703964613)
                ·
                  refine ⟨1173094708271396569493365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6256505110780781703964613 1173094708271396569493365)
                  ·
                    refine ⟨109977628900443428390003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1173094708271396569493365 109977628900443428390003)
                    ·
                      rfl

theorem cell23_642542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_642542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_642542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_642542 prefixEnd_642542 := by exact prefixLift 642542
  have htrace : WordTrace (prefixWord ++ tailWord_642542) baseStart_642542 baseEnd_642542 := by
    simpa [prefixWord, tailWord_642542, baseEnd_642542] using wordTrace_append hprefix tailTrace_642542
  have hstable : (prefixWord ++ tailWord_642542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642542).length < 2 ^ (prefixWord ++ tailWord_642542).sum := by decide
  have hdescent : baseEnd_642542 < baseStart_642542 := by decide
  rcases family_descends (prefixWord ++ tailWord_642542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642580 : List Nat := [2, 4, 3, 1, 3, 1, 1, 3, 5]
def baseStart_642580 : Nat := 118140960795 + 642580 * 2 ^ 59
def prefixEnd_642580 : Nat := 4983230072969 + 3 ^ 40 * 642580 * 2
def baseEnd_642580 : Nat := 36661377662911237388315

theorem tailTrace_642580 : CollatzResearch.WordTrace tailWord_642580 prefixEnd_642580 36661377662911237388315 := by
  unfold tailWord_642580
  simp only [CollatzResearch.WordTrace]
  refine ⟨11718409006024939385974597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15624545341366585847966129 11718409006024939385974597)
  ·
    refine ⟨2197201688629676134870237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11718409006024939385974597 2197201688629676134870237)
    ·
      refine ⟨823950633236128550576339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2197201688629676134870237 823950633236128550576339)
      ·
        refine ⟨1235925949854192825864509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 823950633236128550576339 1235925949854192825864509)
        ·
          refine ⟨463472231195322309699191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1235925949854192825864509 463472231195322309699191)
          ·
            refine ⟨695208346792983464548787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 463472231195322309699191 695208346792983464548787)
            ·
              refine ⟨1042812520189475196823181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 695208346792983464548787 1042812520189475196823181)
              ·
                refine ⟨391054695071053198808693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1042812520189475196823181 391054695071053198808693)
                ·
                  refine ⟨36661377662911237388315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 391054695071053198808693 36661377662911237388315)
                  ·
                    rfl

theorem cell23_642580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 3, 5].length) (baseStart_642580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_642580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_642580 prefixEnd_642580 := by exact prefixLift 642580
  have htrace : WordTrace (prefixWord ++ tailWord_642580) baseStart_642580 baseEnd_642580 := by
    simpa [prefixWord, tailWord_642580, baseEnd_642580] using wordTrace_append hprefix tailTrace_642580
  have hstable : (prefixWord ++ tailWord_642580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642580).length < 2 ^ (prefixWord ++ tailWord_642580).sum := by decide
  have hdescent : baseEnd_642580 < baseStart_642580 := by decide
  rcases family_descends (prefixWord ++ tailWord_642580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642602 : List Nat := [3, 1, 4, 1, 1, 1, 1, 3, 8]
def baseStart_642602 : Nat := 118140960795 + 642602 * 2 ^ 59
def prefixEnd_642602 : Nat := 4983230072969 + 3 ^ 40 * 642602 * 2
def baseEnd_642602 : Nat := 36662632837844450046637

theorem tailTrace_642602 : CollatzResearch.WordTrace tailWord_642602 prefixEnd_642602 36662632837844450046637 := by
  unfold tailWord_642602
  simp only [CollatzResearch.WordTrace]
  refine ⟨5859405104492544132312515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15625080278646784352833373 5859405104492544132312515)
  ·
    refine ⟨8789107656738816198468773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5859405104492544132312515 8789107656738816198468773)
    ·
      refine ⟨1647957685638528037212895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8789107656738816198468773 1647957685638528037212895)
      ·
        refine ⟨2471936528457792055819343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1647957685638528037212895 2471936528457792055819343)
        ·
          refine ⟨3707904792686688083729015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2471936528457792055819343 3707904792686688083729015)
          ·
            refine ⟨5561857189030032125593523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3707904792686688083729015 5561857189030032125593523)
            ·
              refine ⟨8342785783545048188390285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5561857189030032125593523 8342785783545048188390285)
              ·
                refine ⟨3128544668829393070646357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8342785783545048188390285 3128544668829393070646357)
                ·
                  refine ⟨36662632837844450046637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3128544668829393070646357 36662632837844450046637)
                  ·
                    rfl

theorem cell23_642602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 8].length) (baseStart_642602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_642602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_642602 prefixEnd_642602 := by exact prefixLift 642602
  have htrace : WordTrace (prefixWord ++ tailWord_642602) baseStart_642602 baseEnd_642602 := by
    simpa [prefixWord, tailWord_642602, baseEnd_642602] using wordTrace_append hprefix tailTrace_642602
  have hstable : (prefixWord ++ tailWord_642602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642602).length < 2 ^ (prefixWord ++ tailWord_642602).sum := by decide
  have hdescent : baseEnd_642602 < baseStart_642602 := by decide
  rcases family_descends (prefixWord ++ tailWord_642602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642606 : List Nat := [4, 1, 3, 1, 2, 1, 3, 1, 3, 4]
def baseStart_642606 : Nat := 118140960795 + 642606 * 2 ^ 59
def prefixEnd_642606 : Nat := 4983230072969 + 3 ^ 40 * 642606 * 2
def baseEnd_642606 : Nat := 109988583154406011589905

theorem tailTrace_642606 : CollatzResearch.WordTrace tailWord_642606 prefixEnd_642606 109988583154406011589905 := by
  unfold tailWord_642606
  simp only [CollatzResearch.WordTrace]
  refine ⟨2929720788744460651549459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15625177539970456808263781 2929720788744460651549459)
  ·
    refine ⟨4394581183116690977324189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2929720788744460651549459 4394581183116690977324189)
    ·
      refine ⟨1647967943668759116496571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4394581183116690977324189 1647967943668759116496571)
      ·
        refine ⟨2471951915503138674744857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1647967943668759116496571 2471951915503138674744857)
        ·
          refine ⟨1853963936627354006058643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2471951915503138674744857 1853963936627354006058643)
          ·
            refine ⟨2780945904941031009087965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1853963936627354006058643 2780945904941031009087965)
            ·
              refine ⟨1042854714352886628407987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2780945904941031009087965 1042854714352886628407987)
              ·
                refine ⟨1564282071529329942611981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1042854714352886628407987 1564282071529329942611981)
                ·
                  refine ⟨586605776823498728479493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1564282071529329942611981 586605776823498728479493)
                  ·
                    refine ⟨109988583154406011589905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 586605776823498728479493 109988583154406011589905)
                    ·
                      rfl

theorem cell23_642606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_642606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_642606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_642606 prefixEnd_642606 := by exact prefixLift 642606
  have htrace : WordTrace (prefixWord ++ tailWord_642606) baseStart_642606 baseEnd_642606 := by
    simpa [prefixWord, tailWord_642606, baseEnd_642606] using wordTrace_append hprefix tailTrace_642606
  have hstable : (prefixWord ++ tailWord_642606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642606).length < 2 ^ (prefixWord ++ tailWord_642606).sum := by decide
  have hdescent : baseEnd_642606 < baseStart_642606 := by decide
  rcases family_descends (prefixWord ++ tailWord_642606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642629 : List Nat := [1, 3, 1, 1, 1, 4, 2, 1, 5, 1, 3]
def baseStart_642629 : Nat := 118140960795 + 642629 * 2 ^ 59
def prefixEnd_642629 : Nat := 4983230072969 + 3 ^ 40 * 642629 * 2
def baseEnd_642629 : Nat := 329977559518271444782109

theorem tailTrace_642629 : CollatzResearch.WordTrace tailWord_642629 prefixEnd_642629 329977559518271444782109 := by
  unfold tailWord_642629
  simp only [CollatzResearch.WordTrace]
  refine ⟨23438605188872360140482941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15625736792581573426988627 23438605188872360140482941)
  ·
    refine ⟨8789476945827135052681103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23438605188872360140482941 8789476945827135052681103)
    ·
      refine ⟨13184215418740702579021655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8789476945827135052681103 13184215418740702579021655)
      ·
        refine ⟨19776323128111053868532483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13184215418740702579021655 19776323128111053868532483)
        ·
          refine ⟨29664484692166580802798725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19776323128111053868532483 29664484692166580802798725)
          ·
            refine ⟨5562090879781233900524761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29664484692166580802798725 5562090879781233900524761)
            ·
              refine ⟨4171568159835925425393571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5562090879781233900524761 4171568159835925425393571)
              ·
                refine ⟨6257352239753888138090357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4171568159835925425393571 6257352239753888138090357)
                ·
                  refine ⟨586626772476927012945971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6257352239753888138090357 586626772476927012945971)
                  ·
                    refine ⟨879940158715390519418957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 586626772476927012945971 879940158715390519418957)
                    ·
                      refine ⟨329977559518271444782109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 879940158715390519418957 329977559518271444782109)
                      ·
                        rfl

theorem cell23_642629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 5, 1, 3].length) (baseStart_642629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_642629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_642629 prefixEnd_642629 := by exact prefixLift 642629
  have htrace : WordTrace (prefixWord ++ tailWord_642629) baseStart_642629 baseEnd_642629 := by
    simpa [prefixWord, tailWord_642629, baseEnd_642629] using wordTrace_append hprefix tailTrace_642629
  have hstable : (prefixWord ++ tailWord_642629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642629).length < 2 ^ (prefixWord ++ tailWord_642629).sum := by decide
  have hdescent : baseEnd_642629 < baseStart_642629 := by decide
  rcases family_descends (prefixWord ++ tailWord_642629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642653 : List Nat := [1, 4, 4, 2, 1, 1, 2, 2, 6]
def baseStart_642653 : Nat := 118140960795 + 642653 * 2 ^ 59
def prefixEnd_642653 : Nat := 4983230072969 + 3 ^ 40 * 642653 * 2
def baseEnd_642653 : Nat := 36665542561553261209111

theorem tailTrace_642653 : CollatzResearch.WordTrace tailWord_642653 prefixEnd_642653 36665542561553261209111 := by
  unfold tailWord_642653
  simp only [CollatzResearch.WordTrace]
  refine ⟨23439480540785412239356613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15626320360523608159571075 23439480540785412239356613)
  ·
    refine ⟨4394902601397264794879365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23439480540785412239356613 4394902601397264794879365)
    ·
      refine ⟨824044237761987149039881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4394902601397264794879365 824044237761987149039881)
      ·
        refine ⟨618033178321490361779911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 824044237761987149039881 618033178321490361779911)
        ·
          refine ⟨927049767482235542669867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 618033178321490361779911 927049767482235542669867)
          ·
            refine ⟨1390574651223353314004801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 927049767482235542669867 1390574651223353314004801)
            ·
              refine ⟨1042930988417514985503601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1390574651223353314004801 1042930988417514985503601)
              ·
                refine ⟨782198241313136239127701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1042930988417514985503601 782198241313136239127701)
                ·
                  refine ⟨36665542561553261209111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 782198241313136239127701 36665542561553261209111)
                  ·
                    rfl

theorem cell23_642653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 2, 6].length) (baseStart_642653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_642653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_642653 prefixEnd_642653 := by exact prefixLift 642653
  have htrace : WordTrace (prefixWord ++ tailWord_642653) baseStart_642653 baseEnd_642653 := by
    simpa [prefixWord, tailWord_642653, baseEnd_642653] using wordTrace_append hprefix tailTrace_642653
  have hstable : (prefixWord ++ tailWord_642653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642653).length < 2 ^ (prefixWord ++ tailWord_642653).sum := by decide
  have hdescent : baseEnd_642653 < baseStart_642653 := by decide
  rcases family_descends (prefixWord ++ tailWord_642653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642720 : List Nat := [2, 1, 1, 4, 3, 1, 2, 4, 1, 2, 2]
def baseStart_642720 : Nat := 118140960795 + 642720 * 2 ^ 59
def prefixEnd_642720 : Nat := 4983230072969 + 3 ^ 40 * 642720 * 2
def baseEnd_642720 : Nat := 330024286257830588744191

theorem tailTrace_642720 : CollatzResearch.WordTrace tailWord_642720 prefixEnd_642720 330024286257830588744191 := by
  unfold tailWord_642720
  simp only [CollatzResearch.WordTrace]
  refine ⟨11720962115771341341022807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15627949487695121788030409 11720962115771341341022807)
  ·
    refine ⟨17581443173657012011534211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11720962115771341341022807 17581443173657012011534211)
    ·
      refine ⟨26372164760485518017301317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17581443173657012011534211 26372164760485518017301317)
      ·
        refine ⟨4944780892591034628243997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26372164760485518017301317 4944780892591034628243997)
        ·
          refine ⟨1854292834721637985591499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4944780892591034628243997 1854292834721637985591499)
          ·
            refine ⟨2781439252082456978387249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1854292834721637985591499 2781439252082456978387249)
            ·
              refine ⟨2086079439061842733790437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2781439252082456978387249 2086079439061842733790437)
              ·
                refine ⟨391139894824095512585707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2086079439061842733790437 391139894824095512585707)
                ·
                  refine ⟨586709842236143268878561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 391139894824095512585707 586709842236143268878561)
                  ·
                    refine ⟨440032381677107451658921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 586709842236143268878561 440032381677107451658921)
                    ·
                      refine ⟨330024286257830588744191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 440032381677107451658921 330024286257830588744191)
                      ·
                        rfl

theorem cell23_642720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 4, 1, 2, 2].length) (baseStart_642720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_642720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_642720 prefixEnd_642720 := by exact prefixLift 642720
  have htrace : WordTrace (prefixWord ++ tailWord_642720) baseStart_642720 baseEnd_642720 := by
    simpa [prefixWord, tailWord_642720, baseEnd_642720] using wordTrace_append hprefix tailTrace_642720
  have hstable : (prefixWord ++ tailWord_642720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642720).length < 2 ^ (prefixWord ++ tailWord_642720).sum := by decide
  have hdescent : baseEnd_642720 < baseStart_642720 := by decide
  rcases family_descends (prefixWord ++ tailWord_642720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642732 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 5]
def baseStart_642732 : Nat := 118140960795 + 642732 * 2 ^ 59
def prefixEnd_642732 : Nat := 4983230072969 + 3 ^ 40 * 642732 * 2
def baseEnd_642732 : Nat := 330030448025684541794135

theorem tailTrace_642732 : CollatzResearch.WordTrace tailWord_642732 prefixEnd_642732 330030448025684541794135 := by
  unfold tailWord_642732
  simp only [CollatzResearch.WordTrace]
  refine ⟨11721180953749604365741225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15628241271666139154321633 11721180953749604365741225)
  ·
    refine ⟨8790885715312203274305919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11721180953749604365741225 8790885715312203274305919)
    ·
      refine ⟨13186328572968304911458879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8790885715312203274305919 13186328572968304911458879)
      ·
        refine ⟨19779492859452457367188319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13186328572968304911458879 19779492859452457367188319)
        ·
          refine ⟨29669239289178686050782479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19779492859452457367188319 29669239289178686050782479)
          ·
            refine ⟨44503858933768029076173719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29669239289178686050782479 44503858933768029076173719)
            ·
              refine ⟨66755788400652043614260579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44503858933768029076173719 66755788400652043614260579)
              ·
                refine ⟨100133682600978065421390869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66755788400652043614260579 100133682600978065421390869)
                ·
                  refine ⟨4693766371920846816627697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 100133682600978065421390869 4693766371920846816627697)
                  ·
                    refine ⟨3520324778940635112470773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4693766371920846816627697 3520324778940635112470773)
                    ·
                      refine ⟨330030448025684541794135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3520324778940635112470773 330030448025684541794135)
                      ·
                        rfl

theorem cell23_642732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 5].length) (baseStart_642732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_642732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_642732 prefixEnd_642732 := by exact prefixLift 642732
  have htrace : WordTrace (prefixWord ++ tailWord_642732) baseStart_642732 baseEnd_642732 := by
    simpa [prefixWord, tailWord_642732, baseEnd_642732] using wordTrace_append hprefix tailTrace_642732
  have hstable : (prefixWord ++ tailWord_642732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642732).length < 2 ^ (prefixWord ++ tailWord_642732).sum := by decide
  have hdescent : baseEnd_642732 < baseStart_642732 := by decide
  rcases family_descends (prefixWord ++ tailWord_642732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642736 : List Nat := [2, 1, 1, 1, 2, 1, 4, 5, 2, 1, 3]
def baseStart_642736 : Nat := 118140960795 + 642736 * 2 ^ 59
def prefixEnd_642736 : Nat := 4983230072969 + 3 ^ 40 * 642736 * 2
def baseEnd_642736 : Nat := 330032501948302526144117

theorem tailTrace_642736 : CollatzResearch.WordTrace tailWord_642736 prefixEnd_642736 330032501948302526144117 := by
  unfold tailWord_642736
  simp only [CollatzResearch.WordTrace]
  refine ⟨11721253899742358707314031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15628338532989811609752041 11721253899742358707314031)
  ·
    refine ⟨17581880849613538060971047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11721253899742358707314031 17581880849613538060971047)
    ·
      refine ⟨26372821274420307091456571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17581880849613538060971047 26372821274420307091456571)
      ·
        refine ⟨39559231911630460637184857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26372821274420307091456571 39559231911630460637184857)
        ·
          refine ⟨29669423933722845477888643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39559231911630460637184857 29669423933722845477888643)
          ·
            refine ⟨44504135900584268216832965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29669423933722845477888643 44504135900584268216832965)
            ·
              refine ⟨8344525481359550290656181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44504135900584268216832965 8344525481359550290656181)
              ·
                refine ⟨782299263877457839749017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8344525481359550290656181 782299263877457839749017)
                ·
                  refine ⟨586724447908093379811763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 782299263877457839749017 586724447908093379811763)
                  ·
                    refine ⟨880086671862140069717645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 586724447908093379811763 880086671862140069717645)
                    ·
                      refine ⟨330032501948302526144117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 880086671862140069717645 330032501948302526144117)
                      ·
                        rfl

theorem cell23_642736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 5, 2, 1, 3].length) (baseStart_642736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_642736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_642736 prefixEnd_642736 := by exact prefixLift 642736
  have htrace : WordTrace (prefixWord ++ tailWord_642736) baseStart_642736 baseEnd_642736 := by
    simpa [prefixWord, tailWord_642736, baseEnd_642736] using wordTrace_append hprefix tailTrace_642736
  have hstable : (prefixWord ++ tailWord_642736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642736).length < 2 ^ (prefixWord ++ tailWord_642736).sum := by decide
  have hdescent : baseEnd_642736 < baseStart_642736 := by decide
  rcases family_descends (prefixWord ++ tailWord_642736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642787 : List Nat := [1, 1, 1, 7, 2, 2, 2, 1, 2, 1, 3]
def baseStart_642787 : Nat := 118140960795 + 642787 * 2 ^ 59
def prefixEnd_642787 : Nat := 4983230072969 + 3 ^ 40 * 642787 * 2
def baseEnd_642787 : Nat := 330058689461681826606383

theorem tailTrace_642787 : CollatzResearch.WordTrace tailWord_642787 prefixEnd_642787 330058689461681826606383 := by
  unfold tailWord_642787
  simp only [CollatzResearch.WordTrace]
  refine ⟨23444367922299953124734615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15629578614866635416489743 23444367922299953124734615)
  ·
    refine ⟨35166551883449929687101923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23444367922299953124734615 35166551883449929687101923)
    ·
      refine ⟨52749827825174894530652885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35166551883449929687101923 52749827825174894530652885)
      ·
        refine ⟨1236324089652536590562177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 52749827825174894530652885 1236324089652536590562177)
        ·
          refine ⟨927243067239402442921633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1236324089652536590562177 927243067239402442921633)
          ·
            refine ⟨695432300429551832191225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 927243067239402442921633 695432300429551832191225)
            ·
              refine ⟨521574225322163874143419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 695432300429551832191225 521574225322163874143419)
              ·
                refine ⟨782361337983245811215129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 521574225322163874143419 782361337983245811215129)
                ·
                  refine ⟨586771003487434358411347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 782361337983245811215129 586771003487434358411347)
                  ·
                    refine ⟨880156505231151537617021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 586771003487434358411347 880156505231151537617021)
                    ·
                      refine ⟨330058689461681826606383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 880156505231151537617021 330058689461681826606383)
                      ·
                        rfl

theorem cell23_642787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_642787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_642787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_642787 prefixEnd_642787 := by exact prefixLift 642787
  have htrace : WordTrace (prefixWord ++ tailWord_642787) baseStart_642787 baseEnd_642787 := by
    simpa [prefixWord, tailWord_642787, baseEnd_642787] using wordTrace_append hprefix tailTrace_642787
  have hstable : (prefixWord ++ tailWord_642787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642787).length < 2 ^ (prefixWord ++ tailWord_642787).sum := by decide
  have hdescent : baseEnd_642787 < baseStart_642787 := by decide
  rcases family_descends (prefixWord ++ tailWord_642787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642789 : List Nat := [1, 3, 1, 4, 1, 1, 2, 1, 1, 4, 4]
def baseStart_642789 : Nat := 118140960795 + 642789 * 2 ^ 59
def prefixEnd_642789 : Nat := 4983230072969 + 3 ^ 40 * 642789 * 2
def baseEnd_642789 : Nat := 330059716422990818781373

theorem tailTrace_642789 : CollatzResearch.WordTrace tailWord_642789 prefixEnd_642789 330059716422990818781373 := by
  unfold tailWord_642789
  simp only [CollatzResearch.WordTrace]
  refine ⟨23444440868292707466307421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15629627245528471644204947 23444440868292707466307421)
  ·
    refine ⟨8791665325609765299865283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23444440868292707466307421 8791665325609765299865283)
    ·
      refine ⟨13187497988414647949797925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8791665325609765299865283 13187497988414647949797925)
      ·
        refine ⟨2472655872827746490587111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13187497988414647949797925 2472655872827746490587111)
        ·
          refine ⟨3708983809241619735880667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2472655872827746490587111 3708983809241619735880667)
          ·
            refine ⟨5563475713862429603821001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3708983809241619735880667 5563475713862429603821001)
            ·
              refine ⟨4172606785396822202865751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5563475713862429603821001 4172606785396822202865751)
              ·
                refine ⟨6258910178095233304298627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4172606785396822202865751 6258910178095233304298627)
                ·
                  refine ⟨9388365267142849956447941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6258910178095233304298627 9388365267142849956447941)
                  ·
                    refine ⟨1760318487589284366833989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9388365267142849956447941 1760318487589284366833989)
                    ·
                      refine ⟨330059716422990818781373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1760318487589284366833989 330059716422990818781373)
                      ·
                        rfl

theorem cell23_642789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_642789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_642789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_642789 prefixEnd_642789 := by exact prefixLift 642789
  have htrace : WordTrace (prefixWord ++ tailWord_642789) baseStart_642789 baseEnd_642789 := by
    simpa [prefixWord, tailWord_642789, baseEnd_642789] using wordTrace_append hprefix tailTrace_642789
  have hstable : (prefixWord ++ tailWord_642789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642789).length < 2 ^ (prefixWord ++ tailWord_642789).sum := by decide
  have hdescent : baseEnd_642789 < baseStart_642789 := by decide
  rcases family_descends (prefixWord ++ tailWord_642789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642809 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 6, 3, 3]
def baseStart_642809 : Nat := 118140960795 + 642809 * 2 ^ 59
def prefixEnd_642809 : Nat := 4983230072969 + 3 ^ 40 * 642809 * 2
def baseEnd_642809 : Nat := 330069986036080740531281

theorem tailTrace_642809 : CollatzResearch.WordTrace tailWord_642809 prefixEnd_642809 330069986036080740531281 := by
  unfold tailWord_642809
  simp only [CollatzResearch.WordTrace]
  refine ⟨23445170328220250882035481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15630113552146833921356987 23445170328220250882035481)
  ·
    refine ⟨17583877746165188161526611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23445170328220250882035481 17583877746165188161526611)
    ·
      refine ⟨26375816619247782242289917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17583877746165188161526611 26375816619247782242289917)
      ·
        refine ⟨9890931232217918340858719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26375816619247782242289917 9890931232217918340858719)
        ·
          refine ⟨14836396848326877511288079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9890931232217918340858719 14836396848326877511288079)
          ·
            refine ⟨22254595272490316266932119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14836396848326877511288079 22254595272490316266932119)
            ·
              refine ⟨33381892908735474400398179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22254595272490316266932119 33381892908735474400398179)
              ·
                refine ⟨50072839363103211600597269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33381892908735474400398179 50072839363103211600597269)
                ·
                  refine ⟨2347164345145463043777997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 50072839363103211600597269 2347164345145463043777997)
                  ·
                    refine ⟨880186629429548641416749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2347164345145463043777997 880186629429548641416749)
                    ·
                      refine ⟨330069986036080740531281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 880186629429548641416749 330069986036080740531281)
                      ·
                        rfl

theorem cell23_642809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 3, 3].length) (baseStart_642809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_642809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_642809 prefixEnd_642809 := by exact prefixLift 642809
  have htrace : WordTrace (prefixWord ++ tailWord_642809) baseStart_642809 baseEnd_642809 := by
    simpa [prefixWord, tailWord_642809, baseEnd_642809] using wordTrace_append hprefix tailTrace_642809
  have hstable : (prefixWord ++ tailWord_642809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642809).length < 2 ^ (prefixWord ++ tailWord_642809).sum := by decide
  have hdescent : baseEnd_642809 < baseStart_642809 := by decide
  rcases family_descends (prefixWord ++ tailWord_642809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642822 : List Nat := [6, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2]
def baseStart_642822 : Nat := 118140960795 + 642822 * 2 ^ 59
def prefixEnd_642822 : Nat := 4983230072969 + 3 ^ 40 * 642822 * 2
def baseEnd_642822 : Nat := 330076661284589189668723

theorem tailTrace_642822 : CollatzResearch.WordTrace tailWord_642822 prefixEnd_642822 330076661284589189668723 := by
  unfold tailWord_642822
  simp only [CollatzResearch.WordTrace]
  refine ⟨732676389911661065695585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15630429651448769401505813 732676389911661065695585)
  ·
    refine ⟨549507292433745799271689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 732676389911661065695585 549507292433745799271689)
    ·
      refine ⟨412130469325309349453767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 549507292433745799271689 412130469325309349453767)
      ·
        refine ⟨618195703987964024180651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 412130469325309349453767 618195703987964024180651)
        ·
          refine ⟨927293555981946036270977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 618195703987964024180651 927293555981946036270977)
          ·
            refine ⟨695470166986459527203233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 927293555981946036270977 695470166986459527203233)
            ·
              refine ⟨521602625239844645402425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 695470166986459527203233 521602625239844645402425)
              ·
                refine ⟨391201968929883484051819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 521602625239844645402425 391201968929883484051819)
                ·
                  refine ⟨586802953394825226077729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 391201968929883484051819 586802953394825226077729)
                  ·
                    refine ⟨440102215046118919558297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 586802953394825226077729 440102215046118919558297)
                    ·
                      refine ⟨330076661284589189668723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 440102215046118919558297 330076661284589189668723)
                      ·
                        rfl

theorem cell23_642822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_642822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_642822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_642822 prefixEnd_642822 := by exact prefixLift 642822
  have htrace : WordTrace (prefixWord ++ tailWord_642822) baseStart_642822 baseEnd_642822 := by
    simpa [prefixWord, tailWord_642822, baseEnd_642822] using wordTrace_append hprefix tailTrace_642822
  have hstable : (prefixWord ++ tailWord_642822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642822).length < 2 ^ (prefixWord ++ tailWord_642822).sum := by decide
  have hdescent : baseEnd_642822 < baseStart_642822 := by decide
  rcases family_descends (prefixWord ++ tailWord_642822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642866 : List Nat := [3, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4]
def baseStart_642866 : Nat := 118140960795 + 642866 * 2 ^ 59
def prefixEnd_642866 : Nat := 4983230072969 + 3 ^ 40 * 642866 * 2
def baseEnd_642866 : Nat := 330099254433387017518519

theorem tailTrace_642866 : CollatzResearch.WordTrace tailWord_642866 prefixEnd_642866 330099254433387017518519 := by
  unfold tailWord_642866
  simp only [CollatzResearch.WordTrace]
  refine ⟨5861812322253437404215113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15631499526009166411240301 5861812322253437404215113)
  ·
    refine ⟨4396359241690078053161335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5861812322253437404215113 4396359241690078053161335)
    ·
      refine ⟨6594538862535117079742003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4396359241690078053161335 6594538862535117079742003)
      ·
        refine ⟨9891808293802675619613005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6594538862535117079742003 9891808293802675619613005)
        ·
          refine ⟨3709428110176003357354877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9891808293802675619613005 3709428110176003357354877)
          ·
            refine ⟨1391035541316001259008079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3709428110176003357354877 1391035541316001259008079)
            ·
              refine ⟨2086553311974001888512119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1391035541316001259008079 2086553311974001888512119)
              ·
                refine ⟨3129829967961002832768179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2086553311974001888512119 3129829967961002832768179)
                ·
                  refine ⟨4694744951941504249152269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3129829967961002832768179 4694744951941504249152269)
                  ·
                    refine ⟨1760529356978064093432101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4694744951941504249152269 1760529356978064093432101)
                    ·
                      refine ⟨330099254433387017518519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1760529356978064093432101 330099254433387017518519)
                      ·
                        rfl

theorem cell23_642866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_642866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_642866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_642866 prefixEnd_642866 := by exact prefixLift 642866
  have htrace : WordTrace (prefixWord ++ tailWord_642866) baseStart_642866 baseEnd_642866 := by
    simpa [prefixWord, tailWord_642866, baseEnd_642866] using wordTrace_append hprefix tailTrace_642866
  have hstable : (prefixWord ++ tailWord_642866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642866).length < 2 ^ (prefixWord ++ tailWord_642866).sum := by decide
  have hdescent : baseEnd_642866 < baseStart_642866 := by decide
  rcases family_descends (prefixWord ++ tailWord_642866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642889 : List Nat := [1, 2, 1, 1, 2, 4, 3, 1, 8]
def baseStart_642889 : Nat := 118140960795 + 642889 * 2 ^ 59
def prefixEnd_642889 : Nat := 4983230072969 + 3 ^ 40 * 642889 * 2
def baseEnd_642889 : Nat := 36679007165382269725657

theorem tailTrace_642889 : CollatzResearch.WordTrace tailWord_642889 prefixEnd_642889 36679007165382269725657 := by
  unfold tailWord_642889
  simp only [CollatzResearch.WordTrace]
  refine ⟨23448088167930424544947721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15632058778620283029965147 23448088167930424544947721)
  ·
    refine ⟨17586066125947818408710791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23448088167930424544947721 17586066125947818408710791)
    ·
      refine ⟨26379099188921727613066187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17586066125947818408710791 26379099188921727613066187)
      ·
        refine ⟨39568648783382591419599281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26379099188921727613066187 39568648783382591419599281)
        ·
          refine ⟨29676486587536943564699461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39568648783382591419599281 29676486587536943564699461)
          ·
            refine ⟨5564341235163176918381149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29676486587536943564699461 5564341235163176918381149)
            ·
              refine ⟨2086627963186191344392931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5564341235163176918381149 2086627963186191344392931)
              ·
                refine ⟨3129941944779287016589397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2086627963186191344392931 3129941944779287016589397)
                ·
                  refine ⟨36679007165382269725657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3129941944779287016589397 36679007165382269725657)
                  ·
                    rfl

theorem cell23_642889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 8].length) (baseStart_642889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_642889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_642889 prefixEnd_642889 := by exact prefixLift 642889
  have htrace : WordTrace (prefixWord ++ tailWord_642889) baseStart_642889 baseEnd_642889 := by
    simpa [prefixWord, tailWord_642889, baseEnd_642889] using wordTrace_append hprefix tailTrace_642889
  have hstable : (prefixWord ++ tailWord_642889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642889).length < 2 ^ (prefixWord ++ tailWord_642889).sum := by decide
  have hdescent : baseEnd_642889 < baseStart_642889 := by decide
  rcases family_descends (prefixWord ++ tailWord_642889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642956 : List Nat := [2, 2, 1, 2, 1, 2, 1, 4, 3, 1, 4]
def baseStart_642956 : Nat := 118140960795 + 642956 * 2 ^ 59
def prefixEnd_642956 : Nat := 4983230072969 + 3 ^ 40 * 642956 * 2
def baseEnd_642956 : Nat := 330145467692291665393105

theorem tailTrace_642956 : CollatzResearch.WordTrace tailWord_642956 prefixEnd_642956 330145467692291665393105 := by
  unfold tailWord_642956
  simp only [CollatzResearch.WordTrace]
  refine ⟨11725265929343847493818361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15633687905791796658424481 11725265929343847493818361)
  ·
    refine ⟨8793949447007885620363771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11725265929343847493818361 8793949447007885620363771)
    ·
      refine ⟨13190924170511828430545657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8793949447007885620363771 13190924170511828430545657)
      ·
        refine ⟨9893193127883871322909243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13190924170511828430545657 9893193127883871322909243)
        ·
          refine ⟨14839789691825806984363865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9893193127883871322909243 14839789691825806984363865)
          ·
            refine ⟨11129842268869355238272899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14839789691825806984363865 11129842268869355238272899)
            ·
              refine ⟨16694763403304032857409349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11129842268869355238272899 16694763403304032857409349)
              ·
                refine ⟨3130268138119506160764253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16694763403304032857409349 3130268138119506160764253)
                ·
                  refine ⟨1173850551794814810286595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3130268138119506160764253 1173850551794814810286595)
                  ·
                    refine ⟨1760775827692222215429893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1173850551794814810286595 1760775827692222215429893)
                    ·
                      refine ⟨330145467692291665393105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1760775827692222215429893 330145467692291665393105)
                      ·
                        rfl

theorem cell23_642956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_642956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_642956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_642956 prefixEnd_642956 := by exact prefixLift 642956
  have htrace : WordTrace (prefixWord ++ tailWord_642956) baseStart_642956 baseEnd_642956 := by
    simpa [prefixWord, tailWord_642956, baseEnd_642956] using wordTrace_append hprefix tailTrace_642956
  have hstable : (prefixWord ++ tailWord_642956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642956).length < 2 ^ (prefixWord ++ tailWord_642956).sum := by decide
  have hdescent : baseEnd_642956 < baseStart_642956 := by decide
  rcases family_descends (prefixWord ++ tailWord_642956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642959 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 5]
def baseStart_642959 : Nat := 118140960795 + 642959 * 2 ^ 59
def prefixEnd_642959 : Nat := 4983230072969 + 3 ^ 40 * 642959 * 2
def baseEnd_642959 : Nat := 330147008134255153655591

theorem tailTrace_642959 : CollatzResearch.WordTrace tailWord_642959 prefixEnd_642959 330147008134255153655591 := by
  unfold tailWord_642959
  simp only [CollatzResearch.WordTrace]
  refine ⟨23450641277676826499995931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15633760851784550999997287 23450641277676826499995931)
  ·
    refine ⟨35175961916515239749993897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23450641277676826499995931 35175961916515239749993897)
    ·
      refine ⟨26381971437386429812495423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35175961916515239749993897 26381971437386429812495423)
      ·
        refine ⟨39572957156079644718743135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26381971437386429812495423 39572957156079644718743135)
        ·
          refine ⟨59359435734119467078114703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39572957156079644718743135 59359435734119467078114703)
          ·
            refine ⟨89039153601179200617172055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59359435734119467078114703 89039153601179200617172055)
            ·
              refine ⟨133558730401768800925758083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89039153601179200617172055 133558730401768800925758083)
              ·
                refine ⟨200338095602653201388637125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133558730401768800925758083 200338095602653201388637125)
                ·
                  refine ⟨37563392925497475260369461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 200338095602653201388637125 37563392925497475260369461)
                  ·
                    refine ⟨3521568086765388305659637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37563392925497475260369461 3521568086765388305659637)
                    ·
                      refine ⟨330147008134255153655591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3521568086765388305659637 330147008134255153655591)
                      ·
                        rfl

theorem cell23_642959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 5].length) (baseStart_642959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_642959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_642959 prefixEnd_642959 := by exact prefixLift 642959
  have htrace : WordTrace (prefixWord ++ tailWord_642959) baseStart_642959 baseEnd_642959 := by
    simpa [prefixWord, tailWord_642959, baseEnd_642959] using wordTrace_append hprefix tailTrace_642959
  have hstable : (prefixWord ++ tailWord_642959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642959).length < 2 ^ (prefixWord ++ tailWord_642959).sum := by decide
  have hdescent : baseEnd_642959 < baseStart_642959 := by decide
  rcases family_descends (prefixWord ++ tailWord_642959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642970 : List Nat := [3, 1, 1, 4, 2, 3, 1, 2, 1, 5]
def baseStart_642970 : Nat := 118140960795 + 642970 * 2 ^ 59
def prefixEnd_642970 : Nat := 4983230072969 + 3 ^ 40 * 642970 * 2
def baseEnd_642970 : Nat := 110050885473818203539347

theorem tailTrace_642970 : CollatzResearch.WordTrace tailWord_642970 prefixEnd_642970 110050885473818203539347 := by
  unfold tailWord_642970
  simp only [CollatzResearch.WordTrace]
  refine ⟨5862760620159243844661591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15634028320424650252430909 5862760620159243844661591)
  ·
    refine ⟨8794140930238865766992387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5862760620159243844661591 8794140930238865766992387)
    ·
      refine ⟨13191211395358298650488581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8794140930238865766992387 13191211395358298650488581)
      ·
        refine ⟨2473352136629680996966609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13191211395358298650488581 2473352136629680996966609)
        ·
          refine ⟨1855014102472260747724957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2473352136629680996966609 1855014102472260747724957)
          ·
            refine ⟨695630288427097780396859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1855014102472260747724957 695630288427097780396859)
            ·
              refine ⟨1043445432640646670595289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 695630288427097780396859 1043445432640646670595289)
              ·
                refine ⟨782584074480485002946467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1043445432640646670595289 782584074480485002946467)
                ·
                  refine ⟨1173876111720727504419701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 782584074480485002946467 1173876111720727504419701)
                  ·
                    refine ⟨110050885473818203539347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1173876111720727504419701 110050885473818203539347)
                    ·
                      rfl

theorem cell23_642970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 2, 1, 5].length) (baseStart_642970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_642970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_642970 prefixEnd_642970 := by exact prefixLift 642970
  have htrace : WordTrace (prefixWord ++ tailWord_642970) baseStart_642970 baseEnd_642970 := by
    simpa [prefixWord, tailWord_642970, baseEnd_642970] using wordTrace_append hprefix tailTrace_642970
  have hstable : (prefixWord ++ tailWord_642970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642970).length < 2 ^ (prefixWord ++ tailWord_642970).sum := by decide
  have hdescent : baseEnd_642970 < baseStart_642970 := by decide
  rcases family_descends (prefixWord ++ tailWord_642970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642973 : List Nat := [1, 4, 2, 1, 2, 3, 1, 1, 3, 1, 4]
def baseStart_642973 : Nat := 118140960795 + 642973 * 2 ^ 59
def prefixEnd_642973 : Nat := 4983230072969 + 3 ^ 40 * 642973 * 2
def baseEnd_642973 : Nat := 330154196863418098880527

theorem tailTrace_642973 : CollatzResearch.WordTrace tailWord_642973 prefixEnd_642973 330154196863418098880527 := by
  unfold tailWord_642973
  simp only [CollatzResearch.WordTrace]
  refine ⟨23451151899626106891005573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15634101266417404594003715 23451151899626106891005573)
  ·
    refine ⟨4397090981179895042063545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23451151899626106891005573 4397090981179895042063545)
    ·
      refine ⟨3297818235884921281547659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4397090981179895042063545 3297818235884921281547659)
      ·
        refine ⟨4946727353827381922321489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3297818235884921281547659 4946727353827381922321489)
        ·
          refine ⟨3710045515370536441741117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4946727353827381922321489 3710045515370536441741117)
          ·
            refine ⟨1391267068263951165652919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3710045515370536441741117 1391267068263951165652919)
            ·
              refine ⟨2086900602395926748479379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1391267068263951165652919 2086900602395926748479379)
              ·
                refine ⟨3130350903593890122719069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2086900602395926748479379 3130350903593890122719069)
                ·
                  refine ⟨1173881588847708796019651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3130350903593890122719069 1173881588847708796019651)
                  ·
                    refine ⟨1760822383271563194029477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1173881588847708796019651 1760822383271563194029477)
                    ·
                      refine ⟨330154196863418098880527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1760822383271563194029477 330154196863418098880527)
                      ·
                        rfl

theorem cell23_642973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_642973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_642973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_642973 prefixEnd_642973 := by exact prefixLift 642973
  have htrace : WordTrace (prefixWord ++ tailWord_642973) baseStart_642973 baseEnd_642973 := by
    simpa [prefixWord, tailWord_642973, baseEnd_642973] using wordTrace_append hprefix tailTrace_642973
  have hstable : (prefixWord ++ tailWord_642973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642973).length < 2 ^ (prefixWord ++ tailWord_642973).sum := by decide
  have hdescent : baseEnd_642973 < baseStart_642973 := by decide
  rcases family_descends (prefixWord ++ tailWord_642973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642977 : List Nat := [1, 2, 3, 4, 2, 1, 2, 1, 2, 3, 2]
def baseStart_642977 : Nat := 118140960795 + 642977 * 2 ^ 59
def prefixEnd_642977 : Nat := 4983230072969 + 3 ^ 40 * 642977 * 2
def baseEnd_642977 : Nat := 330156250786036083230509

theorem tailTrace_642977 : CollatzResearch.WordTrace tailWord_642977 prefixEnd_642977 330156250786036083230509 := by
  unfold tailWord_642977
  simp only [CollatzResearch.WordTrace]
  refine ⟨23451297791611615574151185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15634198527741077049434123 23451297791611615574151185)
  ·
    refine ⟨17588473343708711680613389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23451297791611615574151185 17588473343708711680613389)
    ·
      refine ⟨6595677503890766880230021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17588473343708711680613389 6595677503890766880230021)
      ·
        refine ⟨1236689531979518790043129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6595677503890766880230021 1236689531979518790043129)
        ·
          refine ⟨927517148984639092532347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1236689531979518790043129 927517148984639092532347)
          ·
            refine ⟨1391275723476958638798521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 927517148984639092532347 1391275723476958638798521)
            ·
              refine ⟨1043456792607718979098891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1391275723476958638798521 1043456792607718979098891)
              ·
                refine ⟨1565185188911578468648337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1043456792607718979098891 1565185188911578468648337)
                ·
                  refine ⟨1173888891683683851486253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1565185188911578468648337 1173888891683683851486253)
                  ·
                    refine ⟨440208334381381444307345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1173888891683683851486253 440208334381381444307345)
                    ·
                      refine ⟨330156250786036083230509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 440208334381381444307345 330156250786036083230509)
                      ·
                        rfl

theorem cell23_642977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_642977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_642977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_642977 prefixEnd_642977 := by exact prefixLift 642977
  have htrace : WordTrace (prefixWord ++ tailWord_642977) baseStart_642977 baseEnd_642977 := by
    simpa [prefixWord, tailWord_642977, baseEnd_642977] using wordTrace_append hprefix tailTrace_642977
  have hstable : (prefixWord ++ tailWord_642977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642977).length < 2 ^ (prefixWord ++ tailWord_642977).sum := by decide
  have hdescent : baseEnd_642977 < baseStart_642977 := by decide
  rcases family_descends (prefixWord ++ tailWord_642977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642983 : List Nat := [1, 1, 6, 1, 2, 2, 1, 2, 1, 6]
def baseStart_642983 : Nat := 118140960795 + 642983 * 2 ^ 59
def prefixEnd_642983 : Nat := 4983230072969 + 3 ^ 40 * 642983 * 2
def baseEnd_642983 : Nat := 110053110556654353251827

theorem tailTrace_642983 : CollatzResearch.WordTrace tailWord_642983 prefixEnd_642983 110053110556654353251827 := by
  unfold tailWord_642983
  simp only [CollatzResearch.WordTrace]
  refine ⟨23451516629589878598869603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15634344419726585732579735 23451516629589878598869603)
  ·
    refine ⟨35177274944384817898304405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23451516629589878598869603 35177274944384817898304405)
    ·
      refine ⟨1648934763018038338983019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 35177274944384817898304405 1648934763018038338983019)
      ·
        refine ⟨2473402144527057508474529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1648934763018038338983019 2473402144527057508474529)
        ·
          refine ⟨1855051608395293131355897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2473402144527057508474529 1855051608395293131355897)
          ·
            refine ⟨1391288706296469848516923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1855051608395293131355897 1391288706296469848516923)
            ·
              refine ⟨2086933059444704772775385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1391288706296469848516923 2086933059444704772775385)
              ·
                refine ⟨1565199794583528579581539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2086933059444704772775385 1565199794583528579581539)
                ·
                  refine ⟨2347799691875292869372309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1565199794583528579581539 2347799691875292869372309)
                  ·
                    refine ⟨110053110556654353251827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2347799691875292869372309 110053110556654353251827)
                    ·
                      rfl

theorem cell23_642983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_642983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_642983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_642983 prefixEnd_642983 := by exact prefixLift 642983
  have htrace : WordTrace (prefixWord ++ tailWord_642983) baseStart_642983 baseEnd_642983 := by
    simpa [prefixWord, tailWord_642983, baseEnd_642983] using wordTrace_append hprefix tailTrace_642983
  have hstable : (prefixWord ++ tailWord_642983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642983).length < 2 ^ (prefixWord ++ tailWord_642983).sum := by decide
  have hdescent : baseEnd_642983 < baseStart_642983 := by decide
  rcases family_descends (prefixWord ++ tailWord_642983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_642993 : List Nat := [1, 2, 2, 4, 2, 1, 3, 1, 1, 1, 5]
def baseStart_642993 : Nat := 118140960795 + 642993 * 2 ^ 59
def prefixEnd_642993 : Nat := 4983230072969 + 3 ^ 40 * 642993 * 2
def baseEnd_642993 : Nat := 330164466476508020630435

theorem tailTrace_642993 : CollatzResearch.WordTrace tailWord_642993 prefixEnd_642993 330164466476508020630435 := by
  unfold tailWord_642993
  simp only [CollatzResearch.WordTrace]
  refine ⟨23451881359553650306733633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15634587573035766871155755 23451881359553650306733633)
  ·
    refine ⟨17588911019665237730050225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23451881359553650306733633 17588911019665237730050225)
    ·
      refine ⟨13191683264748928297537669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17588911019665237730050225 13191683264748928297537669)
      ·
        refine ⟨2473440612140424055788313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13191683264748928297537669 2473440612140424055788313)
        ·
          refine ⟨1855080459105318041841235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2473440612140424055788313 1855080459105318041841235)
          ·
            refine ⟨2782620688657977062761853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1855080459105318041841235 2782620688657977062761853)
            ·
              refine ⟨1043482758246741398535695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2782620688657977062761853 1043482758246741398535695)
              ·
                refine ⟨1565224137370112097803543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1043482758246741398535695 1565224137370112097803543)
                ·
                  refine ⟨2347836206055168146705315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1565224137370112097803543 2347836206055168146705315)
                  ·
                    refine ⟨3521754309082752220057973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2347836206055168146705315 3521754309082752220057973)
                    ·
                      refine ⟨330164466476508020630435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3521754309082752220057973 330164466476508020630435)
                      ·
                        rfl

theorem cell23_642993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_642993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_642993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_642993 prefixEnd_642993 := by exact prefixLift 642993
  have htrace : WordTrace (prefixWord ++ tailWord_642993) baseStart_642993 baseEnd_642993 := by
    simpa [prefixWord, tailWord_642993, baseEnd_642993] using wordTrace_append hprefix tailTrace_642993
  have hstable : (prefixWord ++ tailWord_642993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_642993).length < 2 ^ (prefixWord ++ tailWord_642993).sum := by decide
  have hdescent : baseEnd_642993 < baseStart_642993 := by decide
  rcases family_descends (prefixWord ++ tailWord_642993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643007 : List Nat := [1, 1, 2, 2, 2, 1, 5, 4, 1, 2, 2]
def baseStart_643007 : Nat := 118140960795 + 643007 * 2 ^ 59
def prefixEnd_643007 : Nat := 4983230072969 + 3 ^ 40 * 643007 * 2
def baseEnd_643007 : Nat := 330171655205670965855371

theorem tailTrace_643007 : CollatzResearch.WordTrace tailWord_643007 prefixEnd_643007 330171655205670965855371 := by
  unfold tailWord_643007
  simp only [CollatzResearch.WordTrace]
  refine ⟨23452391981502930697743275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15634927987668620465162183 23452391981502930697743275)
  ·
    refine ⟨35178587972254396046614913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23452391981502930697743275 35178587972254396046614913)
    ·
      refine ⟨26383940979190797034961185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35178587972254396046614913 26383940979190797034961185)
      ·
        refine ⟨19787955734393097776220889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26383940979190797034961185 19787955734393097776220889)
        ·
          refine ⟨14840966800794823332165667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19787955734393097776220889 14840966800794823332165667)
          ·
            refine ⟨22261450201192234998248501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14840966800794823332165667 22261450201192234998248501)
            ·
              refine ⟨2087010956361772031085797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22261450201192234998248501 2087010956361772031085797)
              ·
                refine ⟨391314554317832255828587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2087010956361772031085797 391314554317832255828587)
                ·
                  refine ⟨586971831476748383742881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 391314554317832255828587 586971831476748383742881)
                  ·
                    refine ⟨440228873607561287807161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 586971831476748383742881 440228873607561287807161)
                    ·
                      refine ⟨330171655205670965855371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 440228873607561287807161 330171655205670965855371)
                      ·
                        rfl

theorem cell23_643007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 4, 1, 2, 2].length) (baseStart_643007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_643007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_643007 prefixEnd_643007 := by exact prefixLift 643007
  have htrace : WordTrace (prefixWord ++ tailWord_643007) baseStart_643007 baseEnd_643007 := by
    simpa [prefixWord, tailWord_643007, baseEnd_643007] using wordTrace_append hprefix tailTrace_643007
  have hstable : (prefixWord ++ tailWord_643007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643007).length < 2 ^ (prefixWord ++ tailWord_643007).sum := by decide
  have hdescent : baseEnd_643007 < baseStart_643007 := by decide
  rcases family_descends (prefixWord ++ tailWord_643007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643023 : List Nat := [1, 1, 2, 1, 1, 5, 4, 1, 1, 3, 3]
def baseStart_643023 : Nat := 118140960795 + 643023 * 2 ^ 59
def prefixEnd_643023 : Nat := 4983230072969 + 3 ^ 40 * 643023 * 2
def baseEnd_643023 : Nat := 330179870896142903255297

theorem tailTrace_643023 : CollatzResearch.WordTrace tailWord_643023 prefixEnd_643023 330179870896142903255297 := by
  unfold tailWord_643023
  simp only [CollatzResearch.WordTrace]
  refine ⟨23452975549444965430325723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15635317032963310286883815 23452975549444965430325723)
  ·
    refine ⟨35179463324167448145488585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23452975549444965430325723 35179463324167448145488585)
    ·
      refine ⟨26384597493125586109116439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35179463324167448145488585 26384597493125586109116439)
      ·
        refine ⟨39576896239688379163674659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26384597493125586109116439 39576896239688379163674659)
        ·
          refine ⟨59365344359532568745511989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39576896239688379163674659 59365344359532568745511989)
          ·
            refine ⟨5565501033706178319891749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59365344359532568745511989 5565501033706178319891749)
            ·
              refine ⟨1043531443819908434979703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5565501033706178319891749 1043531443819908434979703)
              ·
                refine ⟨1565297165729862652469555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1043531443819908434979703 1565297165729862652469555)
                ·
                  refine ⟨2347945748594793978704333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1565297165729862652469555 2347945748594793978704333)
                  ·
                    refine ⟨880479655723047742014125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2347945748594793978704333 880479655723047742014125)
                    ·
                      refine ⟨330179870896142903255297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 880479655723047742014125 330179870896142903255297)
                      ·
                        rfl

theorem cell23_643023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 3, 3].length) (baseStart_643023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_643023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_643023 prefixEnd_643023 := by exact prefixLift 643023
  have htrace : WordTrace (prefixWord ++ tailWord_643023) baseStart_643023 baseEnd_643023 := by
    simpa [prefixWord, tailWord_643023, baseEnd_643023] using wordTrace_append hprefix tailTrace_643023
  have hstable : (prefixWord ++ tailWord_643023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643023).length < 2 ^ (prefixWord ++ tailWord_643023).sum := by decide
  have hdescent : baseEnd_643023 < baseStart_643023 := by decide
  rcases family_descends (prefixWord ++ tailWord_643023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643056 : List Nat := [2, 1, 1, 1, 3, 2, 3, 2, 2, 6]
def baseStart_643056 : Nat := 118140960795 + 643056 * 2 ^ 59
def prefixEnd_643056 : Nat := 4983230072969 + 3 ^ 40 * 643056 * 2
def baseEnd_643056 : Nat := 110065605252580424714215

theorem tailTrace_643056 : CollatzResearch.WordTrace tailWord_643056 prefixEnd_643056 110065605252580424714215 := by
  unfold tailWord_643056
  simp only [CollatzResearch.WordTrace]
  refine ⟨11727089579162706033138511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15636119438883608044184681 11727089579162706033138511)
  ·
    refine ⟨17590634368744059049707767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11727089579162706033138511 17590634368744059049707767)
    ·
      refine ⟨26385951553116088574561651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17590634368744059049707767 26385951553116088574561651)
      ·
        refine ⟨39578927329674132861842477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26385951553116088574561651 39578927329674132861842477)
        ·
          refine ⟨14842097748627799823190929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39578927329674132861842477 14842097748627799823190929)
          ·
            refine ⟨11131573311470849867393197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14842097748627799823190929 11131573311470849867393197)
            ·
              refine ⟨4174339991801568700272449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11131573311470849867393197 4174339991801568700272449)
              ·
                refine ⟨3130754993851176525204337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4174339991801568700272449 3130754993851176525204337)
                ·
                  refine ⟨2348066245388382393903253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3130754993851176525204337 2348066245388382393903253)
                  ·
                    refine ⟨110065605252580424714215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2348066245388382393903253 110065605252580424714215)
                    ·
                      rfl

theorem cell23_643056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 2, 6].length) (baseStart_643056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_643056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_643056 prefixEnd_643056 := by exact prefixLift 643056
  have htrace : WordTrace (prefixWord ++ tailWord_643056) baseStart_643056 baseEnd_643056 := by
    simpa [prefixWord, tailWord_643056, baseEnd_643056] using wordTrace_append hprefix tailTrace_643056
  have hstable : (prefixWord ++ tailWord_643056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643056).length < 2 ^ (prefixWord ++ tailWord_643056).sum := by decide
  have hdescent : baseEnd_643056 < baseStart_643056 := by decide
  rcases family_descends (prefixWord ++ tailWord_643056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643066 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 6, 1, 5]
def baseStart_643066 : Nat := 118140960795 + 643066 * 2 ^ 59
def prefixEnd_643066 : Nat := 4983230072969 + 3 ^ 40 * 643066 * 2
def baseEnd_643066 : Nat := 330201950564286235017599

theorem tailTrace_643066 : CollatzResearch.WordTrace tailWord_643066 prefixEnd_643066 330201950564286235017599 := by
  unfold tailWord_643066
  simp only [CollatzResearch.WordTrace]
  refine ⟨5863635972072295943535263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15636362592192789182760701 5863635972072295943535263)
  ·
    refine ⟨8795453958108443915302895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5863635972072295943535263 8795453958108443915302895)
    ·
      refine ⟨13193180937162665872954343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8795453958108443915302895 13193180937162665872954343)
      ·
        refine ⟨19789771405743998809431515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13193180937162665872954343 19789771405743998809431515)
        ·
          refine ⟨29684657108615998214147273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19789771405743998809431515 29684657108615998214147273)
          ·
            refine ⟨22263492831461998660610455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29684657108615998214147273 22263492831461998660610455)
            ·
              refine ⟨33395239247192997990915683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22263492831461998660610455 33395239247192997990915683)
              ·
                refine ⟨50092858870789496986373525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33395239247192997990915683 50092858870789496986373525)
                ·
                  refine ⟨2348102759568257671236259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 50092858870789496986373525 2348102759568257671236259)
                  ·
                    refine ⟨3522154139352386506854389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2348102759568257671236259 3522154139352386506854389)
                    ·
                      refine ⟨330201950564286235017599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3522154139352386506854389 330201950564286235017599)
                      ·
                        rfl

theorem cell23_643066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 6, 1, 5].length) (baseStart_643066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_643066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_643066 prefixEnd_643066 := by exact prefixLift 643066
  have htrace : WordTrace (prefixWord ++ tailWord_643066) baseStart_643066 baseEnd_643066 := by
    simpa [prefixWord, tailWord_643066, baseEnd_643066] using wordTrace_append hprefix tailTrace_643066
  have hstable : (prefixWord ++ tailWord_643066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643066).length < 2 ^ (prefixWord ++ tailWord_643066).sum := by decide
  have hdescent : baseEnd_643066 < baseStart_643066 := by decide
  rcases family_descends (prefixWord ++ tailWord_643066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643078 : List Nat := [6, 2, 1, 2, 1, 1, 2, 2, 1, 2, 3]
def baseStart_643078 : Nat := 118140960795 + 643078 * 2 ^ 59
def prefixEnd_643078 : Nat := 4983230072969 + 3 ^ 40 * 643078 * 2
def baseEnd_643078 : Nat := 330208112332140188067545

theorem tailTrace_643078 : CollatzResearch.WordTrace tailWord_643078 prefixEnd_643078 330208112332140188067545 := by
  unfold tailWord_643078
  simp only [CollatzResearch.WordTrace]
  refine ⟨732968173882678431986809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15636654376163806549051925 732968173882678431986809)
  ·
    refine ⟨549726130412008823990107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 732968173882678431986809 549726130412008823990107)
    ·
      refine ⟨824589195618013235985161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 549726130412008823990107 824589195618013235985161)
      ·
        refine ⟨618441896713509926988871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 824589195618013235985161 618441896713509926988871)
        ·
          refine ⟨927662845070264890483307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 618441896713509926988871 927662845070264890483307)
          ·
            refine ⟨1391494267605397335724961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 927662845070264890483307 1391494267605397335724961)
            ·
              refine ⟨1043620700704048001793721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1391494267605397335724961 1043620700704048001793721)
              ·
                refine ⟨782715525528036001345291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1043620700704048001793721 782715525528036001345291)
                ·
                  refine ⟨1174073288292054002017937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 782715525528036001345291 1174073288292054002017937)
                  ·
                    refine ⟨880554966219040501513453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1174073288292054002017937 880554966219040501513453)
                    ·
                      refine ⟨330208112332140188067545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 880554966219040501513453 330208112332140188067545)
                      ·
                        rfl

theorem cell23_643078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_643078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_643078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_643078 prefixEnd_643078 := by exact prefixLift 643078
  have htrace : WordTrace (prefixWord ++ tailWord_643078) baseStart_643078 baseEnd_643078 := by
    simpa [prefixWord, tailWord_643078, baseEnd_643078] using wordTrace_append hprefix tailTrace_643078
  have hstable : (prefixWord ++ tailWord_643078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643078).length < 2 ^ (prefixWord ++ tailWord_643078).sum := by decide
  have hdescent : baseEnd_643078 < baseStart_643078 := by decide
  rcases family_descends (prefixWord ++ tailWord_643078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643116 : List Nat := [2, 2, 1, 1, 1, 2, 2, 2, 3, 7]
def baseStart_643116 : Nat := 118140960795 + 643116 * 2 ^ 59
def prefixEnd_643116 : Nat := 4983230072969 + 3 ^ 40 * 643116 * 2
def baseEnd_643116 : Nat := 110075874865670346464123

theorem tailTrace_643116 : CollatzResearch.WordTrace tailWord_643116 prefixEnd_643116 110075874865670346464123 := by
  unfold tailWord_643116
  simp only [CollatzResearch.WordTrace]
  refine ⟨11728183769054021156730601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15637578358738694875640801 11728183769054021156730601)
  ·
    refine ⟨8796137826790515867547951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11728183769054021156730601 8796137826790515867547951)
    ·
      refine ⟨13194206740185773801321927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8796137826790515867547951 13194206740185773801321927)
      ·
        refine ⟨19791310110278660701982891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13194206740185773801321927 19791310110278660701982891)
        ·
          refine ⟨29686965165417991052974337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19791310110278660701982891 29686965165417991052974337)
          ·
            refine ⟨22265223874063493289730753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29686965165417991052974337 22265223874063493289730753)
            ·
              refine ⟨16698917905547619967298065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22265223874063493289730753 16698917905547619967298065)
              ·
                refine ⟨12524188429160714975473549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16698917905547619967298065 12524188429160714975473549)
                ·
                  refine ⟨4696570660935268115802581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12524188429160714975473549 4696570660935268115802581)
                  ·
                    refine ⟨110075874865670346464123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4696570660935268115802581 110075874865670346464123)
                    ·
                      rfl

theorem cell23_643116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 7].length) (baseStart_643116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_643116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_643116 prefixEnd_643116 := by exact prefixLift 643116
  have htrace : WordTrace (prefixWord ++ tailWord_643116) baseStart_643116 baseEnd_643116 := by
    simpa [prefixWord, tailWord_643116, baseEnd_643116] using wordTrace_append hprefix tailTrace_643116
  have hstable : (prefixWord ++ tailWord_643116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643116).length < 2 ^ (prefixWord ++ tailWord_643116).sum := by decide
  have hdescent : baseEnd_643116 < baseStart_643116 := by decide
  rcases family_descends (prefixWord ++ tailWord_643116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643133 : List Nat := [1, 4, 1, 3, 1, 1, 1, 2, 4, 5]
def baseStart_643133 : Nat := 118140960795 + 643133 * 2 ^ 59
def prefixEnd_643133 : Nat := 4983230072969 + 3 ^ 40 * 643133 * 2
def baseEnd_643133 : Nat := 110078784589379157626597

theorem tailTrace_643133 : CollatzResearch.WordTrace tailWord_643133 prefixEnd_643133 110078784589379157626597 := by
  unfold tailWord_643133
  simp only [CollatzResearch.WordTrace]
  refine ⟨23456987579046454216830053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15637991719364302811220035 23456987579046454216830053)
  ·
    refine ⟨4398185171071210165655635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23456987579046454216830053 4398185171071210165655635)
    ·
      refine ⟨6597277756606815248483453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4398185171071210165655635 6597277756606815248483453)
      ·
        refine ⟨2473979158727555718181295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6597277756606815248483453 2473979158727555718181295)
        ·
          refine ⟨3710968738091333577271943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2473979158727555718181295 3710968738091333577271943)
          ·
            refine ⟨5566453107137000365907915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3710968738091333577271943 5566453107137000365907915)
            ·
              refine ⟨8349679660705500548861873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5566453107137000365907915 8349679660705500548861873)
              ·
                refine ⟨6262259745529125411646405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8349679660705500548861873 6262259745529125411646405)
                ·
                  refine ⟨1174173702286711014683701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6262259745529125411646405 1174173702286711014683701)
                  ·
                    refine ⟨110078784589379157626597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1174173702286711014683701 110078784589379157626597)
                    ·
                      rfl

theorem cell23_643133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 4, 5].length) (baseStart_643133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_643133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_643133 prefixEnd_643133 := by exact prefixLift 643133
  have htrace : WordTrace (prefixWord ++ tailWord_643133) baseStart_643133 baseEnd_643133 := by
    simpa [prefixWord, tailWord_643133, baseEnd_643133] using wordTrace_append hprefix tailTrace_643133
  have hstable : (prefixWord ++ tailWord_643133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643133).length < 2 ^ (prefixWord ++ tailWord_643133).sum := by decide
  have hdescent : baseEnd_643133 < baseStart_643133 := by decide
  rcases family_descends (prefixWord ++ tailWord_643133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643150 : List Nat := [4, 1, 1, 1, 1, 5, 2, 1, 2, 5]
def baseStart_643150 : Nat := 118140960795 + 643150 * 2 ^ 59
def prefixEnd_643150 : Nat := 4983230072969 + 3 ^ 40 * 643150 * 2
def baseEnd_643150 : Nat := 110081694313087968789071

theorem tailTrace_643150 : CollatzResearch.WordTrace tailWord_643150 prefixEnd_643150 110081694313087968789071 := by
  unfold tailWord_643150
  simp only [CollatzResearch.WordTrace]
  refine ⟨2932200952498108265024863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15638405079989910746799269 2932200952498108265024863)
  ·
    refine ⟨4398301428747162397537295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2932200952498108265024863 4398301428747162397537295)
    ·
      refine ⟨6597452143120743596305943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4398301428747162397537295 6597452143120743596305943)
      ·
        refine ⟨9896178214681115394458915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6597452143120743596305943 9896178214681115394458915)
        ·
          refine ⟨14844267322021673091688373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9896178214681115394458915 14844267322021673091688373)
          ·
            refine ⟨1391650061439531852345785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14844267322021673091688373 1391650061439531852345785)
            ·
              refine ⟨1043737546079648889259339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1391650061439531852345785 1043737546079648889259339)
              ·
                refine ⟨1565606319119473333889009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1043737546079648889259339 1565606319119473333889009)
                ·
                  refine ⟨1174204739339605000416757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1565606319119473333889009 1174204739339605000416757)
                  ·
                    refine ⟨110081694313087968789071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1174204739339605000416757 110081694313087968789071)
                    ·
                      rfl

theorem cell23_643150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 2, 5].length) (baseStart_643150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_643150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_643150 prefixEnd_643150 := by exact prefixLift 643150
  have htrace : WordTrace (prefixWord ++ tailWord_643150) baseStart_643150 baseEnd_643150 := by
    simpa [prefixWord, tailWord_643150, baseEnd_643150] using wordTrace_append hprefix tailTrace_643150
  have hstable : (prefixWord ++ tailWord_643150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643150).length < 2 ^ (prefixWord ++ tailWord_643150).sum := by decide
  have hdescent : baseEnd_643150 < baseStart_643150 := by decide
  rcases family_descends (prefixWord ++ tailWord_643150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643237 : List Nat := [1, 3, 1, 2, 1, 3, 4, 1, 3, 1, 3]
def baseStart_643237 : Nat := 118140960795 + 643237 * 2 ^ 59
def prefixEnd_643237 : Nat := 4983230072969 + 3 ^ 40 * 643237 * 2
def baseEnd_643237 : Nat := 330289755756205065979313

theorem tailTrace_643237 : CollatzResearch.WordTrace tailWord_643237 prefixEnd_643237 330289755756205065979313 := by
  unfold tailWord_643237
  simp only [CollatzResearch.WordTrace]
  refine ⟨23460780770669679978615965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15640520513779786652410643 23460780770669679978615965)
  ·
    refine ⟨8797792789001129991980987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23460780770669679978615965 8797792789001129991980987)
    ·
      refine ⟨13196689183501694987971481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8797792789001129991980987 13196689183501694987971481)
      ·
        refine ⟨9897516887626271240978611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13196689183501694987971481 9897516887626271240978611)
        ·
          refine ⟨14846275331439406861467917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9897516887626271240978611 14846275331439406861467917)
          ·
            refine ⟨5567353249289777573050469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14846275331439406861467917 5567353249289777573050469)
            ·
              refine ⟨1043878734241833294946963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5567353249289777573050469 1043878734241833294946963)
              ·
                refine ⟨1565818101362749942420445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1043878734241833294946963 1565818101362749942420445)
                ·
                  refine ⟨587181788011031228407667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1565818101362749942420445 587181788011031228407667)
                  ·
                    refine ⟨880772682016546842611501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 587181788011031228407667 880772682016546842611501)
                    ·
                      refine ⟨330289755756205065979313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 880772682016546842611501 330289755756205065979313)
                      ·
                        rfl

theorem cell23_643237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 3, 1, 3].length) (baseStart_643237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_643237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_643237 prefixEnd_643237 := by exact prefixLift 643237
  have htrace : WordTrace (prefixWord ++ tailWord_643237) baseStart_643237 baseEnd_643237 := by
    simpa [prefixWord, tailWord_643237, baseEnd_643237] using wordTrace_append hprefix tailTrace_643237
  have hstable : (prefixWord ++ tailWord_643237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643237).length < 2 ^ (prefixWord ++ tailWord_643237).sum := by decide
  have hdescent : baseEnd_643237 < baseStart_643237 := by decide
  rcases family_descends (prefixWord ++ tailWord_643237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643263 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 5]
def baseStart_643263 : Nat := 118140960795 + 643263 * 2 ^ 59
def prefixEnd_643263 : Nat := 4983230072969 + 3 ^ 40 * 643263 * 2
def baseEnd_643263 : Nat := 330303106253221964254193

theorem tailTrace_643263 : CollatzResearch.WordTrace tailWord_643263 prefixEnd_643263 330303106253221964254193 := by
  unfold tailWord_643263
  simp only [CollatzResearch.WordTrace]
  refine ⟨23461729068575486419062443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15641152712383657612708295 23461729068575486419062443)
  ·
    refine ⟨35192593602863229628593665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23461729068575486419062443 35192593602863229628593665)
    ·
      refine ⟨26394445202147422221445249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35192593602863229628593665 26394445202147422221445249)
      ·
        refine ⟨19795833901610566666083937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26394445202147422221445249 19795833901610566666083937)
        ·
          refine ⟨14846875426207924999562953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19795833901610566666083937 14846875426207924999562953)
          ·
            refine ⟨11135156569655943749672215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14846875426207924999562953 11135156569655943749672215)
            ·
              refine ⟨16702734854483915624508323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11135156569655943749672215 16702734854483915624508323)
              ·
                refine ⟨25054102281725873436762485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16702734854483915624508323 25054102281725873436762485)
                ·
                  refine ⟨2348822088911800634696483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25054102281725873436762485 2348822088911800634696483)
                  ·
                    refine ⟨3523233133367700952044725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2348822088911800634696483 3523233133367700952044725)
                    ·
                      refine ⟨330303106253221964254193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3523233133367700952044725 330303106253221964254193)
                      ·
                        rfl

theorem cell23_643263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 5].length) (baseStart_643263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_643263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_643263 prefixEnd_643263 := by exact prefixLift 643263
  have htrace : WordTrace (prefixWord ++ tailWord_643263) baseStart_643263 baseEnd_643263 := by
    simpa [prefixWord, tailWord_643263, baseEnd_643263] using wordTrace_append hprefix tailTrace_643263
  have hstable : (prefixWord ++ tailWord_643263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643263).length < 2 ^ (prefixWord ++ tailWord_643263).sum := by decide
  have hdescent : baseEnd_643263 < baseStart_643263 := by decide
  rcases family_descends (prefixWord ++ tailWord_643263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643304 : List Nat := [2, 1, 4, 1, 2, 2, 4, 1, 2, 4]
def baseStart_643304 : Nat := 118140960795 + 643304 * 2 ^ 59
def prefixEnd_643304 : Nat := 4983230072969 + 3 ^ 40 * 643304 * 2
def baseEnd_643304 : Nat := 110108052986685434613835

theorem tailTrace_643304 : CollatzResearch.WordTrace tailWord_643304 prefixEnd_643304 110108052986685434613835 := by
  unfold tailWord_643304
  simp only [CollatzResearch.WordTrace]
  refine ⟨11731612230713475210652483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15642149640951300280869977 11731612230713475210652483)
  ·
    refine ⟨17597418346070212815978725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11731612230713475210652483 17597418346070212815978725)
    ·
      refine ⟨3299515939888164902996011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17597418346070212815978725 3299515939888164902996011)
      ·
        refine ⟨4949273909832247354494017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3299515939888164902996011 4949273909832247354494017)
        ·
          refine ⟨3711955432374185515870513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4949273909832247354494017 3711955432374185515870513)
          ·
            refine ⟨2783966574280639136902885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3711955432374185515870513 2783966574280639136902885)
            ·
              refine ⟨521993732677619838169291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2783966574280639136902885 521993732677619838169291)
              ·
                refine ⟨782990599016429757253937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 521993732677619838169291 782990599016429757253937)
                ·
                  refine ⟨587242949262322317940453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 782990599016429757253937 587242949262322317940453)
                  ·
                    refine ⟨110108052986685434613835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 587242949262322317940453 110108052986685434613835)
                    ·
                      rfl

theorem cell23_643304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_643304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_643304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_643304 prefixEnd_643304 := by exact prefixLift 643304
  have htrace : WordTrace (prefixWord ++ tailWord_643304) baseStart_643304 baseEnd_643304 := by
    simpa [prefixWord, tailWord_643304, baseEnd_643304] using wordTrace_append hprefix tailTrace_643304
  have hstable : (prefixWord ++ tailWord_643304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643304).length < 2 ^ (prefixWord ++ tailWord_643304).sum := by decide
  have hdescent : baseEnd_643304 < baseStart_643304 := by decide
  rcases family_descends (prefixWord ++ tailWord_643304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643314 : List Nat := [3, 2, 1, 3, 2, 1, 3, 2, 1, 2, 3]
def baseStart_643314 : Nat := 118140960795 + 643314 * 2 ^ 59
def prefixEnd_643314 : Nat := 4983230072969 + 3 ^ 40 * 643314 * 2
def baseEnd_643314 : Nat := 330329293766601264716459

theorem tailTrace_643314 : CollatzResearch.WordTrace tailWord_643314 prefixEnd_643314 330329293766601264716459 := by
  unfold tailWord_643314
  simp only [CollatzResearch.WordTrace]
  refine ⟨5865897297847680532292249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15642392794260481419445997 5865897297847680532292249)
  ·
    refine ⟨4399422973385760399219187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5865897297847680532292249 4399422973385760399219187)
    ·
      refine ⟨6599134460078640598828781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4399422973385760399219187 6599134460078640598828781)
      ·
        refine ⟨2474675422529490224560793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6599134460078640598828781 2474675422529490224560793)
        ·
          refine ⟨1856006566897117668420595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2474675422529490224560793 1856006566897117668420595)
          ·
            refine ⟨2784009850345676502630893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1856006566897117668420595 2784009850345676502630893)
            ·
              refine ⟨1044003693879628688486585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2784009850345676502630893 1044003693879628688486585)
              ·
                refine ⟨783002770409721516364939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1044003693879628688486585 783002770409721516364939)
                ·
                  refine ⟨1174504155614582274547409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 783002770409721516364939 1174504155614582274547409)
                  ·
                    refine ⟨880878116710936705910557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1174504155614582274547409 880878116710936705910557)
                    ·
                      refine ⟨330329293766601264716459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 880878116710936705910557 330329293766601264716459)
                      ·
                        rfl

theorem cell23_643314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_643314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_643314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_643314 prefixEnd_643314 := by exact prefixLift 643314
  have htrace : WordTrace (prefixWord ++ tailWord_643314) baseStart_643314 baseEnd_643314 := by
    simpa [prefixWord, tailWord_643314, baseEnd_643314] using wordTrace_append hprefix tailTrace_643314
  have hstable : (prefixWord ++ tailWord_643314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643314).length < 2 ^ (prefixWord ++ tailWord_643314).sum := by decide
  have hdescent : baseEnd_643314 < baseStart_643314 := by decide
  rcases family_descends (prefixWord ++ tailWord_643314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643343 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 3, 8]
def baseStart_643343 : Nat := 118140960795 + 643343 * 2 ^ 59
def prefixEnd_643343 : Nat := 4983230072969 + 3 ^ 40 * 643343 * 2
def baseEnd_643343 : Nat := 110114728235193883751275

theorem tailTrace_643343 : CollatzResearch.WordTrace tailWord_643343 prefixEnd_643343 110114728235193883751275 := by
  unfold tailWord_643343
  simp only [CollatzResearch.WordTrace]
  refine ⟨23464646908285660081974683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15643097938857106721316455 23464646908285660081974683)
  ·
    refine ⟨35196970362428490122962025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23464646908285660081974683 35196970362428490122962025)
    ·
      refine ⟨26397727771821367592221519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35196970362428490122962025 26397727771821367592221519)
      ·
        refine ⟨39596591657732051388332279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26397727771821367592221519 39596591657732051388332279)
        ·
          refine ⟨59394887486598077082498419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39596591657732051388332279 59394887486598077082498419)
          ·
            refine ⟨89092331229897115623747629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59394887486598077082498419 89092331229897115623747629)
            ·
              refine ⟨33409624211211418358905361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89092331229897115623747629 33409624211211418358905361)
              ·
                refine ⟨25057218158408563769179021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33409624211211418358905361 25057218158408563769179021)
                ·
                  refine ⟨9396456809403211413442133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25057218158408563769179021 9396456809403211413442133)
                  ·
                    refine ⟨110114728235193883751275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 9396456809403211413442133 110114728235193883751275)
                    ·
                      rfl

theorem cell23_643343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 8].length) (baseStart_643343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_643343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_643343 prefixEnd_643343 := by exact prefixLift 643343
  have htrace : WordTrace (prefixWord ++ tailWord_643343) baseStart_643343 baseEnd_643343 := by
    simpa [prefixWord, tailWord_643343, baseEnd_643343] using wordTrace_append hprefix tailTrace_643343
  have hstable : (prefixWord ++ tailWord_643343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643343).length < 2 ^ (prefixWord ++ tailWord_643343).sum := by decide
  have hdescent : baseEnd_643343 < baseStart_643343 := by decide
  rcases family_descends (prefixWord ++ tailWord_643343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643360 : List Nat := [2, 1, 1, 5, 2, 1, 1, 1, 1, 8]
def baseStart_643360 : Nat := 118140960795 + 643360 * 2 ^ 59
def prefixEnd_643360 : Nat := 4983230072969 + 3 ^ 40 * 643360 * 2
def baseEnd_643360 : Nat := 110117637958902694913749

theorem tailTrace_643360 : CollatzResearch.WordTrace tailWord_643360 prefixEnd_643360 110117637958902694913749 := by
  unfold tailWord_643360
  simp only [CollatzResearch.WordTrace]
  refine ⟨11732633474612035992671767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15643511299482714656895689 11732633474612035992671767)
  ·
    refine ⟨17598950211918053989007651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11732633474612035992671767 17598950211918053989007651)
    ·
      refine ⟨26398425317877080983511477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17598950211918053989007651 26398425317877080983511477)
      ·
        refine ⟨2474852373550976342204201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26398425317877080983511477 2474852373550976342204201)
        ·
          refine ⟨1856139280163232256653151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2474852373550976342204201 1856139280163232256653151)
          ·
            refine ⟨2784208920244848384979727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1856139280163232256653151 2784208920244848384979727)
            ·
              refine ⟨4176313380367272577469591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2784208920244848384979727 4176313380367272577469591)
              ·
                refine ⟨6264470070550908866204387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4176313380367272577469591 6264470070550908866204387)
                ·
                  refine ⟨9396705105826363299306581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6264470070550908866204387 9396705105826363299306581)
                  ·
                    refine ⟨110117637958902694913749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 9396705105826363299306581 110117637958902694913749)
                    ·
                      rfl

theorem cell23_643360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 1, 8].length) (baseStart_643360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_643360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_643360 prefixEnd_643360 := by exact prefixLift 643360
  have htrace : WordTrace (prefixWord ++ tailWord_643360) baseStart_643360 baseEnd_643360 := by
    simpa [prefixWord, tailWord_643360, baseEnd_643360] using wordTrace_append hprefix tailTrace_643360
  have hstable : (prefixWord ++ tailWord_643360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643360).length < 2 ^ (prefixWord ++ tailWord_643360).sum := by decide
  have hdescent : baseEnd_643360 < baseStart_643360 := by decide
  rcases family_descends (prefixWord ++ tailWord_643360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643437 : List Nat := [1, 5, 1, 1, 1, 2, 2, 3, 2, 5]
def baseStart_643437 : Nat := 118140960795 + 643437 * 2 ^ 59
def prefixEnd_643437 : Nat := 4983230072969 + 3 ^ 40 * 643437 * 2
def baseEnd_643437 : Nat := 110130817295701427826131

theorem tailTrace_643437 : CollatzResearch.WordTrace tailWord_643437 prefixEnd_643437 110130817295701427826131 := by
  unfold tailWord_643437
  simp only [CollatzResearch.WordTrace]
  refine ⟨23468075369945114135896565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15645383579963409423931043 23468075369945114135896565)
  ·
    refine ⟨2200132065932354450240303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23468075369945114135896565 2200132065932354450240303)
    ·
      refine ⟨3300198098898531675360455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2200132065932354450240303 3300198098898531675360455)
      ·
        refine ⟨4950297148347797513040683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3300198098898531675360455 4950297148347797513040683)
        ·
          refine ⟨7425445722521696269561025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4950297148347797513040683 7425445722521696269561025)
          ·
            refine ⟨5569084291891272202170769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7425445722521696269561025 5569084291891272202170769)
            ·
              refine ⟨4176813218918454151628077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5569084291891272202170769 4176813218918454151628077)
              ·
                refine ⟨1566304957094420306860529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4176813218918454151628077 1566304957094420306860529)
                ·
                  refine ⟨1174728717820815230145397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1566304957094420306860529 1174728717820815230145397)
                  ·
                    refine ⟨110130817295701427826131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1174728717820815230145397 110130817295701427826131)
                    ·
                      rfl

theorem cell23_643437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_643437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_643437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_643437 prefixEnd_643437 := by exact prefixLift 643437
  have htrace : WordTrace (prefixWord ++ tailWord_643437) baseStart_643437 baseEnd_643437 := by
    simpa [prefixWord, tailWord_643437, baseEnd_643437] using wordTrace_append hprefix tailTrace_643437
  have hstable : (prefixWord ++ tailWord_643437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643437).length < 2 ^ (prefixWord ++ tailWord_643437).sum := by decide
  have hdescent : baseEnd_643437 < baseStart_643437 := by decide
  rcases family_descends (prefixWord ++ tailWord_643437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643458 : List Nat := [3, 4, 2, 1, 3, 1, 1, 1, 7]
def baseStart_643458 : Nat := 118140960795 + 643458 * 2 ^ 59
def prefixEnd_643458 : Nat := 4983230072969 + 3 ^ 40 * 643458 * 2
def baseEnd_643458 : Nat := 36711470553427633479533

theorem tailTrace_643458 : CollatzResearch.WordTrace tailWord_643458 prefixEnd_643458 36711470553427633479533 := by
  unfold tailWord_643458
  simp only [CollatzResearch.WordTrace]
  refine ⟨5867210325717258680602757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15645894201912689814940685 5867210325717258680602757)
  ·
    refine ⟨1100101936071986002613017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5867210325717258680602757 1100101936071986002613017)
    ·
      refine ⟨825076452053989501959763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1100101936071986002613017 825076452053989501959763)
      ·
        refine ⟨1237614678080984252939645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 825076452053989501959763 1237614678080984252939645)
        ·
          refine ⟨464105504280369094852367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1237614678080984252939645 464105504280369094852367)
          ·
            refine ⟨696158256420553642278551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 464105504280369094852367 696158256420553642278551)
            ·
              refine ⟨1044237384630830463417827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 696158256420553642278551 1044237384630830463417827)
              ·
                refine ⟨1566356076946245695126741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1044237384630830463417827 1566356076946245695126741)
                ·
                  refine ⟨36711470553427633479533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1566356076946245695126741 36711470553427633479533)
                  ·
                    rfl

theorem cell23_643458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_643458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_643458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_643458 prefixEnd_643458 := by exact prefixLift 643458
  have htrace : WordTrace (prefixWord ++ tailWord_643458) baseStart_643458 baseEnd_643458 := by
    simpa [prefixWord, tailWord_643458, baseEnd_643458] using wordTrace_append hprefix tailTrace_643458
  have hstable : (prefixWord ++ tailWord_643458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643458).length < 2 ^ (prefixWord ++ tailWord_643458).sum := by decide
  have hdescent : baseEnd_643458 < baseStart_643458 := by decide
  rcases family_descends (prefixWord ++ tailWord_643458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643477 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 6, 2, 3]
def baseStart_643477 : Nat := 118140960795 + 643477 * 2 ^ 59
def prefixEnd_643477 : Nat := 4983230072969 + 3 ^ 40 * 643477 * 2
def baseEnd_643477 : Nat := 330412991113284126978209

theorem tailTrace_643477 : CollatzResearch.WordTrace tailWord_643477 prefixEnd_643477 330412991113284126978209 := by
  unfold tailWord_643477
  simp only [CollatzResearch.WordTrace]
  refine ⟨23469534289800200967352685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15646356193200133978235123 23469534289800200967352685)
  ·
    refine ⟨8801075358675075362757257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23469534289800200967352685 8801075358675075362757257)
    ·
      refine ⟨6600806519006306522067943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8801075358675075362757257 6600806519006306522067943)
      ·
        refine ⟨9901209778509459783101915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6600806519006306522067943 9901209778509459783101915)
        ·
          refine ⟨14851814667764189674652873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9901209778509459783101915 14851814667764189674652873)
          ·
            refine ⟨11138861000823142255989655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14851814667764189674652873 11138861000823142255989655)
            ·
              refine ⟨16708291501234713383984483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11138861000823142255989655 16708291501234713383984483)
              ·
                refine ⟨25062437251852070075976725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16708291501234713383984483 25062437251852070075976725)
                ·
                  refine ⟨1174801746180565784811409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 25062437251852070075976725 1174801746180565784811409)
                  ·
                    refine ⟨881101309635424338608557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1174801746180565784811409 881101309635424338608557)
                    ·
                      refine ⟨330412991113284126978209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 881101309635424338608557 330412991113284126978209)
                      ·
                        rfl

theorem cell23_643477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 6, 2, 3].length) (baseStart_643477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_643477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_643477 prefixEnd_643477 := by exact prefixLift 643477
  have htrace : WordTrace (prefixWord ++ tailWord_643477) baseStart_643477 baseEnd_643477 := by
    simpa [prefixWord, tailWord_643477, baseEnd_643477] using wordTrace_append hprefix tailTrace_643477
  have hstable : (prefixWord ++ tailWord_643477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643477).length < 2 ^ (prefixWord ++ tailWord_643477).sum := by decide
  have hdescent : baseEnd_643477 < baseStart_643477 := by decide
  rcases family_descends (prefixWord ++ tailWord_643477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643500 : List Nat := [2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 8]
def baseStart_643500 : Nat := 118140960795 + 643500 * 2 ^ 59
def prefixEnd_643500 : Nat := 4983230072969 + 3 ^ 40 * 643500 * 2
def baseEnd_643500 : Nat := 330424801168337536990603

theorem tailTrace_643500 : CollatzResearch.WordTrace tailWord_643500 prefixEnd_643500 330424801168337536990603 := by
  unfold tailWord_643500
  simp only [CollatzResearch.WordTrace]
  refine ⟨11735186584358437947719977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15646915445811250596959969 11735186584358437947719977)
  ·
    refine ⟨8801389938268828460789983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11735186584358437947719977 8801389938268828460789983)
    ·
      refine ⟨13202084907403242691184975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8801389938268828460789983 13202084907403242691184975)
      ·
        refine ⟨19803127361104864036777463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13202084907403242691184975 19803127361104864036777463)
        ·
          refine ⟨29704691041657296055166195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19803127361104864036777463 29704691041657296055166195)
          ·
            refine ⟨44557036562485944082749293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29704691041657296055166195 44557036562485944082749293)
            ·
              refine ⟨16708888710932229031030985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44557036562485944082749293 16708888710932229031030985)
              ·
                refine ⟨12531666533199171773273239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16708888710932229031030985 12531666533199171773273239)
                ·
                  refine ⟨18797499799798757659909859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12531666533199171773273239 18797499799798757659909859)
                  ·
                    refine ⟨28196249699698136489864789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18797499799798757659909859 28196249699698136489864789)
                    ·
                      refine ⟨330424801168337536990603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 28196249699698136489864789 330424801168337536990603)
                      ·
                        rfl

theorem cell23_643500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 8].length) (baseStart_643500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_643500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_643500 prefixEnd_643500 := by exact prefixLift 643500
  have htrace : WordTrace (prefixWord ++ tailWord_643500) baseStart_643500 baseEnd_643500 := by
    simpa [prefixWord, tailWord_643500, baseEnd_643500] using wordTrace_append hprefix tailTrace_643500
  have hstable : (prefixWord ++ tailWord_643500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643500).length < 2 ^ (prefixWord ++ tailWord_643500).sum := by decide
  have hdescent : baseEnd_643500 < baseStart_643500 := by decide
  rcases family_descends (prefixWord ++ tailWord_643500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643518 : List Nat := [4, 2, 1, 1, 1, 1, 6, 2, 1, 4]
def baseStart_643518 : Nat := 118140960795 + 643518 * 2 ^ 59
def prefixEnd_643518 : Nat := 4983230072969 + 3 ^ 40 * 643518 * 2
def baseEnd_643518 : Nat := 110144681273372822188507

theorem tailTrace_643518 : CollatzResearch.WordTrace tailWord_643518 prefixEnd_643518 110144681273372822188507 := by
  unfold tailWord_643518
  simp only [CollatzResearch.WordTrace]
  refine ⟨2933878710331458121199401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15647353121767776646396805 2933878710331458121199401)
  ·
    refine ⟨2200409032748593590899551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2933878710331458121199401 2200409032748593590899551)
    ·
      refine ⟨3300613549122890386349327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2200409032748593590899551 3300613549122890386349327)
      ·
        refine ⟨4950920323684335579523991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3300613549122890386349327 4950920323684335579523991)
        ·
          refine ⟨7426380485526503369285987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4950920323684335579523991 7426380485526503369285987)
          ·
            refine ⟨11139570728289755053928981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7426380485526503369285987 11139570728289755053928981)
            ·
              refine ⟨522167377888582268152921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11139570728289755053928981 522167377888582268152921)
              ·
                refine ⟨391625533416436701114691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 522167377888582268152921 391625533416436701114691)
                ·
                  refine ⟨587438300124655051672037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 391625533416436701114691 587438300124655051672037)
                  ·
                    refine ⟨110144681273372822188507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 587438300124655051672037 110144681273372822188507)
                    ·
                      rfl

theorem cell23_643518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_643518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_643518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_643518 prefixEnd_643518 := by exact prefixLift 643518
  have htrace : WordTrace (prefixWord ++ tailWord_643518) baseStart_643518 baseEnd_643518 := by
    simpa [prefixWord, tailWord_643518, baseEnd_643518] using wordTrace_append hprefix tailTrace_643518
  have hstable : (prefixWord ++ tailWord_643518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643518).length < 2 ^ (prefixWord ++ tailWord_643518).sum := by decide
  have hdescent : baseEnd_643518 < baseStart_643518 := by decide
  rcases family_descends (prefixWord ++ tailWord_643518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643527 : List Nat := [1, 1, 4, 1, 1, 4, 1, 2, 3, 5]
def baseStart_643527 : Nat := 118140960795 + 643527 * 2 ^ 59
def prefixEnd_643527 : Nat := 4983230072969 + 3 ^ 40 * 643527 * 2
def baseEnd_643527 : Nat := 110146221715336310450993

theorem tailTrace_643527 : CollatzResearch.WordTrace tailWord_643527 prefixEnd_643527 110146221715336310450993 := by
  unfold tailWord_643527
  simp only [CollatzResearch.WordTrace]
  refine ⟨23471357939619059506672835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15647571959746039671115223 23471357939619059506672835)
  ·
    refine ⟨35207036909428589260009253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23471357939619059506672835 35207036909428589260009253)
    ·
      refine ⟨6601319420517860486251735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35207036909428589260009253 6601319420517860486251735)
      ·
        refine ⟨9901979130776790729377603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6601319420517860486251735 9901979130776790729377603)
        ·
          refine ⟨14852968696165186094066405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9901979130776790729377603 14852968696165186094066405)
          ·
            refine ⟨2784931630530972392637451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14852968696165186094066405 2784931630530972392637451)
            ·
              refine ⟨4177397445796458588956177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2784931630530972392637451 4177397445796458588956177)
              ·
                refine ⟨3133048084347343941717133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4177397445796458588956177 3133048084347343941717133)
                ·
                  refine ⟨1174893031630253978143925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3133048084347343941717133 1174893031630253978143925)
                  ·
                    refine ⟨110146221715336310450993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1174893031630253978143925 110146221715336310450993)
                    ·
                      rfl

theorem cell23_643527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 3, 5].length) (baseStart_643527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_643527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_643527 prefixEnd_643527 := by exact prefixLift 643527
  have htrace : WordTrace (prefixWord ++ tailWord_643527) baseStart_643527 baseEnd_643527 := by
    simpa [prefixWord, tailWord_643527, baseEnd_643527] using wordTrace_append hprefix tailTrace_643527
  have hstable : (prefixWord ++ tailWord_643527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643527).length < 2 ^ (prefixWord ++ tailWord_643527).sum := by decide
  have hdescent : baseEnd_643527 < baseStart_643527 := by decide
  rcases family_descends (prefixWord ++ tailWord_643527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643534 : List Nat := [4, 1, 1, 1, 2, 1, 1, 4, 1, 5, 2]
def baseStart_643534 : Nat := 118140960795 + 643534 * 2 ^ 59
def prefixEnd_643534 : Nat := 4983230072969 + 3 ^ 40 * 643534 * 2
def baseEnd_643534 : Nat := 330442259510590403965447

theorem tailTrace_643534 : CollatzResearch.WordTrace tailWord_643534 prefixEnd_643534 330442259510590403965447 := by
  unfold tailWord_643534
  simp only [CollatzResearch.WordTrace]
  refine ⟨2933951656324212462772207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15647742167062466468118437 2933951656324212462772207)
  ·
    refine ⟨4400927484486318694158311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2933951656324212462772207 4400927484486318694158311)
    ·
      refine ⟨6601391226729478041237467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4400927484486318694158311 6601391226729478041237467)
      ·
        refine ⟨9902086840094217061856201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6601391226729478041237467 9902086840094217061856201)
        ·
          refine ⟨7426565130070662796392151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9902086840094217061856201 7426565130070662796392151)
          ·
            refine ⟨11139847695105994194588227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7426565130070662796392151 11139847695105994194588227)
            ·
              refine ⟨16709771542658991291882341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11139847695105994194588227 16709771542658991291882341)
              ·
                refine ⟨3133082164248560867227939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16709771542658991291882341 3133082164248560867227939)
                ·
                  refine ⟨4699623246372841300841909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3133082164248560867227939 4699623246372841300841909)
                  ·
                    refine ⟨440589679347453871953929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4699623246372841300841909 440589679347453871953929)
                    ·
                      refine ⟨330442259510590403965447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 440589679347453871953929 330442259510590403965447)
                      ·
                        rfl

theorem cell23_643534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 1, 5, 2].length) (baseStart_643534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_643534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_643534 prefixEnd_643534 := by exact prefixLift 643534
  have htrace : WordTrace (prefixWord ++ tailWord_643534) baseStart_643534 baseEnd_643534 := by
    simpa [prefixWord, tailWord_643534, baseEnd_643534] using wordTrace_append hprefix tailTrace_643534
  have hstable : (prefixWord ++ tailWord_643534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643534).length < 2 ^ (prefixWord ++ tailWord_643534).sum := by decide
  have hdescent : baseEnd_643534 < baseStart_643534 := by decide
  rcases family_descends (prefixWord ++ tailWord_643534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643541 : List Nat := [1, 3, 2, 3, 1, 3, 1, 2, 3, 1, 3]
def baseStart_643541 : Nat := 118140960795 + 643541 * 2 ^ 59
def prefixEnd_643541 : Nat := 4983230072969 + 3 ^ 40 * 643541 * 2
def baseEnd_643541 : Nat := 330445853875171876577915

theorem tailTrace_643541 : CollatzResearch.WordTrace tailWord_643541 prefixEnd_643541 330445853875171876577915 := by
  unfold tailWord_643541
  simp only [CollatzResearch.WordTrace]
  refine ⟨23471868561568339897682477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15647912374378893265121651 23471868561568339897682477)
  ·
    refine ⟨8801950710588127461630929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23471868561568339897682477 8801950710588127461630929)
    ·
      refine ⟨6601463032941095596223197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8801950710588127461630929 6601463032941095596223197)
      ·
        refine ⟨2475548637352910848583699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6601463032941095596223197 2475548637352910848583699)
        ·
          refine ⟨3713322956029366272875549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2475548637352910848583699 3713322956029366272875549)
          ·
            refine ⟨1392496108511012352328331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3713322956029366272875549 1392496108511012352328331)
            ·
              refine ⟨2088744162766518528492497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1392496108511012352328331 2088744162766518528492497)
              ·
                refine ⟨1566558122074888896369373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2088744162766518528492497 1566558122074888896369373)
                ·
                  refine ⟨587459295778083336138515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1566558122074888896369373 587459295778083336138515)
                  ·
                    refine ⟨881188943667125004207773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 587459295778083336138515 881188943667125004207773)
                    ·
                      refine ⟨330445853875171876577915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 881188943667125004207773 330445853875171876577915)
                      ·
                        rfl

theorem cell23_643541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_643541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_643541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_643541 prefixEnd_643541 := by exact prefixLift 643541
  have htrace : WordTrace (prefixWord ++ tailWord_643541) baseStart_643541 baseEnd_643541 := by
    simpa [prefixWord, tailWord_643541, baseEnd_643541] using wordTrace_append hprefix tailTrace_643541
  have hstable : (prefixWord ++ tailWord_643541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643541).length < 2 ^ (prefixWord ++ tailWord_643541).sum := by decide
  have hdescent : baseEnd_643541 < baseStart_643541 := by decide
  rcases family_descends (prefixWord ++ tailWord_643541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643551 : List Nat := [1, 1, 2, 3, 3, 2, 3, 1, 2, 3, 2]
def baseStart_643551 : Nat := 118140960795 + 643551 * 2 ^ 59
def prefixEnd_643551 : Nat := 4983230072969 + 3 ^ 40 * 643551 * 2
def baseEnd_643551 : Nat := 330450988681716837452869

theorem tailTrace_643551 : CollatzResearch.WordTrace tailWord_643551 prefixEnd_643551 330450988681716837452869 := by
  unfold tailWord_643551
  simp only [CollatzResearch.WordTrace]
  refine ⟨23472233291532111605546507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15648155527688074403697671 23472233291532111605546507)
  ·
    refine ⟨35208349937298167408319761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23472233291532111605546507 35208349937298167408319761)
    ·
      refine ⟨26406262452973625556239821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35208349937298167408319761 26406262452973625556239821)
      ·
        refine ⟨9902348419865109583589933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26406262452973625556239821 9902348419865109583589933)
        ·
          refine ⟨3713380657449416093846225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9902348419865109583589933 3713380657449416093846225)
          ·
            refine ⟨2785035493087062070384669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3713380657449416093846225 2785035493087062070384669)
            ·
              refine ⟨1044388309907648276394251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2785035493087062070384669 1044388309907648276394251)
              ·
                refine ⟨1566582464861472414591377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1044388309907648276394251 1566582464861472414591377)
                ·
                  refine ⟨1174936848646104310943533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1566582464861472414591377 1174936848646104310943533)
                  ·
                    refine ⟨440601318242289116603825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1174936848646104310943533 440601318242289116603825)
                    ·
                      refine ⟨330450988681716837452869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 440601318242289116603825 330450988681716837452869)
                      ·
                        rfl

theorem cell23_643551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 2, 3, 2].length) (baseStart_643551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_643551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_643551 prefixEnd_643551 := by exact prefixLift 643551
  have htrace : WordTrace (prefixWord ++ tailWord_643551) baseStart_643551 baseEnd_643551 := by
    simpa [prefixWord, tailWord_643551, baseEnd_643551] using wordTrace_append hprefix tailTrace_643551
  have hstable : (prefixWord ++ tailWord_643551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643551).length < 2 ^ (prefixWord ++ tailWord_643551).sum := by decide
  have hdescent : baseEnd_643551 < baseStart_643551 := by decide
  rcases family_descends (prefixWord ++ tailWord_643551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643564 : List Nat := [2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 4]
def baseStart_643564 : Nat := 118140960795 + 643564 * 2 ^ 59
def prefixEnd_643564 : Nat := 4983230072969 + 3 ^ 40 * 643564 * 2
def baseEnd_643564 : Nat := 330457663930225286590309

theorem tailTrace_643564 : CollatzResearch.WordTrace tailWord_643564 prefixEnd_643564 330457663930225286590309 := by
  unfold tailWord_643564
  simp only [CollatzResearch.WordTrace]
  refine ⟨11736353720242507412884873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15648471626990009883846497 11736353720242507412884873)
  ·
    refine ⟨8802265290181880559663655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11736353720242507412884873 8802265290181880559663655)
    ·
      refine ⟨13203397935272820839495483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8802265290181880559663655 13203397935272820839495483)
      ·
        refine ⟨19805096902909231259243225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13203397935272820839495483 19805096902909231259243225)
        ·
          refine ⟨14853822677181923444432419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19805096902909231259243225 14853822677181923444432419)
          ·
            refine ⟨22280734015772885166648629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14853822677181923444432419 22280734015772885166648629)
            ·
              refine ⟨2088818813978707984373309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22280734015772885166648629 2088818813978707984373309)
              ·
                refine ⟨783307055242015494139991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2088818813978707984373309 783307055242015494139991)
                ·
                  refine ⟨1174960582863023241209987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 783307055242015494139991 1174960582863023241209987)
                  ·
                    refine ⟨1762440874294534861814981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1174960582863023241209987 1762440874294534861814981)
                    ·
                      refine ⟨330457663930225286590309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1762440874294534861814981 330457663930225286590309)
                      ·
                        rfl

theorem cell23_643564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 4].length) (baseStart_643564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_643564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_643564 prefixEnd_643564 := by exact prefixLift 643564
  have htrace : WordTrace (prefixWord ++ tailWord_643564) baseStart_643564 baseEnd_643564 := by
    simpa [prefixWord, tailWord_643564, baseEnd_643564] using wordTrace_append hprefix tailTrace_643564
  have hstable : (prefixWord ++ tailWord_643564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643564).length < 2 ^ (prefixWord ++ tailWord_643564).sum := by decide
  have hdescent : baseEnd_643564 < baseStart_643564 := by decide
  rcases family_descends (prefixWord ++ tailWord_643564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643567 : List Nat := [1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 5]
def baseStart_643567 : Nat := 118140960795 + 643567 * 2 ^ 59
def prefixEnd_643567 : Nat := 4983230072969 + 3 ^ 40 * 643567 * 2
def baseEnd_643567 : Nat := 330459204372188774852795

theorem tailTrace_643567 : CollatzResearch.WordTrace tailWord_643567 prefixEnd_643567 330459204372188774852795 := by
  unfold tailWord_643567
  simp only [CollatzResearch.WordTrace]
  refine ⟨23472816859474146338128955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15648544572982764225419303 23472816859474146338128955)
  ·
    refine ⟨35209225289211219507193433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23472816859474146338128955 35209225289211219507193433)
    ·
      refine ⟨26406918966908414630395075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35209225289211219507193433 26406918966908414630395075)
      ·
        refine ⟨39610378450362621945592613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26406918966908414630395075 39610378450362621945592613)
        ·
          refine ⟨7426945959442991614798615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39610378450362621945592613 7426945959442991614798615)
          ·
            refine ⟨11140418939164487422197923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7426945959442991614798615 11140418939164487422197923)
            ·
              refine ⟨16710628408746731133296885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11140418939164487422197923 16710628408746731133296885)
              ·
                refine ⟨1566621413320006043746583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16710628408746731133296885 1566621413320006043746583)
                ·
                  refine ⟨2349932119980009065619875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1566621413320006043746583 2349932119980009065619875)
                  ·
                    refine ⟨3524898179970013598429813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2349932119980009065619875 3524898179970013598429813)
                    ·
                      refine ⟨330459204372188774852795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3524898179970013598429813 330459204372188774852795)
                      ·
                        rfl

theorem cell23_643567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 5].length) (baseStart_643567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_643567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_643567 prefixEnd_643567 := by exact prefixLift 643567
  have htrace : WordTrace (prefixWord ++ tailWord_643567) baseStart_643567 baseEnd_643567 := by
    simpa [prefixWord, tailWord_643567, baseEnd_643567] using wordTrace_append hprefix tailTrace_643567
  have hstable : (prefixWord ++ tailWord_643567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643567).length < 2 ^ (prefixWord ++ tailWord_643567).sum := by decide
  have hdescent : baseEnd_643567 < baseStart_643567 := by decide
  rcases family_descends (prefixWord ++ tailWord_643567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643577 : List Nat := [1, 2, 1, 3, 1, 2, 2, 2, 3, 2, 4]
def baseStart_643577 : Nat := 118140960795 + 643577 * 2 ^ 59
def prefixEnd_643577 : Nat := 4983230072969 + 3 ^ 40 * 643577 * 2
def baseEnd_643577 : Nat := 330464339178733735727749

theorem tailTrace_643577 : CollatzResearch.WordTrace tailWord_643577 prefixEnd_643577 330464339178733735727749 := by
  unfold tailWord_643577
  simp only [CollatzResearch.WordTrace]
  refine ⟨23473181589437918045992985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15648787726291945363995323 23473181589437918045992985)
  ·
    refine ⟨17604886192078438534494739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23473181589437918045992985 17604886192078438534494739)
    ·
      refine ⟨26407329288117657801742109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17604886192078438534494739 26407329288117657801742109)
      ·
        refine ⟨9902748483044121675653291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26407329288117657801742109 9902748483044121675653291)
        ·
          refine ⟨14854122724566182513479937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9902748483044121675653291 14854122724566182513479937)
          ·
            refine ⟨11140592043424636885109953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14854122724566182513479937 11140592043424636885109953)
            ·
              refine ⟨8355444032568477663832465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11140592043424636885109953 8355444032568477663832465)
              ·
                refine ⟨6266583024426358247874349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8355444032568477663832465 6266583024426358247874349)
                ·
                  refine ⟨2349968634159884342952881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6266583024426358247874349 2349968634159884342952881)
                  ·
                    refine ⟨1762476475619913257214661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2349968634159884342952881 1762476475619913257214661)
                    ·
                      refine ⟨330464339178733735727749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1762476475619913257214661 330464339178733735727749)
                      ·
                        rfl

theorem cell23_643577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_643577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_643577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_643577 prefixEnd_643577 := by exact prefixLift 643577
  have htrace : WordTrace (prefixWord ++ tailWord_643577) baseStart_643577 baseEnd_643577 := by
    simpa [prefixWord, tailWord_643577, baseEnd_643577] using wordTrace_append hprefix tailTrace_643577
  have hstable : (prefixWord ++ tailWord_643577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643577).length < 2 ^ (prefixWord ++ tailWord_643577).sum := by decide
  have hdescent : baseEnd_643577 < baseStart_643577 := by decide
  rcases family_descends (prefixWord ++ tailWord_643577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643591 : List Nat := [1, 1, 4, 3, 3, 2, 1, 1, 1, 6]
def baseStart_643591 : Nat := 118140960795 + 643591 * 2 ^ 59
def prefixEnd_643591 : Nat := 4983230072969 + 3 ^ 40 * 643591 * 2
def baseEnd_643591 : Nat := 110157175969298893650895

theorem tailTrace_643591 : CollatzResearch.WordTrace tailWord_643591 prefixEnd_643591 110157175969298893650895 := by
  unfold tailWord_643591
  simp only [CollatzResearch.WordTrace]
  refine ⟨23473692211387198437002627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15649128140924798958001751 23473692211387198437002627)
  ·
    refine ⟨35210538317080797655503941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23473692211387198437002627 35210538317080797655503941)
    ·
      refine ⟨6601975934452649560406989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35210538317080797655503941 6601975934452649560406989)
      ·
        refine ⟨2475740975419743585152621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6601975934452649560406989 2475740975419743585152621)
        ·
          refine ⟨928402865782403844432233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2475740975419743585152621 928402865782403844432233)
          ·
            refine ⟨696302149336802883324175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 928402865782403844432233 696302149336802883324175)
            ·
              refine ⟨1044453224005204324986263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 696302149336802883324175 1044453224005204324986263)
              ·
                refine ⟨1566679836007806487479395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1044453224005204324986263 1566679836007806487479395)
                ·
                  refine ⟨2350019754011709731219093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1566679836007806487479395 2350019754011709731219093)
                  ·
                    refine ⟨110157175969298893650895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2350019754011709731219093 110157175969298893650895)
                    ·
                      rfl

theorem cell23_643591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 6].length) (baseStart_643591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_643591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_643591 prefixEnd_643591 := by exact prefixLift 643591
  have htrace : WordTrace (prefixWord ++ tailWord_643591) baseStart_643591 baseEnd_643591 := by
    simpa [prefixWord, tailWord_643591, baseEnd_643591] using wordTrace_append hprefix tailTrace_643591
  have hstable : (prefixWord ++ tailWord_643591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643591).length < 2 ^ (prefixWord ++ tailWord_643591).sum := by decide
  have hdescent : baseEnd_643591 < baseStart_643591 := by decide
  rcases family_descends (prefixWord ++ tailWord_643591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643598 : List Nat := [4, 1, 1, 2, 3, 1, 2, 2, 3, 2, 2]
def baseStart_643598 : Nat := 118140960795 + 643598 * 2 ^ 59
def prefixEnd_643598 : Nat := 4983230072969 + 3 ^ 40 * 643598 * 2
def baseEnd_643598 : Nat := 330475122272478153565153

theorem tailTrace_643598 : CollatzResearch.WordTrace tailWord_643598 prefixEnd_643598 330475122272478153565153 := by
  unfold tailWord_643598
  simp only [CollatzResearch.WordTrace]
  refine ⟨2934243440295229829063431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15649298348241225755004965 2934243440295229829063431)
  ·
    refine ⟨4401365160442844743595147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2934243440295229829063431 4401365160442844743595147)
    ·
      refine ⟨6602047740664267115392721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4401365160442844743595147 6602047740664267115392721)
      ·
        refine ⟨4951535805498200336544541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6602047740664267115392721 4951535805498200336544541)
        ·
          refine ⟨1856825927061825126204203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4951535805498200336544541 1856825927061825126204203)
          ·
            refine ⟨2785238890592737689306305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1856825927061825126204203 2785238890592737689306305)
            ·
              refine ⟨2088929167944553266979729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2785238890592737689306305 2088929167944553266979729)
              ·
                refine ⟨1566696875958414950234797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2088929167944553266979729 1566696875958414950234797)
                ·
                  refine ⟨587511328484405606338049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1566696875958414950234797 587511328484405606338049)
                  ·
                    refine ⟨440633496363304204753537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 587511328484405606338049 440633496363304204753537)
                    ·
                      refine ⟨330475122272478153565153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 440633496363304204753537 330475122272478153565153)
                      ·
                        rfl

theorem cell23_643598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 3, 2, 2].length) (baseStart_643598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_643598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_643598 prefixEnd_643598 := by exact prefixLift 643598
  have htrace : WordTrace (prefixWord ++ tailWord_643598) baseStart_643598 baseEnd_643598 := by
    simpa [prefixWord, tailWord_643598, baseEnd_643598] using wordTrace_append hprefix tailTrace_643598
  have hstable : (prefixWord ++ tailWord_643598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643598).length < 2 ^ (prefixWord ++ tailWord_643598).sum := by decide
  have hdescent : baseEnd_643598 < baseStart_643598 := by decide
  rcases family_descends (prefixWord ++ tailWord_643598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643641 : List Nat := [1, 2, 1, 5, 1, 1, 2, 2, 3, 3, 2]
def baseStart_643641 : Nat := 118140960795 + 643641 * 2 ^ 59
def prefixEnd_643641 : Nat := 4983230072969 + 3 ^ 40 * 643641 * 2
def baseEnd_643641 : Nat := 330497201940621485327455

theorem tailTrace_643641 : CollatzResearch.WordTrace tailWord_643641 prefixEnd_643641 330497201940621485327455 := by
  unfold tailWord_643641
  simp only [CollatzResearch.WordTrace]
  refine ⟨23475515861206056976322777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15650343907470704650881851 23475515861206056976322777)
  ·
    refine ⟨17606636895904542732242083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23475515861206056976322777 17606636895904542732242083)
    ·
      refine ⟨26409955343856814098363125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17606636895904542732242083 26409955343856814098363125)
      ·
        refine ⟨2475933313486576321721543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26409955343856814098363125 2475933313486576321721543)
        ·
          refine ⟨3713899970229864482582315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2475933313486576321721543 3713899970229864482582315)
          ·
            refine ⟨5570849955344796723873473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3713899970229864482582315 5570849955344796723873473)
            ·
              refine ⟨4178137466508597542905105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5570849955344796723873473 4178137466508597542905105)
              ·
                refine ⟨3133603099881448157178829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4178137466508597542905105 3133603099881448157178829)
                ·
                  refine ⟨1175101162455543058942061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3133603099881448157178829 1175101162455543058942061)
                  ·
                    refine ⟨440662935920828647103273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1175101162455543058942061 440662935920828647103273)
                    ·
                      refine ⟨330497201940621485327455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 440662935920828647103273 330497201940621485327455)
                      ·
                        rfl

theorem cell23_643641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_643641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_643641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_643641 prefixEnd_643641 := by exact prefixLift 643641
  have htrace : WordTrace (prefixWord ++ tailWord_643641) baseStart_643641 baseEnd_643641 := by
    simpa [prefixWord, tailWord_643641, baseEnd_643641] using wordTrace_append hprefix tailTrace_643641
  have hstable : (prefixWord ++ tailWord_643641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643641).length < 2 ^ (prefixWord ++ tailWord_643641).sum := by decide
  have hdescent : baseEnd_643641 < baseStart_643641 := by decide
  rcases family_descends (prefixWord ++ tailWord_643641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643647 : List Nat := [1, 1, 2, 2, 3, 2, 2, 1, 1, 8]
def baseStart_643647 : Nat := 118140960795 + 643647 * 2 ^ 59
def prefixEnd_643647 : Nat := 4983230072969 + 3 ^ 40 * 643647 * 2
def baseEnd_643647 : Nat := 110166760941516153950809

theorem tailTrace_643647 : CollatzResearch.WordTrace tailWord_643647 prefixEnd_643647 110166760941516153950809 := by
  unfold tailWord_643647
  simp only [CollatzResearch.WordTrace]
  refine ⟨23475734699184320001041195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15650489799456213334027463 23475734699184320001041195)
  ·
    refine ⟨35213602048776480001561793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23475734699184320001041195 35213602048776480001561793)
    ·
      refine ⟨26410201536582360001171345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35213602048776480001561793 26410201536582360001171345)
      ·
        refine ⟨19807651152436770000878509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26410201536582360001171345 19807651152436770000878509)
        ·
          refine ⟨7427869182163788750329441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19807651152436770000878509 7427869182163788750329441)
          ·
            refine ⟨5570901886622841562747081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7427869182163788750329441 5570901886622841562747081)
            ·
              refine ⟨4178176414967131172060311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5570901886622841562747081 4178176414967131172060311)
              ·
                refine ⟨6267264622450696758090467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4178176414967131172060311 6267264622450696758090467)
                ·
                  refine ⟨9400896933676045137135701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6267264622450696758090467 9400896933676045137135701)
                  ·
                    refine ⟨110166760941516153950809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 9400896933676045137135701 110166760941516153950809)
                    ·
                      rfl

theorem cell23_643647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 8].length) (baseStart_643647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_643647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_643647 prefixEnd_643647 := by exact prefixLift 643647
  have htrace : WordTrace (prefixWord ++ tailWord_643647) baseStart_643647 baseEnd_643647 := by
    simpa [prefixWord, tailWord_643647, baseEnd_643647] using wordTrace_append hprefix tailTrace_643647
  have hstable : (prefixWord ++ tailWord_643647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643647).length < 2 ^ (prefixWord ++ tailWord_643647).sum := by decide
  have hdescent : baseEnd_643647 < baseStart_643647 := by decide
  rcases family_descends (prefixWord ++ tailWord_643647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643648 : List Nat := [2, 1, 1, 2, 2, 2, 6, 1, 2, 1, 3]
def baseStart_643648 : Nat := 118140960795 + 643648 * 2 ^ 59
def prefixEnd_643648 : Nat := 4983230072969 + 3 ^ 40 * 643648 * 2
def baseEnd_643648 : Nat := 330500796305202957939923

theorem tailTrace_643648 : CollatzResearch.WordTrace tailWord_643648 prefixEnd_643648 330500796305202957939923 := by
  unfold tailWord_643648
  simp only [CollatzResearch.WordTrace]
  refine ⟨11737885586090348585913799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15650514114787131447885065 11737885586090348585913799)
  ·
    refine ⟨17606828379135522878870699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11737885586090348585913799 17606828379135522878870699)
    ·
      refine ⟨26410242568703284318306049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17606828379135522878870699 26410242568703284318306049)
      ·
        refine ⟨19807681926527463238729537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26410242568703284318306049 19807681926527463238729537)
        ·
          refine ⟨14855761444895597429047153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19807681926527463238729537 14855761444895597429047153)
          ·
            refine ⟨11141821083671698071785365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14855761444895597429047153 11141821083671698071785365)
            ·
              refine ⟨522272863297110847114939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11141821083671698071785365 522272863297110847114939)
              ·
                refine ⟨783409294945666270672409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 522272863297110847114939 783409294945666270672409)
                ·
                  refine ⟨587556971209249703004307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 783409294945666270672409 587556971209249703004307)
                  ·
                    refine ⟨881335456813874554506461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 587556971209249703004307 881335456813874554506461)
                    ·
                      refine ⟨330500796305202957939923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 881335456813874554506461 330500796305202957939923)
                      ·
                        rfl

theorem cell23_643648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 1, 2, 1, 3].length) (baseStart_643648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_643648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_643648 prefixEnd_643648 := by exact prefixLift 643648
  have htrace : WordTrace (prefixWord ++ tailWord_643648) baseStart_643648 baseEnd_643648 := by
    simpa [prefixWord, tailWord_643648, baseEnd_643648] using wordTrace_append hprefix tailTrace_643648
  have hstable : (prefixWord ++ tailWord_643648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643648).length < 2 ^ (prefixWord ++ tailWord_643648).sum := by decide
  have hdescent : baseEnd_643648 < baseStart_643648 := by decide
  rcases family_descends (prefixWord ++ tailWord_643648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643658 : List Nat := [3, 1, 2, 1, 1, 4, 3, 2, 1, 3, 2]
def baseStart_643658 : Nat := 118140960795 + 643658 * 2 ^ 59
def prefixEnd_643658 : Nat := 4983230072969 + 3 ^ 40 * 643658 * 2
def baseEnd_643658 : Nat := 330505931111747918814877

theorem tailTrace_643658 : CollatzResearch.WordTrace tailWord_643658 prefixEnd_643658 330505931111747918814877 := by
  unfold tailWord_643658
  simp only [CollatzResearch.WordTrace]
  refine ⟨5869033975536117219922907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15650757268096312586461085 5869033975536117219922907)
  ·
    refine ⟨8803550963304175829884361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5869033975536117219922907 8803550963304175829884361)
    ·
      refine ⟨6602663222478131872413271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8803550963304175829884361 6602663222478131872413271)
      ·
        refine ⟨9903994833717197808619907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6602663222478131872413271 9903994833717197808619907)
        ·
          refine ⟨14855992250575796712929861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9903994833717197808619907 14855992250575796712929861)
          ·
            refine ⟨2785498546982961883674349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14855992250575796712929861 2785498546982961883674349)
            ·
              refine ⟨1044561955118610706377881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2785498546982961883674349 1044561955118610706377881)
              ·
                refine ⟨783421466338958029783411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1044561955118610706377881 783421466338958029783411)
                ·
                  refine ⟨1175132199508437044675117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 783421466338958029783411 1175132199508437044675117)
                  ·
                    refine ⟨440674574815663891753169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1175132199508437044675117 440674574815663891753169)
                    ·
                      refine ⟨330505931111747918814877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 440674574815663891753169 330505931111747918814877)
                      ·
                        rfl

theorem cell23_643658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 2, 1, 3, 2].length) (baseStart_643658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_643658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_643658 prefixEnd_643658 := by exact prefixLift 643658
  have htrace : WordTrace (prefixWord ++ tailWord_643658) baseStart_643658 baseEnd_643658 := by
    simpa [prefixWord, tailWord_643658, baseEnd_643658] using wordTrace_append hprefix tailTrace_643658
  have hstable : (prefixWord ++ tailWord_643658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643658).length < 2 ^ (prefixWord ++ tailWord_643658).sum := by decide
  have hdescent : baseEnd_643658 < baseStart_643658 := by decide
  rcases family_descends (prefixWord ++ tailWord_643658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643671 : List Nat := [1, 1, 3, 2, 2, 2, 3, 2, 1, 4, 2]
def baseStart_643671 : Nat := 118140960795 + 643671 * 2 ^ 59
def prefixEnd_643671 : Nat := 4983230072969 + 3 ^ 40 * 643671 * 2
def baseEnd_643671 : Nat := 330512606360256367952317

theorem tailTrace_643671 : CollatzResearch.WordTrace tailWord_643671 prefixEnd_643671 330512606360256367952317 := by
  unfold tailWord_643671
  simp only [CollatzResearch.WordTrace]
  refine ⟨23476610051097372099914867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15651073367398248066609911 23476610051097372099914867)
  ·
    refine ⟨35214915076646058149872301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23476610051097372099914867 35214915076646058149872301)
    ·
      refine ⟨13205593153742271806202113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35214915076646058149872301 13205593153742271806202113)
      ·
        refine ⟨9904194865306703854651585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13205593153742271806202113 9904194865306703854651585)
        ·
          refine ⟨7428146148980027890988689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9904194865306703854651585 7428146148980027890988689)
          ·
            refine ⟨5571109611735020918241517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7428146148980027890988689 5571109611735020918241517)
            ·
              refine ⟨2089166104400632844340569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5571109611735020918241517 2089166104400632844340569)
              ·
                refine ⟨1566874578300474633255427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2089166104400632844340569 1566874578300474633255427)
                ·
                  refine ⟨2350311867450711949883141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1566874578300474633255427 2350311867450711949883141)
                  ·
                    refine ⟨440683475147008490603089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2350311867450711949883141 440683475147008490603089)
                    ·
                      refine ⟨330512606360256367952317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 440683475147008490603089 330512606360256367952317)
                      ·
                        rfl

theorem cell23_643671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 4, 2].length) (baseStart_643671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_643671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_643671 prefixEnd_643671 := by exact prefixLift 643671
  have htrace : WordTrace (prefixWord ++ tailWord_643671) baseStart_643671 baseEnd_643671 := by
    simpa [prefixWord, tailWord_643671, baseEnd_643671] using wordTrace_append hprefix tailTrace_643671
  have hstable : (prefixWord ++ tailWord_643671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643671).length < 2 ^ (prefixWord ++ tailWord_643671).sum := by decide
  have hdescent : baseEnd_643671 < baseStart_643671 := by decide
  rcases family_descends (prefixWord ++ tailWord_643671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643682 : List Nat := [3, 3, 2, 3, 1, 1, 2, 2, 2, 1, 3]
def baseStart_643682 : Nat := 118140960795 + 643682 * 2 ^ 59
def prefixEnd_643682 : Nat := 4983230072969 + 3 ^ 40 * 643682 * 2
def baseEnd_643682 : Nat := 330518254647455824914767

theorem tailTrace_643682 : CollatzResearch.WordTrace tailWord_643682 prefixEnd_643682 330518254647455824914767 := by
  unfold tailWord_643682
  simp only [CollatzResearch.WordTrace]
  refine ⟨5869252813514380244641325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15651340836038347319043533 5869252813514380244641325)
  ·
    refine ⟨2200969805067892591740497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5869252813514380244641325 2200969805067892591740497)
    ·
      refine ⟨1650727353800919443805373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2200969805067892591740497 1650727353800919443805373)
      ·
        refine ⟨619022757675344791427015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1650727353800919443805373 619022757675344791427015)
        ·
          refine ⟨928534136513017187140523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 619022757675344791427015 928534136513017187140523)
          ·
            refine ⟨1392801204769525780710785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 928534136513017187140523 1392801204769525780710785)
            ·
              refine ⟨1044600903577144335533089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1392801204769525780710785 1044600903577144335533089)
              ·
                refine ⟨783450677682858251649817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1044600903577144335533089 783450677682858251649817)
                ·
                  refine ⟨587588008262143688737363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 783450677682858251649817 587588008262143688737363)
                  ·
                    refine ⟨881382012393215533106045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 587588008262143688737363 881382012393215533106045)
                    ·
                      refine ⟨330518254647455824914767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 881382012393215533106045 330518254647455824914767)
                      ·
                        rfl

theorem cell23_643682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_643682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_643682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_643682 prefixEnd_643682 := by exact prefixLift 643682
  have htrace : WordTrace (prefixWord ++ tailWord_643682) baseStart_643682 baseEnd_643682 := by
    simpa [prefixWord, tailWord_643682, baseEnd_643682] using wordTrace_append hprefix tailTrace_643682
  have hstable : (prefixWord ++ tailWord_643682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643682).length < 2 ^ (prefixWord ++ tailWord_643682).sum := by decide
  have hdescent : baseEnd_643682 < baseStart_643682 := by decide
  rcases family_descends (prefixWord ++ tailWord_643682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643684 : List Nat := [2, 3, 1, 1, 2, 2, 2, 2, 2, 2, 4]
def baseStart_643684 : Nat := 118140960795 + 643684 * 2 ^ 59
def prefixEnd_643684 : Nat := 4983230072969 + 3 ^ 40 * 643684 * 2
def baseEnd_643684 : Nat := 330519281608764817089757

theorem tailTrace_643684 : CollatzResearch.WordTrace tailWord_643684 prefixEnd_643684 330519281608764817089757 := by
  unfold tailWord_643684
  simp only [CollatzResearch.WordTrace]
  refine ⟨11738542100025137660069053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15651389466700183546758737 11738542100025137660069053)
  ·
    refine ⟨4401953287509426622525895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11738542100025137660069053 4401953287509426622525895)
    ·
      refine ⟨6602929931264139933788843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4401953287509426622525895 6602929931264139933788843)
      ·
        refine ⟨9904394896896209900683265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6602929931264139933788843 9904394896896209900683265)
        ·
          refine ⟨7428296172672157425512449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9904394896896209900683265 7428296172672157425512449)
          ·
            refine ⟨5571222129504118069134337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7428296172672157425512449 5571222129504118069134337)
            ·
              refine ⟨4178416597128088551850753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5571222129504118069134337 4178416597128088551850753)
              ·
                refine ⟨3133812447846066413888065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4178416597128088551850753 3133812447846066413888065)
                ·
                  refine ⟨2350359335884549810416049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3133812447846066413888065 2350359335884549810416049)
                  ·
                    refine ⟨1762769501913412357812037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2350359335884549810416049 1762769501913412357812037)
                    ·
                      refine ⟨330519281608764817089757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1762769501913412357812037 330519281608764817089757)
                      ·
                        rfl

theorem cell23_643684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_643684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_643684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_643684 prefixEnd_643684 := by exact prefixLift 643684
  have htrace : WordTrace (prefixWord ++ tailWord_643684) baseStart_643684 baseEnd_643684 := by
    simpa [prefixWord, tailWord_643684, baseEnd_643684] using wordTrace_append hprefix tailTrace_643684
  have hstable : (prefixWord ++ tailWord_643684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643684).length < 2 ^ (prefixWord ++ tailWord_643684).sum := by decide
  have hdescent : baseEnd_643684 < baseStart_643684 := by decide
  rcases family_descends (prefixWord ++ tailWord_643684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643697 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 1, 3, 8]
def baseStart_643697 : Nat := 118140960795 + 643697 * 2 ^ 59
def prefixEnd_643697 : Nat := 4983230072969 + 3 ^ 40 * 643697 * 2
def baseEnd_643697 : Nat := 330525956857273266227197

theorem tailTrace_643697 : CollatzResearch.WordTrace tailWord_643697 prefixEnd_643697 330525956857273266227197 := by
  unfold tailWord_643697
  simp only [CollatzResearch.WordTrace]
  refine ⟨23477558349003178540361345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15651705566002119026907563 23477558349003178540361345)
  ·
    refine ⟨17608168761752383905271009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23477558349003178540361345 17608168761752383905271009)
    ·
      refine ⟨13206126571314287928953257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17608168761752383905271009 13206126571314287928953257)
      ·
        refine ⟨9904594928485715946714943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13206126571314287928953257 9904594928485715946714943)
        ·
          refine ⟨14856892392728573920072415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9904594928485715946714943 14856892392728573920072415)
          ·
            refine ⟨22285338589092860880108623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14856892392728573920072415 22285338589092860880108623)
            ·
              refine ⟨33428007883639291320162935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22285338589092860880108623 33428007883639291320162935)
              ·
                refine ⟨50142011825458936980244403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33428007883639291320162935 50142011825458936980244403)
                ·
                  refine ⟨75213017738188405470366605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50142011825458936980244403 75213017738188405470366605)
                  ·
                    refine ⟨28204881651820652051387477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 75213017738188405470366605 28204881651820652051387477)
                    ·
                      refine ⟨330525956857273266227197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 28204881651820652051387477 330525956857273266227197)
                      ·
                        rfl

theorem cell23_643697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_643697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_643697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_643697 prefixEnd_643697 := by exact prefixLift 643697
  have htrace : WordTrace (prefixWord ++ tailWord_643697) baseStart_643697 baseEnd_643697 := by
    simpa [prefixWord, tailWord_643697, baseEnd_643697] using wordTrace_append hprefix tailTrace_643697
  have hstable : (prefixWord ++ tailWord_643697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643697).length < 2 ^ (prefixWord ++ tailWord_643697).sum := by decide
  have hdescent : baseEnd_643697 < baseStart_643697 := by decide
  rcases family_descends (prefixWord ++ tailWord_643697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643704 : List Nat := [2, 1, 2, 1, 1, 1, 2, 5, 2, 3, 3]
def baseStart_643704 : Nat := 118140960795 + 643704 * 2 ^ 59
def prefixEnd_643704 : Nat := 4983230072969 + 3 ^ 40 * 643704 * 2
def baseEnd_643704 : Nat := 330529551221854738839665

theorem tailTrace_643704 : CollatzResearch.WordTrace tailWord_643704 prefixEnd_643704 330529551221854738839665 := by
  unfold tailWord_643704
  simp only [CollatzResearch.WordTrace]
  refine ⟨11738906829988909367933083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15651875773318545823910777 11738906829988909367933083)
  ·
    refine ⟨17608360244983364051899625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11738906829988909367933083 17608360244983364051899625)
    ·
      refine ⟨13206270183737523038924719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17608360244983364051899625 13206270183737523038924719)
      ·
        refine ⟨19809405275606284558387079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13206270183737523038924719 19809405275606284558387079)
        ·
          refine ⟨29714107913409426837580619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19809405275606284558387079 29714107913409426837580619)
          ·
            refine ⟨44571161870114140256370929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29714107913409426837580619 44571161870114140256370929)
            ·
              refine ⟨33428371402585605192278197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44571161870114140256370929 33428371402585605192278197)
              ·
                refine ⟨3133909818992400486776081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33428371402585605192278197 3133909818992400486776081)
                ·
                  refine ⟨2350432364244300365082061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3133909818992400486776081 2350432364244300365082061)
                  ·
                    refine ⟨881412136591612636905773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2350432364244300365082061 881412136591612636905773)
                    ·
                      refine ⟨330529551221854738839665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 881412136591612636905773 330529551221854738839665)
                      ·
                        rfl

theorem cell23_643704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 2, 3, 3].length) (baseStart_643704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_643704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_643704 prefixEnd_643704 := by exact prefixLift 643704
  have htrace : WordTrace (prefixWord ++ tailWord_643704) baseStart_643704 baseEnd_643704 := by
    simpa [prefixWord, tailWord_643704, baseEnd_643704] using wordTrace_append hprefix tailTrace_643704
  have hstable : (prefixWord ++ tailWord_643704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643704).length < 2 ^ (prefixWord ++ tailWord_643704).sum := by decide
  have hdescent : baseEnd_643704 < baseStart_643704 := by decide
  rcases family_descends (prefixWord ++ tailWord_643704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643724 : List Nat := [2, 2, 1, 2, 1, 1, 2, 5, 2, 5]
def baseStart_643724 : Nat := 118140960795 + 643724 * 2 ^ 59
def prefixEnd_643724 : Nat := 4983230072969 + 3 ^ 40 * 643724 * 2
def baseEnd_643724 : Nat := 110179940278314886863191

theorem tailTrace_643724 : CollatzResearch.WordTrace tailWord_643724 prefixEnd_643724 110179940278314886863191 := by
  unfold tailWord_643724
  simp only [CollatzResearch.WordTrace]
  refine ⟨11739271559952681075797113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15652362079936908101062817 11739271559952681075797113)
  ·
    refine ⟨8804453669964510806847835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11739271559952681075797113 8804453669964510806847835)
    ·
      refine ⟨13206680504946766210271753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8804453669964510806847835 13206680504946766210271753)
      ·
        refine ⟨9905010378710074657703815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13206680504946766210271753 9905010378710074657703815)
        ·
          refine ⟨14857515568065111986555723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9905010378710074657703815 14857515568065111986555723)
          ·
            refine ⟨22286273352097667979833585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14857515568065111986555723 22286273352097667979833585)
            ·
              refine ⟨16714705014073250984875189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22286273352097667979833585 16714705014073250984875189)
              ·
                refine ⟨1567003595069367279832049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16714705014073250984875189 1567003595069367279832049)
                ·
                  refine ⟨1175252696302025459874037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1567003595069367279832049 1175252696302025459874037)
                  ·
                    refine ⟨110179940278314886863191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1175252696302025459874037 110179940278314886863191)
                    ·
                      rfl

theorem cell23_643724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 2, 5].length) (baseStart_643724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_643724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_643724 prefixEnd_643724 := by exact prefixLift 643724
  have htrace : WordTrace (prefixWord ++ tailWord_643724) baseStart_643724 baseEnd_643724 := by
    simpa [prefixWord, tailWord_643724, baseEnd_643724] using wordTrace_append hprefix tailTrace_643724
  have hstable : (prefixWord ++ tailWord_643724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643724).length < 2 ^ (prefixWord ++ tailWord_643724).sum := by decide
  have hdescent : baseEnd_643724 < baseStart_643724 := by decide
  rcases family_descends (prefixWord ++ tailWord_643724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643784 : List Nat := [2, 1, 3, 1, 2, 3, 1, 2, 8]
def baseStart_643784 : Nat := 118140960795 + 643784 * 2 ^ 59
def prefixEnd_643784 : Nat := 4983230072969 + 3 ^ 40 * 643784 * 2
def baseEnd_643784 : Nat := 36730069963801602871033

theorem tailTrace_643784 : CollatzResearch.WordTrace tailWord_643784 prefixEnd_643784 36730069963801602871033 := by
  unfold tailWord_643784
  simp only [CollatzResearch.WordTrace]
  refine ⟨11740365749843996199389203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15653820999791994932518937 11740365749843996199389203)
  ·
    refine ⟨17610548624765994299083805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11740365749843996199389203 17610548624765994299083805)
    ·
      refine ⟨6603955734287247862156427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17610548624765994299083805 6603955734287247862156427)
      ·
        refine ⟨9905933601430871793234641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6603955734287247862156427 9905933601430871793234641)
        ·
          refine ⟨7429450201073153844925981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9905933601430871793234641 7429450201073153844925981)
          ·
            refine ⟨2786043825402432691847243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7429450201073153844925981 2786043825402432691847243)
            ·
              refine ⟨4179065738103649037770865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2786043825402432691847243 4179065738103649037770865)
              ·
                refine ⟨3134299303577736778328149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4179065738103649037770865 3134299303577736778328149)
                ·
                  refine ⟨36730069963801602871033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3134299303577736778328149 36730069963801602871033)
                  ·
                    rfl

theorem cell23_643784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 8].length) (baseStart_643784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_643784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_643784 prefixEnd_643784 := by exact prefixLift 643784
  have htrace : WordTrace (prefixWord ++ tailWord_643784) baseStart_643784 baseEnd_643784 := by
    simpa [prefixWord, tailWord_643784, baseEnd_643784] using wordTrace_append hprefix tailTrace_643784
  have hstable : (prefixWord ++ tailWord_643784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643784).length < 2 ^ (prefixWord ++ tailWord_643784).sum := by decide
  have hdescent : baseEnd_643784 < baseStart_643784 := by decide
  rcases family_descends (prefixWord ++ tailWord_643784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643928 : List Nat := [2, 1, 2, 2, 1, 1, 1, 3, 5, 3, 2]
def baseStart_643928 : Nat := 118140960795 + 643928 * 2 ^ 59
def prefixEnd_643928 : Nat := 4983230072969 + 3 ^ 40 * 643928 * 2
def baseEnd_643928 : Nat := 330644570888461862438635

theorem tailTrace_643928 : CollatzResearch.WordTrace tailWord_643928 prefixEnd_643928 330644570888461862438635 := by
  unfold tailWord_643928
  simp only [CollatzResearch.WordTrace]
  refine ⟨11742991805583152496010219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15657322407444203328013625 11742991805583152496010219)
  ·
    refine ⟨17614487708374728744015329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11742991805583152496010219 17614487708374728744015329)
    ·
      refine ⟨13210865781281046558011497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17614487708374728744015329 13210865781281046558011497)
      ·
        refine ⟨9908149335960784918508623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13210865781281046558011497 9908149335960784918508623)
        ·
          refine ⟨14862224003941177377762935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9908149335960784918508623 14862224003941177377762935)
          ·
            refine ⟨22293336005911766066644403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14862224003941177377762935 22293336005911766066644403)
            ·
              refine ⟨33440004008867649099966605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22293336005911766066644403 33440004008867649099966605)
              ·
                refine ⟨12540001503325368412487477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33440004008867649099966605 12540001503325368412487477)
                ·
                  refine ⟨1175625140936753288670701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12540001503325368412487477 1175625140936753288670701)
                  ·
                    refine ⟨440859427851282483251513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1175625140936753288670701 440859427851282483251513)
                    ·
                      refine ⟨330644570888461862438635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 440859427851282483251513 330644570888461862438635)
                      ·
                        rfl

theorem cell23_643928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 5, 3, 2].length) (baseStart_643928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_643928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_643928 prefixEnd_643928 := by exact prefixLift 643928
  have htrace : WordTrace (prefixWord ++ tailWord_643928) baseStart_643928 baseEnd_643928 := by
    simpa [prefixWord, tailWord_643928, baseEnd_643928] using wordTrace_append hprefix tailTrace_643928
  have hstable : (prefixWord ++ tailWord_643928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643928).length < 2 ^ (prefixWord ++ tailWord_643928).sum := by decide
  have hdescent : baseEnd_643928 < baseStart_643928 := by decide
  rcases family_descends (prefixWord ++ tailWord_643928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643941 : List Nat := [1, 3, 1, 3, 1, 1, 2, 2, 2, 3, 4]
def baseStart_643941 : Nat := 118140960795 + 643941 * 2 ^ 59
def prefixEnd_643941 : Nat := 4983230072969 + 3 ^ 40 * 643941 * 2
def baseEnd_643941 : Nat := 330651246136970311576075

theorem tailTrace_643941 : CollatzResearch.WordTrace tailWord_643941 prefixEnd_643941 330651246136970311576075 := by
  unfold tailWord_643941
  simp only [CollatzResearch.WordTrace]
  refine ⟨23486457760119208212243677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15657638506746138808162451 23486457760119208212243677)
  ·
    refine ⟨8807421660044703079591379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23486457760119208212243677 8807421660044703079591379)
    ·
      refine ⟨13211132490067054619387069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8807421660044703079591379 13211132490067054619387069)
      ·
        refine ⟨4954174683775145482270151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13211132490067054619387069 4954174683775145482270151)
        ·
          refine ⟨7431262025662718223405227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4954174683775145482270151 7431262025662718223405227)
          ·
            refine ⟨11146893038494077335107841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7431262025662718223405227 11146893038494077335107841)
            ·
              refine ⟨8360169778870558001330881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11146893038494077335107841 8360169778870558001330881)
              ·
                refine ⟨6270127334152918500998161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8360169778870558001330881 6270127334152918500998161)
                ·
                  refine ⟨4702595500614688875748621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6270127334152918500998161 4702595500614688875748621)
                  ·
                    refine ⟨1763473312730508328405733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4702595500614688875748621 1763473312730508328405733)
                    ·
                      refine ⟨330651246136970311576075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1763473312730508328405733 330651246136970311576075)
                      ·
                        rfl

theorem cell23_643941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_643941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_643941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_643941 prefixEnd_643941 := by exact prefixLift 643941
  have htrace : WordTrace (prefixWord ++ tailWord_643941) baseStart_643941 baseEnd_643941 := by
    simpa [prefixWord, tailWord_643941, baseEnd_643941] using wordTrace_append hprefix tailTrace_643941
  have hstable : (prefixWord ++ tailWord_643941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643941).length < 2 ^ (prefixWord ++ tailWord_643941).sum := by decide
  have hdescent : baseEnd_643941 < baseStart_643941 := by decide
  rcases family_descends (prefixWord ++ tailWord_643941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643961 : List Nat := [1, 2, 1, 3, 2, 3, 1, 1, 1, 3, 5]
def baseStart_643961 : Nat := 118140960795 + 643961 * 2 ^ 59
def prefixEnd_643961 : Nat := 4983230072969 + 3 ^ 40 * 643961 * 2
def baseEnd_643961 : Nat := 330661515750060233325983

theorem tailTrace_643961 : CollatzResearch.WordTrace tailWord_643961 prefixEnd_643961 330661515750060233325983 := by
  unfold tailWord_643961
  simp only [CollatzResearch.WordTrace]
  refine ⟨23487187220046751627971737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15658124813364501085314491 23487187220046751627971737)
  ·
    refine ⟨17615390415035063720978803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23487187220046751627971737 17615390415035063720978803)
    ·
      refine ⟨26423085622552595581468205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17615390415035063720978803 26423085622552595581468205)
      ·
        refine ⟨9908657108457223343050577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26423085622552595581468205 9908657108457223343050577)
        ·
          refine ⟨7431492831342917507287933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9908657108457223343050577 7431492831342917507287933)
          ·
            refine ⟨2786809811753594065232975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7431492831342917507287933 2786809811753594065232975)
            ·
              refine ⟨4180214717630391097849463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2786809811753594065232975 4180214717630391097849463)
              ·
                refine ⟨6270322076445586646774195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4180214717630391097849463 6270322076445586646774195)
                ·
                  refine ⟨9405483114668379970161293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6270322076445586646774195 9405483114668379970161293)
                  ·
                    refine ⟨3527056168000642488810485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9405483114668379970161293 3527056168000642488810485)
                    ·
                      refine ⟨330661515750060233325983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3527056168000642488810485 330661515750060233325983)
                      ·
                        rfl

theorem cell23_643961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_643961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_643961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_643961 prefixEnd_643961 := by exact prefixLift 643961
  have htrace : WordTrace (prefixWord ++ tailWord_643961) baseStart_643961 baseEnd_643961 := by
    simpa [prefixWord, tailWord_643961, baseEnd_643961] using wordTrace_append hprefix tailTrace_643961
  have hstable : (prefixWord ++ tailWord_643961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643961).length < 2 ^ (prefixWord ++ tailWord_643961).sum := by decide
  have hdescent : baseEnd_643961 < baseStart_643961 := by decide
  rcases family_descends (prefixWord ++ tailWord_643961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643970 : List Nat := [3, 4, 2, 2, 1, 1, 3, 2, 1, 2, 2]
def baseStart_643970 : Nat := 118140960795 + 643970 * 2 ^ 59
def prefixEnd_643970 : Nat := 4983230072969 + 3 ^ 40 * 643970 * 2
def baseEnd_643970 : Nat := 330666137075950698113443

theorem tailTrace_643970 : CollatzResearch.WordTrace tailWord_643970 prefixEnd_643970 330666137075950698113443 := by
  unfold tailWord_643970
  simp only [CollatzResearch.WordTrace]
  refine ⟨5871878869253536541262341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15658343651342764110032909 5871878869253536541262341)
  ·
    refine ⟨1100977287985038101486689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5871878869253536541262341 1100977287985038101486689)
    ·
      refine ⟨825732965988778576115017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1100977287985038101486689 825732965988778576115017)
      ·
        refine ⟨619299724491583932086263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 825732965988778576115017 619299724491583932086263)
        ·
          refine ⟨928949586737375898129395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 619299724491583932086263 928949586737375898129395)
          ·
            refine ⟨1393424380106063847194093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 928949586737375898129395 1393424380106063847194093)
            ·
              refine ⟨522534142539773942697785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1393424380106063847194093 522534142539773942697785)
              ·
                refine ⟨391900606904830457023339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 522534142539773942697785 391900606904830457023339)
                ·
                  refine ⟨587850910357245685535009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 391900606904830457023339 587850910357245685535009)
                  ·
                    refine ⟨440888182767934264151257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 587850910357245685535009 440888182767934264151257)
                    ·
                      refine ⟨330666137075950698113443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 440888182767934264151257 330666137075950698113443)
                      ·
                        rfl

theorem cell23_643970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_643970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_643970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_643970 prefixEnd_643970 := by exact prefixLift 643970
  have htrace : WordTrace (prefixWord ++ tailWord_643970) baseStart_643970 baseEnd_643970 := by
    simpa [prefixWord, tailWord_643970, baseEnd_643970] using wordTrace_append hprefix tailTrace_643970
  have hstable : (prefixWord ++ tailWord_643970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643970).length < 2 ^ (prefixWord ++ tailWord_643970).sum := by decide
  have hdescent : baseEnd_643970 < baseStart_643970 := by decide
  rcases family_descends (prefixWord ++ tailWord_643970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643986 : List Nat := [3, 2, 3, 2, 2, 2, 2, 1, 2, 1, 3]
def baseStart_643986 : Nat := 118140960795 + 643986 * 2 ^ 59
def prefixEnd_643986 : Nat := 4983230072969 + 3 ^ 40 * 643986 * 2
def baseEnd_643986 : Nat := 330674352766422635513369

theorem tailTrace_643986 : CollatzResearch.WordTrace tailWord_643986 prefixEnd_643986 330674352766422635513369 := by
  unfold tailWord_643986
  simp only [CollatzResearch.WordTrace]
  refine ⟨5872024761239045224407953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15658732696637453931754541 5872024761239045224407953)
  ·
    refine ⟨4404018570929283918305965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5872024761239045224407953 4404018570929283918305965)
    ·
      refine ⟨1651506964098481469364737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4404018570929283918305965 1651506964098481469364737)
      ·
        refine ⟨1238630223073861102023553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1651506964098481469364737 1238630223073861102023553)
        ·
          refine ⟨928972667305395826517665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1238630223073861102023553 928972667305395826517665)
          ·
            refine ⟨696729500479046869888249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 928972667305395826517665 696729500479046869888249)
            ·
              refine ⟨522547125359285152416187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 696729500479046869888249 522547125359285152416187)
              ·
                refine ⟨783820688038927728624281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 522547125359285152416187 783820688038927728624281)
                ·
                  refine ⟨587865516029195796468211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 783820688038927728624281 587865516029195796468211)
                  ·
                    refine ⟨881798274043793694702317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 587865516029195796468211 881798274043793694702317)
                    ·
                      refine ⟨330674352766422635513369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 881798274043793694702317 330674352766422635513369)
                      ·
                        rfl

theorem cell23_643986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_643986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_643986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_643986 prefixEnd_643986 := by exact prefixLift 643986
  have htrace : WordTrace (prefixWord ++ tailWord_643986) baseStart_643986 baseEnd_643986 := by
    simpa [prefixWord, tailWord_643986, baseEnd_643986] using wordTrace_append hprefix tailTrace_643986
  have hstable : (prefixWord ++ tailWord_643986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643986).length < 2 ^ (prefixWord ++ tailWord_643986).sum := by decide
  have hdescent : baseEnd_643986 < baseStart_643986 := by decide
  rcases family_descends (prefixWord ++ tailWord_643986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643988 : List Nat := [2, 4, 2, 1, 1, 1, 2, 1, 1, 4, 4]
def baseStart_643988 : Nat := 118140960795 + 643988 * 2 ^ 59
def prefixEnd_643988 : Nat := 4983230072969 + 3 ^ 40 * 643988 * 2
def baseEnd_643988 : Nat := 330675379727731627688359

theorem tailTrace_643988 : CollatzResearch.WordTrace tailWord_643988 prefixEnd_643988 330675379727731627688359 := by
  unfold tailWord_643988
  simp only [CollatzResearch.WordTrace]
  refine ⟨11744085995474467619602309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15658781327299290159469745 11744085995474467619602309)
  ·
    refine ⟨2202016124151462678675433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11744085995474467619602309 2202016124151462678675433)
    ·
      refine ⟨1651512093113597009006575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2202016124151462678675433 1651512093113597009006575)
      ·
        refine ⟨2477268139670395513509863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1651512093113597009006575 2477268139670395513509863)
        ·
          refine ⟨3715902209505593270264795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2477268139670395513509863 3715902209505593270264795)
          ·
            refine ⟨5573853314258389905397193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3715902209505593270264795 5573853314258389905397193)
            ·
              refine ⟨4180389985693792429047895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5573853314258389905397193 4180389985693792429047895)
              ·
                refine ⟨6270584978540688643571843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4180389985693792429047895 6270584978540688643571843)
                ·
                  refine ⟨9405877467811032965357765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6270584978540688643571843 9405877467811032965357765)
                  ·
                    refine ⟨1763602025214568681004581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9405877467811032965357765 1763602025214568681004581)
                    ·
                      refine ⟨330675379727731627688359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1763602025214568681004581 330675379727731627688359)
                      ·
                        rfl

theorem cell23_643988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_643988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_643988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_643988 prefixEnd_643988 := by exact prefixLift 643988
  have htrace : WordTrace (prefixWord ++ tailWord_643988) baseStart_643988 baseEnd_643988 := by
    simpa [prefixWord, tailWord_643988, baseEnd_643988] using wordTrace_append hprefix tailTrace_643988
  have hstable : (prefixWord ++ tailWord_643988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643988).length < 2 ^ (prefixWord ++ tailWord_643988).sum := by decide
  have hdescent : baseEnd_643988 < baseStart_643988 := by decide
  rcases family_descends (prefixWord ++ tailWord_643988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_643996 : List Nat := [2, 2, 3, 3, 3, 1, 1, 2, 1, 3, 2]
def baseStart_643996 : Nat := 118140960795 + 643996 * 2 ^ 59
def prefixEnd_643996 : Nat := 4983230072969 + 3 ^ 40 * 643996 * 2
def baseEnd_643996 : Nat := 330679487572967596388323

theorem tailTrace_643996 : CollatzResearch.WordTrace tailWord_643996 prefixEnd_643996 330679487572967596388323 := by
  unfold tailWord_643996
  simp only [CollatzResearch.WordTrace]
  refine ⟨11744231887459976302747921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15658975849946635070330561 11744231887459976302747921)
  ·
    refine ⟨8808173915594982227060941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11744231887459976302747921 8808173915594982227060941)
    ·
      refine ⟨3303065218348118335147853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8808173915594982227060941 3303065218348118335147853)
      ·
        refine ⟨1238649456880544375680445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3303065218348118335147853 1238649456880544375680445)
        ·
          refine ⟨464493546330204140880167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1238649456880544375680445 464493546330204140880167)
          ·
            refine ⟨696740319495306211320251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 464493546330204140880167 696740319495306211320251)
            ·
              refine ⟨1045110479242959316980377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 696740319495306211320251 1045110479242959316980377)
              ·
                refine ⟨783832859432219487735283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1045110479242959316980377 783832859432219487735283)
                ·
                  refine ⟨1175749289148329231602925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 783832859432219487735283 1175749289148329231602925)
                  ·
                    refine ⟨440905983430623461851097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1175749289148329231602925 440905983430623461851097)
                    ·
                      refine ⟨330679487572967596388323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 440905983430623461851097 330679487572967596388323)
                      ·
                        rfl

theorem cell23_643996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_643996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_643996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_643996 prefixEnd_643996 := by exact prefixLift 643996
  have htrace : WordTrace (prefixWord ++ tailWord_643996) baseStart_643996 baseEnd_643996 := by
    simpa [prefixWord, tailWord_643996, baseEnd_643996] using wordTrace_append hprefix tailTrace_643996
  have hstable : (prefixWord ++ tailWord_643996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_643996).length < 2 ^ (prefixWord ++ tailWord_643996).sum := by decide
  have hdescent : baseEnd_643996 < baseStart_643996 := by decide
  rcases family_descends (prefixWord ++ tailWord_643996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644011 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 6, 5]
def baseStart_644011 : Nat := 118140960795 + 644011 * 2 ^ 59
def prefixEnd_644011 : Nat := 4983230072969 + 3 ^ 40 * 644011 * 2
def baseEnd_644011 : Nat := 110229063260928345900251

theorem tailTrace_644011 : CollatzResearch.WordTrace tailWord_644011 prefixEnd_644011 110229063260928345900251 := by
  unfold tailWord_644011
  simp only [CollatzResearch.WordTrace]
  refine ⟨23489010869865610167291887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15659340579910406778194591 23489010869865610167291887)
  ·
    refine ⟨35233516304798415250937831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23489010869865610167291887 35233516304798415250937831)
    ·
      refine ⟨52850274457197622876406747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35233516304798415250937831 52850274457197622876406747)
      ·
        refine ⟨79275411685796434314610121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52850274457197622876406747 79275411685796434314610121)
        ·
          refine ⟨59456558764347325735957591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79275411685796434314610121 59456558764347325735957591)
          ·
            refine ⟨89184838146520988603936387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59456558764347325735957591 89184838146520988603936387)
            ·
              refine ⟨133777257219781482905904581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89184838146520988603936387 133777257219781482905904581)
              ·
                refine ⟨25083235728709028044857109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 133777257219781482905904581 25083235728709028044857109)
                ·
                  refine ⟨1175776674783235689602677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 25083235728709028044857109 1175776674783235689602677)
                  ·
                    refine ⟨110229063260928345900251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1175776674783235689602677 110229063260928345900251)
                    ·
                      rfl

theorem cell23_644011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 6, 5].length) (baseStart_644011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_644011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_644011 prefixEnd_644011 := by exact prefixLift 644011
  have htrace : WordTrace (prefixWord ++ tailWord_644011) baseStart_644011 baseEnd_644011 := by
    simpa [prefixWord, tailWord_644011, baseEnd_644011] using wordTrace_append hprefix tailTrace_644011
  have hstable : (prefixWord ++ tailWord_644011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644011).length < 2 ^ (prefixWord ++ tailWord_644011).sum := by decide
  have hdescent : baseEnd_644011 < baseStart_644011 := by decide
  rcases family_descends (prefixWord ++ tailWord_644011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644032 : List Nat := [2, 1, 1, 2, 3, 5, 2, 2, 5]
def baseStart_644032 : Nat := 118140960795 + 644032 * 2 ^ 59
def prefixEnd_644032 : Nat := 4983230072969 + 3 ^ 40 * 644032 * 2
def baseEnd_644032 : Nat := 36744219208503272837573

theorem tailTrace_644032 : CollatzResearch.WordTrace tailWord_644032 prefixEnd_644032 36744219208503272837573 := by
  unfold tailWord_644032
  simp only [CollatzResearch.WordTrace]
  refine ⟨11744888401394765376903175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15659851201859687169204233 11744888401394765376903175)
  ·
    refine ⟨17617332602092148065354763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11744888401394765376903175 17617332602092148065354763)
    ·
      refine ⟨26425998903138222098032145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17617332602092148065354763 26425998903138222098032145)
      ·
        refine ⟨19819499177353666573524109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26425998903138222098032145 19819499177353666573524109)
        ·
          refine ⟨7432312191507624965071541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19819499177353666573524109 7432312191507624965071541)
          ·
            refine ⟨696779267953839840475457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7432312191507624965071541 696779267953839840475457)
            ·
              refine ⟨522584450965379880356593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 696779267953839840475457 522584450965379880356593)
              ·
                refine ⟨391938338224034910267445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 522584450965379880356593 391938338224034910267445)
                ·
                  refine ⟨36744219208503272837573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 391938338224034910267445 36744219208503272837573)
                  ·
                    rfl

theorem cell23_644032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 2, 5].length) (baseStart_644032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_644032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_644032 prefixEnd_644032 := by exact prefixLift 644032
  have htrace : WordTrace (prefixWord ++ tailWord_644032) baseStart_644032 baseEnd_644032 := by
    simpa [prefixWord, tailWord_644032, baseEnd_644032] using wordTrace_append hprefix tailTrace_644032
  have hstable : (prefixWord ++ tailWord_644032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644032).length < 2 ^ (prefixWord ++ tailWord_644032).sum := by decide
  have hdescent : baseEnd_644032 < baseStart_644032 := by decide
  rcases family_descends (prefixWord ++ tailWord_644032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644092 : List Nat := [2, 2, 2, 1, 2, 3, 2, 4, 1, 4]
def baseStart_644092 : Nat := 118140960795 + 644092 * 2 ^ 59
def prefixEnd_644092 : Nat := 4983230072969 + 3 ^ 40 * 644092 * 2
def baseEnd_644092 : Nat := 110242927238599740262627

theorem tailTrace_644092 : CollatzResearch.WordTrace tailWord_644092 prefixEnd_644092 110242927238599740262627 := by
  unfold tailWord_644092
  simp only [CollatzResearch.WordTrace]
  refine ⟨11745982591286080500495265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15661310121714774000660353 11745982591286080500495265)
  ·
    refine ⟨8809486943464560375371449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11745982591286080500495265 8809486943464560375371449)
    ·
      refine ⟨6607115207598420281528587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8809486943464560375371449 6607115207598420281528587)
      ·
        refine ⟨9910672811397630422292881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6607115207598420281528587 9910672811397630422292881)
        ·
          refine ⟨7433004608548222816719661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9910672811397630422292881 7433004608548222816719661)
          ·
            refine ⟨2787376728205583556269873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7433004608548222816719661 2787376728205583556269873)
            ·
              refine ⟨2090532546154187667202405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2787376728205583556269873 2090532546154187667202405)
              ·
                refine ⟨391974852403910187600451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2090532546154187667202405 391974852403910187600451)
                ·
                  refine ⟨587962278605865281400677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 391974852403910187600451 587962278605865281400677)
                  ·
                    refine ⟨110242927238599740262627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 587962278605865281400677 110242927238599740262627)
                    ·
                      rfl

theorem cell23_644092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 4, 1, 4].length) (baseStart_644092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_644092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_644092 prefixEnd_644092 := by exact prefixLift 644092
  have htrace : WordTrace (prefixWord ++ tailWord_644092) baseStart_644092 baseEnd_644092 := by
    simpa [prefixWord, tailWord_644092, baseEnd_644092] using wordTrace_append hprefix tailTrace_644092
  have hstable : (prefixWord ++ tailWord_644092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644092).length < 2 ^ (prefixWord ++ tailWord_644092).sum := by decide
  have hdescent : baseEnd_644092 < baseStart_644092 := by decide
  rcases family_descends (prefixWord ++ tailWord_644092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644168 : List Nat := [2, 1, 3, 1, 1, 1, 3, 3, 1, 1, 6]
def baseStart_644168 : Nat := 118140960795 + 644168 * 2 ^ 59
def prefixEnd_644168 : Nat := 4983230072969 + 3 ^ 40 * 644168 * 2
def baseEnd_644168 : Nat := 330767806245540923437531

theorem tailTrace_644168 : CollatzResearch.WordTrace tailWord_644168 prefixEnd_644168 330767806245540923437531 := by
  unfold tailWord_644168
  simp only [CollatzResearch.WordTrace]
  refine ⟨11747368565148412990378579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15663158086864550653838105 11747368565148412990378579)
  ·
    refine ⟨17621052847722619485567869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11747368565148412990378579 17621052847722619485567869)
    ·
      refine ⟨6607894817895982307087951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17621052847722619485567869 6607894817895982307087951)
      ·
        refine ⟨9911842226843973460631927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6607894817895982307087951 9911842226843973460631927)
        ·
          refine ⟨14867763340265960190947891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9911842226843973460631927 14867763340265960190947891)
          ·
            refine ⟨22301645010398940286421837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14867763340265960190947891 22301645010398940286421837)
            ·
              refine ⟨8363116878899602607408189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22301645010398940286421837 8363116878899602607408189)
              ·
                refine ⟨3136168829587350977778071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8363116878899602607408189 3136168829587350977778071)
                ·
                  refine ⟨4704253244381026466667107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3136168829587350977778071 4704253244381026466667107)
                  ·
                    refine ⟨7056379866571539700000661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4704253244381026466667107 7056379866571539700000661)
                    ·
                      refine ⟨330767806245540923437531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7056379866571539700000661 330767806245540923437531)
                      ·
                        rfl

theorem cell23_644168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_644168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_644168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_644168 prefixEnd_644168 := by exact prefixLift 644168
  have htrace : WordTrace (prefixWord ++ tailWord_644168) baseStart_644168 baseEnd_644168 := by
    simpa [prefixWord, tailWord_644168, baseEnd_644168] using wordTrace_append hprefix tailTrace_644168
  have hstable : (prefixWord ++ tailWord_644168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644168).length < 2 ^ (prefixWord ++ tailWord_644168).sum := by decide
  have hdescent : baseEnd_644168 < baseStart_644168 := by decide
  rcases family_descends (prefixWord ++ tailWord_644168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644172 : List Nat := [2, 2, 1, 3, 1, 1, 1, 3, 5, 2, 2]
def baseStart_644172 : Nat := 118140960795 + 644172 * 2 ^ 59
def prefixEnd_644172 : Nat := 4983230072969 + 3 ^ 40 * 644172 * 2
def baseEnd_644172 : Nat := 330769860168158907787513

theorem tailTrace_644172 : CollatzResearch.WordTrace tailWord_644172 prefixEnd_644172 330769860168158907787513 := by
  unfold tailWord_644172
  simp only [CollatzResearch.WordTrace]
  refine ⟨11747441511141167331951385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15663255348188223109268513 11747441511141167331951385)
  ·
    refine ⟨8810581133355875498963539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11747441511141167331951385 8810581133355875498963539)
    ·
      refine ⟨13215871700033813248445309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8810581133355875498963539 13215871700033813248445309)
      ·
        refine ⟨4955951887512679968166991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13215871700033813248445309 4955951887512679968166991)
        ·
          refine ⟨7433927831269019952250487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4955951887512679968166991 7433927831269019952250487)
          ·
            refine ⟨11150891746903529928375731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7433927831269019952250487 11150891746903529928375731)
            ·
              refine ⟨16726337620355294892563597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11150891746903529928375731 16726337620355294892563597)
              ·
                refine ⟨6272376607633235584711349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16726337620355294892563597 6272376607633235584711349)
                ·
                  refine ⟨588035306965615836066689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6272376607633235584711349 588035306965615836066689)
                  ·
                    refine ⟨441026480224211877050017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 588035306965615836066689 441026480224211877050017)
                    ·
                      refine ⟨330769860168158907787513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 441026480224211877050017 330769860168158907787513)
                      ·
                        rfl

theorem cell23_644172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 5, 2, 2].length) (baseStart_644172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_644172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_644172 prefixEnd_644172 := by exact prefixLift 644172
  have htrace : WordTrace (prefixWord ++ tailWord_644172) baseStart_644172 baseEnd_644172 := by
    simpa [prefixWord, tailWord_644172, baseEnd_644172] using wordTrace_append hprefix tailTrace_644172
  have hstable : (prefixWord ++ tailWord_644172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644172).length < 2 ^ (prefixWord ++ tailWord_644172).sum := by decide
  have hdescent : baseEnd_644172 < baseStart_644172 := by decide
  rcases family_descends (prefixWord ++ tailWord_644172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644200 : List Nat := [2, 1, 4, 4, 1, 2, 2, 2, 1, 1, 3]
def baseStart_644200 : Nat := 118140960795 + 644200 * 2 ^ 59
def prefixEnd_644200 : Nat := 4983230072969 + 3 ^ 40 * 644200 * 2
def baseEnd_644200 : Nat := 330784237626484798237385

theorem tailTrace_644200 : CollatzResearch.WordTrace tailWord_644200 prefixEnd_644200 330784237626484798237385 := by
  unfold tailWord_644200
  simp only [CollatzResearch.WordTrace]
  refine ⟨11747952133090447722961027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15663936177453930297281369 11747952133090447722961027)
  ·
    refine ⟨17621928199635671584441541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11747952133090447722961027 17621928199635671584441541)
    ·
      refine ⟨3304111537431688422082789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17621928199635671584441541 3304111537431688422082789)
      ·
        refine ⟨619520913268441579140523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3304111537431688422082789 619520913268441579140523)
        ·
          refine ⟨929281369902662368710785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 619520913268441579140523 929281369902662368710785)
          ·
            refine ⟨696961027426996776533089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 929281369902662368710785 696961027426996776533089)
            ·
              refine ⟨522720770570247582399817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 696961027426996776533089 522720770570247582399817)
              ·
                refine ⟨392040577927685686799863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 522720770570247582399817 392040577927685686799863)
                ·
                  refine ⟨588060866891528530199795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 392040577927685686799863 588060866891528530199795)
                  ·
                    refine ⟨882091300337292795299693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 588060866891528530199795 882091300337292795299693)
                    ·
                      refine ⟨330784237626484798237385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 882091300337292795299693 330784237626484798237385)
                      ·
                        rfl

theorem cell23_644200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_644200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_644200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_644200 prefixEnd_644200 := by exact prefixLift 644200
  have htrace : WordTrace (prefixWord ++ tailWord_644200) baseStart_644200 baseEnd_644200 := by
    simpa [prefixWord, tailWord_644200, baseEnd_644200] using wordTrace_append hprefix tailTrace_644200
  have hstable : (prefixWord ++ tailWord_644200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644200).length < 2 ^ (prefixWord ++ tailWord_644200).sum := by decide
  have hdescent : baseEnd_644200 < baseStart_644200 := by decide
  rcases family_descends (prefixWord ++ tailWord_644200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644208 : List Nat := [2, 1, 1, 1, 5, 1, 1, 1, 1, 9]
def baseStart_644208 : Nat := 118140960795 + 644208 * 2 ^ 59
def prefixEnd_644208 : Nat := 4983230072969 + 3 ^ 40 * 644208 * 2
def baseEnd_644208 : Nat := 110262781823906922312449

theorem tailTrace_644208 : CollatzResearch.WordTrace tailWord_644208 prefixEnd_644208 110262781823906922312449 := by
  unfold tailWord_644208
  simp only [CollatzResearch.WordTrace]
  refine ⟨11748098025075956406106639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15664130700101275208142185 11748098025075956406106639)
  ·
    refine ⟨17622147037613934609159959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11748098025075956406106639 17622147037613934609159959)
    ·
      refine ⟨26433220556420901913739939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17622147037613934609159959 26433220556420901913739939)
      ·
        refine ⟨39649830834631352870609909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26433220556420901913739939 39649830834631352870609909)
        ·
          refine ⟨3717171640746689331619679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39649830834631352870609909 3717171640746689331619679)
          ·
            refine ⟨5575757461120033997429519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3717171640746689331619679 5575757461120033997429519)
            ·
              refine ⟨8363636191680050996144279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5575757461120033997429519 8363636191680050996144279)
              ·
                refine ⟨12545454287520076494216419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8363636191680050996144279 12545454287520076494216419)
                ·
                  refine ⟨18818181431280114741324629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12545454287520076494216419 18818181431280114741324629)
                  ·
                    refine ⟨110262781823906922312449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 18818181431280114741324629 110262781823906922312449)
                    ·
                      rfl

theorem cell23_644208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 1, 9].length) (baseStart_644208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_644208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_644208 prefixEnd_644208 := by exact prefixLift 644208
  have htrace : WordTrace (prefixWord ++ tailWord_644208) baseStart_644208 baseEnd_644208 := by
    simpa [prefixWord, tailWord_644208, baseEnd_644208] using wordTrace_append hprefix tailTrace_644208
  have hstable : (prefixWord ++ tailWord_644208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644208).length < 2 ^ (prefixWord ++ tailWord_644208).sum := by decide
  have hdescent : baseEnd_644208 < baseStart_644208 := by decide
  rcases family_descends (prefixWord ++ tailWord_644208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644275 : List Nat := [1, 1, 1, 2, 3, 2, 4, 1, 2, 2, 4]
def baseStart_644275 : Nat := 118140960795 + 644275 * 2 ^ 59
def prefixEnd_644275 : Nat := 4983230072969 + 3 ^ 40 * 644275 * 2
def baseEnd_644275 : Nat := 330822748675572004799539

theorem tailTrace_644275 : CollatzResearch.WordTrace tailWord_644275 prefixEnd_644275 330822748675572004799539 := by
  unfold tailWord_644275
  simp only [CollatzResearch.WordTrace]
  refine ⟨23498639740909183254902279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15665759827272788836601519 23498639740909183254902279)
  ·
    refine ⟨35247959611363774882353419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23498639740909183254902279 35247959611363774882353419)
    ·
      refine ⟨52871939417045662323530129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35247959611363774882353419 52871939417045662323530129)
      ·
        refine ⟨39653954562784246742647597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52871939417045662323530129 39653954562784246742647597)
        ·
          refine ⟨14870232961044092528492849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39653954562784246742647597 14870232961044092528492849)
          ·
            refine ⟨11152674720783069396369637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14870232961044092528492849 11152674720783069396369637)
            ·
              refine ⟨2091126510146825511819307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11152674720783069396369637 2091126510146825511819307)
              ·
                refine ⟨3136689765220238267728961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2091126510146825511819307 3136689765220238267728961)
                ·
                  refine ⟨2352517323915178700796721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3136689765220238267728961 2352517323915178700796721)
                  ·
                    refine ⟨1764387992936384025597541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2352517323915178700796721 1764387992936384025597541)
                    ·
                      refine ⟨330822748675572004799539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1764387992936384025597541 330822748675572004799539)
                      ·
                        rfl

theorem cell23_644275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 2, 4].length) (baseStart_644275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_644275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_644275 prefixEnd_644275 := by exact prefixLift 644275
  have htrace : WordTrace (prefixWord ++ tailWord_644275) baseStart_644275 baseEnd_644275 := by
    simpa [prefixWord, tailWord_644275, baseEnd_644275] using wordTrace_append hprefix tailTrace_644275
  have hstable : (prefixWord ++ tailWord_644275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644275).length < 2 ^ (prefixWord ++ tailWord_644275).sum := by decide
  have hdescent : baseEnd_644275 < baseStart_644275 := by decide
  rcases family_descends (prefixWord ++ tailWord_644275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644285 : List Nat := [1, 4, 1, 2, 1, 1, 4, 2, 7]
def baseStart_644285 : Nat := 118140960795 + 644285 * 2 ^ 59
def prefixEnd_644285 : Nat := 4983230072969 + 3 ^ 40 * 644285 * 2
def baseEnd_644285 : Nat := 36758653720235218408277

theorem tailTrace_644285 : CollatzResearch.WordTrace tailWord_644285 prefixEnd_644285 36758653720235218408277 := by
  unfold tailWord_644285
  simp only [CollatzResearch.WordTrace]
  refine ⟨23499004470872954962766309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15666002980581969975177539 23499004470872954962766309)
  ·
    refine ⟨4406063338288679055518683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23499004470872954962766309 4406063338288679055518683)
    ·
      refine ⟨6609095007433018583278025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4406063338288679055518683 6609095007433018583278025)
      ·
        refine ⟨4956821255574763937458519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6609095007433018583278025 4956821255574763937458519)
        ·
          refine ⟨7435231883362145906187779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4956821255574763937458519 7435231883362145906187779)
          ·
            refine ⟨11152847825043218859281669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7435231883362145906187779 11152847825043218859281669)
            ·
              refine ⟨2091158967195603536115313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11152847825043218859281669 2091158967195603536115313)
              ·
                refine ⟨1568369225396702652086485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2091158967195603536115313 1568369225396702652086485)
                ·
                  refine ⟨36758653720235218408277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1568369225396702652086485 36758653720235218408277)
                  ·
                    rfl

theorem cell23_644285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 7].length) (baseStart_644285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_644285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_644285 prefixEnd_644285 := by exact prefixLift 644285
  have htrace : WordTrace (prefixWord ++ tailWord_644285) baseStart_644285 baseEnd_644285 := by
    simpa [prefixWord, tailWord_644285, baseEnd_644285] using wordTrace_append hprefix tailTrace_644285
  have hstable : (prefixWord ++ tailWord_644285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644285).length < 2 ^ (prefixWord ++ tailWord_644285).sum := by decide
  have hdescent : baseEnd_644285 < baseStart_644285 := by decide
  rcases family_descends (prefixWord ++ tailWord_644285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644295 : List Nat := [1, 1, 4, 1, 1, 1, 1, 4, 1, 5, 3]
def baseStart_644295 : Nat := 118140960795 + 644295 * 2 ^ 59
def prefixEnd_644295 : Nat := 4983230072969 + 3 ^ 40 * 644295 * 2
def baseEnd_644295 : Nat := 330833018288661926549447

theorem tailTrace_644295 : CollatzResearch.WordTrace tailWord_644295 prefixEnd_644295 330833018288661926549447 := by
  unfold tailWord_644295
  simp only [CollatzResearch.WordTrace]
  refine ⟨23499369200836726670630339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15666246133891151113753559 23499369200836726670630339)
  ·
    refine ⟨35249053801255090005945509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23499369200836726670630339 35249053801255090005945509)
    ·
      refine ⟨6609197587735329376114783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35249053801255090005945509 6609197587735329376114783)
      ·
        refine ⟨9913796381602994064172175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6609197587735329376114783 9913796381602994064172175)
        ·
          refine ⟨14870694572404491096258263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9913796381602994064172175 14870694572404491096258263)
          ·
            refine ⟨22306041858606736644387395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14870694572404491096258263 22306041858606736644387395)
            ·
              refine ⟨33459062787910104966581093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22306041858606736644387395 33459062787910104966581093)
              ·
                refine ⟨6273574272733144681233955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33459062787910104966581093 6273574272733144681233955)
                ·
                  refine ⟨9410361409099717021850933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6273574272733144681233955 9410361409099717021850933)
                  ·
                    refine ⟨882221382103098470798525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9410361409099717021850933 882221382103098470798525)
                    ·
                      refine ⟨330833018288661926549447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 882221382103098470798525 330833018288661926549447)
                      ·
                        rfl

theorem cell23_644295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 5, 3].length) (baseStart_644295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_644295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_644295 prefixEnd_644295 := by exact prefixLift 644295
  have htrace : WordTrace (prefixWord ++ tailWord_644295) baseStart_644295 baseEnd_644295 := by
    simpa [prefixWord, tailWord_644295, baseEnd_644295] using wordTrace_append hprefix tailTrace_644295
  have hstable : (prefixWord ++ tailWord_644295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644295).length < 2 ^ (prefixWord ++ tailWord_644295).sum := by decide
  have hdescent : baseEnd_644295 < baseStart_644295 := by decide
  rcases family_descends (prefixWord ++ tailWord_644295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644352 : List Nat := [2, 1, 1, 2, 1, 1, 3, 2, 4, 4, 2]
def baseStart_644352 : Nat := 118140960795 + 644352 * 2 ^ 59
def prefixEnd_644352 : Nat := 4983230072969 + 3 ^ 40 * 644352 * 2
def baseEnd_644352 : Nat := 330862286685968203536685

theorem tailTrace_644352 : CollatzResearch.WordTrace tailWord_644352 prefixEnd_644352 330862286685968203536685 := by
  unfold tailWord_644352
  simp only [CollatzResearch.WordTrace]
  refine ⟨11750724080815112702727655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15667632107753483603636873 11750724080815112702727655)
  ·
    refine ⟨17626086121222669054091483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11750724080815112702727655 17626086121222669054091483)
    ·
      refine ⟨26439129181834003581137225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17626086121222669054091483 26439129181834003581137225)
      ·
        refine ⟨19829346886375502685852919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26439129181834003581137225 19829346886375502685852919)
        ·
          refine ⟨29744020329563254028779379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19829346886375502685852919 29744020329563254028779379)
          ·
            refine ⟨44616030494344881043169069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29744020329563254028779379 44616030494344881043169069)
            ·
              refine ⟨16731011435379330391188401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44616030494344881043169069 16731011435379330391188401)
              ·
                refine ⟨12548258576534497793391301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16731011435379330391188401 12548258576534497793391301)
                ·
                  refine ⟨2352798483100218336260869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12548258576534497793391301 2352798483100218336260869)
                  ·
                    refine ⟨441149715581290938048913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2352798483100218336260869 441149715581290938048913)
                    ·
                      refine ⟨330862286685968203536685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 441149715581290938048913 330862286685968203536685)
                      ·
                        rfl

theorem cell23_644352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 4, 4, 2].length) (baseStart_644352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_644352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_644352 prefixEnd_644352 := by exact prefixLift 644352
  have htrace : WordTrace (prefixWord ++ tailWord_644352) baseStart_644352 baseEnd_644352 := by
    simpa [prefixWord, tailWord_644352, baseEnd_644352] using wordTrace_append hprefix tailTrace_644352
  have hstable : (prefixWord ++ tailWord_644352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644352).length < 2 ^ (prefixWord ++ tailWord_644352).sum := by decide
  have hdescent : baseEnd_644352 < baseStart_644352 := by decide
  rcases family_descends (prefixWord ++ tailWord_644352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644370 : List Nat := [3, 2, 4, 2, 1, 2, 2, 2, 5]
def baseStart_644370 : Nat := 118140960795 + 644370 * 2 ^ 59
def prefixEnd_644370 : Nat := 4983230072969 + 3 ^ 40 * 644370 * 2
def baseEnd_644370 : Nat := 36763503259749903679067

theorem tailTrace_644370 : CollatzResearch.WordTrace tailWord_644370 prefixEnd_644370 36763503259749903679067 := by
  unfold tailWord_644370
  simp only [CollatzResearch.WordTrace]
  refine ⟨5875526168891253619902641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15668069783710009653073709 5875526168891253619902641)
  ·
    refine ⟨4406644626668440214926981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5875526168891253619902641 4406644626668440214926981)
    ·
      refine ⟨826245867500332540298809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4406644626668440214926981 826245867500332540298809)
      ·
        refine ⟨619684400625249405224107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 826245867500332540298809 619684400625249405224107)
        ·
          refine ⟨929526600937874107836161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 619684400625249405224107 929526600937874107836161)
          ·
            refine ⟨697144950703405580877121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 929526600937874107836161 697144950703405580877121)
            ·
              refine ⟨522858713027554185657841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 697144950703405580877121 522858713027554185657841)
              ·
                refine ⟨392144034770665639243381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 522858713027554185657841 392144034770665639243381)
                ·
                  refine ⟨36763503259749903679067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 392144034770665639243381 36763503259749903679067)
                  ·
                    rfl

theorem cell23_644370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 2, 5].length) (baseStart_644370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_644370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_644370 prefixEnd_644370 := by exact prefixLift 644370
  have htrace : WordTrace (prefixWord ++ tailWord_644370) baseStart_644370 baseEnd_644370 := by
    simpa [prefixWord, tailWord_644370, baseEnd_644370] using wordTrace_append hprefix tailTrace_644370
  have hstable : (prefixWord ++ tailWord_644370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644370).length < 2 ^ (prefixWord ++ tailWord_644370).sum := by decide
  have hdescent : baseEnd_644370 < baseStart_644370 := by decide
  rcases family_descends (prefixWord ++ tailWord_644370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644386 : List Nat := [3, 3, 1, 1, 4, 1, 1, 1, 2, 4, 2]
def baseStart_644386 : Nat := 118140960795 + 644386 * 2 ^ 59
def prefixEnd_644386 : Nat := 4983230072969 + 3 ^ 40 * 644386 * 2
def baseEnd_644386 : Nat := 330879745028221070511529

theorem tailTrace_644386 : CollatzResearch.WordTrace tailWord_644386 prefixEnd_644386 330879745028221070511529 := by
  unfold tailWord_644386
  simp only [CollatzResearch.WordTrace]
  refine ⟨5875672060876762303048253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15668458829004699474795341 5875672060876762303048253)
  ·
    refine ⟨2203377022828785863643095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5875672060876762303048253 2203377022828785863643095)
    ·
      refine ⟨3305065534243178795464643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2203377022828785863643095 3305065534243178795464643)
      ·
        refine ⟨4957598301364768193196965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3305065534243178795464643 4957598301364768193196965)
        ·
          refine ⟨929549681505894036224431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4957598301364768193196965 929549681505894036224431)
          ·
            refine ⟨1394324522258841054336647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 929549681505894036224431 1394324522258841054336647)
            ·
              refine ⟨2091486783388261581504971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1394324522258841054336647 2091486783388261581504971)
              ·
                refine ⟨3137230175082392372257457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2091486783388261581504971 3137230175082392372257457)
                ·
                  refine ⟨2352922631311794279193093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3137230175082392372257457 2352922631311794279193093)
                  ·
                    refine ⟨441172993370961427348705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2352922631311794279193093 441172993370961427348705)
                    ·
                      refine ⟨330879745028221070511529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 441172993370961427348705 330879745028221070511529)
                      ·
                        rfl

theorem cell23_644386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 2, 4, 2].length) (baseStart_644386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_644386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_644386 prefixEnd_644386 := by exact prefixLift 644386
  have htrace : WordTrace (prefixWord ++ tailWord_644386) baseStart_644386 baseEnd_644386 := by
    simpa [prefixWord, tailWord_644386, baseEnd_644386] using wordTrace_append hprefix tailTrace_644386
  have hstable : (prefixWord ++ tailWord_644386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644386).length < 2 ^ (prefixWord ++ tailWord_644386).sum := by decide
  have hdescent : baseEnd_644386 < baseStart_644386 := by decide
  rcases family_descends (prefixWord ++ tailWord_644386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644436 : List Nat := [2, 4, 1, 1, 2, 1, 4, 1, 3, 1, 3]
def baseStart_644436 : Nat := 118140960795 + 644436 * 2 ^ 59
def prefixEnd_644436 : Nat := 4983230072969 + 3 ^ 40 * 644436 * 2
def baseEnd_644436 : Nat := 330905419060945874886299

theorem tailTrace_644436 : CollatzResearch.WordTrace tailWord_644436 prefixEnd_644436 330905419060945874886299 := by
  unfold tailWord_644436
  simp only [CollatzResearch.WordTrace]
  refine ⟨11752255946662953875756581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15669674595550605167675441 11752255946662953875756581)
  ·
    refine ⟨2203547989999303851704359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11752255946662953875756581 2203547989999303851704359)
    ·
      refine ⟨3305321984998955777556539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2203547989999303851704359 3305321984998955777556539)
      ·
        refine ⟨4957982977498433666334809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3305321984998955777556539 4957982977498433666334809)
        ·
          refine ⟨3718487233123825249751107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4957982977498433666334809 3718487233123825249751107)
          ·
            refine ⟨5577730849685737874626661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3718487233123825249751107 5577730849685737874626661)
            ·
              refine ⟨1045824534316075851492499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5577730849685737874626661 1045824534316075851492499)
              ·
                refine ⟨1568736801474113777238749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1045824534316075851492499 1568736801474113777238749)
                ·
                  refine ⟨588276300552792666464531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1568736801474113777238749 588276300552792666464531)
                  ·
                    refine ⟨882414450829188999696797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 588276300552792666464531 882414450829188999696797)
                    ·
                      refine ⟨330905419060945874886299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 882414450829188999696797 330905419060945874886299)
                      ·
                        rfl

theorem cell23_644436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_644436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_644436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_644436 prefixEnd_644436 := by exact prefixLift 644436
  have htrace : WordTrace (prefixWord ++ tailWord_644436) baseStart_644436 baseEnd_644436 := by
    simpa [prefixWord, tailWord_644436, baseEnd_644436] using wordTrace_append hprefix tailTrace_644436
  have hstable : (prefixWord ++ tailWord_644436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644436).length < 2 ^ (prefixWord ++ tailWord_644436).sum := by decide
  have hdescent : baseEnd_644436 < baseStart_644436 := by decide
  rcases family_descends (prefixWord ++ tailWord_644436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644442 : List Nat := [3, 1, 1, 2, 1, 2, 2, 1, 5, 1, 4]
def baseStart_644442 : Nat := 118140960795 + 644442 * 2 ^ 59
def prefixEnd_644442 : Nat := 4983230072969 + 3 ^ 40 * 644442 * 2
def baseEnd_644442 : Nat := 330908499944872851411271

theorem tailTrace_644442 : CollatzResearch.WordTrace tailWord_644442 prefixEnd_644442 330908499944872851411271 := by
  unfold tailWord_644442
  simp only [CollatzResearch.WordTrace]
  refine ⟨5876182682826042694057895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15669820487536113850821053 5876182682826042694057895)
  ·
    refine ⟨8814274024239064041086843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5876182682826042694057895 8814274024239064041086843)
    ·
      refine ⟨13221411036358596061630265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8814274024239064041086843 13221411036358596061630265)
      ·
        refine ⟨9916058277268947046222699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13221411036358596061630265 9916058277268947046222699)
        ·
          refine ⟨14874087415903420569334049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9916058277268947046222699 14874087415903420569334049)
          ·
            refine ⟨11155565561927565427000537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14874087415903420569334049 11155565561927565427000537)
            ·
              refine ⟨8366674171445674070250403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11155565561927565427000537 8366674171445674070250403)
              ·
                refine ⟨12550011257168511105375605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8366674171445674070250403 12550011257168511105375605)
                ·
                  refine ⟨1176563555359547916128963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12550011257168511105375605 1176563555359547916128963)
                  ·
                    refine ⟨1764845333039321874193445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1176563555359547916128963 1764845333039321874193445)
                    ·
                      refine ⟨330908499944872851411271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1764845333039321874193445 330908499944872851411271)
                      ·
                        rfl

theorem cell23_644442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_644442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_644442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_644442 prefixEnd_644442 := by exact prefixLift 644442
  have htrace : WordTrace (prefixWord ++ tailWord_644442) baseStart_644442 baseEnd_644442 := by
    simpa [prefixWord, tailWord_644442, baseEnd_644442] using wordTrace_append hprefix tailTrace_644442
  have hstable : (prefixWord ++ tailWord_644442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644442).length < 2 ^ (prefixWord ++ tailWord_644442).sum := by decide
  have hdescent : baseEnd_644442 < baseStart_644442 := by decide
  rcases family_descends (prefixWord ++ tailWord_644442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_644456 : List Nat := [2, 1, 4, 2, 3, 1, 2, 2, 1, 5]
def baseStart_644456 : Nat := 118140960795 + 644456 * 2 ^ 59
def prefixEnd_644456 : Nat := 4983230072969 + 3 ^ 40 * 644456 * 2
def baseEnd_644456 : Nat := 110305229558011932212069

theorem tailTrace_644456 : CollatzResearch.WordTrace tailWord_644456 prefixEnd_644456 110305229558011932212069 := by
  unfold tailWord_644456
  simp only [CollatzResearch.WordTrace]
  refine ⟨11752620676626725583620611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15670160902168967444827481 11752620676626725583620611)
  ·
    refine ⟨17628931014940088375430917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11752620676626725583620611 17628931014940088375430917)
    ·
      refine ⟨3305424565301266570393297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17628931014940088375430917 3305424565301266570393297)
      ·
        refine ⟨2479068423975949927794973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3305424565301266570393297 2479068423975949927794973)
        ·
          refine ⟨929650658990981222923115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2479068423975949927794973 929650658990981222923115)
          ·
            refine ⟨1394475988486471834384673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 929650658990981222923115 1394475988486471834384673)
            ·
              refine ⟨1045856991364853875788505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1394475988486471834384673 1045856991364853875788505)
              ·
                refine ⟨784392743523640406841379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1045856991364853875788505 784392743523640406841379)
                ·
                  refine ⟨1176589115285460610262069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 784392743523640406841379 1176589115285460610262069)
                  ·
                    refine ⟨110305229558011932212069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1176589115285460610262069 110305229558011932212069)
                    ·
                      rfl

theorem cell23_644456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_644456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_644456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_644456 prefixEnd_644456 := by exact prefixLift 644456
  have htrace : WordTrace (prefixWord ++ tailWord_644456) baseStart_644456 baseEnd_644456 := by
    simpa [prefixWord, tailWord_644456, baseEnd_644456] using wordTrace_append hprefix tailTrace_644456
  have hstable : (prefixWord ++ tailWord_644456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_644456).length < 2 ^ (prefixWord ++ tailWord_644456).sum := by decide
  have hdescent : baseEnd_644456 < baseStart_644456 := by decide
  rcases family_descends (prefixWord ++ tailWord_644456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
