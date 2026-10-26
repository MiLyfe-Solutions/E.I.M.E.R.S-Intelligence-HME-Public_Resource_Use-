import V185TrunkScan23Chunk1015

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6015453 : List Nat := [1, 4, 3, 1, 1, 1, 1, 1, 2, 2, 6]
def baseStart_6015453 : Nat := 118140960795 + 6015453 * 2 ^ 59
def prefixEnd_6015453 : Nat := 4983230072969 + 3 ^ 40 * 6015453 * 2
def baseEnd_6015453 : Nat := 3088818743530558246172941

theorem tailTrace_6015453 : CollatzResearch.WordTrace tailWord_6015453 prefixEnd_6015453 3088818743530558246172941 := by
  unfold tailWord_6015453
  simp only [CollatzResearch.WordTrace]
  refine ⟨219401595476048613425395013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146267730317365742283596675 219401595476048613425395013)
  ·
    refine ⟨41137799151759115017261565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 219401595476048613425395013 41137799151759115017261565)
    ·
      refine ⟨15426674681909668131473087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41137799151759115017261565 15426674681909668131473087)
      ·
        refine ⟨23140012022864502197209631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15426674681909668131473087 23140012022864502197209631)
        ·
          refine ⟨34710018034296753295814447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23140012022864502197209631 34710018034296753295814447)
          ·
            refine ⟨52065027051445129943721671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34710018034296753295814447 52065027051445129943721671)
            ·
              refine ⟨78097540577167694915582507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52065027051445129943721671 78097540577167694915582507)
              ·
                refine ⟨117146310865751542373373761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78097540577167694915582507 117146310865751542373373761)
                ·
                  refine ⟨87859733149313656780030321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117146310865751542373373761 87859733149313656780030321)
                  ·
                    refine ⟨65894799861985242585022741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 87859733149313656780030321 65894799861985242585022741)
                    ·
                      refine ⟨3088818743530558246172941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65894799861985242585022741 3088818743530558246172941)
                      ·
                        rfl

theorem cell23_6015453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_6015453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015453 prefixEnd_6015453 := by exact prefixLift 6015453
  have htrace : WordTrace (prefixWord ++ tailWord_6015453) baseStart_6015453 baseEnd_6015453 := by
    simpa [prefixWord, tailWord_6015453, baseEnd_6015453] using wordTrace_append hprefix tailTrace_6015453
  have hstable : (prefixWord ++ tailWord_6015453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015453).length < 2 ^ (prefixWord ++ tailWord_6015453).sum := by decide
  have hdescent : baseEnd_6015453 < baseStart_6015453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6015495 : List Nat := [1, 1, 4, 3, 4, 1, 2, 2, 1, 2, 2]
def baseStart_6015495 : Nat := 118140960795 + 6015495 * 2 ^ 59
def prefixEnd_6015495 : Nat := 4983230072969 + 3 ^ 40 * 6015495 * 2
def baseEnd_6015495 : Nat := 3088840309718047081847749

theorem tailTrace_6015495 : CollatzResearch.WordTrace tailWord_6015495 prefixEnd_6015495 3088840309718047081847749 := by
  unfold tailWord_6015495
  simp only [CollatzResearch.WordTrace]
  refine ⟨219403127341896454598423939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146268751561264303065615959 219403127341896454598423939)
  ·
    refine ⟨329104691012844681897635909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219403127341896454598423939 329104691012844681897635909)
    ·
      refine ⟨61707129564908377855806733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 329104691012844681897635909 61707129564908377855806733)
      ·
        refine ⟨23140173586840641695927525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61707129564908377855806733 23140173586840641695927525)
        ·
          refine ⟨4338782547532620317986411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23140173586840641695927525 4338782547532620317986411)
          ·
            refine ⟨6508173821298930476979617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4338782547532620317986411 6508173821298930476979617)
            ·
              refine ⟨4881130365974197857734713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6508173821298930476979617 4881130365974197857734713)
              ·
                refine ⟨3660847774480648393301035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4881130365974197857734713 3660847774480648393301035)
                ·
                  refine ⟨5491271661720972589951553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3660847774480648393301035 5491271661720972589951553)
                  ·
                    refine ⟨4118453746290729442463665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5491271661720972589951553 4118453746290729442463665)
                    ·
                      refine ⟨3088840309718047081847749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4118453746290729442463665 3088840309718047081847749)
                      ·
                        rfl

theorem cell23_6015495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_6015495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015495 prefixEnd_6015495 := by exact prefixLift 6015495
  have htrace : WordTrace (prefixWord ++ tailWord_6015495) baseStart_6015495 baseEnd_6015495 := by
    simpa [prefixWord, tailWord_6015495, baseEnd_6015495] using wordTrace_append hprefix tailTrace_6015495
  have hstable : (prefixWord ++ tailWord_6015495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015495).length < 2 ^ (prefixWord ++ tailWord_6015495).sum := by decide
  have hdescent : baseEnd_6015495 < baseStart_6015495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6015503 : List Nat := [1, 1, 2, 1, 1, 1, 2, 5, 2, 4, 3]
def baseStart_6015503 : Nat := 118140960795 + 6015503 * 2 ^ 59
def prefixEnd_6015503 : Nat := 4983230072969 + 3 ^ 40 * 6015503 * 2
def baseEnd_6015503 : Nat := 3088844417563283050547711

theorem tailTrace_6015503 : CollatzResearch.WordTrace tailWord_6015503 prefixEnd_6015503 3088844417563283050547711 := by
  unfold tailWord_6015503
  simp only [CollatzResearch.WordTrace]
  refine ⟨219403419125867471964715163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146268946083911647976476775 219403419125867471964715163)
  ·
    refine ⟨329105128688801207947072745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219403419125867471964715163 329105128688801207947072745)
    ·
      refine ⟨246828846516600905960304559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329105128688801207947072745 246828846516600905960304559)
      ·
        refine ⟨370243269774901358940456839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246828846516600905960304559 370243269774901358940456839)
        ·
          refine ⟨555364904662352038410685259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 370243269774901358940456839 555364904662352038410685259)
          ·
            refine ⟨833047356993528057616027889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 555364904662352038410685259 833047356993528057616027889)
            ·
              refine ⟨624785517745146043212020917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 833047356993528057616027889 624785517745146043212020917)
              ·
                refine ⟨58573642288607441551126961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 624785517745146043212020917 58573642288607441551126961)
                ·
                  refine ⟨43930231716455581163345221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58573642288607441551126961 43930231716455581163345221)
                  ·
                    refine ⟨8236918446835421468127229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43930231716455581163345221 8236918446835421468127229)
                    ·
                      refine ⟨3088844417563283050547711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8236918446835421468127229 3088844417563283050547711)
                      ·
                        rfl

theorem cell23_6015503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 4, 3].length) (baseStart_6015503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015503 prefixEnd_6015503 := by exact prefixLift 6015503
  have htrace : WordTrace (prefixWord ++ tailWord_6015503) baseStart_6015503 baseEnd_6015503 := by
    simpa [prefixWord, tailWord_6015503, baseEnd_6015503] using wordTrace_append hprefix tailTrace_6015503
  have hstable : (prefixWord ++ tailWord_6015503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015503).length < 2 ^ (prefixWord ++ tailWord_6015503).sum := by decide
  have hdescent : baseEnd_6015503 < baseStart_6015503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6015513 : List Nat := [1, 2, 1, 2, 1, 1, 2, 5, 2, 2, 4]
def baseStart_6015513 : Nat := 118140960795 + 6015513 * 2 ^ 59
def prefixEnd_6015513 : Nat := 4983230072969 + 3 ^ 40 * 6015513 * 2
def baseEnd_6015513 : Nat := 3088849552369828011422665

theorem tailTrace_6015513 : CollatzResearch.WordTrace tailWord_6015513 prefixEnd_6015513 3088849552369828011422665 := by
  unfold tailWord_6015513
  simp only [CollatzResearch.WordTrace]
  refine ⟨219403783855831243672579193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146269189237220829115052795 219403783855831243672579193)
  ·
    refine ⟨164552837891873432754434395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219403783855831243672579193 164552837891873432754434395)
    ·
      refine ⟨246829256837810149131651593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164552837891873432754434395 246829256837810149131651593)
      ·
        refine ⟨185121942628357611848738695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246829256837810149131651593 185121942628357611848738695)
        ·
          refine ⟨277682913942536417773108043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185121942628357611848738695 277682913942536417773108043)
          ·
            refine ⟨416524370913804626659662065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277682913942536417773108043 416524370913804626659662065)
            ·
              refine ⟨312393278185353469994746549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 416524370913804626659662065 312393278185353469994746549)
              ·
                refine ⟨29286869829876887812007489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 312393278185353469994746549 29286869829876887812007489)
                ·
                  refine ⟨21965152372407665859005617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29286869829876887812007489 21965152372407665859005617)
                  ·
                    refine ⟨16473864279305749394254213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21965152372407665859005617 16473864279305749394254213)
                    ·
                      refine ⟨3088849552369828011422665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16473864279305749394254213 3088849552369828011422665)
                      ·
                        rfl

theorem cell23_6015513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 2, 4].length) (baseStart_6015513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015513 prefixEnd_6015513 := by exact prefixLift 6015513
  have htrace : WordTrace (prefixWord ++ tailWord_6015513) baseStart_6015513 baseEnd_6015513 := by
    simpa [prefixWord, tailWord_6015513, baseEnd_6015513] using wordTrace_append hprefix tailTrace_6015513
  have hstable : (prefixWord ++ tailWord_6015513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015513).length < 2 ^ (prefixWord ++ tailWord_6015513).sum := by decide
  have hdescent : baseEnd_6015513 < baseStart_6015513 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6015517 : List Nat := [1, 4, 2, 2, 1, 2, 1, 3, 1, 4, 2]
def baseStart_6015517 : Nat := 118140960795 + 6015517 * 2 ^ 59
def prefixEnd_6015517 : Nat := 4983230072969 + 3 ^ 40 * 6015517 * 2
def baseEnd_6015517 : Nat := 3088851606292445995772647

theorem tailTrace_6015517 : CollatzResearch.WordTrace tailWord_6015517 prefixEnd_6015517 3088851606292445995772647 := by
  unfold tailWord_6015517
  simp only [CollatzResearch.WordTrace]
  refine ⟨219403929747816752355724805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146269286498544501570483203 219403929747816752355724805)
  ·
    refine ⟨41138236827715641066698401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 219403929747816752355724805 41138236827715641066698401)
    ·
      refine ⟨30853677620786730800023801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41138236827715641066698401 30853677620786730800023801)
      ·
        refine ⟨23140258215590048100017851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30853677620786730800023801 23140258215590048100017851)
        ·
          refine ⟨34710387323385072150026777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23140258215590048100017851 34710387323385072150026777)
          ·
            refine ⟨26032790492538804112520083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34710387323385072150026777 26032790492538804112520083)
            ·
              refine ⟨39049185738808206168780125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26032790492538804112520083 39049185738808206168780125)
              ·
                refine ⟨14643444652053077313292547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39049185738808206168780125 14643444652053077313292547)
                ·
                  refine ⟨21965166978079615969938821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14643444652053077313292547 21965166978079615969938821)
                  ·
                    refine ⟨4118468808389927994363529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21965166978079615969938821 4118468808389927994363529)
                    ·
                      refine ⟨3088851606292445995772647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4118468808389927994363529 3088851606292445995772647)
                      ·
                        rfl

theorem cell23_6015517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_6015517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015517 prefixEnd_6015517 := by exact prefixLift 6015517
  have htrace : WordTrace (prefixWord ++ tailWord_6015517) baseStart_6015517 baseEnd_6015517 := by
    simpa [prefixWord, tailWord_6015517, baseEnd_6015517] using wordTrace_append hprefix tailTrace_6015517
  have hstable : (prefixWord ++ tailWord_6015517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015517).length < 2 ^ (prefixWord ++ tailWord_6015517).sum := by decide
  have hdescent : baseEnd_6015517 < baseStart_6015517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6015523 : List Nat := [1, 1, 1, 4, 4, 1, 1, 1, 9]
def baseStart_6015523 : Nat := 118140960795 + 6015523 * 2 ^ 59
def prefixEnd_6015523 : Nat := 4983230072969 + 3 ^ 40 * 6015523 * 2
def baseEnd_6015523 : Nat := 343206076352930330255291

theorem tailTrace_6015523 : CollatzResearch.WordTrace tailWord_6015523 prefixEnd_6015523 343206076352930330255291 := by
  unfold tailWord_6015523
  simp only [CollatzResearch.WordTrace]
  refine ⟨219404148585795015380443223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146269432390530010253628815 219404148585795015380443223)
  ·
    refine ⟨329106222878692523070664835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219404148585795015380443223 329106222878692523070664835)
    ·
      refine ⟨493659334318038784605997253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329106222878692523070664835 493659334318038784605997253)
      ·
        refine ⟨92561125184632272113624485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 493659334318038784605997253 92561125184632272113624485)
        ·
          refine ⟨17355210972118551021304591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92561125184632272113624485 17355210972118551021304591)
          ·
            refine ⟨26032816458177826531956887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17355210972118551021304591 26032816458177826531956887)
            ·
              refine ⟨39049224687266739797935331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26032816458177826531956887 39049224687266739797935331)
              ·
                refine ⟨58573837030900109696902997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39049224687266739797935331 58573837030900109696902997)
                ·
                  refine ⟨343206076352930330255291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 58573837030900109696902997 343206076352930330255291)
                  ·
                    rfl

theorem cell23_6015523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 9].length) (baseStart_6015523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015523 prefixEnd_6015523 := by exact prefixLift 6015523
  have htrace : WordTrace (prefixWord ++ tailWord_6015523) baseStart_6015523 baseEnd_6015523 := by
    simpa [prefixWord, tailWord_6015523, baseEnd_6015523] using wordTrace_append hprefix tailTrace_6015523
  have hstable : (prefixWord ++ tailWord_6015523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015523).length < 2 ^ (prefixWord ++ tailWord_6015523).sum := by decide
  have hdescent : baseEnd_6015523 < baseStart_6015523 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6015560 : List Nat := [2, 1, 3, 1, 1, 1, 1, 3, 1, 7, 2]
def baseStart_6015560 : Nat := 118140960795 + 6015560 * 2 ^ 59
def prefixEnd_6015560 : Nat := 4983230072969 + 3 ^ 40 * 6015560 * 2
def baseEnd_6015560 : Nat := 3088873685960589327534949

theorem tailTrace_6015560 : CollatzResearch.WordTrace tailWord_6015560 prefixEnd_6015560 3088873685960589327534949 := by
  unfold tailWord_6015560
  simp only [CollatzResearch.WordTrace]
  refine ⟨109702749043330485349770067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146270332057773980466360089 109702749043330485349770067)
  ·
    refine ⟨164554123564995728024655101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109702749043330485349770067 164554123564995728024655101)
    ·
      refine ⟨61707796336873398009245663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164554123564995728024655101 61707796336873398009245663)
      ·
        refine ⟨92561694505310097013868495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61707796336873398009245663 92561694505310097013868495)
        ·
          refine ⟨138842541757965145520802743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92561694505310097013868495 138842541757965145520802743)
          ·
            refine ⟨208263812636947718281204115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138842541757965145520802743 208263812636947718281204115)
            ·
              refine ⟨312395718955421577421806173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208263812636947718281204115 312395718955421577421806173)
              ·
                refine ⟨117148394608283091533177315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 312395718955421577421806173 117148394608283091533177315)
                ·
                  refine ⟨175722591912424637299765973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117148394608283091533177315 175722591912424637299765973)
                  ·
                    refine ⟨4118498247947452436713265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 175722591912424637299765973 4118498247947452436713265)
                    ·
                      refine ⟨3088873685960589327534949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4118498247947452436713265 3088873685960589327534949)
                      ·
                        rfl

theorem cell23_6015560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 1, 7, 2].length) (baseStart_6015560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015560 prefixEnd_6015560 := by exact prefixLift 6015560
  have htrace : WordTrace (prefixWord ++ tailWord_6015560) baseStart_6015560 baseEnd_6015560 := by
    simpa [prefixWord, tailWord_6015560, baseEnd_6015560] using wordTrace_append hprefix tailTrace_6015560
  have hstable : (prefixWord ++ tailWord_6015560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015560).length < 2 ^ (prefixWord ++ tailWord_6015560).sum := by decide
  have hdescent : baseEnd_6015560 < baseStart_6015560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6015563 : List Nat := [1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 5]
def baseStart_6015563 : Nat := 118140960795 + 6015563 * 2 ^ 59
def prefixEnd_6015563 : Nat := 4983230072969 + 3 ^ 40 * 6015563 * 2
def baseEnd_6015563 : Nat := 3088875226402552815797435

theorem tailTrace_6015563 : CollatzResearch.WordTrace tailWord_6015563 prefixEnd_6015563 3088875226402552815797435 := by
  unfold tailWord_6015563
  simp only [CollatzResearch.WordTrace]
  refine ⟨219405607505650102211899343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146270405003766734807932895 219405607505650102211899343)
  ·
    refine ⟨329108411258475153317849015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219405607505650102211899343 329108411258475153317849015)
    ·
      refine ⟨493662616887712729976773523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329108411258475153317849015 493662616887712729976773523)
      ·
        refine ⟨740493925331569094965160285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 493662616887712729976773523 740493925331569094965160285)
        ·
          refine ⟨277685221999338410611935107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 740493925331569094965160285 277685221999338410611935107)
          ·
            refine ⟨416527832999007615917902661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277685221999338410611935107 416527832999007615917902661)
            ·
              refine ⟨78098968687313927984606749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 416527832999007615917902661 78098968687313927984606749)
              ·
                refine ⟨29287113257742722994227531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78098968687313927984606749 29287113257742722994227531)
                ·
                  refine ⟨43930669886614084491341297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29287113257742722994227531 43930669886614084491341297)
                  ·
                    refine ⟨32948002414960563368505973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43930669886614084491341297 32948002414960563368505973)
                    ·
                      refine ⟨3088875226402552815797435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32948002414960563368505973 3088875226402552815797435)
                      ·
                        rfl

theorem cell23_6015563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 5].length) (baseStart_6015563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015563 prefixEnd_6015563 := by exact prefixLift 6015563
  have htrace : WordTrace (prefixWord ++ tailWord_6015563) baseStart_6015563 baseEnd_6015563 := by
    simpa [prefixWord, tailWord_6015563, baseEnd_6015563] using wordTrace_append hprefix tailTrace_6015563
  have hstable : (prefixWord ++ tailWord_6015563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015563).length < 2 ^ (prefixWord ++ tailWord_6015563).sum := by decide
  have hdescent : baseEnd_6015563 < baseStart_6015563 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6015593 : List Nat := [1, 2, 1, 1, 1, 4, 1, 2, 2, 3, 5]
def baseStart_6015593 : Nat := 118140960795 + 6015593 * 2 ^ 59
def prefixEnd_6015593 : Nat := 4983230072969 + 3 ^ 40 * 6015593 * 2
def baseEnd_6015593 : Nat := 3088890630822187698422297

theorem tailTrace_6015593 : CollatzResearch.WordTrace tailWord_6015593 prefixEnd_6015593 3088890630822187698422297 := by
  unfold tailWord_6015593
  simp only [CollatzResearch.WordTrace]
  refine ⟨219406701695541417335491433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146271134463694278223660955 219406701695541417335491433)
  ·
    refine ⟨164555026271656063001618575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219406701695541417335491433 164555026271656063001618575)
    ·
      refine ⟨246832539407484094502427863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164555026271656063001618575 246832539407484094502427863)
      ·
        refine ⟨370248809111226141753641795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246832539407484094502427863 370248809111226141753641795)
        ·
          refine ⟨555373213666839212630462693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 370248809111226141753641795 555373213666839212630462693)
          ·
            refine ⟨104132477562532352368211755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 555373213666839212630462693 104132477562532352368211755)
            ·
              refine ⟨156198716343798528552317633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104132477562532352368211755 156198716343798528552317633)
              ·
                refine ⟨117149037257848896414238225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156198716343798528552317633 117149037257848896414238225)
                ·
                  refine ⟨87861777943386672310678669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117149037257848896414238225 87861777943386672310678669)
                  ·
                    refine ⟨32948166728770002116504501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 87861777943386672310678669 32948166728770002116504501)
                    ·
                      refine ⟨3088890630822187698422297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32948166728770002116504501 3088890630822187698422297)
                      ·
                        rfl

theorem cell23_6015593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 3, 5].length) (baseStart_6015593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015593 prefixEnd_6015593 := by exact prefixLift 6015593
  have htrace : WordTrace (prefixWord ++ tailWord_6015593) baseStart_6015593 baseEnd_6015593 := by
    simpa [prefixWord, tailWord_6015593, baseEnd_6015593] using wordTrace_append hprefix tailTrace_6015593
  have hstable : (prefixWord ++ tailWord_6015593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015593).length < 2 ^ (prefixWord ++ tailWord_6015593).sum := by decide
  have hdescent : baseEnd_6015593 < baseStart_6015593 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6015603 : List Nat := [1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 6]
def baseStart_6015603 : Nat := 118140960795 + 6015603 * 2 ^ 59
def prefixEnd_6015603 : Nat := 4983230072969 + 3 ^ 40 * 6015603 * 2
def baseEnd_6015603 : Nat := 3088895765628732659297251

theorem tailTrace_6015603 : CollatzResearch.WordTrace tailWord_6015603 prefixEnd_6015603 3088895765628732659297251 := by
  unfold tailWord_6015603
  simp only [CollatzResearch.WordTrace]
  refine ⟨219407066425505189043355463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146271377617003459362236975 219407066425505189043355463)
  ·
    refine ⟨329110599638257783565033195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219407066425505189043355463 329110599638257783565033195)
    ·
      refine ⟨493665899457386675347549793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329110599638257783565033195 493665899457386675347549793)
      ·
        refine ⟨370249424593040006510662345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 493665899457386675347549793 370249424593040006510662345)
        ·
          refine ⟨277687068444780004882996759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 370249424593040006510662345 277687068444780004882996759)
          ·
            refine ⟨416530602667170007324495139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277687068444780004882996759 416530602667170007324495139)
            ·
              refine ⟨624795904000755010986742709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 416530602667170007324495139 624795904000755010986742709)
              ·
                refine ⟨58574616000070782280007129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 624795904000755010986742709 58574616000070782280007129)
                ·
                  refine ⟨43930962000053086710005347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58574616000070782280007129 43930962000053086710005347)
                  ·
                    refine ⟨65896443000079630065008021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43930962000053086710005347 65896443000079630065008021)
                    ·
                      refine ⟨3088895765628732659297251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65896443000079630065008021 3088895765628732659297251)
                      ·
                        rfl

theorem cell23_6015603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 6].length) (baseStart_6015603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015603 prefixEnd_6015603 := by exact prefixLift 6015603
  have htrace : WordTrace (prefixWord ++ tailWord_6015603) baseStart_6015603 baseEnd_6015603 := by
    simpa [prefixWord, tailWord_6015603, baseEnd_6015603] using wordTrace_append hprefix tailTrace_6015603
  have hstable : (prefixWord ++ tailWord_6015603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015603).length < 2 ^ (prefixWord ++ tailWord_6015603).sum := by decide
  have hdescent : baseEnd_6015603 < baseStart_6015603 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6015633 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 8]
def baseStart_6015633 : Nat := 118140960795 + 6015633 * 2 ^ 59
def prefixEnd_6015633 : Nat := 4983230072969 + 3 ^ 40 * 6015633 * 2
def baseEnd_6015633 : Nat := 3088911170048367541922113

theorem tailTrace_6015633 : CollatzResearch.WordTrace tailWord_6015633 prefixEnd_6015633 3088911170048367541922113 := by
  unfold tailWord_6015633
  simp only [CollatzResearch.WordTrace]
  refine ⟨219408160615396504166947553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146272107076931002777965035 219408160615396504166947553)
  ·
    refine ⟨164556120461547378125210665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219408160615396504166947553 164556120461547378125210665)
    ·
      refine ⟨123417090346160533593907999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164556120461547378125210665 123417090346160533593907999)
      ·
        refine ⟨185125635519240800390861999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123417090346160533593907999 185125635519240800390861999)
        ·
          refine ⟨277688453278861200586292999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185125635519240800390861999 277688453278861200586292999)
          ·
            refine ⟨416532679918291800879439499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277688453278861200586292999 416532679918291800879439499)
            ·
              refine ⟨624799019877437701319159249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 416532679918291800879439499 624799019877437701319159249)
              ·
                refine ⟨468599264908078275989369437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 624799019877437701319159249 468599264908078275989369437)
                ·
                  refine ⟨175724724340529353496013539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 468599264908078275989369437 175724724340529353496013539)
                  ·
                    refine ⟨263587086510794030244020309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 175724724340529353496013539 263587086510794030244020309)
                    ·
                      refine ⟨3088911170048367541922113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 263587086510794030244020309 3088911170048367541922113)
                      ·
                        rfl

theorem cell23_6015633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 8].length) (baseStart_6015633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015633 prefixEnd_6015633 := by exact prefixLift 6015633
  have htrace : WordTrace (prefixWord ++ tailWord_6015633) baseStart_6015633 baseEnd_6015633 := by
    simpa [prefixWord, tailWord_6015633, baseEnd_6015633] using wordTrace_append hprefix tailTrace_6015633
  have hstable : (prefixWord ++ tailWord_6015633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015633).length < 2 ^ (prefixWord ++ tailWord_6015633).sum := by decide
  have hdescent : baseEnd_6015633 < baseStart_6015633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6015644 : List Nat := [2, 2, 3, 2, 2, 2, 2, 1, 2, 2, 3]
def baseStart_6015644 : Nat := 118140960795 + 6015644 * 2 ^ 59
def prefixEnd_6015644 : Nat := 4983230072969 + 3 ^ 40 * 6015644 * 2
def baseEnd_6015644 : Nat := 3088916818335566998884563

theorem tailTrace_6015644 : CollatzResearch.WordTrace tailWord_6015644 prefixEnd_6015644 3088916818335566998884563 := by
  unfold tailWord_6015644
  simp only [CollatzResearch.WordTrace]
  refine ⟨109704280909178326522798993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146272374545571102030398657 109704280909178326522798993)
  ·
    refine ⟨82278210681883744892099245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109704280909178326522798993 82278210681883744892099245)
    ·
      refine ⟨30854329005706404334537217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82278210681883744892099245 30854329005706404334537217)
      ·
        refine ⟨23140746754279803250902913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30854329005706404334537217 23140746754279803250902913)
        ·
          refine ⟨17355560065709852438177185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23140746754279803250902913 17355560065709852438177185)
          ·
            refine ⟨13016670049282389328632889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17355560065709852438177185 13016670049282389328632889)
            ·
              refine ⟨9762502536961791996474667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13016670049282389328632889 9762502536961791996474667)
              ·
                refine ⟨14643753805442687994712001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9762502536961791996474667 14643753805442687994712001)
                ·
                  refine ⟨10982815354082015996034001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14643753805442687994712001 10982815354082015996034001)
                  ·
                    refine ⟨8237111515561511997025501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10982815354082015996034001 8237111515561511997025501)
                    ·
                      refine ⟨3088916818335566998884563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8237111515561511997025501 3088916818335566998884563)
                      ·
                        rfl

theorem cell23_6015644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_6015644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015644 prefixEnd_6015644 := by exact prefixLift 6015644
  have htrace : WordTrace (prefixWord ++ tailWord_6015644) baseStart_6015644 baseEnd_6015644 := by
    simpa [prefixWord, tailWord_6015644, baseEnd_6015644] using wordTrace_append hprefix tailTrace_6015644
  have hstable : (prefixWord ++ tailWord_6015644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015644).length < 2 ^ (prefixWord ++ tailWord_6015644).sum := by decide
  have hdescent : baseEnd_6015644 < baseStart_6015644 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6015697 : List Nat := [1, 2, 2, 1, 2, 3, 2, 4, 1, 1, 4]
def baseStart_6015697 : Nat := 118140960795 + 6015697 * 2 ^ 59
def prefixEnd_6015697 : Nat := 4983230072969 + 3 ^ 40 * 6015697 * 2
def baseEnd_6015697 : Nat := 3088944032810255291521819

theorem tailTrace_6015697 : CollatzResearch.WordTrace tailWord_6015697 prefixEnd_6015697 3088944032810255291521819 := by
  unfold tailWord_6015697
  simp only [CollatzResearch.WordTrace]
  refine ⟨219410494887164643097277345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146273663258109762064851563 219410494887164643097277345)
  ·
    refine ⟨164557871165373482322958009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219410494887164643097277345 164557871165373482322958009)
    ·
      refine ⟨123418403374030111742218507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164557871165373482322958009 123418403374030111742218507)
      ·
        refine ⟨185127605061045167613327761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123418403374030111742218507 185127605061045167613327761)
        ·
          refine ⟨138845703795783875709995821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185127605061045167613327761 138845703795783875709995821)
          ·
            refine ⟨52067138923418953391248433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138845703795783875709995821 52067138923418953391248433)
            ·
              refine ⟨39050354192564215043436325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52067138923418953391248433 39050354192564215043436325)
              ·
                refine ⟨7321941411105790320644311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39050354192564215043436325 7321941411105790320644311)
                ·
                  refine ⟨10982912116658685480966467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7321941411105790320644311 10982912116658685480966467)
                  ·
                    refine ⟨16474368174988028221449701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10982912116658685480966467 16474368174988028221449701)
                    ·
                      refine ⟨3088944032810255291521819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16474368174988028221449701 3088944032810255291521819)
                      ·
                        rfl

theorem cell23_6015697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 4, 1, 1, 4].length) (baseStart_6015697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015697 prefixEnd_6015697 := by exact prefixLift 6015697
  have htrace : WordTrace (prefixWord ++ tailWord_6015697) baseStart_6015697 baseEnd_6015697 := by
    simpa [prefixWord, tailWord_6015697, baseEnd_6015697] using wordTrace_append hprefix tailTrace_6015697
  have hstable : (prefixWord ++ tailWord_6015697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015697).length < 2 ^ (prefixWord ++ tailWord_6015697).sum := by decide
  have hdescent : baseEnd_6015697 < baseStart_6015697 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6015701 : List Nat := [1, 3, 2, 5, 1, 1, 1, 1, 1, 5, 2]
def baseStart_6015701 : Nat := 118140960795 + 6015701 * 2 ^ 59
def prefixEnd_6015701 : Nat := 4983230072969 + 3 ^ 40 * 6015701 * 2
def baseEnd_6015701 : Nat := 3088946086732873275871801

theorem tailTrace_6015701 : CollatzResearch.WordTrace tailWord_6015701 prefixEnd_6015701 3088946086732873275871801 := by
  unfold tailWord_6015701
  simp only [CollatzResearch.WordTrace]
  refine ⟨219410640779150151780422957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146273760519433434520281971 219410640779150151780422957)
  ·
    refine ⟨82278990292181306917658609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219410640779150151780422957 82278990292181306917658609)
    ·
      refine ⟨61709242719135980188243957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82278990292181306917658609 61709242719135980188243957)
      ·
        refine ⟨5785241504918998142647871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61709242719135980188243957 5785241504918998142647871)
        ·
          refine ⟨8677862257378497213971807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5785241504918998142647871 8677862257378497213971807)
          ·
            refine ⟨13016793386067745820957711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8677862257378497213971807 13016793386067745820957711)
            ·
              refine ⟨19525190079101618731436567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13016793386067745820957711 19525190079101618731436567)
              ·
                refine ⟨29287785118652428097154851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19525190079101618731436567 29287785118652428097154851)
                ·
                  refine ⟨43931677677978642145732277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29287785118652428097154851 43931677677978642145732277)
                  ·
                    refine ⟨4118594782310497701162401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43931677677978642145732277 4118594782310497701162401)
                    ·
                      refine ⟨3088946086732873275871801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4118594782310497701162401 3088946086732873275871801)
                      ·
                        rfl

theorem cell23_6015701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_6015701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015701 prefixEnd_6015701 := by exact prefixLift 6015701
  have htrace : WordTrace (prefixWord ++ tailWord_6015701) baseStart_6015701 baseEnd_6015701 := by
    simpa [prefixWord, tailWord_6015701, baseEnd_6015701] using wordTrace_append hprefix tailTrace_6015701
  have hstable : (prefixWord ++ tailWord_6015701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015701).length < 2 ^ (prefixWord ++ tailWord_6015701).sum := by decide
  have hdescent : baseEnd_6015701 < baseStart_6015701 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6015708 : List Nat := [2, 2, 5, 1, 1, 1, 1, 5, 1, 1, 3]
def baseStart_6015708 : Nat := 118140960795 + 6015708 * 2 ^ 59
def prefixEnd_6015708 : Nat := 4983230072969 + 3 ^ 40 * 6015708 * 2
def baseEnd_6015708 : Nat := 3088949681097454748484269

theorem tailTrace_6015708 : CollatzResearch.WordTrace tailWord_6015708 prefixEnd_6015708 3088949681097454748484269 := by
  unfold tailWord_6015708
  simp only [CollatzResearch.WordTrace]
  refine ⟨109705448045062395987963889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146273930726749861317285185 109705448045062395987963889)
  ·
    refine ⟨82279086033796796990972917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109705448045062395987963889 82279086033796796990972917)
    ·
      refine ⟨7713664315668449717903711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82279086033796796990972917 7713664315668449717903711)
      ·
        refine ⟨11570496473502674576855567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7713664315668449717903711 11570496473502674576855567)
        ·
          refine ⟨17355744710254011865283351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11570496473502674576855567 17355744710254011865283351)
          ·
            refine ⟨26033617065381017797925027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17355744710254011865283351 26033617065381017797925027)
            ·
              refine ⟨39050425598071526696887541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26033617065381017797925027 39050425598071526696887541)
              ·
                refine ⟨3660977399819205627833207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39050425598071526696887541 3660977399819205627833207)
                ·
                  refine ⟨5491466099728808441749811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3660977399819205627833207 5491466099728808441749811)
                  ·
                    refine ⟨8237199149593212662624717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5491466099728808441749811 8237199149593212662624717)
                    ·
                      refine ⟨3088949681097454748484269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8237199149593212662624717 3088949681097454748484269)
                      ·
                        rfl

theorem cell23_6015708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_6015708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015708 prefixEnd_6015708 := by exact prefixLift 6015708
  have htrace : WordTrace (prefixWord ++ tailWord_6015708) baseStart_6015708 baseEnd_6015708 := by
    simpa [prefixWord, tailWord_6015708, baseEnd_6015708] using wordTrace_append hprefix tailTrace_6015708
  have hstable : (prefixWord ++ tailWord_6015708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015708).length < 2 ^ (prefixWord ++ tailWord_6015708).sum := by decide
  have hdescent : baseEnd_6015708 < baseStart_6015708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6015751 : List Nat := [1, 1, 4, 4, 1, 2, 2, 2, 1, 2, 3]
def baseStart_6015751 : Nat := 118140960795 + 6015751 * 2 ^ 59
def prefixEnd_6015751 : Nat := 4983230072969 + 3 ^ 40 * 6015751 * 2
def baseEnd_6015751 : Nat := 3088971760765598080246571

theorem tailTrace_6015751 : CollatzResearch.WordTrace tailWord_6015751 prefixEnd_6015751 3088971760765598080246571 := by
  unfold tailWord_6015751
  simp only [CollatzResearch.WordTrace]
  refine ⟨219412464428969010319743107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146274976285979340213162071 219412464428969010319743107)
  ·
    refine ⟨329118696643453515479614661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219412464428969010319743107 329118696643453515479614661)
    ·
      refine ⟨61709755620647534152427749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 329118696643453515479614661 61709755620647534152427749)
      ·
        refine ⟨11570579178871412653580203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61709755620647534152427749 11570579178871412653580203)
        ·
          refine ⟨17355868768307118980370305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11570579178871412653580203 17355868768307118980370305)
          ·
            refine ⟨13016901576230339235277729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17355868768307118980370305 13016901576230339235277729)
            ·
              refine ⟨9762676182172754426458297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13016901576230339235277729 9762676182172754426458297)
              ·
                refine ⟨7322007136629565819843723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9762676182172754426458297 7322007136629565819843723)
                ·
                  refine ⟨10983010704944348729765585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7322007136629565819843723 10983010704944348729765585)
                  ·
                    refine ⟨8237258028708261547324189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10983010704944348729765585 8237258028708261547324189)
                    ·
                      refine ⟨3088971760765598080246571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8237258028708261547324189 3088971760765598080246571)
                      ·
                        rfl

theorem cell23_6015751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_6015751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015751 prefixEnd_6015751 := by exact prefixLift 6015751
  have htrace : WordTrace (prefixWord ++ tailWord_6015751) baseStart_6015751 baseEnd_6015751 := by
    simpa [prefixWord, tailWord_6015751, baseEnd_6015751] using wordTrace_append hprefix tailTrace_6015751
  have hstable : (prefixWord ++ tailWord_6015751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015751).length < 2 ^ (prefixWord ++ tailWord_6015751).sum := by decide
  have hdescent : baseEnd_6015751 < baseStart_6015751 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6015804 : List Nat := [2, 2, 2, 2, 1, 1, 1, 5, 1, 4, 2]
def baseStart_6015804 : Nat := 118140960795 + 6015804 * 2 ^ 59
def prefixEnd_6015804 : Nat := 4983230072969 + 3 ^ 40 * 6015804 * 2
def baseEnd_6015804 : Nat := 3088998975240286372883827

theorem tailTrace_6015804 : CollatzResearch.WordTrace tailWord_6015804 prefixEnd_6015804 3088998975240286372883827 := by
  unfold tailWord_6015804
  simp only [CollatzResearch.WordTrace]
  refine ⟨109707198748888500185711233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146276264998518000247614977 109707198748888500185711233)
  ·
    refine ⟨82280399061666375139283425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109707198748888500185711233 82280399061666375139283425)
    ·
      refine ⟨61710299296249781354462569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82280399061666375139283425 61710299296249781354462569)
      ·
        refine ⟨46282724472187336015846927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61710299296249781354462569 46282724472187336015846927)
        ·
          refine ⟨69424086708281004023770391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46282724472187336015846927 69424086708281004023770391)
          ·
            refine ⟨104136130062421506035655587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69424086708281004023770391 104136130062421506035655587)
            ·
              refine ⟨156204195093632259053483381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104136130062421506035655587 156204195093632259053483381)
              ·
                refine ⟨14644143290028024286264067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 156204195093632259053483381 14644143290028024286264067)
                ·
                  refine ⟨21966214935042036429396101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14644143290028024286264067 21966214935042036429396101)
                  ·
                    refine ⟨4118665300320381830511769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21966214935042036429396101 4118665300320381830511769)
                    ·
                      refine ⟨3088998975240286372883827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4118665300320381830511769 3088998975240286372883827)
                      ·
                        rfl

theorem cell23_6015804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 1, 4, 2].length) (baseStart_6015804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015804 prefixEnd_6015804 := by exact prefixLift 6015804
  have htrace : WordTrace (prefixWord ++ tailWord_6015804) baseStart_6015804 baseEnd_6015804 := by
    simpa [prefixWord, tailWord_6015804, baseEnd_6015804] using wordTrace_append hprefix tailTrace_6015804
  have hstable : (prefixWord ++ tailWord_6015804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015804).length < 2 ^ (prefixWord ++ tailWord_6015804).sum := by decide
  have hdescent : baseEnd_6015804 < baseStart_6015804 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6015807 : List Nat := [1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 5]
def baseStart_6015807 : Nat := 118140960795 + 6015807 * 2 ^ 59
def prefixEnd_6015807 : Nat := 4983230072969 + 3 ^ 40 * 6015807 * 2
def baseEnd_6015807 : Nat := 3089000515682249861146313

theorem tailTrace_6015807 : CollatzResearch.WordTrace tailWord_6015807 prefixEnd_6015807 3089000515682249861146313 := by
  unfold tailWord_6015807
  simp only [CollatzResearch.WordTrace]
  refine ⟨219414506916766131883781675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146276337944510754589187783 219414506916766131883781675)
  ·
    refine ⟨329121760375149197825672513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219414506916766131883781675 329121760375149197825672513)
    ·
      refine ⟨246841320281361898369254385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329121760375149197825672513 246841320281361898369254385)
      ·
        refine ⟨185130990211021423776940789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246841320281361898369254385 185130990211021423776940789)
        ·
          refine ⟨17356030332283258479088199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 185130990211021423776940789 17356030332283258479088199)
          ·
            refine ⟨26034045498424887718632299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17356030332283258479088199 26034045498424887718632299)
            ·
              refine ⟨39051068247637331577948449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26034045498424887718632299 39051068247637331577948449)
              ·
                refine ⟨29288301185727998683461337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39051068247637331577948449 29288301185727998683461337)
                ·
                  refine ⟨21966225889295999012596003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29288301185727998683461337 21966225889295999012596003)
                  ·
                    refine ⟨32949338833943998518894005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21966225889295999012596003 32949338833943998518894005)
                    ·
                      refine ⟨3089000515682249861146313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32949338833943998518894005 3089000515682249861146313)
                      ·
                        rfl

theorem cell23_6015807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 5].length) (baseStart_6015807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015807 prefixEnd_6015807 := by exact prefixLift 6015807
  have htrace : WordTrace (prefixWord ++ tailWord_6015807) baseStart_6015807 baseEnd_6015807 := by
    simpa [prefixWord, tailWord_6015807, baseEnd_6015807] using wordTrace_append hprefix tailTrace_6015807
  have hstable : (prefixWord ++ tailWord_6015807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015807).length < 2 ^ (prefixWord ++ tailWord_6015807).sum := by decide
  have hdescent : baseEnd_6015807 < baseStart_6015807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6015904 : List Nat := [2, 1, 1, 4, 1, 1, 3, 3, 3, 4]
def baseStart_6015904 : Nat := 118140960795 + 6015904 * 2 ^ 59
def prefixEnd_6015904 : Nat := 4983230072969 + 3 ^ 40 * 6015904 * 2
def baseEnd_6015904 : Nat := 1029683441101911993877789

theorem tailTrace_6015904 : CollatzResearch.WordTrace tailWord_6015904 prefixEnd_6015904 1029683441101911993877789 := by
  unfold tailWord_6015904
  simp only [CollatzResearch.WordTrace]
  refine ⟨109709022398707358725031383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146278696531609811633375177 109709022398707358725031383)
  ·
    refine ⟨164563533598061038087547075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109709022398707358725031383 164563533598061038087547075)
    ·
      refine ⟨246845300397091557131320613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164563533598061038087547075 246845300397091557131320613)
      ·
        refine ⟨46283493824454666962122615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 246845300397091557131320613 46283493824454666962122615)
        ·
          refine ⟨69425240736682000443183923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46283493824454666962122615 69425240736682000443183923)
          ·
            refine ⟨104137861105023000664775885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69425240736682000443183923 104137861105023000664775885)
            ·
              refine ⟨39051697914383625249290957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104137861105023000664775885 39051697914383625249290957)
              ·
                refine ⟨14644386717893859468484109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39051697914383625249290957 14644386717893859468484109)
                ·
                  refine ⟨5491645019210197300681541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14644386717893859468484109 5491645019210197300681541)
                  ·
                    refine ⟨1029683441101911993877789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5491645019210197300681541 1029683441101911993877789)
                    ·
                      rfl

theorem cell23_6015904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 3, 4].length) (baseStart_6015904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015904 prefixEnd_6015904 := by exact prefixLift 6015904
  have htrace : WordTrace (prefixWord ++ tailWord_6015904) baseStart_6015904 baseEnd_6015904 := by
    simpa [prefixWord, tailWord_6015904, baseEnd_6015904] using wordTrace_append hprefix tailTrace_6015904
  have hstable : (prefixWord ++ tailWord_6015904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015904).length < 2 ^ (prefixWord ++ tailWord_6015904).sum := by decide
  have hdescent : baseEnd_6015904 < baseStart_6015904 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6015942 : List Nat := [6, 1, 3, 1, 1, 1, 1, 2, 2, 5]
def baseStart_6015942 : Nat := 118140960795 + 6015942 * 2 ^ 59
def prefixEnd_6015942 : Nat := 4983230072969 + 3 ^ 40 * 6015942 * 2
def baseEnd_6015942 : Nat := 1029689945190202277652731

theorem tailTrace_6015942 : CollatzResearch.WordTrace tailWord_6015942 prefixEnd_6015942 1029689945190202277652731 := by
  unfold tailWord_6015942
  simp only [CollatzResearch.WordTrace]
  refine ⟨6856857211602407810623315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 146279620514184699959964053 6856857211602407810623315)
  ·
    refine ⟨10285285817403611715934973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6856857211602407810623315 10285285817403611715934973)
    ·
      refine ⟨3856982181526354393475615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10285285817403611715934973 3856982181526354393475615)
      ·
        refine ⟨5785473272289531590213423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3856982181526354393475615 5785473272289531590213423)
        ·
          refine ⟨8678209908434297385320135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5785473272289531590213423 8678209908434297385320135)
          ·
            refine ⟨13017314862651446077980203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8678209908434297385320135 13017314862651446077980203)
            ·
              refine ⟨19525972293977169116970305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13017314862651446077980203 19525972293977169116970305)
              ·
                refine ⟨14644479220482876837727729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19525972293977169116970305 14644479220482876837727729)
                ·
                  refine ⟨10983359415362157628295797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14644479220482876837727729 10983359415362157628295797)
                  ·
                    refine ⟨1029689945190202277652731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10983359415362157628295797 1029689945190202277652731)
                    ·
                      rfl

theorem cell23_6015942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_6015942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015942 prefixEnd_6015942 := by exact prefixLift 6015942
  have htrace : WordTrace (prefixWord ++ tailWord_6015942) baseStart_6015942 baseEnd_6015942 := by
    simpa [prefixWord, tailWord_6015942, baseEnd_6015942] using wordTrace_append hprefix tailTrace_6015942
  have hstable : (prefixWord ++ tailWord_6015942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015942).length < 2 ^ (prefixWord ++ tailWord_6015942).sum := by decide
  have hdescent : baseEnd_6015942 < baseStart_6015942 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6015971 : List Nat := [1, 1, 1, 6, 1, 1, 1, 2, 4, 3, 2]
def baseStart_6015971 : Nat := 118140960795 + 6015971 * 2 ^ 59
def prefixEnd_6015971 : Nat := 4983230072969 + 3 ^ 40 * 6015971 * 2
def baseEnd_6015971 : Nat := 3089084726509587219495559

theorem tailTrace_6015971 : CollatzResearch.WordTrace tailWord_6015971 prefixEnd_6015971 3089084726509587219495559 := by
  unfold tailWord_6015971
  simp only [CollatzResearch.WordTrace]
  refine ⟨219420488488171987892751767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146280325658781325261834511 219420488488171987892751767)
  ·
    refine ⟨329130732732257981839127651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219420488488171987892751767 329130732732257981839127651)
    ·
      refine ⟨493696099098386972758691477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329130732732257981839127651 493696099098386972758691477)
      ·
        refine ⟨23142004645236889348063663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 493696099098386972758691477 23142004645236889348063663)
        ·
          refine ⟨34713006967855334022095495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23142004645236889348063663 34713006967855334022095495)
          ·
            refine ⟨52069510451783001033143243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34713006967855334022095495 52069510451783001033143243)
            ·
              refine ⟨78104265677674501549714865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52069510451783001033143243 78104265677674501549714865)
              ·
                refine ⟨58578199258255876162286149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78104265677674501549714865 58578199258255876162286149)
                ·
                  refine ⟨10983412360922976780428653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58578199258255876162286149 10983412360922976780428653)
                  ·
                    refine ⟨4118779635346116292660745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10983412360922976780428653 4118779635346116292660745)
                    ·
                      refine ⟨3089084726509587219495559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4118779635346116292660745 3089084726509587219495559)
                      ·
                        rfl

theorem cell23_6015971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_6015971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015971 prefixEnd_6015971 := by exact prefixLift 6015971
  have htrace : WordTrace (prefixWord ++ tailWord_6015971) baseStart_6015971 baseEnd_6015971 := by
    simpa [prefixWord, tailWord_6015971, baseEnd_6015971] using wordTrace_append hprefix tailTrace_6015971
  have hstable : (prefixWord ++ tailWord_6015971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015971).length < 2 ^ (prefixWord ++ tailWord_6015971).sum := by decide
  have hdescent : baseEnd_6015971 < baseStart_6015971 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6015977 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 7, 6]
def baseStart_6015977 : Nat := 118140960795 + 6015977 * 2 ^ 59
def prefixEnd_6015977 : Nat := 4983230072969 + 3 ^ 40 * 6015977 * 2
def baseEnd_6015977 : Nat := 1029695935797838065340177

theorem tailTrace_6015977 : CollatzResearch.WordTrace tailWord_6015977 prefixEnd_6015977 1029695935797838065340177 := by
  unfold tailWord_6015977
  simp only [CollatzResearch.WordTrace]
  refine ⟨219420707326150250917470185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146280471550766833944980123 219420707326150250917470185)
  ·
    refine ⟨164565530494612688188102639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219420707326150250917470185 164565530494612688188102639)
    ·
      refine ⟨246848295741919032282153959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164565530494612688188102639 246848295741919032282153959)
      ·
        refine ⟨370272443612878548423230939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246848295741919032282153959 370272443612878548423230939)
        ·
          refine ⟨555408665419317822634846409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 370272443612878548423230939 555408665419317822634846409)
          ·
            refine ⟨416556499064488366976134807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 555408665419317822634846409 416556499064488366976134807)
            ·
              refine ⟨624834748596732550464202211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 416556499064488366976134807 624834748596732550464202211)
              ·
                refine ⟨937252122895098825696303317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 624834748596732550464202211 937252122895098825696303317)
                ·
                  refine ⟨21966846630353878727257109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 937252122895098825696303317 21966846630353878727257109)
                  ·
                    refine ⟨1029695935797838065340177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21966846630353878727257109 1029695935797838065340177)
                    ·
                      rfl

theorem cell23_6015977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 6].length) (baseStart_6015977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015977 prefixEnd_6015977 := by exact prefixLift 6015977
  have htrace : WordTrace (prefixWord ++ tailWord_6015977) baseStart_6015977 baseEnd_6015977 := by
    simpa [prefixWord, tailWord_6015977, baseEnd_6015977] using wordTrace_append hprefix tailTrace_6015977
  have hstable : (prefixWord ++ tailWord_6015977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015977).length < 2 ^ (prefixWord ++ tailWord_6015977).sum := by decide
  have hdescent : baseEnd_6015977 < baseStart_6015977 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6015987 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 5]
def baseStart_6015987 : Nat := 118140960795 + 6015987 * 2 ^ 59
def prefixEnd_6015987 : Nat := 4983230072969 + 3 ^ 40 * 6015987 * 2
def baseEnd_6015987 : Nat := 3089092942200059156895485

theorem tailTrace_6015987 : CollatzResearch.WordTrace tailWord_6015987 prefixEnd_6015987 3089092942200059156895485 := by
  unfold tailWord_6015987
  simp only [CollatzResearch.WordTrace]
  refine ⟨219421072056114022625334215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146280714704076015083556143 219421072056114022625334215)
  ·
    refine ⟨329131608084171033938001323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219421072056114022625334215 329131608084171033938001323)
    ·
      refine ⟨493697412126256550907001985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329131608084171033938001323 493697412126256550907001985)
      ·
        refine ⟨370273059094692413180251489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 493697412126256550907001985 370273059094692413180251489)
        ·
          refine ⟨277704794321019309885188617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 370273059094692413180251489 277704794321019309885188617)
          ·
            refine ⟨208278595740764482413891463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277704794321019309885188617 208278595740764482413891463)
            ·
              refine ⟨312417893611146723620837195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208278595740764482413891463 312417893611146723620837195)
              ·
                refine ⟨468626840416720085431255793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 312417893611146723620837195 468626840416720085431255793)
                ·
                  refine ⟨351470130312540064073441845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 468626840416720085431255793 351470130312540064073441845)
                  ·
                    refine ⟨32950324716800631006885173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 351470130312540064073441845 32950324716800631006885173)
                    ·
                      refine ⟨3089092942200059156895485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32950324716800631006885173 3089092942200059156895485)
                      ·
                        rfl

theorem cell23_6015987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 5].length) (baseStart_6015987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015987 prefixEnd_6015987 := by exact prefixLift 6015987
  have htrace : WordTrace (prefixWord ++ tailWord_6015987) baseStart_6015987 baseEnd_6015987 := by
    simpa [prefixWord, tailWord_6015987, baseEnd_6015987] using wordTrace_append hprefix tailTrace_6015987
  have hstable : (prefixWord ++ tailWord_6015987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015987).length < 2 ^ (prefixWord ++ tailWord_6015987).sum := by decide
  have hdescent : baseEnd_6015987 < baseStart_6015987 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6015994 : List Nat := [3, 1, 1, 1, 1, 2, 1, 3, 6, 4]
def baseStart_6015994 : Nat := 118140960795 + 6015994 * 2 ^ 59
def prefixEnd_6015994 : Nat := 4983230072969 + 3 ^ 40 * 6015994 * 2
def baseEnd_6015994 : Nat := 1029698845521546876502651

theorem tailTrace_6015994 : CollatzResearch.WordTrace tailWord_6015994 prefixEnd_6015994 1029698845521546876502651 := by
  unfold tailWord_6015994
  simp only [CollatzResearch.WordTrace]
  refine ⟨54855331841772165705209759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146280884911392441880559357 54855331841772165705209759)
  ·
    refine ⟨82282997762658248557814639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54855331841772165705209759 82282997762658248557814639)
    ·
      refine ⟨123424496643987372836721959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82282997762658248557814639 123424496643987372836721959)
      ·
        refine ⟨185136744965981059255082939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123424496643987372836721959 185136744965981059255082939)
        ·
          refine ⟨277705117448971588882624409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185136744965981059255082939 277705117448971588882624409)
          ·
            refine ⟨208278838086728691661968307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277705117448971588882624409 208278838086728691661968307)
            ·
              refine ⟨312418257130093037492952461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208278838086728691661968307 312418257130093037492952461)
              ·
                refine ⟨117156846423784889059857173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 312418257130093037492952461 117156846423784889059857173)
                ·
                  refine ⟨5491727176114916674680805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 117156846423784889059857173 5491727176114916674680805)
                  ·
                    refine ⟨1029698845521546876502651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5491727176114916674680805 1029698845521546876502651)
                    ·
                      rfl

theorem cell23_6015994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 6, 4].length) (baseStart_6015994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6015994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6015994 prefixEnd_6015994 := by exact prefixLift 6015994
  have htrace : WordTrace (prefixWord ++ tailWord_6015994) baseStart_6015994 baseEnd_6015994 := by
    simpa [prefixWord, tailWord_6015994, baseEnd_6015994] using wordTrace_append hprefix tailTrace_6015994
  have hstable : (prefixWord ++ tailWord_6015994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6015994).length < 2 ^ (prefixWord ++ tailWord_6015994).sum := by decide
  have hdescent : baseEnd_6015994 < baseStart_6015994 := by decide
  rcases family_descends (prefixWord ++ tailWord_6015994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6016011 : List Nat := [1, 1, 1, 1, 6, 2, 1, 4, 2, 4]
def baseStart_6016011 : Nat := 118140960795 + 6016011 * 2 ^ 59
def prefixEnd_6016011 : Nat := 4983230072969 + 3 ^ 40 * 6016011 * 2
def baseEnd_6016011 : Nat := 1029701755245255687665125

theorem tailTrace_6016011 : CollatzResearch.WordTrace tailWord_6016011 prefixEnd_6016011 1029701755245255687665125 := by
  unfold tailWord_6016011
  simp only [CollatzResearch.WordTrace]
  refine ⟨219421947408027074724207887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146281298272018049816138591 219421947408027074724207887)
  ·
    refine ⟨329132921112040612086311831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219421947408027074724207887 329132921112040612086311831)
    ·
      refine ⟨493699381668060918129467747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329132921112040612086311831 493699381668060918129467747)
      ·
        refine ⟨740549072502091377194201621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 493699381668060918129467747 740549072502091377194201621)
        ·
          refine ⟨34713237773535533305978201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 740549072502091377194201621 34713237773535533305978201)
          ·
            refine ⟨26034928330151649979483651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34713237773535533305978201 26034928330151649979483651)
            ·
              refine ⟨39052392495227474969225477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26034928330151649979483651 39052392495227474969225477)
              ·
                refine ⟨7322323592855151556729777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39052392495227474969225477 7322323592855151556729777)
                ·
                  refine ⟨5491742694641363667547333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7322323592855151556729777 5491742694641363667547333)
                  ·
                    refine ⟨1029701755245255687665125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5491742694641363667547333 1029701755245255687665125)
                    ·
                      rfl

theorem cell23_6016011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 4, 2, 4].length) (baseStart_6016011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6016011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6016011 prefixEnd_6016011 := by exact prefixLift 6016011
  have htrace : WordTrace (prefixWord ++ tailWord_6016011) baseStart_6016011 baseEnd_6016011 := by
    simpa [prefixWord, tailWord_6016011, baseEnd_6016011] using wordTrace_append hprefix tailTrace_6016011
  have hstable : (prefixWord ++ tailWord_6016011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6016011).length < 2 ^ (prefixWord ++ tailWord_6016011).sum := by decide
  have hdescent : baseEnd_6016011 < baseStart_6016011 := by decide
  rcases family_descends (prefixWord ++ tailWord_6016011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6016012 : List Nat := [2, 2, 1, 2, 3, 4, 2, 2, 1, 1, 3]
def baseStart_6016012 : Nat := 118140960795 + 6016012 * 2 ^ 59
def prefixEnd_6016012 : Nat := 4983230072969 + 3 ^ 40 * 6016012 * 2
def baseEnd_6016012 : Nat := 3089105779216421559082871

theorem tailTrace_6016012 : CollatzResearch.WordTrace tailWord_6016012 prefixEnd_6016012 3089105779216421559082871 := by
  unfold tailWord_6016012
  simp only [CollatzResearch.WordTrace]
  refine ⟨109710991940511725947497145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146281322587348967929996193 109710991940511725947497145)
  ·
    refine ⟨82283243955383794460622859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109710991940511725947497145 82283243955383794460622859)
    ·
      refine ⟨123424865933075691690934289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82283243955383794460622859 123424865933075691690934289)
      ·
        refine ⟨92568649449806768768200717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123424865933075691690934289 92568649449806768768200717)
        ·
          refine ⟨34713243543677538288075269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92568649449806768768200717 34713243543677538288075269)
          ·
            refine ⟨6508733164439538429014113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34713243543677538288075269 6508733164439538429014113)
            ·
              refine ⟨4881549873329653821760585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6508733164439538429014113 4881549873329653821760585)
              ·
                refine ⟨3661162404997240366320439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4881549873329653821760585 3661162404997240366320439)
                ·
                  refine ⟨5491743607495860549480659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3661162404997240366320439 5491743607495860549480659)
                  ·
                    refine ⟨8237615411243790824220989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5491743607495860549480659 8237615411243790824220989)
                    ·
                      refine ⟨3089105779216421559082871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8237615411243790824220989 3089105779216421559082871)
                      ·
                        rfl

theorem cell23_6016012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 2, 1, 1, 3].length) (baseStart_6016012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6016012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6016012 prefixEnd_6016012 := by exact prefixLift 6016012
  have htrace : WordTrace (prefixWord ++ tailWord_6016012) baseStart_6016012 baseEnd_6016012 := by
    simpa [prefixWord, tailWord_6016012, baseEnd_6016012] using wordTrace_append hprefix tailTrace_6016012
  have hstable : (prefixWord ++ tailWord_6016012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6016012).length < 2 ^ (prefixWord ++ tailWord_6016012).sum := by decide
  have hdescent : baseEnd_6016012 < baseStart_6016012 := by decide
  rcases family_descends (prefixWord ++ tailWord_6016012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6016021 : List Nat := [1, 3, 2, 1, 4, 1, 1, 2, 3, 2, 3]
def baseStart_6016021 : Nat := 118140960795 + 6016021 * 2 ^ 59
def prefixEnd_6016021 : Nat := 4983230072969 + 3 ^ 40 * 6016021 * 2
def baseEnd_6016021 : Nat := 3089110400542312023870329

theorem tailTrace_6016021 : CollatzResearch.WordTrace tailWord_6016021 prefixEnd_6016021 3089110400542312023870329 := by
  unfold tailWord_6016021
  simp only [CollatzResearch.WordTrace]
  refine ⟨219422312137990846432071917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146281541425327230954714611 219422312137990846432071917)
  ·
    refine ⟨82283367051746567412026969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219422312137990846432071917 82283367051746567412026969)
    ·
      refine ⟨61712525288809925559020227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82283367051746567412026969 61712525288809925559020227)
      ·
        refine ⟨92568787933214888338530341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61712525288809925559020227 92568787933214888338530341)
        ·
          refine ⟨17356647737477791563474439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92568787933214888338530341 17356647737477791563474439)
          ·
            refine ⟨26034971606216687345211659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17356647737477791563474439 26034971606216687345211659)
            ·
              refine ⟨39052457409325031017817489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26034971606216687345211659 39052457409325031017817489)
              ·
                refine ⟨29289343056993773263363117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39052457409325031017817489 29289343056993773263363117)
                ·
                  refine ⟨10983503646372664973761169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29289343056993773263363117 10983503646372664973761169)
                  ·
                    refine ⟨8237627734779498730320877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10983503646372664973761169 8237627734779498730320877)
                    ·
                      refine ⟨3089110400542312023870329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8237627734779498730320877 3089110400542312023870329)
                      ·
                        rfl

theorem cell23_6016021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 3, 2, 3].length) (baseStart_6016021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6016021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6016021 prefixEnd_6016021 := by exact prefixLift 6016021
  have htrace : WordTrace (prefixWord ++ tailWord_6016021) baseStart_6016021 baseEnd_6016021 := by
    simpa [prefixWord, tailWord_6016021, baseEnd_6016021] using wordTrace_append hprefix tailTrace_6016021
  have hstable : (prefixWord ++ tailWord_6016021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6016021).length < 2 ^ (prefixWord ++ tailWord_6016021).sum := by decide
  have hdescent : baseEnd_6016021 < baseStart_6016021 := by decide
  rcases family_descends (prefixWord ++ tailWord_6016021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6016024 : List Nat := [2, 1, 2, 3, 2, 2, 3, 8]
def baseStart_6016024 : Nat := 118140960795 + 6016024 * 2 ^ 59
def prefixEnd_6016024 : Nat := 4983230072969 + 3 ^ 40 * 6016024 * 2
def baseEnd_6016024 : Nat := 114411553369787981930845

theorem tailTrace_6016024 : CollatzResearch.WordTrace tailWord_6016024 prefixEnd_6016024 114411553369787981930845 := by
  unfold tailWord_6016024
  simp only [CollatzResearch.WordTrace]
  refine ⟨109711210778489988972215563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146281614371319985296287417 109711210778489988972215563)
  ·
    refine ⟨164566816167734983458323345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109711210778489988972215563 164566816167734983458323345)
    ·
      refine ⟨123425112125801237593742509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164566816167734983458323345 123425112125801237593742509)
      ·
        refine ⟨46284417047175464097653441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123425112125801237593742509 46284417047175464097653441)
        ·
          refine ⟨34713312785381598073240081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46284417047175464097653441 34713312785381598073240081)
          ·
            refine ⟨26034984589036198554930061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34713312785381598073240081 26034984589036198554930061)
            ·
              refine ⟨9763119220888574458098773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26034984589036198554930061 9763119220888574458098773)
              ·
                refine ⟨114411553369787981930845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9763119220888574458098773 114411553369787981930845)
                ·
                  rfl

theorem cell23_6016024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 8].length) (baseStart_6016024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6016024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6016024 prefixEnd_6016024 := by exact prefixLift 6016024
  have htrace : WordTrace (prefixWord ++ tailWord_6016024) baseStart_6016024 baseEnd_6016024 := by
    simpa [prefixWord, tailWord_6016024, baseEnd_6016024] using wordTrace_append hprefix tailTrace_6016024
  have hstable : (prefixWord ++ tailWord_6016024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6016024).length < 2 ^ (prefixWord ++ tailWord_6016024).sum := by decide
  have hdescent : baseEnd_6016024 < baseStart_6016024 := by decide
  rcases family_descends (prefixWord ++ tailWord_6016024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6016031 : List Nat := [1, 1, 2, 4, 1, 4, 2, 1, 1, 2, 4]
def baseStart_6016031 : Nat := 118140960795 + 6016031 * 2 ^ 59
def prefixEnd_6016031 : Nat := 4983230072969 + 3 ^ 40 * 6016031 * 2
def baseEnd_6016031 : Nat := 3089115535348856984745283

theorem tailTrace_6016031 : CollatzResearch.WordTrace tailWord_6016031 prefixEnd_6016031 3089115535348856984745283 := by
  unfold tailWord_6016031
  simp only [CollatzResearch.WordTrace]
  refine ⟨219422676867954618139935947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146281784578636412093290631 219422676867954618139935947)
  ·
    refine ⟨329134015301931927209903921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219422676867954618139935947 329134015301931927209903921)
    ·
      refine ⟨246850511476448945407427941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329134015301931927209903921 246850511476448945407427941)
      ·
        refine ⟨46284470901834177263892739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 246850511476448945407427941 46284470901834177263892739)
        ·
          refine ⟨69426706352751265895839109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46284470901834177263892739 69426706352751265895839109)
          ·
            refine ⟨13017507441140862355469833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69426706352751265895839109 13017507441140862355469833)
            ·
              refine ⟨9763130580855646766602375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13017507441140862355469833 9763130580855646766602375)
              ·
                refine ⟨14644695871283470149903563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9763130580855646766602375 14644695871283470149903563)
                ·
                  refine ⟨21967043806925205224855345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14644695871283470149903563 21967043806925205224855345)
                  ·
                    refine ⟨16475282855193903918641509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21967043806925205224855345 16475282855193903918641509)
                    ·
                      refine ⟨3089115535348856984745283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16475282855193903918641509 3089115535348856984745283)
                      ·
                        rfl

theorem cell23_6016031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_6016031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6016031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6016031 prefixEnd_6016031 := by exact prefixLift 6016031
  have htrace : WordTrace (prefixWord ++ tailWord_6016031) baseStart_6016031 baseEnd_6016031 := by
    simpa [prefixWord, tailWord_6016031, baseEnd_6016031] using wordTrace_append hprefix tailTrace_6016031
  have hstable : (prefixWord ++ tailWord_6016031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6016031).length < 2 ^ (prefixWord ++ tailWord_6016031).sum := by decide
  have hdescent : baseEnd_6016031 < baseStart_6016031 := by decide
  rcases family_descends (prefixWord ++ tailWord_6016031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6016051 : List Nat := [1, 1, 1, 2, 4, 1, 1, 4, 4, 1, 3]
def baseStart_6016051 : Nat := 118140960795 + 6016051 * 2 ^ 59
def prefixEnd_6016051 : Nat := 4983230072969 + 3 ^ 40 * 6016051 * 2
def baseEnd_6016051 : Nat := 3089125804961946906495191

theorem tailTrace_6016051 : CollatzResearch.WordTrace tailWord_6016051 prefixEnd_6016051 3089125804961946906495191 := by
  unfold tailWord_6016051
  simp only [CollatzResearch.WordTrace]
  refine ⟨219423406327882161555664007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146282270885254774370442671 219423406327882161555664007)
  ·
    refine ⟨329135109491823242333496011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219423406327882161555664007 329135109491823242333496011)
    ·
      refine ⟨493702664237734863500244017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329135109491823242333496011 493702664237734863500244017)
      ·
        refine ⟨370276998178301147625183013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 493702664237734863500244017 370276998178301147625183013)
        ·
          refine ⟨69426937158431465179721815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 370276998178301147625183013 69426937158431465179721815)
          ·
            refine ⟨104140405737647197769582723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69426937158431465179721815 104140405737647197769582723)
            ·
              refine ⟨156210608606470796654374085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104140405737647197769582723 156210608606470796654374085)
              ·
                refine ⟨29289489113713274372695141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 156210608606470796654374085 29289489113713274372695141)
                ·
                  refine ⟨5491779208821238944880339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29289489113713274372695141 5491779208821238944880339)
                  ·
                    refine ⟨8237668813231858417320509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5491779208821238944880339 8237668813231858417320509)
                    ·
                      refine ⟨3089125804961946906495191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8237668813231858417320509 3089125804961946906495191)
                      ·
                        rfl

theorem cell23_6016051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 4, 1, 3].length) (baseStart_6016051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6016051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6016051 prefixEnd_6016051 := by exact prefixLift 6016051
  have htrace : WordTrace (prefixWord ++ tailWord_6016051) baseStart_6016051 baseEnd_6016051 := by
    simpa [prefixWord, tailWord_6016051, baseEnd_6016051] using wordTrace_append hprefix tailTrace_6016051
  have hstable : (prefixWord ++ tailWord_6016051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6016051).length < 2 ^ (prefixWord ++ tailWord_6016051).sum := by decide
  have hdescent : baseEnd_6016051 < baseStart_6016051 := by decide
  rcases family_descends (prefixWord ++ tailWord_6016051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6016052 : List Nat := [2, 5, 1, 2, 1, 3, 2, 1, 1, 1, 4]
def baseStart_6016052 : Nat := 118140960795 + 6016052 * 2 ^ 59
def prefixEnd_6016052 : Nat := 4983230072969 + 3 ^ 40 * 6016052 * 2
def baseEnd_6016052 : Nat := 3089126318442601402582687

theorem tailTrace_6016052 : CollatzResearch.WordTrace tailWord_6016052 prefixEnd_6016052 3089126318442601402582687 := by
  unfold tailWord_6016052
  simp only [CollatzResearch.WordTrace]
  refine ⟨109711721400439269363225205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146282295200585692484300273 109711721400439269363225205)
  ·
    refine ⟨10285473881291181502802363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 109711721400439269363225205 10285473881291181502802363)
    ·
      refine ⟨15428210821936772254203545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10285473881291181502802363 15428210821936772254203545)
      ·
        refine ⟨11571158116452579190652659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15428210821936772254203545 11571158116452579190652659)
        ·
          refine ⟨17356737174678868785978989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11571158116452579190652659 17356737174678868785978989)
          ·
            refine ⟨6508776440504575794742121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17356737174678868785978989 6508776440504575794742121)
            ·
              refine ⟨4881582330378431846056591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6508776440504575794742121 4881582330378431846056591)
              ·
                refine ⟨7322373495567647769084887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4881582330378431846056591 7322373495567647769084887)
                ·
                  refine ⟨10983560243351471653627331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7322373495567647769084887 10983560243351471653627331)
                  ·
                    refine ⟨16475340365027207480440997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10983560243351471653627331 16475340365027207480440997)
                    ·
                      refine ⟨3089126318442601402582687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16475340365027207480440997 3089126318442601402582687)
                      ·
                        rfl

theorem cell23_6016052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_6016052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6016052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6016052 prefixEnd_6016052 := by exact prefixLift 6016052
  have htrace : WordTrace (prefixWord ++ tailWord_6016052) baseStart_6016052 baseEnd_6016052 := by
    simpa [prefixWord, tailWord_6016052, baseEnd_6016052] using wordTrace_append hprefix tailTrace_6016052
  have hstable : (prefixWord ++ tailWord_6016052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6016052).length < 2 ^ (prefixWord ++ tailWord_6016052).sum := by decide
  have hdescent : baseEnd_6016052 < baseStart_6016052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6016052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6016074 : List Nat := [3, 1, 2, 1, 1, 2, 2, 1, 1, 5, 4]
def baseStart_6016074 : Nat := 118140960795 + 6016074 * 2 ^ 59
def prefixEnd_6016074 : Nat := 4983230072969 + 3 ^ 40 * 6016074 * 2
def baseEnd_6016074 : Nat := 3089137615017000316507585

theorem tailTrace_6016074 : CollatzResearch.WordTrace tailWord_6016074 prefixEnd_6016074 3089137615017000316507585 := by
  unfold tailWord_6016074
  simp only [CollatzResearch.WordTrace]
  refine ⟨54856061301699709120937819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146282830137865890989167517 54856061301699709120937819)
  ·
    refine ⟨82284091952549563681406729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54856061301699709120937819 82284091952549563681406729)
    ·
      refine ⟨61713068964412172761055047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82284091952549563681406729 61713068964412172761055047)
      ·
        refine ⟨92569603446618259141582571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61713068964412172761055047 92569603446618259141582571)
        ·
          refine ⟨138854405169927388712373857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92569603446618259141582571 138854405169927388712373857)
          ·
            refine ⟨104140803877445541534280393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138854405169927388712373857 104140803877445541534280393)
            ·
              refine ⟨78105602908084156150710295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104140803877445541534280393 78105602908084156150710295)
              ·
                refine ⟨117158404362126234226065443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78105602908084156150710295 117158404362126234226065443)
                ·
                  refine ⟨175737606543189351339098165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117158404362126234226065443 175737606543189351339098165)
                  ·
                    refine ⟨16475400613424001688040453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 175737606543189351339098165 16475400613424001688040453)
                    ·
                      refine ⟨3089137615017000316507585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16475400613424001688040453 3089137615017000316507585)
                      ·
                        rfl

theorem cell23_6016074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_6016074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6016074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6016074 prefixEnd_6016074 := by exact prefixLift 6016074
  have htrace : WordTrace (prefixWord ++ tailWord_6016074) baseStart_6016074 baseEnd_6016074 := by
    simpa [prefixWord, tailWord_6016074, baseEnd_6016074] using wordTrace_append hprefix tailTrace_6016074
  have hstable : (prefixWord ++ tailWord_6016074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6016074).length < 2 ^ (prefixWord ++ tailWord_6016074).sum := by decide
  have hdescent : baseEnd_6016074 < baseStart_6016074 := by decide
  rcases family_descends (prefixWord ++ tailWord_6016074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6016085 : List Nat := [1, 3, 2, 2, 1, 2, 5, 1, 2, 1, 3]
def baseStart_6016085 : Nat := 118140960795 + 6016085 * 2 ^ 59
def prefixEnd_6016085 : Nat := 4983230072969 + 3 ^ 40 * 6016085 * 2
def baseEnd_6016085 : Nat := 3089143263304199773470035

theorem tailTrace_6016085 : CollatzResearch.WordTrace tailWord_6016085 prefixEnd_6016085 3089143263304199773470035 := by
  unfold tailWord_6016085
  simp only [CollatzResearch.WordTrace]
  refine ⟨219424646409758985362401709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146283097606505990241601139 219424646409758985362401709)
  ·
    refine ⟨82284242403659619510900641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219424646409758985362401709 82284242403659619510900641)
    ·
      refine ⟨61713181802744714633175481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82284242403659619510900641 61713181802744714633175481)
      ·
        refine ⟨46284886352058535974881611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61713181802744714633175481 46284886352058535974881611)
        ·
          refine ⟨69427329528087803962322417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46284886352058535974881611 69427329528087803962322417)
          ·
            refine ⟨52070497146065852971741813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69427329528087803962322417 52070497146065852971741813)
            ·
              refine ⟨4881609107443673716100795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52070497146065852971741813 4881609107443673716100795)
              ·
                refine ⟨7322413661165510574151193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4881609107443673716100795 7322413661165510574151193)
                ·
                  refine ⟨5491810245874132930613395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7322413661165510574151193 5491810245874132930613395)
                  ·
                    refine ⟨8237715368811199395920093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5491810245874132930613395 8237715368811199395920093)
                    ·
                      refine ⟨3089143263304199773470035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8237715368811199395920093 3089143263304199773470035)
                      ·
                        rfl

theorem cell23_6016085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 1, 2, 1, 3].length) (baseStart_6016085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6016085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6016085 prefixEnd_6016085 := by exact prefixLift 6016085
  have htrace : WordTrace (prefixWord ++ tailWord_6016085) baseStart_6016085 baseEnd_6016085 := by
    simpa [prefixWord, tailWord_6016085, baseEnd_6016085] using wordTrace_append hprefix tailTrace_6016085
  have hstable : (prefixWord ++ tailWord_6016085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6016085).length < 2 ^ (prefixWord ++ tailWord_6016085).sum := by decide
  have hdescent : baseEnd_6016085 < baseStart_6016085 := by decide
  rcases family_descends (prefixWord ++ tailWord_6016085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6016108 : List Nat := [2, 2, 1, 1, 3, 2, 1, 1, 6, 2, 2]
def baseStart_6016108 : Nat := 118140960795 + 6016108 * 2 ^ 59
def prefixEnd_6016108 : Nat := 4983230072969 + 3 ^ 40 * 6016108 * 2
def baseEnd_6016108 : Nat := 3089155073359253183482429

theorem tailTrace_6016108 : CollatzResearch.WordTrace tailWord_6016108 prefixEnd_6016108 3089155073359253183482429 := by
  unfold tailWord_6016108
  simp only [CollatzResearch.WordTrace]
  refine ⟨109712742644337830145244489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146283656859117106860325985 109712742644337830145244489)
  ·
    refine ⟨82284556983253372608933367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109712742644337830145244489 82284556983253372608933367)
    ·
      refine ⟨123426835474880058913400051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82284556983253372608933367 123426835474880058913400051)
      ·
        refine ⟨185140253212320088370100077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123426835474880058913400051 185140253212320088370100077)
        ·
          refine ⟨69427594954620033138787529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185140253212320088370100077 69427594954620033138787529)
          ·
            refine ⟨52070696215965024854090647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69427594954620033138787529 52070696215965024854090647)
            ·
              refine ⟨78106044323947537281135971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52070696215965024854090647 78106044323947537281135971)
              ·
                refine ⟨117159066485921305921703957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78106044323947537281135971 117159066485921305921703957)
                ·
                  refine ⟨5491831241527561215079873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 117159066485921305921703957 5491831241527561215079873)
                  ·
                    refine ⟨4118873431145670911309905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5491831241527561215079873 4118873431145670911309905)
                    ·
                      refine ⟨3089155073359253183482429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4118873431145670911309905 3089155073359253183482429)
                      ·
                        rfl

theorem cell23_6016108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 2, 2].length) (baseStart_6016108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6016108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6016108 prefixEnd_6016108 := by exact prefixLift 6016108
  have htrace : WordTrace (prefixWord ++ tailWord_6016108) baseStart_6016108 baseEnd_6016108 := by
    simpa [prefixWord, tailWord_6016108, baseEnd_6016108] using wordTrace_append hprefix tailTrace_6016108
  have hstable : (prefixWord ++ tailWord_6016108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6016108).length < 2 ^ (prefixWord ++ tailWord_6016108).sum := by decide
  have hdescent : baseEnd_6016108 < baseStart_6016108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6016108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6016124 : List Nat := [2, 2, 2, 1, 1, 3, 1, 1, 1, 2, 7]
def baseStart_6016124 : Nat := 118140960795 + 6016124 * 2 ^ 59
def prefixEnd_6016124 : Nat := 4983230072969 + 3 ^ 40 * 6016124 * 2
def baseEnd_6016124 : Nat := 3089163289049725120882355

theorem tailTrace_6016124 : CollatzResearch.WordTrace tailWord_6016124 prefixEnd_6016124 3089163289049725120882355 := by
  unfold tailWord_6016124
  simp only [CollatzResearch.WordTrace]
  refine ⟨109713034428308847511535713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146284045904411796682047617 109713034428308847511535713)
  ·
    refine ⟨82284775821231635633651785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109713034428308847511535713 82284775821231635633651785)
    ·
      refine ⟨61713581865923726725238839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82284775821231635633651785 61713581865923726725238839)
      ·
        refine ⟨92570372798885590087858259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61713581865923726725238839 92570372798885590087858259)
        ·
          refine ⟨138855559198328385131787389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92570372798885590087858259 138855559198328385131787389)
          ·
            refine ⟨52070834699373144424420271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138855559198328385131787389 52070834699373144424420271)
            ·
              refine ⟨78106252049059716636630407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52070834699373144424420271 78106252049059716636630407)
              ·
                refine ⟨117159378073589574954945611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78106252049059716636630407 117159378073589574954945611)
                ·
                  refine ⟨175739067110384362432418417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117159378073589574954945611 175739067110384362432418417)
                  ·
                    refine ⟨131804300332788271824313813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 175739067110384362432418417 131804300332788271824313813)
                    ·
                      refine ⟨3089163289049725120882355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 131804300332788271824313813 3089163289049725120882355)
                      ·
                        rfl

theorem cell23_6016124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_6016124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6016124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6016124 prefixEnd_6016124 := by exact prefixLift 6016124
  have htrace : WordTrace (prefixWord ++ tailWord_6016124) baseStart_6016124 baseEnd_6016124 := by
    simpa [prefixWord, tailWord_6016124, baseEnd_6016124] using wordTrace_append hprefix tailTrace_6016124
  have hstable : (prefixWord ++ tailWord_6016124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6016124).length < 2 ^ (prefixWord ++ tailWord_6016124).sum := by decide
  have hdescent : baseEnd_6016124 < baseStart_6016124 := by decide
  rcases family_descends (prefixWord ++ tailWord_6016124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6016125 : List Nat := [1, 4, 1, 1, 3, 1, 2, 4, 2, 2, 2]
def baseStart_6016125 : Nat := 118140960795 + 6016125 * 2 ^ 59
def prefixEnd_6016125 : Nat := 4983230072969 + 3 ^ 40 * 6016125 * 2
def baseEnd_6016125 : Nat := 3089163802530379616969851

theorem tailTrace_6016125 : CollatzResearch.WordTrace tailWord_6016125 prefixEnd_6016125 3089163802530379616969851 := by
  unfold tailWord_6016125
  simp only [CollatzResearch.WordTrace]
  refine ⟨219426105329614072193857829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146284070219742714795905219 219426105329614072193857829)
  ·
    refine ⟨41142394749302638536348343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 219426105329614072193857829 41142394749302638536348343)
    ·
      refine ⟨61713592123953957804522515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41142394749302638536348343 61713592123953957804522515)
      ·
        refine ⟨92570388185930936706783773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61713592123953957804522515 92570388185930936706783773)
        ·
          refine ⟨34713895569724101265043915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92570388185930936706783773 34713895569724101265043915)
          ·
            refine ⟨52070843354586151897565873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34713895569724101265043915 52070843354586151897565873)
            ·
              refine ⟨39053132515939613923174405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52070843354586151897565873 39053132515939613923174405)
              ·
                refine ⟨7322462346738677610595201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39053132515939613923174405 7322462346738677610595201)
                ·
                  refine ⟨5491846760054008207946401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7322462346738677610595201 5491846760054008207946401)
                  ·
                    refine ⟨4118885070040506155959801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5491846760054008207946401 4118885070040506155959801)
                    ·
                      refine ⟨3089163802530379616969851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4118885070040506155959801 3089163802530379616969851)
                      ·
                        rfl

theorem cell23_6016125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 4, 2, 2, 2].length) (baseStart_6016125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6016125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6016125 prefixEnd_6016125 := by exact prefixLift 6016125
  have htrace : WordTrace (prefixWord ++ tailWord_6016125) baseStart_6016125 baseEnd_6016125 := by
    simpa [prefixWord, tailWord_6016125, baseEnd_6016125] using wordTrace_append hprefix tailTrace_6016125
  have hstable : (prefixWord ++ tailWord_6016125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6016125).length < 2 ^ (prefixWord ++ tailWord_6016125).sum := by decide
  have hdescent : baseEnd_6016125 < baseStart_6016125 := by decide
  rcases family_descends (prefixWord ++ tailWord_6016125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6016142 : List Nat := [4, 1, 1, 3, 2, 2, 1, 3, 2, 2, 2]
def baseStart_6016142 : Nat := 118140960795 + 6016142 * 2 ^ 59
def prefixEnd_6016142 : Nat := 4983230072969 + 3 ^ 40 * 6016142 * 2
def baseEnd_6016142 : Nat := 3089172531701506050457273

theorem tailTrace_6016142 : CollatzResearch.WordTrace tailWord_6016142 prefixEnd_6016142 3089172531701506050457273 := by
  unfold tailWord_6016142
  simp only [CollatzResearch.WordTrace]
  refine ⟨27428340671319060512153335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146284483580368322731484453 27428340671319060512153335)
  ·
    refine ⟨41142511006978590768230003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27428340671319060512153335 41142511006978590768230003)
    ·
      refine ⟨61713766510467886152345005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41142511006978590768230003 61713766510467886152345005)
      ·
        refine ⟨23142662441425457307129377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61713766510467886152345005 23142662441425457307129377)
        ·
          refine ⟨17356996831069092980347033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23142662441425457307129377 17356996831069092980347033)
          ·
            refine ⟨13017747623301819735260275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17356996831069092980347033 13017747623301819735260275)
            ·
              refine ⟨19526621434952729602890413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13017747623301819735260275 19526621434952729602890413)
              ·
                refine ⟨7322483038107273601083905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19526621434952729602890413 7322483038107273601083905)
                ·
                  refine ⟨5491862278580455200812929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7322483038107273601083905 5491862278580455200812929)
                  ·
                    refine ⟨4118896708935341400609697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5491862278580455200812929 4118896708935341400609697)
                    ·
                      refine ⟨3089172531701506050457273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4118896708935341400609697 3089172531701506050457273)
                      ·
                        rfl

theorem cell23_6016142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_6016142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6016142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6016142 prefixEnd_6016142 := by exact prefixLift 6016142
  have htrace : WordTrace (prefixWord ++ tailWord_6016142) baseStart_6016142 baseEnd_6016142 := by
    simpa [prefixWord, tailWord_6016142, baseEnd_6016142] using wordTrace_append hprefix tailTrace_6016142
  have hstable : (prefixWord ++ tailWord_6016142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6016142).length < 2 ^ (prefixWord ++ tailWord_6016142).sum := by decide
  have hdescent : baseEnd_6016142 < baseStart_6016142 := by decide
  rcases family_descends (prefixWord ++ tailWord_6016142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6016144 : List Nat := [2, 1, 1, 1, 1, 1, 4, 4, 1, 7]
def baseStart_6016144 : Nat := 118140960795 + 6016144 * 2 ^ 59
def prefixEnd_6016144 : Nat := 4983230072969 + 3 ^ 40 * 6016144 * 2
def baseEnd_6016144 : Nat := 1029724519554271680877421

theorem tailTrace_6016144 : CollatzResearch.WordTrace tailWord_6016144 prefixEnd_6016144 1029724519554271680877421 := by
  unfold tailWord_6016144
  simp only [CollatzResearch.WordTrace]
  refine ⟨109713399158272619219399743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146284532211030158959199657 109713399158272619219399743)
  ·
    refine ⟨164570098737408928829099615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109713399158272619219399743 164570098737408928829099615)
    ·
      refine ⟨246855148106113393243649423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164570098737408928829099615 246855148106113393243649423)
      ·
        refine ⟨370282722159170089865474135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246855148106113393243649423 370282722159170089865474135)
        ·
          refine ⟨555424083238755134798211203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 370282722159170089865474135 555424083238755134798211203)
          ·
            refine ⟨833136124858132702197316805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 555424083238755134798211203 833136124858132702197316805)
            ·
              refine ⟨156213023410899881661996901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 833136124858132702197316805 156213023410899881661996901)
              ·
                refine ⟨29289941889543727811624419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 156213023410899881661996901 29289941889543727811624419)
                ·
                  refine ⟨43934912834315591717436629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29289941889543727811624419 43934912834315591717436629)
                  ·
                    refine ⟨1029724519554271680877421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43934912834315591717436629 1029724519554271680877421)
                    ·
                      rfl

theorem cell23_6016144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 1, 7].length) (baseStart_6016144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6016144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6016144 prefixEnd_6016144 := by exact prefixLift 6016144
  have htrace : WordTrace (prefixWord ++ tailWord_6016144) baseStart_6016144 baseEnd_6016144 := by
    simpa [prefixWord, tailWord_6016144, baseEnd_6016144] using wordTrace_append hprefix tailTrace_6016144
  have hstable : (prefixWord ++ tailWord_6016144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6016144).length < 2 ^ (prefixWord ++ tailWord_6016144).sum := by decide
  have hdescent : baseEnd_6016144 < baseStart_6016144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6016144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6016212 : List Nat := [2, 4, 1, 4, 1, 2, 1, 1, 2, 5]
def baseStart_6016212 : Nat := 118140960795 + 6016212 * 2 ^ 59
def prefixEnd_6016212 : Nat := 4983230072969 + 3 ^ 40 * 6016212 * 2
def baseEnd_6016212 : Nat := 1029736158449106925527317

theorem tailTrace_6016212 : CollatzResearch.WordTrace tailWord_6016212 prefixEnd_6016212 1029736158449106925527317 := by
  unfold tailWord_6016212
  simp only [CollatzResearch.WordTrace]
  refine ⟨109714639240149443026137445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146286185653532590701516593 109714639240149443026137445)
  ·
    refine ⟨20571494857528020567400771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109714639240149443026137445 20571494857528020567400771)
    ·
      refine ⟨30857242286292030851101157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20571494857528020567400771 30857242286292030851101157)
      ·
        refine ⟨5785732928679755784581467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30857242286292030851101157 5785732928679755784581467)
        ·
          refine ⟨8678599393019633676872201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5785732928679755784581467 8678599393019633676872201)
          ·
            refine ⟨6508949544764725257654151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8678599393019633676872201 6508949544764725257654151)
            ·
              refine ⟨9763424317147087886481227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6508949544764725257654151 9763424317147087886481227)
              ·
                refine ⟨14645136475720631829721841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9763424317147087886481227 14645136475720631829721841)
                ·
                  refine ⟨10983852356790473872291381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14645136475720631829721841 10983852356790473872291381)
                  ·
                    refine ⟨1029736158449106925527317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10983852356790473872291381 1029736158449106925527317)
                    ·
                      rfl

theorem cell23_6016212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_6016212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6016212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6016212 prefixEnd_6016212 := by exact prefixLift 6016212
  have htrace : WordTrace (prefixWord ++ tailWord_6016212) baseStart_6016212 baseEnd_6016212 := by
    simpa [prefixWord, tailWord_6016212, baseEnd_6016212] using wordTrace_append hprefix tailTrace_6016212
  have hstable : (prefixWord ++ tailWord_6016212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6016212).length < 2 ^ (prefixWord ++ tailWord_6016212).sum := by decide
  have hdescent : baseEnd_6016212 < baseStart_6016212 := by decide
  rcases family_descends (prefixWord ++ tailWord_6016212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6016225 : List Nat := [1, 2, 3, 1, 3, 2, 1, 5, 1, 4]
def baseStart_6016225 : Nat := 118140960795 + 6016225 * 2 ^ 59
def prefixEnd_6016225 : Nat := 4983230072969 + 3 ^ 40 * 6016225 * 2
def baseEnd_6016225 : Nat := 1029738383531943075239797

theorem tailTrace_6016225 : CollatzResearch.WordTrace tailWord_6016225 prefixEnd_6016225 1029738383531943075239797 := by
  unfold tailWord_6016225
  simp only [CollatzResearch.WordTrace]
  refine ⟨219429752629251789272498129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146286501752834526181665419 219429752629251789272498129)
  ·
    refine ⟨164572314471938841954373597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219429752629251789272498129 164572314471938841954373597)
    ·
      refine ⟨61714617926977065732890099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164572314471938841954373597 61714617926977065732890099)
      ·
        refine ⟨92571926890465598599335149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61714617926977065732890099 92571926890465598599335149)
        ·
          refine ⟨34714472583924599474750681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92571926890465598599335149 34714472583924599474750681)
          ·
            refine ⟨26035854437943449606063011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34714472583924599474750681 26035854437943449606063011)
            ·
              refine ⟨39053781656915174409094517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26035854437943449606063011 39053781656915174409094517)
              ·
                refine ⟨3661292030335797600852611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39053781656915174409094517 3661292030335797600852611)
                ·
                  refine ⟨5491938045503696401278917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3661292030335797600852611 5491938045503696401278917)
                  ·
                    refine ⟨1029738383531943075239797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5491938045503696401278917 1029738383531943075239797)
                    ·
                      rfl

theorem cell23_6016225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 5, 1, 4].length) (baseStart_6016225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6016225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6016225 prefixEnd_6016225 := by exact prefixLift 6016225
  have htrace : WordTrace (prefixWord ++ tailWord_6016225) baseStart_6016225 baseEnd_6016225 := by
    simpa [prefixWord, tailWord_6016225, baseEnd_6016225] using wordTrace_append hprefix tailTrace_6016225
  have hstable : (prefixWord ++ tailWord_6016225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6016225).length < 2 ^ (prefixWord ++ tailWord_6016225).sum := by decide
  have hdescent : baseEnd_6016225 < baseStart_6016225 := by decide
  rcases family_descends (prefixWord ++ tailWord_6016225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6016238 : List Nat := [4, 1, 2, 1, 1, 1, 5, 2, 6]
def baseStart_6016238 : Nat := 118140960795 + 6016238 * 2 ^ 59
def prefixEnd_6016238 : Nat := 4983230072969 + 3 ^ 40 * 6016238 * 2
def baseEnd_6016238 : Nat := 343246869538259741650759

theorem tailTrace_6016238 : CollatzResearch.WordTrace tailWord_6016238 prefixEnd_6016238 343246869538259741650759 := by
  unfold tailWord_6016238
  simp only [CollatzResearch.WordTrace]
  refine ⟨27428778347275586561590171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146286817852136461661814245 27428778347275586561590171)
  ·
    refine ⟨41143167520913379842385257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27428778347275586561590171 41143167520913379842385257)
    ·
      refine ⟨30857375640685034881788943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41143167520913379842385257 30857375640685034881788943)
      ·
        refine ⟨46286063461027552322683415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30857375640685034881788943 46286063461027552322683415)
        ·
          refine ⟨69429095191541328484025123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46286063461027552322683415 69429095191541328484025123)
          ·
            refine ⟨104143642787311992726037685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69429095191541328484025123 104143642787311992726037685)
            ·
              refine ⟨9763466511310499318066033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 104143642787311992726037685 9763466511310499318066033)
              ·
                refine ⟨7322599883482874488549525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9763466511310499318066033 7322599883482874488549525)
                ·
                  refine ⟨343246869538259741650759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7322599883482874488549525 343246869538259741650759)
                  ·
                    rfl

theorem cell23_6016238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 2, 6].length) (baseStart_6016238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6016238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6016238 prefixEnd_6016238 := by exact prefixLift 6016238
  have htrace : WordTrace (prefixWord ++ tailWord_6016238) baseStart_6016238 baseEnd_6016238 := by
    simpa [prefixWord, tailWord_6016238, baseEnd_6016238] using wordTrace_append hprefix tailTrace_6016238
  have hstable : (prefixWord ++ tailWord_6016238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6016238).length < 2 ^ (prefixWord ++ tailWord_6016238).sum := by decide
  have hdescent : baseEnd_6016238 < baseStart_6016238 := by decide
  rcases family_descends (prefixWord ++ tailWord_6016238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6016268 : List Nat := [2, 2, 1, 2, 2, 3, 1, 4, 1, 5]
def baseStart_6016268 : Nat := 118140960795 + 6016268 * 2 ^ 59
def prefixEnd_6016268 : Nat := 4983230072969 + 3 ^ 40 * 6016268 * 2
def baseEnd_6016268 : Nat := 1029745743421324185827231

theorem tailTrace_6016268 : CollatzResearch.WordTrace tailWord_6016268 prefixEnd_6016268 1029745743421324185827231 := by
  unfold tailWord_6016268
  simp only [CollatzResearch.WordTrace]
  refine ⟨109715660484048003808156729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146287547312064005077542305 109715660484048003808156729)
  ·
    refine ⟨82286745363036002856117547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109715660484048003808156729 82286745363036002856117547)
    ·
      refine ⟨123430118044554004284176321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82286745363036002856117547 123430118044554004284176321)
      ·
        refine ⟨92572588533415503213132241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123430118044554004284176321 92572588533415503213132241)
        ·
          refine ⟨69429441400061627409849181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92572588533415503213132241 69429441400061627409849181)
          ·
            refine ⟨26036040525023110278693443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69429441400061627409849181 26036040525023110278693443)
            ·
              refine ⟨39054060787534665418040165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26036040525023110278693443 39054060787534665418040165)
              ·
                refine ⟨7322636397662749765882531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39054060787534665418040165 7322636397662749765882531)
                ·
                  refine ⟨10983954596494124648823797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7322636397662749765882531 10983954596494124648823797)
                  ·
                    refine ⟨1029745743421324185827231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10983954596494124648823797 1029745743421324185827231)
                    ·
                      rfl

theorem cell23_6016268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 4, 1, 5].length) (baseStart_6016268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6016268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6016268 prefixEnd_6016268 := by exact prefixLift 6016268
  have htrace : WordTrace (prefixWord ++ tailWord_6016268) baseStart_6016268 baseEnd_6016268 := by
    simpa [prefixWord, tailWord_6016268, baseEnd_6016268] using wordTrace_append hprefix tailTrace_6016268
  have hstable : (prefixWord ++ tailWord_6016268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6016268).length < 2 ^ (prefixWord ++ tailWord_6016268).sum := by decide
  have hdescent : baseEnd_6016268 < baseStart_6016268 := by decide
  rcases family_descends (prefixWord ++ tailWord_6016268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6016285 : List Nat := [1, 4, 2, 3, 1, 1, 2, 3, 1, 5]
def baseStart_6016285 : Nat := 118140960795 + 6016285 * 2 ^ 59
def prefixEnd_6016285 : Nat := 4983230072969 + 3 ^ 40 * 6016285 * 2
def baseEnd_6016285 : Nat := 1029748653145032996989705

theorem tailTrace_6016285 : CollatzResearch.WordTrace tailWord_6016285 prefixEnd_6016285 1029748653145032996989705 := by
  unfold tailWord_6016285
  simp only [CollatzResearch.WordTrace]
  refine ⟨219431941009034419519682309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146287960672689613013121539 219431941009034419519682309)
  ·
    refine ⟨41143488939193953659940433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 219431941009034419519682309 41143488939193953659940433)
    ·
      refine ⟨30857616704395465244955325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41143488939193953659940433 30857616704395465244955325)
      ·
        refine ⟨11571606264148299466858247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30857616704395465244955325 11571606264148299466858247)
        ·
          refine ⟨17357409396222449200287371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11571606264148299466858247 17357409396222449200287371)
          ·
            refine ⟨26036114094333673800431057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17357409396222449200287371 26036114094333673800431057)
            ·
              refine ⟨19527085570750255350323293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26036114094333673800431057 19527085570750255350323293)
              ·
                refine ⟨7322657089031345756371235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19527085570750255350323293 7322657089031345756371235)
                ·
                  refine ⟨10983985633547018634556853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7322657089031345756371235 10983985633547018634556853)
                  ·
                    refine ⟨1029748653145032996989705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10983985633547018634556853 1029748653145032996989705)
                    ·
                      rfl

theorem cell23_6016285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_6016285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6016285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6016285 prefixEnd_6016285 := by exact prefixLift 6016285
  have htrace : WordTrace (prefixWord ++ tailWord_6016285) baseStart_6016285 baseEnd_6016285 := by
    simpa [prefixWord, tailWord_6016285, baseEnd_6016285] using wordTrace_append hprefix tailTrace_6016285
  have hstable : (prefixWord ++ tailWord_6016285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6016285).length < 2 ^ (prefixWord ++ tailWord_6016285).sum := by decide
  have hdescent : baseEnd_6016285 < baseStart_6016285 := by decide
  rcases family_descends (prefixWord ++ tailWord_6016285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6016318 : List Nat := [4, 2, 1, 2, 1, 1, 1, 3, 1, 1, 6]
def baseStart_6016318 : Nat := 118140960795 + 6016318 * 2 ^ 59
def prefixEnd_6016318 : Nat := 4983230072969 + 3 ^ 40 * 6016318 * 2
def baseEnd_6016318 : Nat := 3089262904296697361856463

theorem tailTrace_6016318 : CollatzResearch.WordTrace tailWord_6016318 prefixEnd_6016318 3089262904296697361856463 := by
  unfold tailWord_6016318
  simp only [CollatzResearch.WordTrace]
  refine ⟨27429143077239358269454201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146288763078609910770422405 27429143077239358269454201)
  ·
    refine ⟨20571857307929518702090651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27429143077239358269454201 20571857307929518702090651)
    ·
      refine ⟨30857785961894278053135977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20571857307929518702090651 30857785961894278053135977)
      ·
        refine ⟨23143339471420708539851983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30857785961894278053135977 23143339471420708539851983)
        ·
          refine ⟨34715009207131062809777975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23143339471420708539851983 34715009207131062809777975)
          ·
            refine ⟨52072513810696594214666963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34715009207131062809777975 52072513810696594214666963)
            ·
              refine ⟨78108770716044891322000445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52072513810696594214666963 78108770716044891322000445)
              ·
                refine ⟨29290789018516834245750167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78108770716044891322000445 29290789018516834245750167)
                ·
                  refine ⟨43936183527775251368625251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29290789018516834245750167 43936183527775251368625251)
                  ·
                    refine ⟨65904275291662877052937877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43936183527775251368625251 65904275291662877052937877)
                    ·
                      refine ⟨3089262904296697361856463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65904275291662877052937877 3089262904296697361856463)
                      ·
                        rfl

theorem cell23_6016318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_6016318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6016318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6016318 prefixEnd_6016318 := by exact prefixLift 6016318
  have htrace : WordTrace (prefixWord ++ tailWord_6016318) baseStart_6016318 baseEnd_6016318 := by
    simpa [prefixWord, tailWord_6016318, baseEnd_6016318] using wordTrace_append hprefix tailTrace_6016318
  have hstable : (prefixWord ++ tailWord_6016318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6016318).length < 2 ^ (prefixWord ++ tailWord_6016318).sum := by decide
  have hdescent : baseEnd_6016318 < baseStart_6016318 := by decide
  rcases family_descends (prefixWord ++ tailWord_6016318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6016356 : List Nat := [2, 3, 1, 1, 3, 2, 4, 2, 1, 2, 2]
def baseStart_6016356 : Nat := 118140960795 + 6016356 * 2 ^ 59
def prefixEnd_6016356 : Nat := 4983230072969 + 3 ^ 40 * 6016356 * 2
def baseEnd_6016356 : Nat := 3089282416561568213181289

theorem tailTrace_6016356 : CollatzResearch.WordTrace tailWord_6016356 prefixEnd_6016356 3089282416561568213181289 := by
  unfold tailWord_6016356
  simp only [CollatzResearch.WordTrace]
  refine ⟨109717265295888599322758461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146289687061184799097011281 109717265295888599322758461)
  ·
    refine ⟨41143974485958224746034423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109717265295888599322758461 41143974485958224746034423)
    ·
      refine ⟨61715961728937337119051635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41143974485958224746034423 61715961728937337119051635)
      ·
        refine ⟨92573942593406005678577453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61715961728937337119051635 92573942593406005678577453)
        ·
          refine ⟨34715228472527252129466545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92573942593406005678577453 34715228472527252129466545)
          ·
            refine ⟨26036421354395439097099909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34715228472527252129466545 26036421354395439097099909)
            ·
              refine ⟨4881829003949144830706233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26036421354395439097099909 4881829003949144830706233)
              ·
                refine ⟨3661371752961858623029675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4881829003949144830706233 3661371752961858623029675)
                ·
                  refine ⟨5492057629442787934544513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3661371752961858623029675 5492057629442787934544513)
                  ·
                    refine ⟨4119043222082090950908385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5492057629442787934544513 4119043222082090950908385)
                    ·
                      refine ⟨3089282416561568213181289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4119043222082090950908385 3089282416561568213181289)
                      ·
                        rfl

theorem cell23_6016356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 2, 1, 2, 2].length) (baseStart_6016356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6016356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6016356 prefixEnd_6016356 := by exact prefixLift 6016356
  have htrace : WordTrace (prefixWord ++ tailWord_6016356) baseStart_6016356 baseEnd_6016356 := by
    simpa [prefixWord, tailWord_6016356, baseEnd_6016356] using wordTrace_append hprefix tailTrace_6016356
  have hstable : (prefixWord ++ tailWord_6016356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6016356).length < 2 ^ (prefixWord ++ tailWord_6016356).sum := by decide
  have hdescent : baseEnd_6016356 < baseStart_6016356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6016356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6016362 : List Nat := [3, 1, 3, 3, 3, 1, 1, 8]
def baseStart_6016362 : Nat := 118140960795 + 6016362 * 2 ^ 59
def prefixEnd_6016362 : Nat := 4983230072969 + 3 ^ 40 * 6016362 * 2
def baseEnd_6016362 : Nat := 114417981386870192211343

theorem tailTrace_6016362 : CollatzResearch.WordTrace tailWord_6016362 prefixEnd_6016362 114417981386870192211343 := by
  unfold tailWord_6016362
  simp only [CollatzResearch.WordTrace]
  refine ⟨54858687357438865417558835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146289832953170307780156893 54858687357438865417558835)
  ·
    refine ⟨82288031036158298126338253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54858687357438865417558835 82288031036158298126338253)
    ·
      refine ⟨30858011638559361797376845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82288031036158298126338253 30858011638559361797376845)
      ·
        refine ⟨11571754364459760674016317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30858011638559361797376845 11571754364459760674016317)
        ·
          refine ⟨4339407886672410252756119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11571754364459760674016317 4339407886672410252756119)
          ·
            refine ⟨6509111830008615379134179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4339407886672410252756119 6509111830008615379134179)
            ·
              refine ⟨9763667745012923068701269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6509111830008615379134179 9763667745012923068701269)
              ·
                refine ⟨114417981386870192211343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9763667745012923068701269 114417981386870192211343)
                ·
                  rfl

theorem cell23_6016362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 8].length) (baseStart_6016362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6016362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6016362 prefixEnd_6016362 := by exact prefixLift 6016362
  have htrace : WordTrace (prefixWord ++ tailWord_6016362) baseStart_6016362 baseEnd_6016362 := by
    simpa [prefixWord, tailWord_6016362, baseEnd_6016362] using wordTrace_append hprefix tailTrace_6016362
  have hstable : (prefixWord ++ tailWord_6016362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6016362).length < 2 ^ (prefixWord ++ tailWord_6016362).sum := by decide
  have hdescent : baseEnd_6016362 < baseStart_6016362 := by decide
  rcases family_descends (prefixWord ++ tailWord_6016362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6016395 : List Nat := [1, 1, 1, 1, 4, 3, 1, 4, 1, 4, 2]
def baseStart_6016395 : Nat := 118140960795 + 6016395 * 2 ^ 59
def prefixEnd_6016395 : Nat := 4983230072969 + 3 ^ 40 * 6016395 * 2
def baseEnd_6016395 : Nat := 3089302442307093560593609

theorem tailTrace_6016395 : CollatzResearch.WordTrace tailWord_6016395 prefixEnd_6016395 3089302442307093560593609 := by
  unfold tailWord_6016395
  simp only [CollatzResearch.WordTrace]
  refine ⟨219435953038635908306186639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146290635359090605537457759 219435953038635908306186639)
  ·
    refine ⟨329153929557953862459279959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219435953038635908306186639 329153929557953862459279959)
    ·
      refine ⟨493730894336930793688919939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329153929557953862459279959 493730894336930793688919939)
      ·
        refine ⟨740596341505396190533379909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 493730894336930793688919939 740596341505396190533379909)
        ·
          refine ⟨138861814032261785725008733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 740596341505396190533379909 138861814032261785725008733)
          ·
            refine ⟨52073180262098169646878275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138861814032261785725008733 52073180262098169646878275)
            ·
              refine ⟨78109770393147254470317413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52073180262098169646878275 78109770393147254470317413)
              ·
                refine ⟨14645581948715110213184515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78109770393147254470317413 14645581948715110213184515)
                ·
                  refine ⟨21968372923072665319776773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14645581948715110213184515 21968372923072665319776773)
                  ·
                    refine ⟨4119069923076124747458145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21968372923072665319776773 4119069923076124747458145)
                    ·
                      refine ⟨3089302442307093560593609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4119069923076124747458145 3089302442307093560593609)
                      ·
                        rfl

theorem cell23_6016395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 4, 2].length) (baseStart_6016395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6016395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6016395 prefixEnd_6016395 := by exact prefixLift 6016395
  have htrace : WordTrace (prefixWord ++ tailWord_6016395) baseStart_6016395 baseEnd_6016395 := by
    simpa [prefixWord, tailWord_6016395, baseEnd_6016395] using wordTrace_append hprefix tailTrace_6016395
  have hstable : (prefixWord ++ tailWord_6016395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6016395).length < 2 ^ (prefixWord ++ tailWord_6016395).sum := by decide
  have hdescent : baseEnd_6016395 < baseStart_6016395 := by decide
  rcases family_descends (prefixWord ++ tailWord_6016395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6016429 : List Nat := [1, 5, 2, 2, 1, 1, 3, 1, 1, 4, 2]
def baseStart_6016429 : Nat := 118140960795 + 6016429 * 2 ^ 59
def prefixEnd_6016429 : Nat := 4983230072969 + 3 ^ 40 * 6016429 * 2
def baseEnd_6016429 : Nat := 3089319900649346427568453

theorem tailTrace_6016429 : CollatzResearch.WordTrace tailWord_6016429 prefixEnd_6016429 3089319900649346427568453 := by
  unfold tailWord_6016429
  simp only [CollatzResearch.WordTrace]
  refine ⟨219437193120512732112924341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146291462080341821408616227 219437193120512732112924341)
  ·
    refine ⟨20572236855048068635586657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 219437193120512732112924341 20572236855048068635586657)
    ·
      refine ⟨15429177641286051476689993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20572236855048068635586657 15429177641286051476689993)
      ·
        refine ⟨11571883230964538607517495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15429177641286051476689993 11571883230964538607517495)
        ·
          refine ⟨17357824846446807911276243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11571883230964538607517495 17357824846446807911276243)
          ·
            refine ⟨26036737269670211866914365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17357824846446807911276243 26036737269670211866914365)
            ·
              refine ⟨9763776476126329450092887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26036737269670211866914365 9763776476126329450092887)
              ·
                refine ⟨14645664714189494175139331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9763776476126329450092887 14645664714189494175139331)
                ·
                  refine ⟨21968497071284241262708997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14645664714189494175139331 21968497071284241262708997)
                  ·
                    refine ⟨4119093200865795236757937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21968497071284241262708997 4119093200865795236757937)
                    ·
                      refine ⟨3089319900649346427568453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4119093200865795236757937 3089319900649346427568453)
                      ·
                        rfl

theorem cell23_6016429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_6016429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6016429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6016429 prefixEnd_6016429 := by exact prefixLift 6016429
  have htrace : WordTrace (prefixWord ++ tailWord_6016429) baseStart_6016429 baseEnd_6016429 := by
    simpa [prefixWord, tailWord_6016429, baseEnd_6016429] using wordTrace_append hprefix tailTrace_6016429
  have hstable : (prefixWord ++ tailWord_6016429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6016429).length < 2 ^ (prefixWord ++ tailWord_6016429).sum := by decide
  have hdescent : baseEnd_6016429 < baseStart_6016429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6016429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6016448 : List Nat := [2, 1, 1, 2, 3, 1, 4, 1, 1, 7]
def baseStart_6016448 : Nat := 118140960795 + 6016448 * 2 ^ 59
def prefixEnd_6016448 : Nat := 4983230072969 + 3 ^ 40 * 6016448 * 2
def baseEnd_6016448 : Nat := 1029776552260593951076955

theorem tailTrace_6016448 : CollatzResearch.WordTrace tailWord_6016448 prefixEnd_6016448 1029776552260593951076955 := by
  unfold tailWord_6016448
  simp only [CollatzResearch.WordTrace]
  refine ⟨109718943053721949178932999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146291924071629265571910665 109718943053721949178932999)
  ·
    refine ⟨164578414580582923768399499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109718943053721949178932999 164578414580582923768399499)
    ·
      refine ⟨246867621870874385652599249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164578414580582923768399499 246867621870874385652599249)
      ·
        refine ⟨185150716403155789239449437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246867621870874385652599249 185150716403155789239449437)
        ·
          refine ⟨69431518651183420964793539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185150716403155789239449437 69431518651183420964793539)
          ·
            refine ⟨104147277976775131447190309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69431518651183420964793539 104147277976775131447190309)
            ·
              refine ⟨19527614620645337146348183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104147277976775131447190309 19527614620645337146348183)
              ·
                refine ⟨29291421930968005719522275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19527614620645337146348183 29291421930968005719522275)
                ·
                  refine ⟨43937132896452008579283413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29291421930968005719522275 43937132896452008579283413)
                  ·
                    refine ⟨1029776552260593951076955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43937132896452008579283413 1029776552260593951076955)
                    ·
                      rfl

theorem cell23_6016448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 1, 7].length) (baseStart_6016448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6016448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6016448 prefixEnd_6016448 := by exact prefixLift 6016448
  have htrace : WordTrace (prefixWord ++ tailWord_6016448) baseStart_6016448 baseEnd_6016448 := by
    simpa [prefixWord, tailWord_6016448, baseEnd_6016448] using wordTrace_append hprefix tailTrace_6016448
  have hstable : (prefixWord ++ tailWord_6016448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6016448).length < 2 ^ (prefixWord ++ tailWord_6016448).sum := by decide
  have hdescent : baseEnd_6016448 < baseStart_6016448 := by decide
  rcases family_descends (prefixWord ++ tailWord_6016448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6016495 : List Nat := [1, 1, 2, 1, 4, 1, 2, 4, 3, 4]
def baseStart_6016495 : Nat := 118140960795 + 6016495 * 2 ^ 59
def prefixEnd_6016495 : Nat := 4983230072969 + 3 ^ 40 * 6016495 * 2
def baseEnd_6016495 : Nat := 1029784596790847723114383

theorem tailTrace_6016495 : CollatzResearch.WordTrace tailWord_6016495 prefixEnd_6016495 1029784596790847723114383 := by
  unfold tailWord_6016495
  simp only [CollatzResearch.WordTrace]
  refine ⟨219439600338273625384826939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146293066892182416923217959 219439600338273625384826939)
  ·
    refine ⟨329159400507410438077240409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219439600338273625384826939 329159400507410438077240409)
    ·
      refine ⟨246869550380557828557930307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329159400507410438077240409 246869550380557828557930307)
      ·
        refine ⟨370304325570836742836895461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246869550380557828557930307 370304325570836742836895461)
        ·
          refine ⟨69432061044531889281917899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 370304325570836742836895461 69432061044531889281917899)
          ·
            refine ⟨104148091566797833922876849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69432061044531889281917899 104148091566797833922876849)
            ·
              refine ⟨78111068675098375442157637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104148091566797833922876849 78111068675098375442157637)
              ·
                refine ⟨14645825376580945395404557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78111068675098375442157637 14645825376580945395404557)
                ·
                  refine ⟨5492184516217854523276709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14645825376580945395404557 5492184516217854523276709)
                  ·
                    refine ⟨1029784596790847723114383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5492184516217854523276709 1029784596790847723114383)
                    ·
                      rfl

theorem cell23_6016495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 3, 4].length) (baseStart_6016495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6016495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6016495 prefixEnd_6016495 := by exact prefixLift 6016495
  have htrace : WordTrace (prefixWord ++ tailWord_6016495) baseStart_6016495 baseEnd_6016495 := by
    simpa [prefixWord, tailWord_6016495, baseEnd_6016495] using wordTrace_append hprefix tailTrace_6016495
  have hstable : (prefixWord ++ tailWord_6016495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6016495).length < 2 ^ (prefixWord ++ tailWord_6016495).sum := by decide
  have hdescent : baseEnd_6016495 < baseStart_6016495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6016495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6016502 : List Nat := [5, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4]
def baseStart_6016502 : Nat := 118140960795 + 6016502 * 2 ^ 59
def prefixEnd_6016502 : Nat := 4983230072969 + 3 ^ 40 * 6016502 * 2
def baseEnd_6016502 : Nat := 3089357384737124641955617

theorem tailTrace_6016502 : CollatzResearch.WordTrace tailWord_6016502 prefixEnd_6016502 3089357384737124641955617 := by
  unfold tailWord_6016502
  simp only [CollatzResearch.WordTrace]
  refine ⟨13714990978078016598770735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 146293237099498843720221173 13714990978078016598770735)
  ·
    refine ⟨20572486467117024898156103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13714990978078016598770735 20572486467117024898156103)
    ·
      refine ⟨30858729700675537347234155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20572486467117024898156103 30858729700675537347234155)
      ·
        refine ⟨46288094551013306020851233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30858729700675537347234155 46288094551013306020851233)
        ·
          refine ⟨34716070913259979515638425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46288094551013306020851233 34716070913259979515638425)
          ·
            refine ⟨26037053184944984636728819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34716070913259979515638425 26037053184944984636728819)
            ·
              refine ⟨39055579777417476955093229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26037053184944984636728819 39055579777417476955093229)
              ·
                refine ⟨14645842416531553858159961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39055579777417476955093229 14645842416531553858159961)
                ·
                  refine ⟨10984381812398665393619971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14645842416531553858159961 10984381812398665393619971)
                  ·
                    refine ⟨16476572718597998090429957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10984381812398665393619971 16476572718597998090429957)
                    ·
                      refine ⟨3089357384737124641955617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16476572718597998090429957 3089357384737124641955617)
                      ·
                        rfl

theorem cell23_6016502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_6016502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6016502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6016502 prefixEnd_6016502 := by exact prefixLift 6016502
  have htrace : WordTrace (prefixWord ++ tailWord_6016502) baseStart_6016502 baseEnd_6016502 := by
    simpa [prefixWord, tailWord_6016502, baseEnd_6016502] using wordTrace_append hprefix tailTrace_6016502
  have hstable : (prefixWord ++ tailWord_6016502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6016502).length < 2 ^ (prefixWord ++ tailWord_6016502).sum := by decide
  have hdescent : baseEnd_6016502 < baseStart_6016502 := by decide
  rcases family_descends (prefixWord ++ tailWord_6016502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6016508 : List Nat := [2, 2, 2, 1, 2, 1, 2, 1, 10]
def baseStart_6016508 : Nat := 118140960795 + 6016508 * 2 ^ 59
def prefixEnd_6016508 : Nat := 4983230072969 + 3 ^ 40 * 6016508 * 2
def baseEnd_6016508 : Nat := 343262273957894624275621

theorem tailTrace_6016508 : CollatzResearch.WordTrace tailWord_6016508 prefixEnd_6016508 343262273957894624275621 := by
  unfold tailWord_6016508
  simp only [CollatzResearch.WordTrace]
  refine ⟨109720037243613264302525089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146293382991484352403366785 109720037243613264302525089)
  ·
    refine ⟨82290027932709948226893817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109720037243613264302525089 82290027932709948226893817)
    ·
      refine ⟨61717520949532461170170363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82290027932709948226893817 61717520949532461170170363)
      ·
        refine ⟨92576281424298691755255545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61717520949532461170170363 92576281424298691755255545)
        ·
          refine ⟨69432211068224018816441659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92576281424298691755255545 69432211068224018816441659)
          ·
            refine ⟨104148316602336028224662489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69432211068224018816441659 104148316602336028224662489)
            ·
              refine ⟨78111237451752021168496867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104148316602336028224662489 78111237451752021168496867)
              ·
                refine ⟨117166856177628031752745301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78111237451752021168496867 117166856177628031752745301)
                ·
                  refine ⟨343262273957894624275621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 117166856177628031752745301 343262273957894624275621)
                  ·
                    rfl

theorem cell23_6016508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 10].length) (baseStart_6016508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6016508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6016508 prefixEnd_6016508 := by exact prefixLift 6016508
  have htrace : WordTrace (prefixWord ++ tailWord_6016508) baseStart_6016508 baseEnd_6016508 := by
    simpa [prefixWord, tailWord_6016508, baseEnd_6016508] using wordTrace_append hprefix tailTrace_6016508
  have hstable : (prefixWord ++ tailWord_6016508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6016508).length < 2 ^ (prefixWord ++ tailWord_6016508).sum := by decide
  have hdescent : baseEnd_6016508 < baseStart_6016508 := by decide
  rcases family_descends (prefixWord ++ tailWord_6016508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6016522 : List Nat := [3, 1, 2, 2, 2, 2, 2, 2, 2, 2, 3]
def baseStart_6016522 : Nat := 118140960795 + 6016522 * 2 ^ 59
def prefixEnd_6016522 : Nat := 4983230072969 + 3 ^ 40 * 6016522 * 2
def baseEnd_6016522 : Nat := 3089367654350214563705525

theorem tailTrace_6016522 : CollatzResearch.WordTrace tailWord_6016522 prefixEnd_6016522 3089367654350214563705525 := by
  unfold tailWord_6016522
  simp only [CollatzResearch.WordTrace]
  refine ⟨54860146277293952249014955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146293723406117205997373213 54860146277293952249014955)
  ·
    refine ⟨82290219415940928373522433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54860146277293952249014955 82290219415940928373522433)
    ·
      refine ⟨61717664561955696280141825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82290219415940928373522433 61717664561955696280141825)
      ·
        refine ⟨46288248421466772210106369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61717664561955696280141825 46288248421466772210106369)
        ·
          refine ⟨34716186316100079157579777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46288248421466772210106369 34716186316100079157579777)
          ·
            refine ⟨26037139737075059368184833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34716186316100079157579777 26037139737075059368184833)
            ·
              refine ⟨19527854802806294526138625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26037139737075059368184833 19527854802806294526138625)
              ·
                refine ⟨14645891102104720894603969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19527854802806294526138625 14645891102104720894603969)
                ·
                  refine ⟨10984418326578540670952977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14645891102104720894603969 10984418326578540670952977)
                  ·
                    refine ⟨8238313744933905503214733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10984418326578540670952977 8238313744933905503214733)
                    ·
                      refine ⟨3089367654350214563705525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8238313744933905503214733 3089367654350214563705525)
                      ·
                        rfl

theorem cell23_6016522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_6016522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6016522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6016522 prefixEnd_6016522 := by exact prefixLift 6016522
  have htrace : WordTrace (prefixWord ++ tailWord_6016522) baseStart_6016522 baseEnd_6016522 := by
    simpa [prefixWord, tailWord_6016522, baseEnd_6016522] using wordTrace_append hprefix tailTrace_6016522
  have hstable : (prefixWord ++ tailWord_6016522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6016522).length < 2 ^ (prefixWord ++ tailWord_6016522).sum := by decide
  have hdescent : baseEnd_6016522 < baseStart_6016522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6016522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6016602 : List Nat := [3, 1, 1, 2, 1, 1, 1, 7, 2, 4]
def baseStart_6016602 : Nat := 118140960795 + 6016602 * 2 ^ 59
def prefixEnd_6016602 : Nat := 4983230072969 + 3 ^ 40 * 6016602 * 2
def baseEnd_6016602 : Nat := 1029802910934191416901719

theorem tailTrace_6016602 : CollatzResearch.WordTrace tailWord_6016602 prefixEnd_6016602 1029802910934191416901719 := by
  unfold tailWord_6016602
  simp only [CollatzResearch.WordTrace]
  refine ⟨54860875737221495664743015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146295668632590655105981373 54860875737221495664743015)
  ·
    refine ⟨82291313605832243497114523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54860875737221495664743015 82291313605832243497114523)
    ·
      refine ⟨123436970408748365245671785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82291313605832243497114523 123436970408748365245671785)
      ·
        refine ⟨92577727806561273934253839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123436970408748365245671785 92577727806561273934253839)
        ·
          refine ⟨138866591709841910901380759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92577727806561273934253839 138866591709841910901380759)
          ·
            refine ⟨208299887564762866352071139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138866591709841910901380759 208299887564762866352071139)
            ·
              refine ⟨312449831347144299528106709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208299887564762866352071139 312449831347144299528106709)
              ·
                refine ⟨7323042922198694520190001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 312449831347144299528106709 7323042922198694520190001)
                ·
                  refine ⟨5492282191649020890142501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7323042922198694520190001 5492282191649020890142501)
                  ·
                    refine ⟨1029802910934191416901719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5492282191649020890142501 1029802910934191416901719)
                    ·
                      rfl

theorem cell23_6016602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 7, 2, 4].length) (baseStart_6016602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6016602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6016602 prefixEnd_6016602 := by exact prefixLift 6016602
  have htrace : WordTrace (prefixWord ++ tailWord_6016602) baseStart_6016602 baseEnd_6016602 := by
    simpa [prefixWord, tailWord_6016602, baseEnd_6016602] using wordTrace_append hprefix tailTrace_6016602
  have hstable : (prefixWord ++ tailWord_6016602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6016602).length < 2 ^ (prefixWord ++ tailWord_6016602).sum := by decide
  have hdescent : baseEnd_6016602 < baseStart_6016602 := by decide
  rcases family_descends (prefixWord ++ tailWord_6016602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6016609 : List Nat := [1, 2, 3, 1, 1, 3, 1, 4, 3, 2, 2]
def baseStart_6016609 : Nat := 118140960795 + 6016609 * 2 ^ 59
def prefixEnd_6016609 : Nat := 4983230072969 + 3 ^ 40 * 6016609 * 2
def baseEnd_6016609 : Nat := 3089412327167155723317625

theorem tailTrace_6016609 : CollatzResearch.WordTrace tailWord_6016609 prefixEnd_6016609 3089412327167155723317625 := by
  unfold tailWord_6016609
  simp only [CollatzResearch.WordTrace]
  refine ⟨219443758259860622854476881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146295838839907081902984587 219443758259860622854476881)
  ·
    refine ⟨164582818694895467140857661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219443758259860622854476881 164582818694895467140857661)
    ·
      refine ⟨61718557010585800177821623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164582818694895467140857661 61718557010585800177821623)
      ·
        refine ⟨92577835515878700266732435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61718557010585800177821623 92577835515878700266732435)
        ·
          refine ⟨138866753273818050400098653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92577835515878700266732435 138866753273818050400098653)
          ·
            refine ⟨52075032477681768900036995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138866753273818050400098653 52075032477681768900036995)
            ·
              refine ⟨78112548716522653350055493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52075032477681768900036995 78112548716522653350055493)
              ·
                refine ⟨14646102884347997503135405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78112548716522653350055493 14646102884347997503135405)
                ·
                  refine ⟨5492288581630499063675777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14646102884347997503135405 5492288581630499063675777)
                  ·
                    refine ⟨4119216436222874297756833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5492288581630499063675777 4119216436222874297756833)
                    ·
                      refine ⟨3089412327167155723317625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4119216436222874297756833 3089412327167155723317625)
                      ·
                        rfl

theorem cell23_6016609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 3, 2, 2].length) (baseStart_6016609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6016609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6016609 prefixEnd_6016609 := by exact prefixLift 6016609
  have htrace : WordTrace (prefixWord ++ tailWord_6016609) baseStart_6016609 baseEnd_6016609 := by
    simpa [prefixWord, tailWord_6016609, baseEnd_6016609] using wordTrace_append hprefix tailTrace_6016609
  have hstable : (prefixWord ++ tailWord_6016609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6016609).length < 2 ^ (prefixWord ++ tailWord_6016609).sum := by decide
  have hdescent : baseEnd_6016609 < baseStart_6016609 := by decide
  rcases family_descends (prefixWord ++ tailWord_6016609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6016629 : List Nat := [1, 3, 4, 2, 1, 2, 2, 1, 1, 1, 5]
def baseStart_6016629 : Nat := 118140960795 + 6016629 * 2 ^ 59
def prefixEnd_6016629 : Nat := 4983230072969 + 3 ^ 40 * 6016629 * 2
def baseEnd_6016629 : Nat := 3089422596780245645067533

theorem tailTrace_6016629 : CollatzResearch.WordTrace tailWord_6016629 prefixEnd_6016629 3089422596780245645067533 := by
  unfold tailWord_6016629
  simp only [CollatzResearch.WordTrace]
  refine ⟨219444487719788166270204941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146296325146525444180136627 219444487719788166270204941)
  ·
    refine ⟨82291682894920562351326853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219444487719788166270204941 82291682894920562351326853)
    ·
      refine ⟨15429690542797605440873785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82291682894920562351326853 15429690542797605440873785)
      ·
        refine ⟨11572267907098204080655339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15429690542797605440873785 11572267907098204080655339)
        ·
          refine ⟨17358401860647306120983009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11572267907098204080655339 17358401860647306120983009)
          ·
            refine ⟨13018801395485479590737257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17358401860647306120983009 13018801395485479590737257)
            ·
              refine ⟨9764101046614109693052943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13018801395485479590737257 9764101046614109693052943)
              ·
                refine ⟨14646151569921164539579415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9764101046614109693052943 14646151569921164539579415)
                ·
                  refine ⟨21969227354881746809369123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14646151569921164539579415 21969227354881746809369123)
                  ·
                    refine ⟨32953841032322620214053685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21969227354881746809369123 32953841032322620214053685)
                    ·
                      refine ⟨3089422596780245645067533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32953841032322620214053685 3089422596780245645067533)
                      ·
                        rfl

theorem cell23_6016629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_6016629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6016629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6016629 prefixEnd_6016629 := by exact prefixLift 6016629
  have htrace : WordTrace (prefixWord ++ tailWord_6016629) baseStart_6016629 baseEnd_6016629 := by
    simpa [prefixWord, tailWord_6016629, baseEnd_6016629] using wordTrace_append hprefix tailTrace_6016629
  have hstable : (prefixWord ++ tailWord_6016629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6016629).length < 2 ^ (prefixWord ++ tailWord_6016629).sum := by decide
  have hdescent : baseEnd_6016629 < baseStart_6016629 := by decide
  rcases family_descends (prefixWord ++ tailWord_6016629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6016645 : List Nat := [1, 3, 1, 1, 4, 1, 2, 1, 2, 7]
def baseStart_6016645 : Nat := 118140960795 + 6016645 * 2 ^ 59
def prefixEnd_6016645 : Nat := 4983230072969 + 3 ^ 40 * 6016645 * 2
def baseEnd_6016645 : Nat := 1029810270823572527489153

theorem tailTrace_6016645 : CollatzResearch.WordTrace tailWord_6016645 prefixEnd_6016645 1029810270823572527489153 := by
  unfold tailWord_6016645
  simp only [CollatzResearch.WordTrace]
  refine ⟨219445071287730201002787389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146296714191820134001858259 219445071287730201002787389)
  ·
    refine ⟨82291901732898825376045271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219445071287730201002787389 82291901732898825376045271)
    ·
      refine ⟨123437852599348238064067907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82291901732898825376045271 123437852599348238064067907)
      ·
        refine ⟨185156778899022357096101861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123437852599348238064067907 185156778899022357096101861)
        ·
          refine ⟨34716896043566691955519099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 185156778899022357096101861 34716896043566691955519099)
          ·
            refine ⟨52075344065350037933278649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34716896043566691955519099 52075344065350037933278649)
            ·
              refine ⟨39056508049012528449958987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52075344065350037933278649 39056508049012528449958987)
              ·
                refine ⟨58584762073518792674938481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39056508049012528449958987 58584762073518792674938481)
                ·
                  refine ⟨43938571555139094506203861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58584762073518792674938481 43938571555139094506203861)
                  ·
                    refine ⟨1029810270823572527489153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43938571555139094506203861 1029810270823572527489153)
                    ·
                      rfl

theorem cell23_6016645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 7].length) (baseStart_6016645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6016645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6016645 prefixEnd_6016645 := by exact prefixLift 6016645
  have htrace : WordTrace (prefixWord ++ tailWord_6016645) baseStart_6016645 baseEnd_6016645 := by
    simpa [prefixWord, tailWord_6016645, baseEnd_6016645] using wordTrace_append hprefix tailTrace_6016645
  have hstable : (prefixWord ++ tailWord_6016645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6016645).length < 2 ^ (prefixWord ++ tailWord_6016645).sum := by decide
  have hdescent : baseEnd_6016645 < baseStart_6016645 := by decide
  rcases family_descends (prefixWord ++ tailWord_6016645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6016665 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 4, 3, 4]
def baseStart_6016665 : Nat := 118140960795 + 6016665 * 2 ^ 59
def prefixEnd_6016665 : Nat := 4983230072969 + 3 ^ 40 * 6016665 * 2
def baseEnd_6016665 : Nat := 3089441082083807504217367

theorem tailTrace_6016665 : CollatzResearch.WordTrace tailWord_6016665 prefixEnd_6016665 3089441082083807504217367 := by
  unfold tailWord_6016665
  simp only [CollatzResearch.WordTrace]
  refine ⟨219445800747657744418515449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146297200498438496279010299 219445800747657744418515449)
  ·
    refine ⟨164584350560743308313886587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219445800747657744418515449 164584350560743308313886587)
    ·
      refine ⟨246876525841114962470829881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164584350560743308313886587 246876525841114962470829881)
      ·
        refine ⟨185157394380836221853122411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246876525841114962470829881 185157394380836221853122411)
        ·
          refine ⟨277736091571254332779683617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185157394380836221853122411 277736091571254332779683617)
          ·
            refine ⟨208302068678440749584762713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277736091571254332779683617 208302068678440749584762713)
            ·
              refine ⟨156226551508830562188572035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208302068678440749584762713 156226551508830562188572035)
              ·
                refine ⟨234339827263245843282858053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156226551508830562188572035 234339827263245843282858053)
                ·
                  refine ⟨43938717611858595615535885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 234339827263245843282858053 43938717611858595615535885)
                  ·
                    refine ⟨16477019104446973355825957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43938717611858595615535885 16477019104446973355825957)
                    ·
                      refine ⟨3089441082083807504217367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16477019104446973355825957 3089441082083807504217367)
                      ·
                        rfl

theorem cell23_6016665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 3, 4].length) (baseStart_6016665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6016665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6016665 prefixEnd_6016665 := by exact prefixLift 6016665
  have htrace : WordTrace (prefixWord ++ tailWord_6016665) baseStart_6016665 baseEnd_6016665 := by
    simpa [prefixWord, tailWord_6016665, baseEnd_6016665] using wordTrace_append hprefix tailTrace_6016665
  have hstable : (prefixWord ++ tailWord_6016665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6016665).length < 2 ^ (prefixWord ++ tailWord_6016665).sum := by decide
  have hdescent : baseEnd_6016665 < baseStart_6016665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6016665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6016680 : List Nat := [2, 1, 7, 1, 2, 1, 1, 1, 1, 1, 5]
def baseStart_6016680 : Nat := 118140960795 + 6016680 * 2 ^ 59
def prefixEnd_6016680 : Nat := 4983230072969 + 3 ^ 40 * 6016680 * 2
def baseEnd_6016680 : Nat := 3089448784293624945529799

theorem tailTrace_6016680 : CollatzResearch.WordTrace tailWord_6016680 prefixEnd_6016680 3089448784293624945529799 := by
  unfold tailWord_6016680
  simp only [CollatzResearch.WordTrace]
  refine ⟨109723173921301700990155747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146297565228402267986874329 109723173921301700990155747)
  ·
    refine ⟨164584760881952551485233621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109723173921301700990155747 164584760881952551485233621)
    ·
      refine ⟨3857455333170762925435163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 164584760881952551485233621 3857455333170762925435163)
      ·
        refine ⟨5786182999756144388152745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3857455333170762925435163 5786182999756144388152745)
        ·
          refine ⟨4339637249817108291114559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5786182999756144388152745 4339637249817108291114559)
          ·
            refine ⟨6509455874725662436671839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4339637249817108291114559 6509455874725662436671839)
            ·
              refine ⟨9764183812088493655007759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6509455874725662436671839 9764183812088493655007759)
              ·
                refine ⟨14646275718132740482511639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9764183812088493655007759 14646275718132740482511639)
                ·
                  refine ⟨21969413577199110723767459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14646275718132740482511639 21969413577199110723767459)
                  ·
                    refine ⟨32954120365798666085651189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21969413577199110723767459 32954120365798666085651189)
                    ·
                      refine ⟨3089448784293624945529799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32954120365798666085651189 3089448784293624945529799)
                      ·
                        rfl

theorem cell23_6016680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_6016680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6016680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6016680 prefixEnd_6016680 := by exact prefixLift 6016680
  have htrace : WordTrace (prefixWord ++ tailWord_6016680) baseStart_6016680 baseEnd_6016680 := by
    simpa [prefixWord, tailWord_6016680, baseEnd_6016680] using wordTrace_append hprefix tailTrace_6016680
  have hstable : (prefixWord ++ tailWord_6016680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6016680).length < 2 ^ (prefixWord ++ tailWord_6016680).sum := by decide
  have hdescent : baseEnd_6016680 < baseStart_6016680 := by decide
  rcases family_descends (prefixWord ++ tailWord_6016680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6016693 : List Nat := [1, 3, 3, 3, 2, 1, 2, 2, 2, 1, 3]
def baseStart_6016693 : Nat := 118140960795 + 6016693 * 2 ^ 59
def prefixEnd_6016693 : Nat := 4983230072969 + 3 ^ 40 * 6016693 * 2
def baseEnd_6016693 : Nat := 3089455459542133394667239

theorem tailTrace_6016693 : CollatzResearch.WordTrace tailWord_6016693 prefixEnd_6016693 3089455459542133394667239 := by
  unfold tailWord_6016693
  simp only [CollatzResearch.WordTrace]
  refine ⟨219446821991556305200534733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146297881327704203467023155 219446821991556305200534733)
  ·
    refine ⟨82292558246833614450200525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219446821991556305200534733 82292558246833614450200525)
    ·
      refine ⟨30859709342562605418825197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82292558246833614450200525 30859709342562605418825197)
      ·
        refine ⟨11572391003460977032059449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30859709342562605418825197 11572391003460977032059449)
        ·
          refine ⟨8679293252595732774044587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11572391003460977032059449 8679293252595732774044587)
          ·
            refine ⟨13018939878893599161066881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8679293252595732774044587 13018939878893599161066881)
            ·
              refine ⟨9764204909170199370800161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13018939878893599161066881 9764204909170199370800161)
              ·
                refine ⟨7323153681877649528100121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9764204909170199370800161 7323153681877649528100121)
                ·
                  refine ⟨5492365261408237146075091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7323153681877649528100121 5492365261408237146075091)
                  ·
                    refine ⟨8238547892112355719112637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5492365261408237146075091 8238547892112355719112637)
                    ·
                      refine ⟨3089455459542133394667239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8238547892112355719112637 3089455459542133394667239)
                      ·
                        rfl

theorem cell23_6016693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_6016693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6016693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6016693 prefixEnd_6016693 := by exact prefixLift 6016693
  have htrace : WordTrace (prefixWord ++ tailWord_6016693) baseStart_6016693 baseEnd_6016693 := by
    simpa [prefixWord, tailWord_6016693, baseEnd_6016693] using wordTrace_append hprefix tailTrace_6016693
  have hstable : (prefixWord ++ tailWord_6016693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6016693).length < 2 ^ (prefixWord ++ tailWord_6016693).sum := by decide
  have hdescent : baseEnd_6016693 < baseStart_6016693 := by decide
  rcases family_descends (prefixWord ++ tailWord_6016693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6016694 : List Nat := [5, 1, 3, 1, 1, 3, 2, 2, 1, 2, 2]
def baseStart_6016694 : Nat := 118140960795 + 6016694 * 2 ^ 59
def prefixEnd_6016694 : Nat := 4983230072969 + 3 ^ 40 * 6016694 * 2
def baseEnd_6016694 : Nat := 3089455973022787890754735

theorem tailTrace_6016694 : CollatzResearch.WordTrace tailWord_6016694 prefixEnd_6016694 3089455973022787890754735 := by
  unfold tailWord_6016694
  simp only [CollatzResearch.WordTrace]
  refine ⟨13715428654034542648207571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 146297905643035121580880757 13715428654034542648207571)
  ·
    refine ⟨20573142981051813972311357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13715428654034542648207571 20573142981051813972311357)
    ·
      refine ⟨7714928617894430239616759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20573142981051813972311357 7714928617894430239616759)
      ·
        refine ⟨11572392926841645359425139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7714928617894430239616759 11572392926841645359425139)
        ·
          refine ⟨17358589390262468039137709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11572392926841645359425139 17358589390262468039137709)
          ·
            refine ⟨6509471021348425514676641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17358589390262468039137709 6509471021348425514676641)
            ·
              refine ⟨4882103266011319136007481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6509471021348425514676641 4882103266011319136007481)
              ·
                refine ⟨3661577449508489352005611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4882103266011319136007481 3661577449508489352005611)
                ·
                  refine ⟨5492366174262734028008417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3661577449508489352005611 5492366174262734028008417)
                  ·
                    refine ⟨4119274630697050521006313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5492366174262734028008417 4119274630697050521006313)
                    ·
                      refine ⟨3089455973022787890754735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4119274630697050521006313 3089455973022787890754735)
                      ·
                        rfl

theorem cell23_6016694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_6016694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6016694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6016694 prefixEnd_6016694 := by exact prefixLift 6016694
  have htrace : WordTrace (prefixWord ++ tailWord_6016694) baseStart_6016694 baseEnd_6016694 := by
    simpa [prefixWord, tailWord_6016694, baseEnd_6016694] using wordTrace_append hprefix tailTrace_6016694
  have hstable : (prefixWord ++ tailWord_6016694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6016694).length < 2 ^ (prefixWord ++ tailWord_6016694).sum := by decide
  have hdescent : baseEnd_6016694 < baseStart_6016694 := by decide
  rcases family_descends (prefixWord ++ tailWord_6016694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6016699 : List Nat := [1, 1, 1, 1, 1, 2, 3, 5, 4, 2, 2]
def baseStart_6016699 : Nat := 118140960795 + 6016699 * 2 ^ 59
def prefixEnd_6016699 : Nat := 4983230072969 + 3 ^ 40 * 6016699 * 2
def baseEnd_6016699 : Nat := 3089458540426060371192211

theorem tailTrace_6016699 : CollatzResearch.WordTrace tailWord_6016699 prefixEnd_6016699 3089458540426060371192211 := by
  unfold tailWord_6016699
  simp only [CollatzResearch.WordTrace]
  refine ⟨219447040829534568225253151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146298027219689712150168767 219447040829534568225253151)
  ·
    refine ⟨329170561244301852337879727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219447040829534568225253151 329170561244301852337879727)
    ·
      refine ⟨493755841866452778506819591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329170561244301852337879727 493755841866452778506819591)
      ·
        refine ⟨740633762799679167760229387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 493755841866452778506819591 740633762799679167760229387)
        ·
          refine ⟨1110950644199518751640344081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 740633762799679167760229387 1110950644199518751640344081)
          ·
            refine ⟨833212983149639063730258061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1110950644199518751640344081 833212983149639063730258061)
            ·
              refine ⟨312454868681114648898846773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 833212983149639063730258061 312454868681114648898846773)
              ·
                refine ⟨29292643938854498334266885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 312454868681114648898846773 29292643938854498334266885)
                ·
                  refine ⟨5492370738535218437675041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29292643938854498334266885 5492370738535218437675041)
                  ·
                    refine ⟨4119278053901413828256281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5492370738535218437675041 4119278053901413828256281)
                    ·
                      refine ⟨3089458540426060371192211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4119278053901413828256281 3089458540426060371192211)
                      ·
                        rfl

theorem cell23_6016699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 4, 2, 2].length) (baseStart_6016699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6016699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6016699 prefixEnd_6016699 := by exact prefixLift 6016699
  have htrace : WordTrace (prefixWord ++ tailWord_6016699) baseStart_6016699 baseEnd_6016699 := by
    simpa [prefixWord, tailWord_6016699, baseEnd_6016699] using wordTrace_append hprefix tailTrace_6016699
  have hstable : (prefixWord ++ tailWord_6016699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6016699).length < 2 ^ (prefixWord ++ tailWord_6016699).sum := by decide
  have hdescent : baseEnd_6016699 < baseStart_6016699 := by decide
  rcases family_descends (prefixWord ++ tailWord_6016699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6016710 : List Nat := [6, 1, 2, 1, 1, 1, 2, 3, 2, 1, 3]
def baseStart_6016710 : Nat := 118140960795 + 6016710 * 2 ^ 59
def prefixEnd_6016710 : Nat := 4983230072969 + 3 ^ 40 * 6016710 * 2
def baseEnd_6016710 : Nat := 3089464188713259828154661

theorem tailTrace_6016710 : CollatzResearch.WordTrace tailWord_6016710 prefixEnd_6016710 3089464188713259828154661 := by
  unfold tailWord_6016710
  simp only [CollatzResearch.WordTrace]
  refine ⟨6857732563515459909496987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 146298294688329811402602389 6857732563515459909496987)
  ·
    refine ⟨10286598845273189864245481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6857732563515459909496987 10286598845273189864245481)
    ·
      refine ⟨7714949133954892398184111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10286598845273189864245481 7714949133954892398184111)
      ·
        refine ⟨11572423700932338597276167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7714949133954892398184111 11572423700932338597276167)
        ·
          refine ⟨17358635551398507895914251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11572423700932338597276167 17358635551398507895914251)
          ·
            refine ⟨26037953327097761843871377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17358635551398507895914251 26037953327097761843871377)
            ·
              refine ⟨19528464995323321382903533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26037953327097761843871377 19528464995323321382903533)
              ·
                refine ⟨7323174373246245518588825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19528464995323321382903533 7323174373246245518588825)
                ·
                  refine ⟨5492380779934684138941619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7323174373246245518588825 5492380779934684138941619)
                  ·
                    refine ⟨8238571169902026208412429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5492380779934684138941619 8238571169902026208412429)
                    ·
                      refine ⟨3089464188713259828154661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8238571169902026208412429 3089464188713259828154661)
                      ·
                        rfl

theorem cell23_6016710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_6016710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6016710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6016710 prefixEnd_6016710 := by exact prefixLift 6016710
  have htrace : WordTrace (prefixWord ++ tailWord_6016710) baseStart_6016710 baseEnd_6016710 := by
    simpa [prefixWord, tailWord_6016710, baseEnd_6016710] using wordTrace_append hprefix tailTrace_6016710
  have hstable : (prefixWord ++ tailWord_6016710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6016710).length < 2 ^ (prefixWord ++ tailWord_6016710).sum := by decide
  have hdescent : baseEnd_6016710 < baseStart_6016710 := by decide
  rcases family_descends (prefixWord ++ tailWord_6016710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6016712 : List Nat := [2, 1, 3, 1, 2, 2, 3, 1, 2, 2, 4]
def baseStart_6016712 : Nat := 118140960795 + 6016712 * 2 ^ 59
def prefixEnd_6016712 : Nat := 4983230072969 + 3 ^ 40 * 6016712 * 2
def baseEnd_6016712 : Nat := 3089465215674568820329651

theorem tailTrace_6016712 : CollatzResearch.WordTrace tailWord_6016712 prefixEnd_6016712 3089465215674568820329651 := by
  unfold tailWord_6016712
  simp only [CollatzResearch.WordTrace]
  refine ⟨109723757489243735722738195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146298343318991647630317593 109723757489243735722738195)
  ·
    refine ⟨164585636233865603584107293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109723757489243735722738195 164585636233865603584107293)
    ·
      refine ⟨61719613587699601344040235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164585636233865603584107293 61719613587699601344040235)
      ·
        refine ⟨92579420381549402016060353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61719613587699601344040235 92579420381549402016060353)
        ·
          refine ⟨69434565286162051512045265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92579420381549402016060353 69434565286162051512045265)
          ·
            refine ⟨52075923964621538634033949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69434565286162051512045265 52075923964621538634033949)
            ·
              refine ⟨19528471486733076987762731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52075923964621538634033949 19528471486733076987762731)
              ·
                refine ⟨29292707230099615481644097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19528471486733076987762731 29292707230099615481644097)
                ·
                  refine ⟨21969530422574711611233073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29292707230099615481644097 21969530422574711611233073)
                  ·
                    refine ⟨16477147816931033708424805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21969530422574711611233073 16477147816931033708424805)
                    ·
                      refine ⟨3089465215674568820329651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16477147816931033708424805 3089465215674568820329651)
                      ·
                        rfl

theorem cell23_6016712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_6016712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6016712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6016712 prefixEnd_6016712 := by exact prefixLift 6016712
  have htrace : WordTrace (prefixWord ++ tailWord_6016712) baseStart_6016712 baseEnd_6016712 := by
    simpa [prefixWord, tailWord_6016712, baseEnd_6016712] using wordTrace_append hprefix tailTrace_6016712
  have hstable : (prefixWord ++ tailWord_6016712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6016712).length < 2 ^ (prefixWord ++ tailWord_6016712).sum := by decide
  have hdescent : baseEnd_6016712 < baseStart_6016712 := by decide
  rcases family_descends (prefixWord ++ tailWord_6016712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6016722 : List Nat := [3, 2, 2, 2, 2, 1, 1, 1, 9]
def baseStart_6016722 : Nat := 118140960795 + 6016722 * 2 ^ 59
def prefixEnd_6016722 : Nat := 4983230072969 + 3 ^ 40 * 6016722 * 2
def baseEnd_6016722 : Nat := 343274483386790420133845

theorem tailTrace_6016722 : CollatzResearch.WordTrace tailWord_6016722 prefixEnd_6016722 343274483386790420133845 := by
  unfold tailWord_6016722
  simp only [CollatzResearch.WordTrace]
  refine ⟨54861969927112810788335105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146298586472300828768893613 54861969927112810788335105)
  ·
    refine ⟨41146477445334608091251329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54861969927112810788335105 41146477445334608091251329)
    ·
      refine ⟨30859858084000956068438497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41146477445334608091251329 30859858084000956068438497)
      ·
        refine ⟨23144893563000717051328873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30859858084000956068438497 23144893563000717051328873)
        ·
          refine ⟨17358670172250537788496655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23144893563000717051328873 17358670172250537788496655)
          ·
            refine ⟨26038005258375806682744983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17358670172250537788496655 26038005258375806682744983)
            ·
              refine ⟨39057007887563710024117475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26038005258375806682744983 39057007887563710024117475)
              ·
                refine ⟨58585511831345565036176213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39057007887563710024117475 58585511831345565036176213)
                ·
                  refine ⟨343274483386790420133845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 58585511831345565036176213 343274483386790420133845)
                  ·
                    rfl

theorem cell23_6016722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 9].length) (baseStart_6016722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6016722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6016722 prefixEnd_6016722 := by exact prefixLift 6016722
  have htrace : WordTrace (prefixWord ++ tailWord_6016722) baseStart_6016722 baseEnd_6016722 := by
    simpa [prefixWord, tailWord_6016722, baseEnd_6016722] using wordTrace_append hprefix tailTrace_6016722
  have hstable : (prefixWord ++ tailWord_6016722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6016722).length < 2 ^ (prefixWord ++ tailWord_6016722).sum := by decide
  have hdescent : baseEnd_6016722 < baseStart_6016722 := by decide
  rcases family_descends (prefixWord ++ tailWord_6016722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6016749 : List Nat := [1, 5, 1, 2, 1, 2, 1, 2, 2, 3, 3]
def baseStart_6016749 : Nat := 118140960795 + 6016749 * 2 ^ 59
def prefixEnd_6016749 : Nat := 4983230072969 + 3 ^ 40 * 6016749 * 2
def baseEnd_6016749 : Nat := 3089484214458785175566981

theorem tailTrace_6016749 : CollatzResearch.WordTrace tailWord_6016749 prefixEnd_6016749 3089484214458785175566981 := by
  unfold tailWord_6016749
  simp only [CollatzResearch.WordTrace]
  refine ⟨219448864479353426764573301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146299242986235617843048867 219448864479353426764573301)
  ·
    refine ⟨20573331044939383759178747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 219448864479353426764573301 20573331044939383759178747)
    ·
      refine ⟨30859996567409075638768121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20573331044939383759178747 30859996567409075638768121)
      ·
        refine ⟨23144997425556806729076091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30859996567409075638768121 23144997425556806729076091)
        ·
          refine ⟨34717496138335210093614137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23144997425556806729076091 34717496138335210093614137)
          ·
            refine ⟨26038122103751407570210603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34717496138335210093614137 26038122103751407570210603)
            ·
              refine ⟨39057183155627111355315905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26038122103751407570210603 39057183155627111355315905)
              ·
                refine ⟨29292887366720333516486929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39057183155627111355315905 29292887366720333516486929)
                ·
                  refine ⟨21969665525040250137365197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29292887366720333516486929 21969665525040250137365197)
                  ·
                    refine ⟨8238624571890093801511949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21969665525040250137365197 8238624571890093801511949)
                    ·
                      refine ⟨3089484214458785175566981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8238624571890093801511949 3089484214458785175566981)
                      ·
                        rfl

theorem cell23_6016749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_6016749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6016749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6016749 prefixEnd_6016749 := by exact prefixLift 6016749
  have htrace : WordTrace (prefixWord ++ tailWord_6016749) baseStart_6016749 baseEnd_6016749 := by
    simpa [prefixWord, tailWord_6016749, baseEnd_6016749] using wordTrace_append hprefix tailTrace_6016749
  have hstable : (prefixWord ++ tailWord_6016749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6016749).length < 2 ^ (prefixWord ++ tailWord_6016749).sum := by decide
  have hdescent : baseEnd_6016749 < baseStart_6016749 := by decide
  rcases family_descends (prefixWord ++ tailWord_6016749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6016756 : List Nat := [2, 6, 1, 1, 1, 1, 1, 3, 7]
def baseStart_6016756 : Nat := 118140960795 + 6016756 * 2 ^ 59
def prefixEnd_6016756 : Nat := 4983230072969 + 3 ^ 40 * 6016756 * 2
def baseEnd_6016756 : Nat := 343276423202596294242161

theorem tailTrace_6016756 : CollatzResearch.WordTrace tailWord_6016756 prefixEnd_6016756 343276423202596294242161 := by
  unfold tailWord_6016756
  simp only [CollatzResearch.WordTrace]
  refine ⟨109724559895164033480039061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146299413193552044640052081 109724559895164033480039061)
  ·
    refine ⟨5143338745085814069376831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 109724559895164033480039061 5143338745085814069376831)
    ·
      refine ⟨7715008117628721104065247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5143338745085814069376831 7715008117628721104065247)
      ·
        refine ⟨11572512176443081656097871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7715008117628721104065247 11572512176443081656097871)
        ·
          refine ⟨17358768264664622484146807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11572512176443081656097871 17358768264664622484146807)
          ·
            refine ⟨26038152396996933726220211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17358768264664622484146807 26038152396996933726220211)
            ·
              refine ⟨39057228595495400589330317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26038152396996933726220211 39057228595495400589330317)
              ·
                refine ⟨14646460723310775220998869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39057228595495400589330317 14646460723310775220998869)
                ·
                  refine ⟨343276423202596294242161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14646460723310775220998869 343276423202596294242161)
                  ·
                    rfl

theorem cell23_6016756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_6016756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6016756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6016756 prefixEnd_6016756 := by exact prefixLift 6016756
  have htrace : WordTrace (prefixWord ++ tailWord_6016756) baseStart_6016756 baseEnd_6016756 := by
    simpa [prefixWord, tailWord_6016756, baseEnd_6016756] using wordTrace_append hprefix tailTrace_6016756
  have hstable : (prefixWord ++ tailWord_6016756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6016756).length < 2 ^ (prefixWord ++ tailWord_6016756).sum := by decide
  have hdescent : baseEnd_6016756 < baseStart_6016756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6016756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6016812 : List Nat := [2, 2, 1, 1, 1, 5, 2, 1, 8]
def baseStart_6016812 : Nat := 118140960795 + 6016812 * 2 ^ 59
def prefixEnd_6016812 : Nat := 4983230072969 + 3 ^ 40 * 6016812 * 2
def baseEnd_6016812 : Nat := 343279618193335381008799

theorem tailTrace_6016812 : CollatzResearch.WordTrace tailWord_6016812 prefixEnd_6016812 343279618193335381008799 := by
  unfold tailWord_6016812
  simp only [CollatzResearch.WordTrace]
  refine ⟨109725581139062594262058345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146300774852083459016077793 109725581139062594262058345)
  ·
    refine ⟨82294185854296945696543759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109725581139062594262058345 82294185854296945696543759)
    ·
      refine ⟨123441278781445418544815639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82294185854296945696543759 123441278781445418544815639)
      ·
        refine ⟨185161918172168127817223459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123441278781445418544815639 185161918172168127817223459)
        ·
          refine ⟨277742877258252191725835189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185161918172168127817223459 277742877258252191725835189)
          ·
            refine ⟨26038394742961142974297049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 277742877258252191725835189 26038394742961142974297049)
            ·
              refine ⟨19528796057220857230722787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26038394742961142974297049 19528796057220857230722787)
              ·
                refine ⟨29293194085831285846084181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19528796057220857230722787 29293194085831285846084181)
                ·
                  refine ⟨343279618193335381008799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29293194085831285846084181 343279618193335381008799)
                  ·
                    rfl

theorem cell23_6016812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 8].length) (baseStart_6016812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6016812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6016812 prefixEnd_6016812 := by exact prefixLift 6016812
  have htrace : WordTrace (prefixWord ++ tailWord_6016812) baseStart_6016812 baseEnd_6016812 := by
    simpa [prefixWord, tailWord_6016812, baseEnd_6016812] using wordTrace_append hprefix tailTrace_6016812
  have hstable : (prefixWord ++ tailWord_6016812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6016812).length < 2 ^ (prefixWord ++ tailWord_6016812).sum := by decide
  have hdescent : baseEnd_6016812 < baseStart_6016812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6016812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6016867 : List Nat := [1, 1, 1, 5, 5, 1, 2, 2, 1, 4]
def baseStart_6016867 : Nat := 118140960795 + 6016867 * 2 ^ 59
def prefixEnd_6016867 : Nat := 4983230072969 + 3 ^ 40 * 6016867 * 2
def baseEnd_6016867 : Nat := 1029848268392005237963813

theorem tailTrace_6016867 : CollatzResearch.WordTrace tailWord_6016867 prefixEnd_6016867 1029848268392005237963813 := by
  unfold tailWord_6016867
  simp only [CollatzResearch.WordTrace]
  refine ⟨219453168292925932917368855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146302112195283955278245903 219453168292925932917368855)
  ·
    refine ⟨329179752439388899376053283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219453168292925932917368855 329179752439388899376053283)
    ·
      refine ⟨493769628659083349064079925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329179752439388899376053283 493769628659083349064079925)
      ·
        refine ⟨46290902686789063974757493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 493769628659083349064079925 46290902686789063974757493)
        ·
          refine ⟨4339772126886474747633515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46290902686789063974757493 4339772126886474747633515)
          ·
            refine ⟨6509658190329712121450273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4339772126886474747633515 6509658190329712121450273)
            ·
              refine ⟨4882243642747284091087705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6509658190329712121450273 4882243642747284091087705)
              ·
                refine ⟨3661682732060463068315779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4882243642747284091087705 3661682732060463068315779)
                ·
                  refine ⟨5492524098090694602473669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3661682732060463068315779 5492524098090694602473669)
                  ·
                    refine ⟨1029848268392005237963813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5492524098090694602473669 1029848268392005237963813)
                    ·
                      rfl

theorem cell23_6016867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 2, 1, 4].length) (baseStart_6016867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6016867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6016867 prefixEnd_6016867 := by exact prefixLift 6016867
  have htrace : WordTrace (prefixWord ++ tailWord_6016867) baseStart_6016867 baseEnd_6016867 := by
    simpa [prefixWord, tailWord_6016867, baseEnd_6016867] using wordTrace_append hprefix tailTrace_6016867
  have hstable : (prefixWord ++ tailWord_6016867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6016867).length < 2 ^ (prefixWord ++ tailWord_6016867).sum := by decide
  have hdescent : baseEnd_6016867 < baseStart_6016867 := by decide
  rcases family_descends (prefixWord ++ tailWord_6016867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6016879 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 4, 6, 2]
def baseStart_6016879 : Nat := 118140960795 + 6016879 * 2 ^ 59
def prefixEnd_6016879 : Nat := 4983230072969 + 3 ^ 40 * 6016879 * 2
def baseEnd_6016879 : Nat := 3089550966943869666941383

theorem tailTrace_6016879 : CollatzResearch.WordTrace tailWord_6016879 prefixEnd_6016879 3089550966943869666941383 := by
  unfold tailWord_6016879
  simp only [CollatzResearch.WordTrace]
  refine ⟨219453605968882458966805691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146302403979254972644537127 219453605968882458966805691)
  ·
    refine ⟨329180408953323688450208537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219453605968882458966805691 329180408953323688450208537)
    ·
      refine ⟨246885306714992766337656403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329180408953323688450208537 246885306714992766337656403)
      ·
        refine ⟨370327960072489149506484605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246885306714992766337656403 370327960072489149506484605)
        ·
          refine ⟨138872985027183431064931727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 370327960072489149506484605 138872985027183431064931727)
          ·
            refine ⟨208309477540775146597397591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138872985027183431064931727 208309477540775146597397591)
            ·
              refine ⟨312464216311162719896096387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208309477540775146597397591 312464216311162719896096387)
              ·
                refine ⟨468696324466744079844144581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 312464216311162719896096387 468696324466744079844144581)
                ·
                  refine ⟨87880560837514514970777109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 468696324466744079844144581 87880560837514514970777109)
                  ·
                    refine ⟨4119401289258492889255177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 87880560837514514970777109 4119401289258492889255177)
                    ·
                      refine ⟨3089550966943869666941383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4119401289258492889255177 3089550966943869666941383)
                      ·
                        rfl

theorem cell23_6016879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 6, 2].length) (baseStart_6016879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6016879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6016879 prefixEnd_6016879 := by exact prefixLift 6016879
  have htrace : WordTrace (prefixWord ++ tailWord_6016879) baseStart_6016879 baseEnd_6016879 := by
    simpa [prefixWord, tailWord_6016879, baseEnd_6016879] using wordTrace_append hprefix tailTrace_6016879
  have hstable : (prefixWord ++ tailWord_6016879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6016879).length < 2 ^ (prefixWord ++ tailWord_6016879).sum := by decide
  have hdescent : baseEnd_6016879 < baseStart_6016879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6016879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6016889 : List Nat := [1, 2, 1, 3, 2, 2, 4, 1, 1, 6]
def baseStart_6016889 : Nat := 118140960795 + 6016889 * 2 ^ 59
def prefixEnd_6016889 : Nat := 4983230072969 + 3 ^ 40 * 6016889 * 2
def baseEnd_6016889 : Nat := 1029852033916804875938779

theorem tailTrace_6016889 : CollatzResearch.WordTrace tailWord_6016889 prefixEnd_6016889 1029852033916804875938779 := by
  unfold tailWord_6016889
  simp only [CollatzResearch.WordTrace]
  refine ⟨219453970698846230674669721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146302647132564153783113147 219453970698846230674669721)
  ·
    refine ⟨164590478024134673006002291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219453970698846230674669721 164590478024134673006002291)
    ·
      refine ⟨246885717036202009509003437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164590478024134673006002291 246885717036202009509003437)
      ·
        refine ⟨92582143888575753565876289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246885717036202009509003437 92582143888575753565876289)
        ·
          refine ⟨69436607916431815174407217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92582143888575753565876289 69436607916431815174407217)
          ·
            refine ⟨52077455937323861380805413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69436607916431815174407217 52077455937323861380805413)
            ·
              refine ⟨9764522988248224008901015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52077455937323861380805413 9764522988248224008901015)
              ·
                refine ⟨14646784482372336013351523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9764522988248224008901015 14646784482372336013351523)
                ·
                  refine ⟨21970176723558504020027285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14646784482372336013351523 21970176723558504020027285)
                  ·
                    refine ⟨1029852033916804875938779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21970176723558504020027285 1029852033916804875938779)
                    ·
                      rfl

theorem cell23_6016889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 6].length) (baseStart_6016889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6016889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6016889 prefixEnd_6016889 := by exact prefixLift 6016889
  have htrace : WordTrace (prefixWord ++ tailWord_6016889) baseStart_6016889 baseEnd_6016889 := by
    simpa [prefixWord, tailWord_6016889, baseEnd_6016889] using wordTrace_append hprefix tailTrace_6016889
  have hstable : (prefixWord ++ tailWord_6016889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6016889).length < 2 ^ (prefixWord ++ tailWord_6016889).sum := by decide
  have hdescent : baseEnd_6016889 < baseStart_6016889 := by decide
  rcases family_descends (prefixWord ++ tailWord_6016889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017006 : List Nat := [4, 1, 2, 1, 3, 1, 1, 2, 2, 1, 5]
def baseStart_6017006 : Nat := 118140960795 + 6017006 * 2 ^ 59
def prefixEnd_6017006 : Nat := 4983230072969 + 3 ^ 40 * 6017006 * 2
def baseEnd_6017006 : Nat := 3089616178986990670053299

theorem tailTrace_6017006 : CollatzResearch.WordTrace tailWord_6017006 prefixEnd_6017006 3089616178986990670053299 := by
  unfold tailWord_6017006
  simp only [CollatzResearch.WordTrace]
  refine ⟨27432279754927794957084859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146305492026281573104452581 27432279754927794957084859)
  ·
    refine ⟨41148419632391692435627289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27432279754927794957084859 41148419632391692435627289)
    ·
      refine ⟨30861314724293769326720467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41148419632391692435627289 30861314724293769326720467)
      ·
        refine ⟨46291972086440653990080701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30861314724293769326720467 46291972086440653990080701)
        ·
          refine ⟨17359489532415245246280263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46291972086440653990080701 17359489532415245246280263)
          ·
            refine ⟨26039234298622867869420395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17359489532415245246280263 26039234298622867869420395)
            ·
              refine ⟨39058851447934301804130593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26039234298622867869420395 39058851447934301804130593)
              ·
                refine ⟨29294138585950726353097945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39058851447934301804130593 29294138585950726353097945)
                ·
                  refine ⟨21970603939463044764823459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29294138585950726353097945 21970603939463044764823459)
                  ·
                    refine ⟨32955905909194567147235189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21970603939463044764823459 32955905909194567147235189)
                    ·
                      refine ⟨3089616178986990670053299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32955905909194567147235189 3089616178986990670053299)
                      ·
                        rfl

theorem cell23_6017006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_6017006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017006 prefixEnd_6017006 := by exact prefixLift 6017006
  have htrace : WordTrace (prefixWord ++ tailWord_6017006) baseStart_6017006 baseEnd_6017006 := by
    simpa [prefixWord, tailWord_6017006, baseEnd_6017006] using wordTrace_append hprefix tailTrace_6017006
  have hstable : (prefixWord ++ tailWord_6017006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017006).length < 2 ^ (prefixWord ++ tailWord_6017006).sum := by decide
  have hdescent : baseEnd_6017006 < baseStart_6017006 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017036 : List Nat := [2, 2, 1, 2, 3, 1, 2, 2, 2, 3, 3]
def baseStart_6017036 : Nat := 118140960795 + 6017036 * 2 ^ 59
def prefixEnd_6017036 : Nat := 4983230072969 + 3 ^ 40 * 6017036 * 2
def baseEnd_6017036 : Nat := 3089631583406625552678161

theorem tailTrace_6017036 : CollatzResearch.WordTrace tailWord_6017036 prefixEnd_6017036 3089631583406625552678161 := by
  unfold tailWord_6017036
  simp only [CollatzResearch.WordTrace]
  refine ⟨109729666114656837390135481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146306221486209116520180641 109729666114656837390135481)
  ·
    refine ⟨82297249585992628042601611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109729666114656837390135481 82297249585992628042601611)
    ·
      refine ⟨123445874378988942063902417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82297249585992628042601611 123445874378988942063902417)
      ·
        refine ⟨92584405784241706547926813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123445874378988942063902417 92584405784241706547926813)
        ·
          refine ⟨34719152169090639955472555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92584405784241706547926813 34719152169090639955472555)
          ·
            refine ⟨52078728253635959933208833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34719152169090639955472555 52078728253635959933208833)
            ·
              refine ⟨39059046190226969949906625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52078728253635959933208833 39059046190226969949906625)
              ·
                refine ⟨29294284642670227462429969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39059046190226969949906625 29294284642670227462429969)
                ·
                  refine ⟨21970713482002670596822477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29294284642670227462429969 21970713482002670596822477)
                  ·
                    refine ⟨8239017555751001473808429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21970713482002670596822477 8239017555751001473808429)
                    ·
                      refine ⟨3089631583406625552678161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8239017555751001473808429 3089631583406625552678161)
                      ·
                        rfl

theorem cell23_6017036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 2, 3, 3].length) (baseStart_6017036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017036 prefixEnd_6017036 := by exact prefixLift 6017036
  have htrace : WordTrace (prefixWord ++ tailWord_6017036) baseStart_6017036 baseEnd_6017036 := by
    simpa [prefixWord, tailWord_6017036, baseEnd_6017036] using wordTrace_append hprefix tailTrace_6017036
  have hstable : (prefixWord ++ tailWord_6017036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017036).length < 2 ^ (prefixWord ++ tailWord_6017036).sum := by decide
  have hdescent : baseEnd_6017036 < baseStart_6017036 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017043 : List Nat := [1, 1, 1, 2, 1, 4, 6, 2, 5]
def baseStart_6017043 : Nat := 118140960795 + 6017043 * 2 ^ 59
def prefixEnd_6017043 : Nat := 4983230072969 + 3 ^ 40 * 6017043 * 2
def baseEnd_6017043 : Nat := 343292797530134113921181

theorem tailTrace_6017043 : CollatzResearch.WordTrace tailWord_6017043 prefixEnd_6017043 343292797530134113921181 := by
  unfold tailWord_6017043
  simp only [CollatzResearch.WordTrace]
  refine ⟨219459587540288314975775783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146306391693525543317183855 219459587540288314975775783)
  ·
    refine ⟨329189381310432472463663675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219459587540288314975775783 329189381310432472463663675)
    ·
      refine ⟨493784071965648708695495513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329189381310432472463663675 493784071965648708695495513)
      ·
        refine ⟨370338053974236531521621635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 493784071965648708695495513 370338053974236531521621635)
        ·
          refine ⟨555507080961354797282432453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 370338053974236531521621635 555507080961354797282432453)
          ·
            refine ⟨104157577680254024490456085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 555507080961354797282432453 104157577680254024490456085)
            ·
              refine ⟨4882386453761907397990129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 104157577680254024490456085 4882386453761907397990129)
              ·
                refine ⟨3661789840321430548492597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4882386453761907397990129 3661789840321430548492597)
                ·
                  refine ⟨343292797530134113921181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3661789840321430548492597 343292797530134113921181)
                  ·
                    rfl

theorem cell23_6017043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 2, 5].length) (baseStart_6017043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017043 prefixEnd_6017043 := by exact prefixLift 6017043
  have htrace : WordTrace (prefixWord ++ tailWord_6017043) baseStart_6017043 baseEnd_6017043 := by
    simpa [prefixWord, tailWord_6017043, baseEnd_6017043] using wordTrace_append hprefix tailTrace_6017043
  have hstable : (prefixWord ++ tailWord_6017043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017043).length < 2 ^ (prefixWord ++ tailWord_6017043).sum := by decide
  have hdescent : baseEnd_6017043 < baseStart_6017043 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017053 : List Nat := [1, 4, 2, 2, 2, 2, 1, 1, 2, 3, 3]
def baseStart_6017053 : Nat := 118140960795 + 6017053 * 2 ^ 59
def prefixEnd_6017053 : Nat := 4983230072969 + 3 ^ 40 * 6017053 * 2
def baseEnd_6017053 : Nat := 3089640312577751986165583

theorem tailTrace_6017053 : CollatzResearch.WordTrace tailWord_6017053 prefixEnd_6017053 3089640312577751986165583 := by
  unfold tailWord_6017053
  simp only [CollatzResearch.WordTrace]
  refine ⟨219459952270252086683639813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146306634846834724455759875 219459952270252086683639813)
  ·
    refine ⟨41148741050672266253182465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 219459952270252086683639813 41148741050672266253182465)
    ·
      refine ⟨30861555788004199689886849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41148741050672266253182465 30861555788004199689886849)
      ·
        refine ⟨23146166841003149767415137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30861555788004199689886849 23146166841003149767415137)
        ·
          refine ⟨17359625130752362325561353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23146166841003149767415137 17359625130752362325561353)
          ·
            refine ⟨13019718848064271744171015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17359625130752362325561353 13019718848064271744171015)
            ·
              refine ⟨19529578272096407616256523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13019718848064271744171015 19529578272096407616256523)
              ·
                refine ⟨29294367408144611424384785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19529578272096407616256523 29294367408144611424384785)
                ·
                  refine ⟨21970775556108458568288589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29294367408144611424384785 21970775556108458568288589)
                  ·
                    refine ⟨8239040833540671963108221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21970775556108458568288589 8239040833540671963108221)
                    ·
                      refine ⟨3089640312577751986165583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8239040833540671963108221 3089640312577751986165583)
                      ·
                        rfl

theorem cell23_6017053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_6017053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017053 prefixEnd_6017053 := by exact prefixLift 6017053
  have htrace : WordTrace (prefixWord ++ tailWord_6017053) baseStart_6017053 baseEnd_6017053 := by
    simpa [prefixWord, tailWord_6017053, baseEnd_6017053] using wordTrace_append hprefix tailTrace_6017053
  have hstable : (prefixWord ++ tailWord_6017053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017053).length < 2 ^ (prefixWord ++ tailWord_6017053).sum := by decide
  have hdescent : baseEnd_6017053 < baseStart_6017053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017073 : List Nat := [1, 2, 2, 3, 1, 5, 1, 1, 2, 5]
def baseStart_6017073 : Nat := 118140960795 + 6017073 * 2 ^ 59
def prefixEnd_6017073 : Nat := 4983230072969 + 3 ^ 40 * 6017073 * 2
def baseEnd_6017073 : Nat := 1029883527396947302638497

theorem tailTrace_6017073 : CollatzResearch.WordTrace tailWord_6017073 prefixEnd_6017073 1029883527396947302638497 := by
  unfold tailWord_6017073
  simp only [CollatzResearch.WordTrace]
  refine ⟨219460681730179630099367873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146307121153453086732911915 219460681730179630099367873)
  ·
    refine ⟨164595511297634722574525905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219460681730179630099367873 164595511297634722574525905)
    ·
      refine ⟨123446633473226041930894429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164595511297634722574525905 123446633473226041930894429)
      ·
        refine ⟨46292487552459765724085411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123446633473226041930894429 46292487552459765724085411)
        ·
          refine ⟨69438731328689648586128117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46292487552459765724085411 69438731328689648586128117)
          ·
            refine ⟨6509881062064654554949511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69438731328689648586128117 6509881062064654554949511)
            ·
              refine ⟨9764821593096981832424267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6509881062064654554949511 9764821593096981832424267)
              ·
                refine ⟨14647232389645472748636401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9764821593096981832424267 14647232389645472748636401)
                ·
                  refine ⟨10985424292234104561477301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14647232389645472748636401 10985424292234104561477301)
                  ·
                    refine ⟨1029883527396947302638497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10985424292234104561477301 1029883527396947302638497)
                    ·
                      rfl

theorem cell23_6017073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 2, 5].length) (baseStart_6017073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017073 prefixEnd_6017073 := by exact prefixLift 6017073
  have htrace : WordTrace (prefixWord ++ tailWord_6017073) baseStart_6017073 baseEnd_6017073 := by
    simpa [prefixWord, tailWord_6017073, baseEnd_6017073] using wordTrace_append hprefix tailTrace_6017073
  have hstable : (prefixWord ++ tailWord_6017073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017073).length < 2 ^ (prefixWord ++ tailWord_6017073).sum := by decide
  have hdescent : baseEnd_6017073 < baseStart_6017073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017099 : List Nat := [1, 1, 1, 1, 3, 1, 2, 5, 8]
def baseStart_6017099 : Nat := 118140960795 + 6017099 * 2 ^ 59
def prefixEnd_6017099 : Nat := 4983230072969 + 3 ^ 40 * 6017099 * 2
def baseEnd_6017099 : Nat := 343295992520873200687819

theorem tailTrace_6017099 : CollatzResearch.WordTrace tailWord_6017099 prefixEnd_6017099 343295992520873200687819 := by
  unfold tailWord_6017099
  simp only [CollatzResearch.WordTrace]
  refine ⟨219461630028085436539814351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146307753352056957693209567 219461630028085436539814351)
  ·
    refine ⟨329192445042128154809721527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219461630028085436539814351 329192445042128154809721527)
    ·
      refine ⟨493788667563192232214582291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329192445042128154809721527 493788667563192232214582291)
      ·
        refine ⟨740683001344788348321873437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 493788667563192232214582291 740683001344788348321873437)
        ·
          refine ⟨277756125504295630620702539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 740683001344788348321873437 277756125504295630620702539)
          ·
            refine ⟨416634188256443445931053809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277756125504295630620702539 416634188256443445931053809)
            ·
              refine ⟨312475641192332584448290357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 416634188256443445931053809 312475641192332584448290357)
              ·
                refine ⟨29294591361781179792027221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 312475641192332584448290357 29294591361781179792027221)
                ·
                  refine ⟨343295992520873200687819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29294591361781179792027221 343295992520873200687819)
                  ·
                    rfl

theorem cell23_6017099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 8].length) (baseStart_6017099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017099 prefixEnd_6017099 := by exact prefixLift 6017099
  have htrace : WordTrace (prefixWord ++ tailWord_6017099) baseStart_6017099 baseEnd_6017099 := by
    simpa [prefixWord, tailWord_6017099, baseEnd_6017099] using wordTrace_append hprefix tailTrace_6017099
  have hstable : (prefixWord ++ tailWord_6017099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017099).length < 2 ^ (prefixWord ++ tailWord_6017099).sum := by decide
  have hdescent : baseEnd_6017099 < baseStart_6017099 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017110 : List Nat := [5, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4]
def baseStart_6017110 : Nat := 118140960795 + 6017110 * 2 ^ 59
def prefixEnd_6017110 : Nat := 4983230072969 + 3 ^ 40 * 6017110 * 2
def baseEnd_6017110 : Nat := 3089669580975058263152821

theorem tailTrace_6017110 : CollatzResearch.WordTrace tailWord_6017110 prefixEnd_6017110 3089669580975058263152821 := by
  unfold tailWord_6017110
  simp only [CollatzResearch.WordTrace]
  refine ⟨13716376951940349088654049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 146308020820697056945643189 13716376951940349088654049)
  ·
    refine ⟨10287282713955261816490537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13716376951940349088654049 10287282713955261816490537)
    ·
      refine ⟨7715462035466446362367903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10287282713955261816490537 7715462035466446362367903)
      ·
        refine ⟨11573193053199669543551855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7715462035466446362367903 11573193053199669543551855)
        ·
          refine ⟨17359789579799504315327783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11573193053199669543551855 17359789579799504315327783)
          ·
            refine ⟨26039684369699256472991675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17359789579799504315327783 26039684369699256472991675)
            ·
              refine ⟨39059526554548884709487513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26039684369699256472991675 39059526554548884709487513)
              ·
                refine ⟨29294644915911663532115635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39059526554548884709487513 29294644915911663532115635)
                ·
                  refine ⟨43941967373867495298173453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29294644915911663532115635 43941967373867495298173453)
                  ·
                    refine ⟨16478237765200310736815045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43941967373867495298173453 16478237765200310736815045)
                    ·
                      refine ⟨3089669580975058263152821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16478237765200310736815045 3089669580975058263152821)
                      ·
                        rfl

theorem cell23_6017110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_6017110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017110 prefixEnd_6017110 := by exact prefixLift 6017110
  have htrace : WordTrace (prefixWord ++ tailWord_6017110) baseStart_6017110 baseEnd_6017110 := by
    simpa [prefixWord, tailWord_6017110, baseEnd_6017110] using wordTrace_append hprefix tailTrace_6017110
  have hstable : (prefixWord ++ tailWord_6017110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017110).length < 2 ^ (prefixWord ++ tailWord_6017110).sum := by decide
  have hdescent : baseEnd_6017110 < baseStart_6017110 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017170 : List Nat := [3, 2, 3, 1, 1, 1, 1, 2, 4, 3, 2]
def baseStart_6017170 : Nat := 118140960795 + 6017170 * 2 ^ 59
def prefixEnd_6017170 : Nat := 4983230072969 + 3 ^ 40 * 6017170 * 2
def baseEnd_6017170 : Nat := 3089700389814328028402545

theorem tailTrace_6017170 : CollatzResearch.WordTrace tailWord_6017170 prefixEnd_6017170 3089700389814328028402545 := by
  unfold tailWord_6017170
  simp only [CollatzResearch.WordTrace]
  refine ⟨54866054902707053916412241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146309479740552143777099309 54866054902707053916412241)
  ·
    refine ⟨41149541177030290437309181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54866054902707053916412241 41149541177030290437309181)
    ·
      refine ⟨15431077941386358913990943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41149541177030290437309181 15431077941386358913990943)
      ·
        refine ⟨23146616912079538370986415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15431077941386358913990943 23146616912079538370986415)
        ·
          refine ⟨34719925368119307556479623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23146616912079538370986415 34719925368119307556479623)
          ·
            refine ⟨52079888052178961334719435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34719925368119307556479623 52079888052178961334719435)
            ·
              refine ⟨78119832078268442002079153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52079888052178961334719435 78119832078268442002079153)
              ·
                refine ⟨58589874058701331501559365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78119832078268442002079153 58589874058701331501559365)
                ·
                  refine ⟨10985601386006499656542381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58589874058701331501559365 10985601386006499656542381)
                  ·
                    refine ⟨4119600519752437371203393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10985601386006499656542381 4119600519752437371203393)
                    ·
                      refine ⟨3089700389814328028402545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4119600519752437371203393 3089700389814328028402545)
                      ·
                        rfl

theorem cell23_6017170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_6017170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017170 prefixEnd_6017170 := by exact prefixLift 6017170
  have htrace : WordTrace (prefixWord ++ tailWord_6017170) baseStart_6017170 baseEnd_6017170 := by
    simpa [prefixWord, tailWord_6017170, baseEnd_6017170] using wordTrace_append hprefix tailTrace_6017170
  have hstable : (prefixWord ++ tailWord_6017170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017170).length < 2 ^ (prefixWord ++ tailWord_6017170).sum := by decide
  have hdescent : baseEnd_6017170 < baseStart_6017170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017197 : List Nat := [1, 5, 2, 1, 2, 2, 3, 1, 1, 5]
def baseStart_6017197 : Nat := 118140960795 + 6017197 * 2 ^ 59
def prefixEnd_6017197 : Nat := 4983230072969 + 3 ^ 40 * 6017197 * 2
def baseEnd_6017197 : Nat := 1029904751263999807588307

theorem tailTrace_6017197 : CollatzResearch.WordTrace tailWord_6017197 prefixEnd_6017197 1029904751263999807588307 := by
  unfold tailWord_6017197
  simp only [CollatzResearch.WordTrace]
  refine ⟨219465204381730399276881845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146310136254486932851254563 219465204381730399276881845)
  ·
    refine ⟨20574862910787224932207673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 219465204381730399276881845 20574862910787224932207673)
    ·
      refine ⟨15431147183090418699155755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20574862910787224932207673 15431147183090418699155755)
      ·
        refine ⟨23146720774635628048733633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15431147183090418699155755 23146720774635628048733633)
        ·
          refine ⟨17360040580976721036550225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23146720774635628048733633 17360040580976721036550225)
          ·
            refine ⟨13020030435732540777412669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17360040580976721036550225 13020030435732540777412669)
            ·
              refine ⟨4882511413399702791529751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13020030435732540777412669 4882511413399702791529751)
              ·
                refine ⟨7323767120099554187294627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4882511413399702791529751 7323767120099554187294627)
                ·
                  refine ⟨10985650680149331280941941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7323767120099554187294627 10985650680149331280941941)
                  ·
                    refine ⟨1029904751263999807588307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10985650680149331280941941 1029904751263999807588307)
                    ·
                      rfl

theorem cell23_6017197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_6017197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017197 prefixEnd_6017197 := by exact prefixLift 6017197
  have htrace : WordTrace (prefixWord ++ tailWord_6017197) baseStart_6017197 baseEnd_6017197 := by
    simpa [prefixWord, tailWord_6017197, baseEnd_6017197] using wordTrace_append hprefix tailTrace_6017197
  have hstable : (prefixWord ++ tailWord_6017197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017197).length < 2 ^ (prefixWord ++ tailWord_6017197).sum := by decide
  have hdescent : baseEnd_6017197 < baseStart_6017197 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017220 : List Nat := [2, 3, 3, 1, 2, 1, 1, 2, 3, 2, 3]
def baseStart_6017220 : Nat := 118140960795 + 6017220 * 2 ^ 59
def prefixEnd_6017220 : Nat := 4983230072969 + 3 ^ 40 * 6017220 * 2
def baseEnd_6017220 : Nat := 3089726063847052832777315

theorem tailTrace_6017220 : CollatzResearch.WordTrace tailWord_6017220 prefixEnd_6017220 3089726063847052832777315 := by
  unfold tailWord_6017220
  simp only [CollatzResearch.WordTrace]
  refine ⟨109733021630323537102484557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146310695507098049469979409 109733021630323537102484557)
  ·
    refine ⟨41149883111371326413431709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109733021630323537102484557 41149883111371326413431709)
    ·
      refine ⟨15431206166764247405036891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41149883111371326413431709 15431206166764247405036891)
      ·
        refine ⟨23146809250146371107555337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15431206166764247405036891 23146809250146371107555337)
        ·
          refine ⟨17360106937609778330666503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23146809250146371107555337 17360106937609778330666503)
          ·
            refine ⟨26040160406414667495999755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17360106937609778330666503 26040160406414667495999755)
            ·
              refine ⟨39060240609622001243999633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26040160406414667495999755 39060240609622001243999633)
              ·
                refine ⟨29295180457216500932999725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39060240609622001243999633 29295180457216500932999725)
                ·
                  refine ⟨10985692671456187849874897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29295180457216500932999725 10985692671456187849874897)
                  ·
                    refine ⟨8239269503592140887406173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10985692671456187849874897 8239269503592140887406173)
                    ·
                      refine ⟨3089726063847052832777315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8239269503592140887406173 3089726063847052832777315)
                      ·
                        rfl

theorem cell23_6017220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_6017220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017220 prefixEnd_6017220 := by exact prefixLift 6017220
  have htrace : WordTrace (prefixWord ++ tailWord_6017220) baseStart_6017220 baseEnd_6017220 := by
    simpa [prefixWord, tailWord_6017220, baseEnd_6017220] using wordTrace_append hprefix tailTrace_6017220
  have hstable : (prefixWord ++ tailWord_6017220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017220).length < 2 ^ (prefixWord ++ tailWord_6017220).sum := by decide
  have hdescent : baseEnd_6017220 < baseStart_6017220 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017230 : List Nat := [4, 1, 1, 1, 4, 2, 2, 1, 1, 2, 4]
def baseStart_6017230 : Nat := 118140960795 + 6017230 * 2 ^ 59
def prefixEnd_6017230 : Nat := 4983230072969 + 3 ^ 40 * 6017230 * 2
def baseEnd_6017230 : Nat := 3089731198653597793652269

theorem tailTrace_6017230 : CollatzResearch.WordTrace tailWord_6017230 prefixEnd_6017230 3089731198653597793652269 := by
  unfold tailWord_6017230
  simp only [CollatzResearch.WordTrace]
  refine ⟨27433300998826355739104143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146310938660407230608555429 27433300998826355739104143)
  ·
    refine ⟨41149951498239533608656215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27433300998826355739104143 41149951498239533608656215)
    ·
      refine ⟨61724927247359300412984323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41149951498239533608656215 61724927247359300412984323)
      ·
        refine ⟨92587390871038950619476485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61724927247359300412984323 92587390871038950619476485)
        ·
          refine ⟨17360135788319803241151841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92587390871038950619476485 17360135788319803241151841)
          ·
            refine ⟨13020101841239852430863881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17360135788319803241151841 13020101841239852430863881)
            ·
              refine ⟨9765076380929889323147911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13020101841239852430863881 9765076380929889323147911)
              ·
                refine ⟨14647614571394833984721867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9765076380929889323147911 14647614571394833984721867)
                ·
                  refine ⟨21971421857092250977082801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14647614571394833984721867 21971421857092250977082801)
                  ·
                    refine ⟨16478566392819188232812101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21971421857092250977082801 16478566392819188232812101)
                    ·
                      refine ⟨3089731198653597793652269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16478566392819188232812101 3089731198653597793652269)
                      ·
                        rfl

theorem cell23_6017230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 1, 2, 4].length) (baseStart_6017230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017230 prefixEnd_6017230 := by exact prefixLift 6017230
  have htrace : WordTrace (prefixWord ++ tailWord_6017230) baseStart_6017230 baseEnd_6017230 := by
    simpa [prefixWord, tailWord_6017230, baseEnd_6017230] using wordTrace_append hprefix tailTrace_6017230
  have hstable : (prefixWord ++ tailWord_6017230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017230).length < 2 ^ (prefixWord ++ tailWord_6017230).sum := by decide
  have hdescent : baseEnd_6017230 < baseStart_6017230 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017233 : List Nat := [1, 2, 2, 1, 2, 2, 3, 3, 1, 3, 3]
def baseStart_6017233 : Nat := 118140960795 + 6017233 * 2 ^ 59
def prefixEnd_6017233 : Nat := 4983230072969 + 3 ^ 40 * 6017233 * 2
def baseEnd_6017233 : Nat := 3089732739095561281914755

theorem tailTrace_6017233 : CollatzResearch.WordTrace tailWord_6017233 prefixEnd_6017233 3089732739095561281914755 := by
  unfold tailWord_6017233
  simp only [CollatzResearch.WordTrace]
  refine ⟨219466517409599977425192353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146311011606399984950128235 219466517409599977425192353)
  ·
    refine ⟨164599888057199983068894265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219466517409599977425192353 164599888057199983068894265)
    ·
      refine ⟨123449916042899987301670699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164599888057199983068894265 123449916042899987301670699)
      ·
        refine ⟨185174874064349980952506049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123449916042899987301670699 185174874064349980952506049)
        ·
          refine ⟨138881155548262485714379537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185174874064349980952506049 138881155548262485714379537)
          ·
            refine ⟨104160866661196864285784653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138881155548262485714379537 104160866661196864285784653)
            ·
              refine ⟨39060324997948824107169245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104160866661196864285784653 39060324997948824107169245)
              ·
                refine ⟨14647621874230809040188467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39060324997948824107169245 14647621874230809040188467)
                ·
                  refine ⟨21971432811346213560282701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14647621874230809040188467 21971432811346213560282701)
                  ·
                    refine ⟨8239287304254830085106013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21971432811346213560282701 8239287304254830085106013)
                    ·
                      refine ⟨3089732739095561281914755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8239287304254830085106013 3089732739095561281914755)
                      ·
                        rfl

theorem cell23_6017233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 3, 3].length) (baseStart_6017233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017233 prefixEnd_6017233 := by exact prefixLift 6017233
  have htrace : WordTrace (prefixWord ++ tailWord_6017233) baseStart_6017233 baseEnd_6017233 := by
    simpa [prefixWord, tailWord_6017233, baseEnd_6017233] using wordTrace_append hprefix tailTrace_6017233
  have hstable : (prefixWord ++ tailWord_6017233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017233).length < 2 ^ (prefixWord ++ tailWord_6017233).sum := by decide
  have hdescent : baseEnd_6017233 < baseStart_6017233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017251 : List Nat := [1, 1, 1, 8, 2, 1, 2, 1, 1, 1, 4]
def baseStart_6017251 : Nat := 118140960795 + 6017251 * 2 ^ 59
def prefixEnd_6017251 : Nat := 4983230072969 + 3 ^ 40 * 6017251 * 2
def baseEnd_6017251 : Nat := 3089741981747342211489673

theorem tailTrace_6017251 : CollatzResearch.WordTrace tailWord_6017251 prefixEnd_6017251 3089741981747342211489673 := by
  unfold tailWord_6017251
  simp only [CollatzResearch.WordTrace]
  refine ⟨219467173923534766499347607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146311449282356510999565071 219467173923534766499347607)
  ·
    refine ⟨329200760885302149749021411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219467173923534766499347607 329200760885302149749021411)
    ·
      refine ⟨493801141327953224623532117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329200760885302149749021411 493801141327953224623532117)
      ·
        refine ⟨5786732124936951851057017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 493801141327953224623532117 5786732124936951851057017)
        ·
          refine ⟨4340049093702713888292763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5786732124936951851057017 4340049093702713888292763)
          ·
            refine ⟨6510073640554070832439145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4340049093702713888292763 6510073640554070832439145)
            ·
              refine ⟨4882555230415553124329359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6510073640554070832439145 4882555230415553124329359)
              ·
                refine ⟨7323832845623329686494039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4882555230415553124329359 7323832845623329686494039)
                ·
                  refine ⟨10985749268434994529741059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7323832845623329686494039 10985749268434994529741059)
                  ·
                    refine ⟨16478623902652491794611589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10985749268434994529741059 16478623902652491794611589)
                    ·
                      refine ⟨3089741981747342211489673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16478623902652491794611589 3089741981747342211489673)
                      ·
                        rfl

theorem cell23_6017251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_6017251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017251 prefixEnd_6017251 := by exact prefixLift 6017251
  have htrace : WordTrace (prefixWord ++ tailWord_6017251) baseStart_6017251 baseEnd_6017251 := by
    simpa [prefixWord, tailWord_6017251, baseEnd_6017251] using wordTrace_append hprefix tailTrace_6017251
  have hstable : (prefixWord ++ tailWord_6017251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017251).length < 2 ^ (prefixWord ++ tailWord_6017251).sum := by decide
  have hdescent : baseEnd_6017251 < baseStart_6017251 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017284 : List Nat := [2, 3, 2, 2, 4, 1, 1, 1, 1, 3, 3]
def baseStart_6017284 : Nat := 118140960795 + 6017284 * 2 ^ 59
def prefixEnd_6017284 : Nat := 4983230072969 + 3 ^ 40 * 6017284 * 2
def baseEnd_6017284 : Nat := 3089758926608940582377021

theorem tailTrace_6017284 : CollatzResearch.WordTrace tailWord_6017284 prefixEnd_6017284 3089758926608940582377021 := by
  unfold tailWord_6017284
  simp only [CollatzResearch.WordTrace]
  refine ⟨109734188766207606567649453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146312251688276808756865937 109734188766207606567649453)
  ·
    refine ⟨41150320787327852462868545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109734188766207606567649453 41150320787327852462868545)
    ·
      refine ⟨30862740590495889347151409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41150320787327852462868545 30862740590495889347151409)
      ·
        refine ⟨23147055442871917010363557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30862740590495889347151409 23147055442871917010363557)
        ·
          refine ⟨4340072895538484439443167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23147055442871917010363557 4340072895538484439443167)
          ·
            refine ⟨6510109343307726659164751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4340072895538484439443167 6510109343307726659164751)
            ·
              refine ⟨9765164014961589988747127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6510109343307726659164751 9765164014961589988747127)
              ·
                refine ⟨14647746022442384983120691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9765164014961589988747127 14647746022442384983120691)
                ·
                  refine ⟨21971619033663577474681037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14647746022442384983120691 21971619033663577474681037)
                  ·
                    refine ⟨8239357137623841553005389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21971619033663577474681037 8239357137623841553005389)
                    ·
                      refine ⟨3089758926608940582377021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8239357137623841553005389 3089758926608940582377021)
                      ·
                        rfl

theorem cell23_6017284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_6017284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017284 prefixEnd_6017284 := by exact prefixLift 6017284
  have htrace : WordTrace (prefixWord ++ tailWord_6017284) baseStart_6017284 baseEnd_6017284 := by
    simpa [prefixWord, tailWord_6017284, baseEnd_6017284] using wordTrace_append hprefix tailTrace_6017284
  have hstable : (prefixWord ++ tailWord_6017284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017284).length < 2 ^ (prefixWord ++ tailWord_6017284).sum := by decide
  have hdescent : baseEnd_6017284 < baseStart_6017284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017343 : List Nat := [1, 1, 2, 2, 4, 1, 1, 2, 4, 5]
def baseStart_6017343 : Nat := 118140960795 + 6017343 * 2 ^ 59
def prefixEnd_6017343 : Nat := 4983230072969 + 3 ^ 40 * 6017343 * 2
def baseEnd_6017343 : Nat := 1029929740655851950513083

theorem tailTrace_6017343 : CollatzResearch.WordTrace tailWord_6017343 prefixEnd_6017343 1029929740655851950513083 := by
  unfold tailWord_6017343
  simp only [CollatzResearch.WordTrace]
  refine ⟨219470529439201466211696683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146313686292800977474464455 219470529439201466211696683)
  ·
    refine ⟨329205794158802199317545025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219470529439201466211696683 329205794158802199317545025)
    ·
      refine ⟨246904345619101649488158769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329205794158802199317545025 246904345619101649488158769)
      ·
        refine ⟨185178259214326237116119077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246904345619101649488158769 185178259214326237116119077)
        ·
          refine ⟨34720923602686169459272327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 185178259214326237116119077 34720923602686169459272327)
          ·
            refine ⟨52081385404029254188908491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34720923602686169459272327 52081385404029254188908491)
            ·
              refine ⟨78122078106043881283362737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52081385404029254188908491 78122078106043881283362737)
              ·
                refine ⟨58591558579532910962522053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78122078106043881283362737 58591558579532910962522053)
                ·
                  refine ⟨10985917233662420805472885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58591558579532910962522053 10985917233662420805472885)
                  ·
                    refine ⟨1029929740655851950513083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10985917233662420805472885 1029929740655851950513083)
                    ·
                      rfl

theorem cell23_6017343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 4, 5].length) (baseStart_6017343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017343 prefixEnd_6017343 := by exact prefixLift 6017343
  have htrace : WordTrace (prefixWord ++ tailWord_6017343) baseStart_6017343 baseEnd_6017343 := by
    simpa [prefixWord, tailWord_6017343, baseEnd_6017343] using wordTrace_append hprefix tailTrace_6017343
  have hstable : (prefixWord ++ tailWord_6017343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017343).length < 2 ^ (prefixWord ++ tailWord_6017343).sum := by decide
  have hdescent : baseEnd_6017343 < baseStart_6017343 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017360 : List Nat := [2, 1, 1, 1, 1, 7, 2, 1, 2, 5]
def baseStart_6017360 : Nat := 118140960795 + 6017360 * 2 ^ 59
def prefixEnd_6017360 : Nat := 4983230072969 + 3 ^ 40 * 6017360 * 2
def baseEnd_6017360 : Nat := 1029932650379560761675557

theorem tailTrace_6017360 : CollatzResearch.WordTrace tailWord_6017360 prefixEnd_6017360 1029932650379560761675557 := by
  unfold tailWord_6017360
  simp only [CollatzResearch.WordTrace]
  refine ⟨109735574740069939057532767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146314099653426585410043689 109735574740069939057532767)
  ·
    refine ⟨164603362110104908586299151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109735574740069939057532767 164603362110104908586299151)
    ·
      refine ⟨246905043165157362879448727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164603362110104908586299151 246905043165157362879448727)
      ·
        refine ⟨370357564747736044319173091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246905043165157362879448727 370357564747736044319173091)
        ·
          refine ⟨555536347121604066478759637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 370357564747736044319173091 555536347121604066478759637)
          ·
            refine ⟨13020383135662595308095929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 555536347121604066478759637 13020383135662595308095929)
            ·
              refine ⟨9765287351746946481071947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13020383135662595308095929 9765287351746946481071947)
              ·
                refine ⟨14647931027620419721607921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9765287351746946481071947 14647931027620419721607921)
                ·
                  refine ⟨10985948270715314791205941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14647931027620419721607921 10985948270715314791205941)
                  ·
                    refine ⟨1029932650379560761675557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10985948270715314791205941 1029932650379560761675557)
                    ·
                      rfl

theorem cell23_6017360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 2, 5].length) (baseStart_6017360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017360 prefixEnd_6017360 := by exact prefixLift 6017360
  have htrace : WordTrace (prefixWord ++ tailWord_6017360) baseStart_6017360 baseEnd_6017360 := by
    simpa [prefixWord, tailWord_6017360, baseEnd_6017360] using wordTrace_append hprefix tailTrace_6017360
  have hstable : (prefixWord ++ tailWord_6017360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017360).length < 2 ^ (prefixWord ++ tailWord_6017360).sum := by decide
  have hdescent : baseEnd_6017360 < baseStart_6017360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017380 : List Nat := [2, 3, 1, 1, 3, 1, 1, 4, 2, 1, 4]
def baseStart_6017380 : Nat := 118140960795 + 6017380 * 2 ^ 59
def prefixEnd_6017380 : Nat := 4983230072969 + 3 ^ 40 * 6017380 * 2
def baseEnd_6017380 : Nat := 3089808220751772206776579

theorem tailTrace_6017380 : CollatzResearch.WordTrace tailWord_6017380 prefixEnd_6017380 3089808220751772206776579 := by
  unfold tailWord_6017380
  simp only [CollatzResearch.WordTrace]
  refine ⟨109735939470033710765396797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146314585960044947687195729 109735939470033710765396797)
  ·
    refine ⟨41150977301262641537023799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109735939470033710765396797 41150977301262641537023799)
    ·
      refine ⟨61726465951893962305535699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41150977301262641537023799 61726465951893962305535699)
      ·
        refine ⟨92589698927840943458303549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61726465951893962305535699 92589698927840943458303549)
        ·
          refine ⟨34721137097940353796863831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92589698927840943458303549 34721137097940353796863831)
          ·
            refine ⟨52081705646910530695295747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34721137097940353796863831 52081705646910530695295747)
            ·
              refine ⟨78122558470365796042943621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52081705646910530695295747 78122558470365796042943621)
              ·
                refine ⟨14647979713193586758051929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78122558470365796042943621 14647979713193586758051929)
                ·
                  refine ⟨10985984784895190068538947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14647979713193586758051929 10985984784895190068538947)
                  ·
                    refine ⟨16478977177342785102808421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10985984784895190068538947 16478977177342785102808421)
                    ·
                      refine ⟨3089808220751772206776579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16478977177342785102808421 3089808220751772206776579)
                      ·
                        rfl

theorem cell23_6017380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_6017380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017380 prefixEnd_6017380 := by exact prefixLift 6017380
  have htrace : WordTrace (prefixWord ++ tailWord_6017380) baseStart_6017380 baseEnd_6017380 := by
    simpa [prefixWord, tailWord_6017380, baseEnd_6017380] using wordTrace_append hprefix tailTrace_6017380
  have hstable : (prefixWord ++ tailWord_6017380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017380).length < 2 ^ (prefixWord ++ tailWord_6017380).sum := by decide
  have hdescent : baseEnd_6017380 < baseStart_6017380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017393 : List Nat := [1, 2, 2, 2, 1, 2, 1, 2, 2, 4, 4]
def baseStart_6017393 : Nat := 118140960795 + 6017393 * 2 ^ 59
def prefixEnd_6017393 : Nat := 4983230072969 + 3 ^ 40 * 6017393 * 2
def baseEnd_6017393 : Nat := 3089814896000280655914019

theorem tailTrace_6017393 : CollatzResearch.WordTrace tailWord_6017393 prefixEnd_6017393 3089814896000280655914019 := by
  unfold tailWord_6017393
  simp only [CollatzResearch.WordTrace]
  refine ⟨219472353089020324751016833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146314902059346883167344555 219472353089020324751016833)
  ·
    refine ⟨164604264816765243563262625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219472353089020324751016833 164604264816765243563262625)
    ·
      refine ⟨123453198612573932672446969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164604264816765243563262625 123453198612573932672446969)
      ·
        refine ⟨92589898959430449504335227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123453198612573932672446969 92589898959430449504335227)
        ·
          refine ⟨138884848439145674256502841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92589898959430449504335227 138884848439145674256502841)
          ·
            refine ⟨104163636329359255692377131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138884848439145674256502841 104163636329359255692377131)
            ·
              refine ⟨156245454494038883538565697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104163636329359255692377131 156245454494038883538565697)
              ·
                refine ⟨117184090870529162653924273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156245454494038883538565697 117184090870529162653924273)
                ·
                  refine ⟨87888068152896871990443205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117184090870529162653924273 87888068152896871990443205)
                  ·
                    refine ⟨16479012778668163498208101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 87888068152896871990443205 16479012778668163498208101)
                    ·
                      refine ⟨3089814896000280655914019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16479012778668163498208101 3089814896000280655914019)
                      ·
                        rfl

theorem cell23_6017393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_6017393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017393 prefixEnd_6017393 := by exact prefixLift 6017393
  have htrace : WordTrace (prefixWord ++ tailWord_6017393) baseStart_6017393 baseEnd_6017393 := by
    simpa [prefixWord, tailWord_6017393, baseEnd_6017393] using wordTrace_append hprefix tailTrace_6017393
  have hstable : (prefixWord ++ tailWord_6017393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017393).length < 2 ^ (prefixWord ++ tailWord_6017393).sum := by decide
  have hdescent : baseEnd_6017393 < baseStart_6017393 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017397 : List Nat := [1, 3, 4, 1, 2, 1, 1, 1, 1, 6, 2]
def baseStart_6017397 : Nat := 118140960795 + 6017397 * 2 ^ 59
def prefixEnd_6017397 : Nat := 4983230072969 + 3 ^ 40 * 6017397 * 2
def baseEnd_6017397 : Nat := 3089816949922898640264001

theorem tailTrace_6017397 : CollatzResearch.WordTrace tailWord_6017397 prefixEnd_6017397 3089816949922898640264001 := by
  unfold tailWord_6017397
  simp only [CollatzResearch.WordTrace]
  refine ⟨219472498981005833434162445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146314999320670555622774963 219472498981005833434162445)
  ·
    refine ⟨82302187117877187537810917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219472498981005833434162445 82302187117877187537810917)
    ·
      refine ⟨15431660084601972663339547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82302187117877187537810917 15431660084601972663339547)
      ·
        refine ⟨23147490126902958995009321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15431660084601972663339547 23147490126902958995009321)
        ·
          refine ⟨17360617595177219246256991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23147490126902958995009321 17360617595177219246256991)
          ·
            refine ⟨26040926392765828869385487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17360617595177219246256991 26040926392765828869385487)
            ·
              refine ⟨39061389589148743304078231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26040926392765828869385487 39061389589148743304078231)
              ·
                refine ⟨58592084383723114956117347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39061389589148743304078231 58592084383723114956117347)
                ·
                  refine ⟨87888126575584672434176021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58592084383723114956117347 87888126575584672434176021)
                  ·
                    refine ⟨4119755933230531520352001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 87888126575584672434176021 4119755933230531520352001)
                    ·
                      refine ⟨3089816949922898640264001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4119755933230531520352001 3089816949922898640264001)
                      ·
                        rfl

theorem cell23_6017397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_6017397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017397 prefixEnd_6017397 := by exact prefixLift 6017397
  have htrace : WordTrace (prefixWord ++ tailWord_6017397) baseStart_6017397 baseEnd_6017397 := by
    simpa [prefixWord, tailWord_6017397, baseEnd_6017397] using wordTrace_append hprefix tailTrace_6017397
  have hstable : (prefixWord ++ tailWord_6017397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017397).length < 2 ^ (prefixWord ++ tailWord_6017397).sum := by decide
  have hdescent : baseEnd_6017397 < baseStart_6017397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017417 : List Nat := [1, 2, 1, 1, 6, 1, 3, 1, 2, 2, 3]
def baseStart_6017417 : Nat := 118140960795 + 6017417 * 2 ^ 59
def prefixEnd_6017417 : Nat := 4983230072969 + 3 ^ 40 * 6017417 * 2
def baseEnd_6017417 : Nat := 3089827219535988562013909

theorem tailTrace_6017417 : CollatzResearch.WordTrace tailWord_6017417 prefixEnd_6017417 3089827219535988562013909 := by
  unfold tailWord_6017417
  simp only [CollatzResearch.WordTrace]
  refine ⟨219473228440933376849890505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146315485627288917899927003 219473228440933376849890505)
  ·
    refine ⟨164604921330700032637417879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219473228440933376849890505 164604921330700032637417879)
    ·
      refine ⟨246907381996050048956126819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164604921330700032637417879 246907381996050048956126819)
      ·
        refine ⟨370361072994075073434190229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246907381996050048956126819 370361072994075073434190229)
        ·
          refine ⟨17360675296597269067227667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 370361072994075073434190229 17360675296597269067227667)
          ·
            refine ⟨26041012944895903600841501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17360675296597269067227667 26041012944895903600841501)
            ·
              refine ⟨9765379854335963850315563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26041012944895903600841501 9765379854335963850315563)
              ·
                refine ⟨14648069781503945775473345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9765379854335963850315563 14648069781503945775473345)
                ·
                  refine ⟨10986052336127959331605009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14648069781503945775473345 10986052336127959331605009)
                  ·
                    refine ⟨8239539252095969498703757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10986052336127959331605009 8239539252095969498703757)
                    ·
                      refine ⟨3089827219535988562013909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8239539252095969498703757 3089827219535988562013909)
                      ·
                        rfl

theorem cell23_6017417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 2, 2, 3].length) (baseStart_6017417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017417 prefixEnd_6017417 := by exact prefixLift 6017417
  have htrace : WordTrace (prefixWord ++ tailWord_6017417) baseStart_6017417 baseEnd_6017417 := by
    simpa [prefixWord, tailWord_6017417, baseEnd_6017417] using wordTrace_append hprefix tailTrace_6017417
  have hstable : (prefixWord ++ tailWord_6017417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017417).length < 2 ^ (prefixWord ++ tailWord_6017417).sum := by decide
  have hdescent : baseEnd_6017417 < baseStart_6017417 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017457 : List Nat := [1, 2, 2, 4, 1, 2, 1, 2, 1, 5, 2]
def baseStart_6017457 : Nat := 118140960795 + 6017457 * 2 ^ 59
def prefixEnd_6017457 : Nat := 4983230072969 + 3 ^ 40 * 6017457 * 2
def baseEnd_6017457 : Nat := 3089847758762168405513725

theorem tailTrace_6017457 : CollatzResearch.WordTrace tailWord_6017457 prefixEnd_6017457 3089847758762168405513725 := by
  unfold tailWord_6017457
  simp only [CollatzResearch.WordTrace]
  refine ⟨219474687360788463681346625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146316458240525642454231083 219474687360788463681346625)
  ·
    refine ⟨164606015520591347761009969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219474687360788463681346625 164606015520591347761009969)
    ·
      refine ⟨123454511640443510820757477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164606015520591347761009969 123454511640443510820757477)
      ·
        refine ⟨23147720932583158278892027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123454511640443510820757477 23147720932583158278892027)
        ·
          refine ⟨34721581398874737418338041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23147720932583158278892027 34721581398874737418338041)
          ·
            refine ⟨26041186049156053063753531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34721581398874737418338041 26041186049156053063753531)
            ·
              refine ⟨39061779073734079595630297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26041186049156053063753531 39061779073734079595630297)
              ·
                refine ⟨29296334305300559696722723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39061779073734079595630297 29296334305300559696722723)
                ·
                  refine ⟨43944501457950839545084085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29296334305300559696722723 43944501457950839545084085)
                  ·
                    refine ⟨4119797011682891207351633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43944501457950839545084085 4119797011682891207351633)
                    ·
                      refine ⟨3089847758762168405513725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4119797011682891207351633 3089847758762168405513725)
                      ·
                        rfl

theorem cell23_6017457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_6017457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017457 prefixEnd_6017457 := by exact prefixLift 6017457
  have htrace : WordTrace (prefixWord ++ tailWord_6017457) baseStart_6017457 baseEnd_6017457 := by
    simpa [prefixWord, tailWord_6017457, baseEnd_6017457] using wordTrace_append hprefix tailTrace_6017457
  have hstable : (prefixWord ++ tailWord_6017457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017457).length < 2 ^ (prefixWord ++ tailWord_6017457).sum := by decide
  have hdescent : baseEnd_6017457 < baseStart_6017457 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017497 : List Nat := [1, 2, 1, 2, 4, 1, 2, 4, 2, 4]
def baseStart_6017497 : Nat := 118140960795 + 6017497 * 2 ^ 59
def prefixEnd_6017497 : Nat := 4983230072969 + 3 ^ 40 * 6017497 * 2
def baseEnd_6017497 : Nat := 1029956099329449416337847

theorem tailTrace_6017497 : CollatzResearch.WordTrace tailWord_6017497 prefixEnd_6017497 1029956099329449416337847 := by
  unfold tailWord_6017497
  simp only [CollatzResearch.WordTrace]
  refine ⟨219476146280643550512802745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146317430853762367008535163 219476146280643550512802745)
  ·
    refine ⟨164607109710482662884602059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219476146280643550512802745 164607109710482662884602059)
    ·
      refine ⟨246910664565723994326903089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164607109710482662884602059 246910664565723994326903089)
      ·
        refine ⟨185182998424292995745177317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246910664565723994326903089 185182998424292995745177317)
        ·
          refine ⟨34721812204554936702220747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 185182998424292995745177317 34721812204554936702220747)
          ·
            refine ⟨52082718306832405053331121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34721812204554936702220747 52082718306832405053331121)
            ·
              refine ⟨39062038730124303789998341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52082718306832405053331121 39062038730124303789998341)
              ·
                refine ⟨7324132261898306960624689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39062038730124303789998341 7324132261898306960624689)
                ·
                  refine ⟨5493099196423730220468517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7324132261898306960624689 5493099196423730220468517)
                  ·
                    refine ⟨1029956099329449416337847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5493099196423730220468517 1029956099329449416337847)
                    ·
                      rfl

theorem cell23_6017497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 4, 2, 4].length) (baseStart_6017497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017497 prefixEnd_6017497 := by exact prefixLift 6017497
  have htrace : WordTrace (prefixWord ++ tailWord_6017497) baseStart_6017497 baseEnd_6017497 := by
    simpa [prefixWord, tailWord_6017497, baseEnd_6017497] using wordTrace_append hprefix tailTrace_6017497
  have hstable : (prefixWord ++ tailWord_6017497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017497).length < 2 ^ (prefixWord ++ tailWord_6017497).sum := by decide
  have hdescent : baseEnd_6017497 < baseStart_6017497 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017514 : List Nat := [3, 1, 3, 1, 3, 2, 1, 3, 2, 4]
def baseStart_6017514 : Nat := 118140960795 + 6017514 * 2 ^ 59
def prefixEnd_6017514 : Nat := 4983230072969 + 3 ^ 40 * 6017514 * 2
def baseEnd_6017514 : Nat := 1029959009053158227500321

theorem tailTrace_6017514 : CollatzResearch.WordTrace tailWord_6017514 prefixEnd_6017514 1029959009053158227500321 := by
  unfold tailWord_6017514
  simp only [CollatzResearch.WordTrace]
  refine ⟨54869191580395490604042899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146317844214387974944114397 54869191580395490604042899)
  ·
    refine ⟨82303787370593235906064349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54869191580395490604042899 82303787370593235906064349)
    ·
      refine ⟨30863920263972463464774131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82303787370593235906064349 30863920263972463464774131)
      ·
        refine ⟨46295880395958695197161197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30863920263972463464774131 46295880395958695197161197)
        ·
          refine ⟨17360955148484510698935449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46295880395958695197161197 17360955148484510698935449)
          ·
            refine ⟨13020716361363383024201587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17360955148484510698935449 13020716361363383024201587)
            ·
              refine ⟨19531074542045074536302381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13020716361363383024201587 19531074542045074536302381)
              ·
                refine ⟨7324152953266902951113393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19531074542045074536302381 7324152953266902951113393)
                ·
                  refine ⟨5493114714950177213335045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7324152953266902951113393 5493114714950177213335045)
                  ·
                    refine ⟨1029959009053158227500321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5493114714950177213335045 1029959009053158227500321)
                    ·
                      rfl

theorem cell23_6017514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_6017514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017514 prefixEnd_6017514 := by exact prefixLift 6017514
  have htrace : WordTrace (prefixWord ++ tailWord_6017514) baseStart_6017514 baseEnd_6017514 := by
    simpa [prefixWord, tailWord_6017514, baseEnd_6017514] using wordTrace_append hprefix tailTrace_6017514
  have hstable : (prefixWord ++ tailWord_6017514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017514).length < 2 ^ (prefixWord ++ tailWord_6017514).sum := by decide
  have hdescent : baseEnd_6017514 < baseStart_6017514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017517 : List Nat := [1, 5, 1, 3, 1, 1, 2, 1, 1, 1, 6]
def baseStart_6017517 : Nat := 118140960795 + 6017517 * 2 ^ 59
def prefixEnd_6017517 : Nat := 4983230072969 + 3 ^ 40 * 6017517 * 2
def baseEnd_6017517 : Nat := 3089878567601438170763449

theorem tailTrace_6017517 : CollatzResearch.WordTrace tailWord_6017517 prefixEnd_6017517 3089878567601438170763449 := by
  unfold tailWord_6017517
  simp only [CollatzResearch.WordTrace]
  refine ⟨219476875740571093928530805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146317917160380729285687203 219476875740571093928530805)
  ·
    refine ⟨20575957100678540055799763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 219476875740571093928530805 20575957100678540055799763)
    ·
      refine ⟨30863935651017810083699645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20575957100678540055799763 30863935651017810083699645)
      ·
        refine ⟨11573975869131678781387367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30863935651017810083699645 11573975869131678781387367)
        ·
          refine ⟨17360963803697518172081051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11573975869131678781387367 17360963803697518172081051)
          ·
            refine ⟨26041445705546277258121577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17360963803697518172081051 26041445705546277258121577)
            ·
              refine ⟨19531084279159707943591183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26041445705546277258121577 19531084279159707943591183)
              ·
                refine ⟨29296626418739561915386775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19531084279159707943591183 29296626418739561915386775)
                ·
                  refine ⟨43944939628109342873080163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29296626418739561915386775 43944939628109342873080163)
                  ·
                    refine ⟨65917409442164014309620245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43944939628109342873080163 65917409442164014309620245)
                    ·
                      refine ⟨3089878567601438170763449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65917409442164014309620245 3089878567601438170763449)
                      ·
                        rfl

theorem cell23_6017517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_6017517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017517 prefixEnd_6017517 := by exact prefixLift 6017517
  have htrace : WordTrace (prefixWord ++ tailWord_6017517) baseStart_6017517 baseEnd_6017517 := by
    simpa [prefixWord, tailWord_6017517, baseEnd_6017517] using wordTrace_append hprefix tailTrace_6017517
  have hstable : (prefixWord ++ tailWord_6017517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017517).length < 2 ^ (prefixWord ++ tailWord_6017517).sum := by decide
  have hdescent : baseEnd_6017517 < baseStart_6017517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017537 : List Nat := [1, 2, 4, 1, 3, 1, 1, 1, 3, 3, 3]
def baseStart_6017537 : Nat := 118140960795 + 6017537 * 2 ^ 59
def prefixEnd_6017537 : Nat := 4983230072969 + 3 ^ 40 * 6017537 * 2
def baseEnd_6017537 : Nat := 3089888837214528092513357

theorem tailTrace_6017537 : CollatzResearch.WordTrace tailWord_6017537 prefixEnd_6017537 3089888837214528092513357 := by
  unfold tailWord_6017537
  simp only [CollatzResearch.WordTrace]
  refine ⟨219477605200498637344258865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146318403466999091562839243 219477605200498637344258865)
  ·
    refine ⟨164608203900373978008194149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219477605200498637344258865 164608203900373978008194149)
    ·
      refine ⟨30864038231320120876536403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164608203900373978008194149 30864038231320120876536403)
      ·
        refine ⟨46296057346980181314804605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30864038231320120876536403 46296057346980181314804605)
        ·
          refine ⟨17361021505117567993051727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46296057346980181314804605 17361021505117567993051727)
          ·
            refine ⟨26041532257676351989577591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17361021505117567993051727 26041532257676351989577591)
            ·
              refine ⟨39062298386514527984366387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26041532257676351989577591 39062298386514527984366387)
              ·
                refine ⟨58593447579771791976549581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39062298386514527984366387 58593447579771791976549581)
                ·
                  refine ⟨21972542842414421991206093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58593447579771791976549581 21972542842414421991206093)
                  ·
                    refine ⟨8239703565905408246702285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21972542842414421991206093 8239703565905408246702285)
                    ·
                      refine ⟨3089888837214528092513357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8239703565905408246702285 3089888837214528092513357)
                      ·
                        rfl

theorem cell23_6017537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_6017537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017537 prefixEnd_6017537 := by exact prefixLift 6017537
  have htrace : WordTrace (prefixWord ++ tailWord_6017537) baseStart_6017537 baseEnd_6017537 := by
    simpa [prefixWord, tailWord_6017537, baseEnd_6017537] using wordTrace_append hprefix tailTrace_6017537
  have hstable : (prefixWord ++ tailWord_6017537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017537).length < 2 ^ (prefixWord ++ tailWord_6017537).sum := by decide
  have hdescent : baseEnd_6017537 < baseStart_6017537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017538 : List Nat := [3, 4, 1, 2, 2, 1, 3, 1, 1, 1, 4]
def baseStart_6017538 : Nat := 118140960795 + 6017538 * 2 ^ 59
def prefixEnd_6017538 : Nat := 4983230072969 + 3 ^ 40 * 6017538 * 2
def baseEnd_6017538 : Nat := 3089889350695182588600853

theorem tailTrace_6017538 : CollatzResearch.WordTrace tailWord_6017538 prefixEnd_6017538 3089889350695182588600853 := by
  unfold tailWord_6017538
  simp only [CollatzResearch.WordTrace]
  refine ⟨54869410418373753628761317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146318427782330009676696845 54869410418373753628761317)
  ·
    refine ⟨10288014453445078805392747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54869410418373753628761317 10288014453445078805392747)
    ·
      refine ⟨15432021680167618208089121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10288014453445078805392747 15432021680167618208089121)
      ·
        refine ⟨11574016260125713656066841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15432021680167618208089121 11574016260125713656066841)
        ·
          refine ⟨8680512195094285242050131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11574016260125713656066841 8680512195094285242050131)
          ·
            refine ⟨13020768292641427863075197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8680512195094285242050131 13020768292641427863075197)
            ·
              refine ⟨4882788109740535448653199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13020768292641427863075197 4882788109740535448653199)
              ·
                refine ⟨7324182164610803172979799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4882788109740535448653199 7324182164610803172979799)
                ·
                  refine ⟨10986273246916204759469699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7324182164610803172979799 10986273246916204759469699)
                  ·
                    refine ⟨16479409870374307139204549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10986273246916204759469699 16479409870374307139204549)
                    ·
                      refine ⟨3089889350695182588600853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16479409870374307139204549 3089889350695182588600853)
                      ·
                        rfl

theorem cell23_6017538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_6017538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017538 prefixEnd_6017538 := by exact prefixLift 6017538
  have htrace : WordTrace (prefixWord ++ tailWord_6017538) baseStart_6017538 baseEnd_6017538 := by
    simpa [prefixWord, tailWord_6017538, baseEnd_6017538] using wordTrace_append hprefix tailTrace_6017538
  have hstable : (prefixWord ++ tailWord_6017538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017538).length < 2 ^ (prefixWord ++ tailWord_6017538).sum := by decide
  have hdescent : baseEnd_6017538 < baseStart_6017538 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017564 : List Nat := [2, 2, 3, 1, 2, 2, 1, 2, 3, 3, 2]
def baseStart_6017564 : Nat := 118140960795 + 6017564 * 2 ^ 59
def prefixEnd_6017564 : Nat := 4983230072969 + 3 ^ 40 * 6017564 * 2
def baseEnd_6017564 : Nat := 3089902701192199486875733

theorem tailTrace_6017564 : CollatzResearch.WordTrace tailWord_6017564 prefixEnd_6017564 3089902701192199486875733 := by
  unfold tailWord_6017564
  simp only [CollatzResearch.WordTrace]
  refine ⟨109739294985700410477745873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146319059980933880636994497 109739294985700410477745873)
  ·
    refine ⟨82304471239275307858309405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109739294985700410477745873 82304471239275307858309405)
    ·
      refine ⟨30864176714728240446866027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82304471239275307858309405 30864176714728240446866027)
      ·
        refine ⟨46296265072092360670299041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30864176714728240446866027 46296265072092360670299041)
        ·
          refine ⟨34722198804069270502724281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46296265072092360670299041 34722198804069270502724281)
          ·
            refine ⟨26041649103051952877043211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34722198804069270502724281 26041649103051952877043211)
            ·
              refine ⟨39062473654577929315564817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26041649103051952877043211 39062473654577929315564817)
              ·
                refine ⟨29296855240933446986673613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39062473654577929315564817 29296855240933446986673613)
                ·
                  refine ⟨10986320715350042620002605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29296855240933446986673613 10986320715350042620002605)
                  ·
                    refine ⟨4119870268256265982500977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10986320715350042620002605 4119870268256265982500977)
                    ·
                      refine ⟨3089902701192199486875733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4119870268256265982500977 3089902701192199486875733)
                      ·
                        rfl

theorem cell23_6017564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 3, 3, 2].length) (baseStart_6017564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017564 prefixEnd_6017564 := by exact prefixLift 6017564
  have htrace : WordTrace (prefixWord ++ tailWord_6017564) baseStart_6017564 baseEnd_6017564 := by
    simpa [prefixWord, tailWord_6017564, baseEnd_6017564] using wordTrace_append hprefix tailTrace_6017564
  have hstable : (prefixWord ++ tailWord_6017564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017564).length < 2 ^ (prefixWord ++ tailWord_6017564).sum := by decide
  have hdescent : baseEnd_6017564 < baseStart_6017564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017580 : List Nat := [2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 5]
def baseStart_6017580 : Nat := 118140960795 + 6017580 * 2 ^ 59
def prefixEnd_6017580 : Nat := 4983230072969 + 3 ^ 40 * 6017580 * 2
def baseEnd_6017580 : Nat := 3089910916882671424275659

theorem tailTrace_6017580 : CollatzResearch.WordTrace tailWord_6017580 prefixEnd_6017580 3089910916882671424275659 := by
  unfold tailWord_6017580
  simp only [CollatzResearch.WordTrace]
  refine ⟨109739586769671427844037097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146319449026228570458716129 109739586769671427844037097)
  ·
    refine ⟨82304690077253570883027823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109739586769671427844037097 82304690077253570883027823)
    ·
      refine ⟨123457035115880356324541735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82304690077253570883027823 123457035115880356324541735)
      ·
        refine ⟨185185552673820534486812603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123457035115880356324541735 185185552673820534486812603)
        ·
          refine ⟨277778329010730801730218905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185185552673820534486812603 277778329010730801730218905)
          ·
            refine ⟨208333746758048101297664179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277778329010730801730218905 208333746758048101297664179)
            ·
              refine ⟨312500620137072151946496269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208333746758048101297664179 312500620137072151946496269)
              ·
                refine ⟨117187732551402056979936101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 312500620137072151946496269 117187732551402056979936101)
                ·
                  refine ⟨21972699853387885683738019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 117187732551402056979936101 21972699853387885683738019)
                  ·
                    refine ⟨32959049780081828525607029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21972699853387885683738019 32959049780081828525607029)
                    ·
                      refine ⟨3089910916882671424275659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32959049780081828525607029 3089910916882671424275659)
                      ·
                        rfl

theorem cell23_6017580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 5].length) (baseStart_6017580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017580 prefixEnd_6017580 := by exact prefixLift 6017580
  have htrace : WordTrace (prefixWord ++ tailWord_6017580) baseStart_6017580 baseEnd_6017580 := by
    simpa [prefixWord, tailWord_6017580, baseEnd_6017580] using wordTrace_append hprefix tailTrace_6017580
  have hstable : (prefixWord ++ tailWord_6017580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017580).length < 2 ^ (prefixWord ++ tailWord_6017580).sum := by decide
  have hdescent : baseEnd_6017580 < baseStart_6017580 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017594 : List Nat := [3, 1, 1, 1, 3, 3, 2, 2, 1, 4, 2]
def baseStart_6017594 : Nat := 118140960795 + 6017594 * 2 ^ 59
def prefixEnd_6017594 : Nat := 4983230072969 + 3 ^ 40 * 6017594 * 2
def baseEnd_6017594 : Nat := 3089918105611834369500595

theorem tailTrace_6017594 : CollatzResearch.WordTrace tailWord_6017594 prefixEnd_6017594 3089918105611834369500595 := by
  unfold tailWord_6017594
  simp only [CollatzResearch.WordTrace]
  refine ⟨54869921040323034019770959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146319789440861424052722557 54869921040323034019770959)
  ·
    refine ⟨82304881560484551029656439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54869921040323034019770959 82304881560484551029656439)
    ·
      refine ⟨123457322340726826544484659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82304881560484551029656439 123457322340726826544484659)
      ·
        refine ⟨185185983511090239816726989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123457322340726826544484659 185185983511090239816726989)
        ·
          refine ⟨69444743816658839931272621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185185983511090239816726989 69444743816658839931272621)
          ·
            refine ⟨26041778931247064974227233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69444743816658839931272621 26041778931247064974227233)
            ·
              refine ⟨19531334198435298730670425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26041778931247064974227233 19531334198435298730670425)
              ·
                refine ⟨14648500648826474048002819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19531334198435298730670425 14648500648826474048002819)
                ·
                  refine ⟨21972750973239711072004229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14648500648826474048002819 21972750973239711072004229)
                  ·
                    refine ⟨4119890807482445826000793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21972750973239711072004229 4119890807482445826000793)
                    ·
                      refine ⟨3089918105611834369500595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4119890807482445826000793 3089918105611834369500595)
                      ·
                        rfl

theorem cell23_6017594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 1, 4, 2].length) (baseStart_6017594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017594 prefixEnd_6017594 := by exact prefixLift 6017594
  have htrace : WordTrace (prefixWord ++ tailWord_6017594) baseStart_6017594 baseEnd_6017594 := by
    simpa [prefixWord, tailWord_6017594, baseEnd_6017594] using wordTrace_append hprefix tailTrace_6017594
  have hstable : (prefixWord ++ tailWord_6017594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017594).length < 2 ^ (prefixWord ++ tailWord_6017594).sum := by decide
  have hdescent : baseEnd_6017594 < baseStart_6017594 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017607 : List Nat := [1, 1, 4, 1, 4, 1, 1, 2, 2, 2, 4]
def baseStart_6017607 : Nat := 118140960795 + 6017607 * 2 ^ 59
def prefixEnd_6017607 : Nat := 4983230072969 + 3 ^ 40 * 6017607 * 2
def baseEnd_6017607 : Nat := 3089924780860342818638035

theorem tailTrace_6017607 : CollatzResearch.WordTrace tailWord_6017607 prefixEnd_6017607 3089924780860342818638035 := by
  unfold tailWord_6017607
  simp only [CollatzResearch.WordTrace]
  refine ⟨219480158310245039299307075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146320105540163359532871383 219480158310245039299307075)
  ·
    refine ⟨329220237465367558948960613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219480158310245039299307075 329220237465367558948960613)
    ·
      refine ⟨61728794524756417302930115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 329220237465367558948960613 61728794524756417302930115)
      ·
        refine ⟨92593191787134625954395173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61728794524756417302930115 92593191787134625954395173)
        ·
          refine ⟨17361223460087742366449095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92593191787134625954395173 17361223460087742366449095)
          ·
            refine ⟨26041835190131613549673643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17361223460087742366449095 26041835190131613549673643)
            ·
              refine ⟨39062752785197420324510465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26041835190131613549673643 39062752785197420324510465)
              ·
                refine ⟨29297064588898065243382849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39062752785197420324510465 29297064588898065243382849)
                ·
                  refine ⟨21972798441673548932537137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29297064588898065243382849 21972798441673548932537137)
                  ·
                    refine ⟨16479598831255161699402853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21972798441673548932537137 16479598831255161699402853)
                    ·
                      refine ⟨3089924780860342818638035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16479598831255161699402853 3089924780860342818638035)
                      ·
                        rfl

theorem cell23_6017607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_6017607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017607 prefixEnd_6017607 := by exact prefixLift 6017607
  have htrace : WordTrace (prefixWord ++ tailWord_6017607) baseStart_6017607 baseEnd_6017607 := by
    simpa [prefixWord, tailWord_6017607, baseEnd_6017607] using wordTrace_append hprefix tailTrace_6017607
  have hstable : (prefixWord ++ tailWord_6017607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017607).length < 2 ^ (prefixWord ++ tailWord_6017607).sum := by decide
  have hdescent : baseEnd_6017607 < baseStart_6017607 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017611 : List Nat := [1, 1, 1, 1, 3, 1, 7, 2, 2, 2, 2]
def baseStart_6017611 : Nat := 118140960795 + 6017611 * 2 ^ 59
def prefixEnd_6017611 : Nat := 4983230072969 + 3 ^ 40 * 6017611 * 2
def baseEnd_6017611 : Nat := 3089926834782960802988017

theorem tailTrace_6017611 : CollatzResearch.WordTrace tailWord_6017611 prefixEnd_6017611 3089926834782960802988017 := by
  unfold tailWord_6017611
  simp only [CollatzResearch.WordTrace]
  refine ⟨219480304202230547982452687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146320202801487031988301791 219480304202230547982452687)
  ·
    refine ⟨329220456303345821973679031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219480304202230547982452687 329220456303345821973679031)
    ·
      refine ⟨493830684455018732960518547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329220456303345821973679031 493830684455018732960518547)
      ·
        refine ⟨740746026682528099440777821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 493830684455018732960518547 740746026682528099440777821)
        ·
          refine ⟨277779760005948037290291683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 740746026682528099440777821 277779760005948037290291683)
          ·
            refine ⟨416669640008922055935437525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277779760005948037290291683 416669640008922055935437525)
            ·
              refine ⟨9765694687709110685986817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 416669640008922055935437525 9765694687709110685986817)
              ·
                refine ⟨7324271015781833014490113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9765694687709110685986817 7324271015781833014490113)
                ·
                  refine ⟨5493203261836374760867585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7324271015781833014490113 5493203261836374760867585)
                  ·
                    refine ⟨4119902446377281070650689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5493203261836374760867585 4119902446377281070650689)
                    ·
                      refine ⟨3089926834782960802988017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4119902446377281070650689 3089926834782960802988017)
                      ·
                        rfl

theorem cell23_6017611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 2, 2, 2, 2].length) (baseStart_6017611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017611 prefixEnd_6017611 := by exact prefixLift 6017611
  have htrace : WordTrace (prefixWord ++ tailWord_6017611) baseStart_6017611 baseEnd_6017611 := by
    simpa [prefixWord, tailWord_6017611, baseEnd_6017611] using wordTrace_append hprefix tailTrace_6017611
  have hstable : (prefixWord ++ tailWord_6017611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017611).length < 2 ^ (prefixWord ++ tailWord_6017611).sum := by decide
  have hdescent : baseEnd_6017611 < baseStart_6017611 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017617 : List Nat := [1, 2, 2, 1, 3, 4, 2, 1, 7]
def baseStart_6017617 : Nat := 118140960795 + 6017617 * 2 ^ 59
def prefixEnd_6017617 : Nat := 4983230072969 + 3 ^ 40 * 6017617 * 2
def baseEnd_6017617 : Nat := 343325546185209753279221

theorem tailTrace_6017617 : CollatzResearch.WordTrace tailWord_6017617 prefixEnd_6017617 343325546185209753279221 := by
  unfold tailWord_6017617
  simp only [CollatzResearch.WordTrace]
  refine ⟨219480523040208811007171105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146320348693472540671447403 219480523040208811007171105)
  ·
    refine ⟨164610392280156608255378329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219480523040208811007171105 164610392280156608255378329)
    ·
      refine ⟨123457794210117456191533747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164610392280156608255378329 123457794210117456191533747)
      ·
        refine ⟨185186691315176184287300621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123457794210117456191533747 185186691315176184287300621)
        ·
          refine ⟨69445009243191069107737733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185186691315176184287300621 69445009243191069107737733)
          ·
            refine ⟨13020939233098325457700825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69445009243191069107737733 13020939233098325457700825)
            ·
              refine ⟨9765704424823744093275619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13020939233098325457700825 9765704424823744093275619)
              ·
                refine ⟨14648556637235616139913429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9765704424823744093275619 14648556637235616139913429)
                ·
                  refine ⟨343325546185209753279221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14648556637235616139913429 343325546185209753279221)
                  ·
                    rfl

theorem cell23_6017617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 7].length) (baseStart_6017617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017617 prefixEnd_6017617 := by exact prefixLift 6017617
  have htrace : WordTrace (prefixWord ++ tailWord_6017617) baseStart_6017617 baseEnd_6017617 := by
    simpa [prefixWord, tailWord_6017617, baseEnd_6017617] using wordTrace_append hprefix tailTrace_6017617
  have hstable : (prefixWord ++ tailWord_6017617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017617).length < 2 ^ (prefixWord ++ tailWord_6017617).sum := by decide
  have hdescent : baseEnd_6017617 < baseStart_6017617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017628 : List Nat := [2, 2, 4, 1, 3, 2, 1, 1, 1, 4, 2]
def baseStart_6017628 : Nat := 118140960795 + 6017628 * 2 ^ 59
def prefixEnd_6017628 : Nat := 4983230072969 + 3 ^ 40 * 6017628 * 2
def baseEnd_6017628 : Nat := 3089935563954087236475439

theorem tailTrace_6017628 : CollatzResearch.WordTrace tailWord_6017628 prefixEnd_6017628 3089935563954087236475439 := by
  unfold tailWord_6017628
  simp only [CollatzResearch.WordTrace]
  refine ⟨109740462121584479942910769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146320616162112639923881025 109740462121584479942910769)
  ·
    refine ⟨82305346591188359957183077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109740462121584479942910769 82305346591188359957183077)
    ·
      refine ⟨15432252485847817491971827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82305346591188359957183077 15432252485847817491971827)
      ·
        refine ⟨23148378728771726237957741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15432252485847817491971827 23148378728771726237957741)
        ·
          refine ⟨8680642023289397339234153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23148378728771726237957741 8680642023289397339234153)
          ·
            refine ⟨6510481517467048004425615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8680642023289397339234153 6510481517467048004425615)
            ·
              refine ⟨9765722276200572006638423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6510481517467048004425615 9765722276200572006638423)
              ·
                refine ⟨14648583414300858009957635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9765722276200572006638423 14648583414300858009957635)
                ·
                  refine ⟨21972875121451287014936453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14648583414300858009957635 21972875121451287014936453)
                  ·
                    refine ⟨4119914085272116315300585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21972875121451287014936453 4119914085272116315300585)
                    ·
                      refine ⟨3089935563954087236475439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4119914085272116315300585 3089935563954087236475439)
                      ·
                        rfl

theorem cell23_6017628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_6017628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017628 prefixEnd_6017628 := by exact prefixLift 6017628
  have htrace : WordTrace (prefixWord ++ tailWord_6017628) baseStart_6017628 baseEnd_6017628 := by
    simpa [prefixWord, tailWord_6017628, baseEnd_6017628] using wordTrace_append hprefix tailTrace_6017628
  have hstable : (prefixWord ++ tailWord_6017628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017628).length < 2 ^ (prefixWord ++ tailWord_6017628).sum := by decide
  have hdescent : baseEnd_6017628 < baseStart_6017628 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017667 : List Nat := [1, 1, 1, 3, 3, 1, 3, 1, 4, 1, 4]
def baseStart_6017667 : Nat := 118140960795 + 6017667 * 2 ^ 59
def prefixEnd_6017667 : Nat := 4983230072969 + 3 ^ 40 * 6017667 * 2
def baseEnd_6017667 : Nat := 3089955589699612583887759

theorem tailTrace_6017667 : CollatzResearch.WordTrace tailWord_6017667 prefixEnd_6017667 3089955589699612583887759 := by
  unfold tailWord_6017667
  simp only [CollatzResearch.WordTrace]
  refine ⟨219482346690027669546491255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146321564460018446364327503 219482346690027669546491255)
  ·
    refine ⟨329223520035041504319736883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219482346690027669546491255 329223520035041504319736883)
    ·
      refine ⟨493835280052562256479605325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329223520035041504319736883 493835280052562256479605325)
      ·
        refine ⟨185188230019710846179851997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 493835280052562256479605325 185188230019710846179851997)
        ·
          refine ⟨69445586257391567317444499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185188230019710846179851997 69445586257391567317444499)
          ·
            refine ⟨104168379386087350976166749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69445586257391567317444499 104168379386087350976166749)
            ·
              refine ⟨39063142269782756616062531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104168379386087350976166749 39063142269782756616062531)
              ·
                refine ⟨58594713404674134924093797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39063142269782756616062531 58594713404674134924093797)
                ·
                  refine ⟨10986508763376400298267587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58594713404674134924093797 10986508763376400298267587)
                  ·
                    refine ⟨16479763145064600447401381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10986508763376400298267587 16479763145064600447401381)
                    ·
                      refine ⟨3089955589699612583887759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16479763145064600447401381 3089955589699612583887759)
                      ·
                        rfl

theorem cell23_6017667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 4, 1, 4].length) (baseStart_6017667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017667 prefixEnd_6017667 := by exact prefixLift 6017667
  have htrace : WordTrace (prefixWord ++ tailWord_6017667) baseStart_6017667 baseEnd_6017667 := by
    simpa [prefixWord, tailWord_6017667, baseEnd_6017667] using wordTrace_append hprefix tailTrace_6017667
  have hstable : (prefixWord ++ tailWord_6017667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017667).length < 2 ^ (prefixWord ++ tailWord_6017667).sum := by decide
  have hdescent : baseEnd_6017667 < baseStart_6017667 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017674 : List Nat := [3, 1, 2, 3, 3, 1, 1, 1, 1, 2, 5]
def baseStart_6017674 : Nat := 118140960795 + 6017674 * 2 ^ 59
def prefixEnd_6017674 : Nat := 4983230072969 + 3 ^ 40 * 6017674 * 2
def baseEnd_6017674 : Nat := 3089959184064194056500227

theorem tailTrace_6017674 : CollatzResearch.WordTrace tailWord_6017674 prefixEnd_6017674 3089959184064194056500227 := by
  unfold tailWord_6017674
  simp only [CollatzResearch.WordTrace]
  refine ⟨54870650500250577435499019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146321734667334873161330717 54870650500250577435499019)
  ·
    refine ⟨82305975750375866153248529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54870650500250577435499019 82305975750375866153248529)
    ·
      refine ⟨61729481812781899614936397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82305975750375866153248529 61729481812781899614936397)
      ·
        refine ⟨23148555679793212355601149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61729481812781899614936397 23148555679793212355601149)
        ·
          refine ⟨8680708379922454633350431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23148555679793212355601149 8680708379922454633350431)
          ·
            refine ⟨13021062569883681950025647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8680708379922454633350431 13021062569883681950025647)
            ·
              refine ⟨19531593854825522925038471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13021062569883681950025647 19531593854825522925038471)
              ·
                refine ⟨29297390782238284387557707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19531593854825522925038471 29297390782238284387557707)
                ·
                  refine ⟨43946086173357426581336561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29297390782238284387557707 43946086173357426581336561)
                  ·
                    refine ⟨32959564630018069936002421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43946086173357426581336561 32959564630018069936002421)
                    ·
                      refine ⟨3089959184064194056500227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32959564630018069936002421 3089959184064194056500227)
                      ·
                        rfl

theorem cell23_6017674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_6017674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017674 prefixEnd_6017674 := by exact prefixLift 6017674
  have htrace : WordTrace (prefixWord ++ tailWord_6017674) baseStart_6017674 baseEnd_6017674 := by
    simpa [prefixWord, tailWord_6017674, baseEnd_6017674] using wordTrace_append hprefix tailTrace_6017674
  have hstable : (prefixWord ++ tailWord_6017674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017674).length < 2 ^ (prefixWord ++ tailWord_6017674).sum := by decide
  have hdescent : baseEnd_6017674 < baseStart_6017674 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017724 : List Nat := [2, 2, 2, 3, 1, 1, 4, 2, 6]
def baseStart_6017724 : Nat := 118140960795 + 6017724 * 2 ^ 59
def prefixEnd_6017724 : Nat := 4983230072969 + 3 ^ 40 * 6017724 * 2
def baseEnd_6017724 : Nat := 343331650899657651208333

theorem tailTrace_6017724 : CollatzResearch.WordTrace tailWord_6017724 prefixEnd_6017724 343331650899657651208333 := by
  unfold tailWord_6017724
  simp only [CollatzResearch.WordTrace]
  refine ⟨109742212825410584140658113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146322950433880778854210817 109742212825410584140658113)
  ·
    refine ⟨82306659619057938105493585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109742212825410584140658113 82306659619057938105493585)
    ·
      refine ⟨61729994714293453579120189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82306659619057938105493585 61729994714293453579120189)
      ·
        refine ⟨23148748017860045092170071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61729994714293453579120189 23148748017860045092170071)
        ·
          refine ⟨34723122026790067638255107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23148748017860045092170071 34723122026790067638255107)
          ·
            refine ⟨52084683040185101457382661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34723122026790067638255107 52084683040185101457382661)
            ·
              refine ⟨9765878070034706523259249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52084683040185101457382661 9765878070034706523259249)
              ·
                refine ⟨7324408552526029892444437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9765878070034706523259249 7324408552526029892444437)
                ·
                  refine ⟨343331650899657651208333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7324408552526029892444437 343331650899657651208333)
                  ·
                    rfl

theorem cell23_6017724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 2, 6].length) (baseStart_6017724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017724 prefixEnd_6017724 := by exact prefixLift 6017724
  have htrace : WordTrace (prefixWord ++ tailWord_6017724) baseStart_6017724 baseEnd_6017724 := by
    simpa [prefixWord, tailWord_6017724, baseEnd_6017724] using wordTrace_append hprefix tailTrace_6017724
  have hstable : (prefixWord ++ tailWord_6017724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017724).length < 2 ^ (prefixWord ++ tailWord_6017724).sum := by decide
  have hdescent : baseEnd_6017724 < baseStart_6017724 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017728 : List Nat := [2, 1, 1, 2, 4, 2, 4, 2, 1, 4]
def baseStart_6017728 : Nat := 118140960795 + 6017728 * 2 ^ 59
def prefixEnd_6017728 : Nat := 4983230072969 + 3 ^ 40 * 6017728 * 2
def baseEnd_6017728 : Nat := 1029995637339845615074993

theorem tailTrace_6017728 : CollatzResearch.WordTrace tailWord_6017728 prefixEnd_6017728 1029995637339845615074993 := by
  unfold tailWord_6017728
  simp only [CollatzResearch.WordTrace]
  refine ⟨109742285771403338482230919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146323047695204451309641225 109742285771403338482230919)
  ·
    refine ⟨164613428657105007723346379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109742285771403338482230919 164613428657105007723346379)
    ·
      refine ⟨246920142985657511585019569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164613428657105007723346379 246920142985657511585019569)
      ·
        refine ⟨185190107239243133688764677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246920142985657511585019569 185190107239243133688764677)
        ·
          refine ⟨34723145107358087566643377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 185190107239243133688764677 34723145107358087566643377)
          ·
            refine ⟨26042358830518565674982533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34723145107358087566643377 26042358830518565674982533)
            ·
              refine ⟨4882942280722231064059225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26042358830518565674982533 4882942280722231064059225)
              ·
                refine ⟨3662206710541673298044419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4882942280722231064059225 3662206710541673298044419)
                ·
                  refine ⟨5493310065812509947066629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3662206710541673298044419 5493310065812509947066629)
                  ·
                    refine ⟨1029995637339845615074993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5493310065812509947066629 1029995637339845615074993)
                    ·
                      rfl

theorem cell23_6017728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 2, 1, 4].length) (baseStart_6017728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017728 prefixEnd_6017728 := by exact prefixLift 6017728
  have htrace : WordTrace (prefixWord ++ tailWord_6017728) baseStart_6017728 baseEnd_6017728 := by
    simpa [prefixWord, tailWord_6017728, baseEnd_6017728] using wordTrace_append hprefix tailTrace_6017728
  have hstable : (prefixWord ++ tailWord_6017728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017728).length < 2 ^ (prefixWord ++ tailWord_6017728).sum := by decide
  have hdescent : baseEnd_6017728 < baseStart_6017728 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017751 : List Nat := [1, 1, 3, 2, 1, 5, 1, 2, 3, 1, 3]
def baseStart_6017751 : Nat := 118140960795 + 6017751 * 2 ^ 59
def prefixEnd_6017751 : Nat := 4983230072969 + 3 ^ 40 * 6017751 * 2
def baseEnd_6017751 : Nat := 3089998722074590255237373

theorem tailTrace_6017751 : CollatzResearch.WordTrace tailWord_6017751 prefixEnd_6017751 3089998722074590255237373 := by
  unfold tailWord_6017751
  simp only [CollatzResearch.WordTrace]
  refine ⟨219485410421723351892549107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146323606947815567928366071 219485410421723351892549107)
  ·
    refine ⟨329228115632585027838823661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219485410421723351892549107 329228115632585027838823661)
    ·
      refine ⟨123460543362219385439558873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 329228115632585027838823661 123460543362219385439558873)
      ·
        refine ⟨92595407521664539079669155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123460543362219385439558873 92595407521664539079669155)
        ·
          refine ⟨138893111282496808619503733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92595407521664539079669155 138893111282496808619503733)
          ·
            refine ⟨13021229182734075808078475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 138893111282496808619503733 13021229182734075808078475)
            ·
              refine ⟨19531843774101113712117713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13021229182734075808078475 19531843774101113712117713)
              ·
                refine ⟨14648882830575835284088285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19531843774101113712117713 14648882830575835284088285)
                ·
                  refine ⟨5493331061465938231533107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14648882830575835284088285 5493331061465938231533107)
                  ·
                    refine ⟨8239996592198907347299661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5493331061465938231533107 8239996592198907347299661)
                    ·
                      refine ⟨3089998722074590255237373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8239996592198907347299661 3089998722074590255237373)
                      ·
                        rfl

theorem cell23_6017751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 3, 1, 3].length) (baseStart_6017751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017751 prefixEnd_6017751 := by exact prefixLift 6017751
  have htrace : WordTrace (prefixWord ++ tailWord_6017751) baseStart_6017751 baseEnd_6017751 := by
    simpa [prefixWord, tailWord_6017751, baseEnd_6017751] using wordTrace_append hprefix tailTrace_6017751
  have hstable : (prefixWord ++ tailWord_6017751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017751).length < 2 ^ (prefixWord ++ tailWord_6017751).sum := by decide
  have hdescent : baseEnd_6017751 < baseStart_6017751 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017754 : List Nat := [3, 1, 1, 2, 2, 2, 2, 4, 1, 5]
def baseStart_6017754 : Nat := 118140960795 + 6017754 * 2 ^ 59
def prefixEnd_6017754 : Nat := 4983230072969 + 3 ^ 40 * 6017754 * 2
def baseEnd_6017754 : Nat := 1030000087505517914499953

theorem tailTrace_6017754 : CollatzResearch.WordTrace tailWord_6017754 prefixEnd_6017754 1030000087505517914499953 := by
  unfold tailWord_6017754
  simp only [CollatzResearch.WordTrace]
  refine ⟨54871379960178120851227079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146323679893808322269938877 54871379960178120851227079)
  ·
    refine ⟨82307069940267181276840619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54871379960178120851227079 82307069940267181276840619)
    ·
      refine ⟨123460604910400771915260929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82307069940267181276840619 123460604910400771915260929)
      ·
        refine ⟨92595453682800578936445697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123460604910400771915260929 92595453682800578936445697)
        ·
          refine ⟨69446590262100434202334273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92595453682800578936445697 69446590262100434202334273)
          ·
            refine ⟨52084942696575325651750705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69446590262100434202334273 52084942696575325651750705)
            ·
              refine ⟨39063707022431494238813029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52084942696575325651750705 39063707022431494238813029)
              ·
                refine ⟨7324445066705905169777443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39063707022431494238813029 7324445066705905169777443)
                ·
                  refine ⟨10986667600058857754666165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7324445066705905169777443 10986667600058857754666165)
                  ·
                    refine ⟨1030000087505517914499953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10986667600058857754666165 1030000087505517914499953)
                    ·
                      rfl

theorem cell23_6017754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 4, 1, 5].length) (baseStart_6017754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017754 prefixEnd_6017754 := by exact prefixLift 6017754
  have htrace : WordTrace (prefixWord ++ tailWord_6017754) baseStart_6017754 baseEnd_6017754 := by
    simpa [prefixWord, tailWord_6017754, baseEnd_6017754] using wordTrace_append hprefix tailTrace_6017754
  have hstable : (prefixWord ++ tailWord_6017754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017754).length < 2 ^ (prefixWord ++ tailWord_6017754).sum := by decide
  have hdescent : baseEnd_6017754 < baseStart_6017754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017761 : List Nat := [1, 2, 3, 1, 4, 2, 1, 1, 1, 5, 2]
def baseStart_6017761 : Nat := 118140960795 + 6017761 * 2 ^ 59
def prefixEnd_6017761 : Nat := 4983230072969 + 3 ^ 40 * 6017761 * 2
def baseEnd_6017761 : Nat := 3090003856881135216112327

theorem tailTrace_6017761 : CollatzResearch.WordTrace tailWord_6017761 prefixEnd_6017761 3090003856881135216112327 := by
  unfold tailWord_6017761
  simp only [CollatzResearch.WordTrace]
  refine ⟨219485775151687123600413137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146323850101124749066942091 219485775151687123600413137)
  ·
    refine ⟨164614331363765342700309853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219485775151687123600413137 164614331363765342700309853)
    ·
      refine ⟨61730374261412003512616195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164614331363765342700309853 61730374261412003512616195)
      ·
        refine ⟨92595561392118005268924293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61730374261412003512616195 92595561392118005268924293)
        ·
          refine ⟨17361667761022125987923305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92595561392118005268924293 17361667761022125987923305)
          ·
            refine ⟨13021250820766594490942479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17361667761022125987923305 13021250820766594490942479)
            ·
              refine ⟨19531876231149891736413719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13021250820766594490942479 19531876231149891736413719)
              ·
                refine ⟨29297814346724837604620579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19531876231149891736413719 29297814346724837604620579)
                ·
                  refine ⟨43946721520087256406930869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29297814346724837604620579 43946721520087256406930869)
                  ·
                    refine ⟨4120005142508180288149769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43946721520087256406930869 4120005142508180288149769)
                    ·
                      refine ⟨3090003856881135216112327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4120005142508180288149769 3090003856881135216112327)
                      ·
                        rfl

theorem cell23_6017761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 5, 2].length) (baseStart_6017761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017761 prefixEnd_6017761 := by exact prefixLift 6017761
  have htrace : WordTrace (prefixWord ++ tailWord_6017761) baseStart_6017761 baseEnd_6017761 := by
    simpa [prefixWord, tailWord_6017761, baseEnd_6017761] using wordTrace_append hprefix tailTrace_6017761
  have hstable : (prefixWord ++ tailWord_6017761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017761).length < 2 ^ (prefixWord ++ tailWord_6017761).sum := by decide
  have hdescent : baseEnd_6017761 < baseStart_6017761 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017784 : List Nat := [2, 1, 2, 1, 1, 2, 5, 1, 4, 4]
def baseStart_6017784 : Nat := 118140960795 + 6017784 * 2 ^ 59
def prefixEnd_6017784 : Nat := 4983230072969 + 3 ^ 40 * 6017784 * 2
def baseEnd_6017784 : Nat := 1030005222312062875374907

theorem tailTrace_6017784 : CollatzResearch.WordTrace tailWord_6017784 prefixEnd_6017784 1030005222312062875374907 := by
  unfold tailWord_6017784
  simp only [CollatzResearch.WordTrace]
  refine ⟨109743307015301899264250203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146324409353735865685666937 109743307015301899264250203)
  ·
    refine ⟨164614960522952848896375305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109743307015301899264250203 164614960522952848896375305)
    ·
      refine ⟨123461220392214636672281479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164614960522952848896375305 123461220392214636672281479)
      ·
        refine ⟨185191830588321955008422219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123461220392214636672281479 185191830588321955008422219)
        ·
          refine ⟨277787745882482932512633329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185191830588321955008422219 277787745882482932512633329)
          ·
            refine ⟨208340809411862199384474997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277787745882482932512633329 208340809411862199384474997)
            ·
              refine ⟨19531950882362081192294531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 208340809411862199384474997 19531950882362081192294531)
              ·
                refine ⟨29297926323543121788441797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19531950882362081192294531 29297926323543121788441797)
                ·
                  refine ⟨5493361185664335335332837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29297926323543121788441797 5493361185664335335332837)
                  ·
                    refine ⟨1030005222312062875374907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5493361185664335335332837 1030005222312062875374907)
                    ·
                      rfl

theorem cell23_6017784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 4, 4].length) (baseStart_6017784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017784 prefixEnd_6017784 := by exact prefixLift 6017784
  have htrace : WordTrace (prefixWord ++ tailWord_6017784) baseStart_6017784 baseEnd_6017784 := by
    simpa [prefixWord, tailWord_6017784, baseEnd_6017784] using wordTrace_append hprefix tailTrace_6017784
  have hstable : (prefixWord ++ tailWord_6017784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017784).length < 2 ^ (prefixWord ++ tailWord_6017784).sum := by decide
  have hdescent : baseEnd_6017784 < baseStart_6017784 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017811 : List Nat := [1, 1, 1, 2, 1, 3, 6, 2, 1, 2, 3]
def baseStart_6017811 : Nat := 118140960795 + 6017811 * 2 ^ 59
def prefixEnd_6017811 : Nat := 4983230072969 + 3 ^ 40 * 6017811 * 2
def baseEnd_6017811 : Nat := 3090029530913860020487097

theorem tailTrace_6017811 : CollatzResearch.WordTrace tailWord_6017811 prefixEnd_6017811 3090029530913860020487097 := by
  unfold tailWord_6017811
  simp only [CollatzResearch.WordTrace]
  refine ⟨219487598801505982139733287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146325065867670654759822191 219487598801505982139733287)
  ·
    refine ⟨329231398202258973209599931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219487598801505982139733287 329231398202258973209599931)
    ·
      refine ⟨493847097303388459814399897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329231398202258973209599931 493847097303388459814399897)
      ·
        refine ⟨370385322977541344860799923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 493847097303388459814399897 370385322977541344860799923)
        ·
          refine ⟨555577984466312017291199885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 370385322977541344860799923 555577984466312017291199885)
          ·
            refine ⟨208341744174867006484199957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 555577984466312017291199885 208341744174867006484199957)
            ·
              refine ⟨9766019258196890928946873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 208341744174867006484199957 9766019258196890928946873)
              ·
                refine ⟨7324514443647668196710155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9766019258196890928946873 7324514443647668196710155)
                ·
                  refine ⟨10986771665471502295065233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7324514443647668196710155 10986771665471502295065233)
                  ·
                    refine ⟨8240078749103626721298925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10986771665471502295065233 8240078749103626721298925)
                    ·
                      refine ⟨3090029530913860020487097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8240078749103626721298925 3090029530913860020487097)
                      ·
                        rfl

theorem cell23_6017811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 2, 1, 2, 3].length) (baseStart_6017811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017811 prefixEnd_6017811 := by exact prefixLift 6017811
  have htrace : WordTrace (prefixWord ++ tailWord_6017811) baseStart_6017811 baseEnd_6017811 := by
    simpa [prefixWord, tailWord_6017811, baseEnd_6017811] using wordTrace_append hprefix tailTrace_6017811
  have hstable : (prefixWord ++ tailWord_6017811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017811).length < 2 ^ (prefixWord ++ tailWord_6017811).sum := by decide
  have hdescent : baseEnd_6017811 < baseStart_6017811 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017827 : List Nat := [1, 1, 1, 4, 2, 1, 1, 2, 1, 9]
def baseStart_6017827 : Nat := 118140960795 + 6017827 * 2 ^ 59
def prefixEnd_6017827 : Nat := 4983230072969 + 3 ^ 40 * 6017827 * 2
def baseEnd_6017827 : Nat := 1030012582201443985962341

theorem tailTrace_6017827 : CollatzResearch.WordTrace tailWord_6017827 prefixEnd_6017827 1030012582201443985962341 := by
  unfold tailWord_6017827
  simp only [CollatzResearch.WordTrace]
  refine ⟨219488182369448016872315735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146325454912965344581543823 219488182369448016872315735)
  ·
    refine ⟨329232273554172025308473603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219488182369448016872315735 329232273554172025308473603)
    ·
      refine ⟨493848410331258037962710405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329232273554172025308473603 493848410331258037962710405)
      ·
        refine ⟨92596576937110882118008201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 493848410331258037962710405 92596576937110882118008201)
        ·
          refine ⟨69447432702833161588506151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92596576937110882118008201 69447432702833161588506151)
          ·
            refine ⟨104171149054249742382759227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69447432702833161588506151 104171149054249742382759227)
            ·
              refine ⟨156256723581374613574138841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104171149054249742382759227 156256723581374613574138841)
              ·
                refine ⟨117192542686030960180604131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156256723581374613574138841 117192542686030960180604131)
                ·
                  refine ⟨175788814029046440270906197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117192542686030960180604131 175788814029046440270906197)
                  ·
                    refine ⟨1030012582201443985962341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 175788814029046440270906197 1030012582201443985962341)
                    ·
                      rfl

theorem cell23_6017827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 9].length) (baseStart_6017827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017827 prefixEnd_6017827 := by exact prefixLift 6017827
  have htrace : WordTrace (prefixWord ++ tailWord_6017827) baseStart_6017827 baseEnd_6017827 := by
    simpa [prefixWord, tailWord_6017827, baseEnd_6017827] using wordTrace_append hprefix tailTrace_6017827
  have hstable : (prefixWord ++ tailWord_6017827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017827).length < 2 ^ (prefixWord ++ tailWord_6017827).sum := by decide
  have hdescent : baseEnd_6017827 < baseStart_6017827 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017841 : List Nat := [1, 2, 2, 3, 2, 1, 1, 3, 4, 1, 3]
def baseStart_6017841 : Nat := 118140960795 + 6017841 * 2 ^ 59
def prefixEnd_6017841 : Nat := 4983230072969 + 3 ^ 40 * 6017841 * 2
def baseEnd_6017841 : Nat := 3090044935333494903111959

theorem tailTrace_6017841 : CollatzResearch.WordTrace tailWord_6017841 prefixEnd_6017841 3090044935333494903111959 := by
  unfold tailWord_6017841
  simp only [CollatzResearch.WordTrace]
  refine ⟨219488692991397297263325377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146325795327598198175550251 219488692991397297263325377)
  ·
    refine ⟨164616519743547972947494033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219488692991397297263325377 164616519743547972947494033)
    ·
      refine ⟨123462389807660979710620525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164616519743547972947494033 123462389807660979710620525)
      ·
        refine ⟨46298396177872867391482697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123462389807660979710620525 46298396177872867391482697)
        ·
          refine ⟨34723797133404650543612023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46298396177872867391482697 34723797133404650543612023)
          ·
            refine ⟨52085695700106975815418035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34723797133404650543612023 52085695700106975815418035)
            ·
              refine ⟨78128543550160463723127053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52085695700106975815418035 78128543550160463723127053)
              ·
                refine ⟨29298203831310173896172645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78128543550160463723127053 29298203831310173896172645)
                ·
                  refine ⟨5493413218370657605532371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29298203831310173896172645 5493413218370657605532371)
                  ·
                    refine ⟨8240119827555986408298557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5493413218370657605532371 8240119827555986408298557)
                    ·
                      refine ⟨3090044935333494903111959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8240119827555986408298557 3090044935333494903111959)
                      ·
                        rfl

theorem cell23_6017841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_6017841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017841 prefixEnd_6017841 := by exact prefixLift 6017841
  have htrace : WordTrace (prefixWord ++ tailWord_6017841) baseStart_6017841 baseEnd_6017841 := by
    simpa [prefixWord, tailWord_6017841, baseEnd_6017841] using wordTrace_append hprefix tailTrace_6017841
  have hstable : (prefixWord ++ tailWord_6017841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017841).length < 2 ^ (prefixWord ++ tailWord_6017841).sum := by decide
  have hdescent : baseEnd_6017841 < baseStart_6017841 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017842 : List Nat := [3, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2]
def baseStart_6017842 : Nat := 118140960795 + 6017842 * 2 ^ 59
def prefixEnd_6017842 : Nat := 4983230072969 + 3 ^ 40 * 6017842 * 2
def baseEnd_6017842 : Nat := 3090045448814149399199455

theorem tailTrace_6017842 : CollatzResearch.WordTrace tailWord_6017842 prefixEnd_6017842 3090045448814149399199455 := by
  unfold tailWord_6017842
  simp only [CollatzResearch.WordTrace]
  refine ⟨54872182366098418608527945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146325819642929116289407853 54872182366098418608527945)
  ·
    refine ⟨41154136774573813956395959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54872182366098418608527945 41154136774573813956395959)
    ·
      refine ⟨61731205161860720934593939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41154136774573813956395959 61731205161860720934593939)
      ·
        refine ⟨92596807742791081401890909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61731205161860720934593939 92596807742791081401890909)
        ·
          refine ⟨34723802903546655525709091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92596807742791081401890909 34723802903546655525709091)
          ·
            refine ⟨52085704355319983288563637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34723802903546655525709091 52085704355319983288563637)
            ·
              refine ⟨4883034783311248433302841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52085704355319983288563637 4883034783311248433302841)
              ·
                refine ⟨3662276087483436324977131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4883034783311248433302841 3662276087483436324977131)
                ·
                  refine ⟨5493414131225154487465697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3662276087483436324977131 5493414131225154487465697)
                  ·
                    refine ⟨4120060598418865865599273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5493414131225154487465697 4120060598418865865599273)
                    ·
                      refine ⟨3090045448814149399199455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4120060598418865865599273 3090045448814149399199455)
                      ·
                        rfl

theorem cell23_6017842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2].length) (baseStart_6017842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017842 prefixEnd_6017842 := by exact prefixLift 6017842
  have htrace : WordTrace (prefixWord ++ tailWord_6017842) baseStart_6017842 baseEnd_6017842 := by
    simpa [prefixWord, tailWord_6017842, baseEnd_6017842] using wordTrace_append hprefix tailTrace_6017842
  have hstable : (prefixWord ++ tailWord_6017842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017842).length < 2 ^ (prefixWord ++ tailWord_6017842).sum := by decide
  have hdescent : baseEnd_6017842 < baseStart_6017842 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017867 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 9]
def baseStart_6017867 : Nat := 118140960795 + 6017867 * 2 ^ 59
def prefixEnd_6017867 : Nat := 4983230072969 + 3 ^ 40 * 6017867 * 2
def baseEnd_6017867 : Nat := 3090058285830511801386839

theorem tailTrace_6017867 : CollatzResearch.WordTrace tailWord_6017867 prefixEnd_6017867 3090058285830511801386839 := by
  unfold tailWord_6017867
  simp only [CollatzResearch.WordTrace]
  refine ⟨219489641289303103703771855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146326427526202069135847903 219489641289303103703771855)
  ·
    refine ⟨329234461933954655555657783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219489641289303103703771855 329234461933954655555657783)
    ·
      refine ⟨493851692900931983333486675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329234461933954655555657783 493851692900931983333486675)
      ·
        refine ⟨740777539351397975000230013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 493851692900931983333486675 740777539351397975000230013)
        ·
          refine ⟨277791577256774240625086255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 740777539351397975000230013 277791577256774240625086255)
          ·
            refine ⟨416687365885161360937629383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277791577256774240625086255 416687365885161360937629383)
            ·
              refine ⟨625031048827742041406444075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 416687365885161360937629383 625031048827742041406444075)
              ·
                refine ⟨937546573241613062109666113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 625031048827742041406444075 937546573241613062109666113)
                ·
                  refine ⟨703159929931209796582249585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 937546573241613062109666113 703159929931209796582249585)
                  ·
                    refine ⟨527369947448407347436687189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 703159929931209796582249585 527369947448407347436687189)
                    ·
                      refine ⟨3090058285830511801386839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 527369947448407347436687189 3090058285830511801386839)
                      ·
                        rfl

theorem cell23_6017867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 9].length) (baseStart_6017867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017867 prefixEnd_6017867 := by exact prefixLift 6017867
  have htrace : WordTrace (prefixWord ++ tailWord_6017867) baseStart_6017867 baseEnd_6017867 := by
    simpa [prefixWord, tailWord_6017867, baseEnd_6017867] using wordTrace_append hprefix tailTrace_6017867
  have hstable : (prefixWord ++ tailWord_6017867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017867).length < 2 ^ (prefixWord ++ tailWord_6017867).sum := by decide
  have hdescent : baseEnd_6017867 < baseStart_6017867 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017868 : List Nat := [2, 2, 1, 3, 3, 2, 1, 1, 3, 3, 2]
def baseStart_6017868 : Nat := 118140960795 + 6017868 * 2 ^ 59
def prefixEnd_6017868 : Nat := 4983230072969 + 3 ^ 40 * 6017868 * 2
def baseEnd_6017868 : Nat := 3090058799311166297474335

theorem tailTrace_6017868 : CollatzResearch.WordTrace tailWord_6017868 prefixEnd_6017868 3090058799311166297474335 := by
  unfold tailWord_6017868
  simp only [CollatzResearch.WordTrace]
  refine ⟨109744838881149740437279129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146326451841532987249705505 109744838881149740437279129)
  ·
    refine ⟨82308629160862305327959347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109744838881149740437279129 82308629160862305327959347)
    ·
      refine ⟨123462943741293457991939021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82308629160862305327959347 123462943741293457991939021)
      ·
        refine ⟨46298603902985046746977133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123462943741293457991939021 46298603902985046746977133)
        ·
          refine ⟨17361976463619392530116425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46298603902985046746977133 17361976463619392530116425)
          ·
            refine ⟨13021482347714544397587319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17361976463619392530116425 13021482347714544397587319)
            ·
              refine ⟨19532223521571816596380979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13021482347714544397587319 19532223521571816596380979)
              ·
                refine ⟨29298335282357724894571469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19532223521571816596380979 29298335282357724894571469)
                ·
                  refine ⟨10986875730884146835464301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29298335282357724894571469 10986875730884146835464301)
                  ·
                    refine ⟨4120078399081555063299113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10986875730884146835464301 4120078399081555063299113)
                    ·
                      refine ⟨3090058799311166297474335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4120078399081555063299113 3090058799311166297474335)
                      ·
                        rfl

theorem cell23_6017868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 3, 3, 2].length) (baseStart_6017868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017868 prefixEnd_6017868 := by exact prefixLift 6017868
  have htrace : WordTrace (prefixWord ++ tailWord_6017868) baseStart_6017868 baseEnd_6017868 := by
    simpa [prefixWord, tailWord_6017868, baseEnd_6017868] using wordTrace_append hprefix tailTrace_6017868
  have hstable : (prefixWord ++ tailWord_6017868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017868).length < 2 ^ (prefixWord ++ tailWord_6017868).sum := by decide
  have hdescent : baseEnd_6017868 < baseStart_6017868 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017881 : List Nat := [1, 2, 1, 2, 2, 4, 1, 1, 3, 4, 2]
def baseStart_6017881 : Nat := 118140960795 + 6017881 * 2 ^ 59
def prefixEnd_6017881 : Nat := 4983230072969 + 3 ^ 40 * 6017881 * 2
def baseEnd_6017881 : Nat := 3090065474559674746611775

theorem tailTrace_6017881 : CollatzResearch.WordTrace tailWord_6017881 prefixEnd_6017881 3090065474559674746611775 := by
  unfold tailWord_6017881
  simp only [CollatzResearch.WordTrace]
  refine ⟨219490151911252384094781497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146326767940834922729854331 219490151911252384094781497)
  ·
    refine ⟨164617613933439288071086123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219490151911252384094781497 164617613933439288071086123)
    ·
      refine ⟨246926420900158932106629185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164617613933439288071086123 246926420900158932106629185)
      ·
        refine ⟨185194815675119199079971889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246926420900158932106629185 185194815675119199079971889)
        ·
          refine ⟨138896111756339399309978917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185194815675119199079971889 138896111756339399309978917)
          ·
            refine ⟨26043020954313637370621047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 138896111756339399309978917 26043020954313637370621047)
            ·
              refine ⟨39064531431470456055931571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26043020954313637370621047 39064531431470456055931571)
              ·
                refine ⟨58596797147205684083897357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39064531431470456055931571 58596797147205684083897357)
                ·
                  refine ⟨21973798930202131531461509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58596797147205684083897357 21973798930202131531461509)
                  ·
                    refine ⟨4120087299412899662149033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21973798930202131531461509 4120087299412899662149033)
                    ·
                      refine ⟨3090065474559674746611775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4120087299412899662149033 3090065474559674746611775)
                      ·
                        rfl

theorem cell23_6017881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 4, 2].length) (baseStart_6017881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017881 prefixEnd_6017881 := by exact prefixLift 6017881
  have htrace : WordTrace (prefixWord ++ tailWord_6017881) baseStart_6017881 baseEnd_6017881 := by
    simpa [prefixWord, tailWord_6017881, baseEnd_6017881] using wordTrace_append hprefix tailTrace_6017881
  have hstable : (prefixWord ++ tailWord_6017881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017881).length < 2 ^ (prefixWord ++ tailWord_6017881).sum := by decide
  have hdescent : baseEnd_6017881 < baseStart_6017881 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017971 : List Nat := [1, 1, 1, 2, 3, 1, 2, 3, 1, 6, 2]
def baseStart_6017971 : Nat := 118140960795 + 6017971 * 2 ^ 59
def prefixEnd_6017971 : Nat := 4983230072969 + 3 ^ 40 * 6017971 * 2
def baseEnd_6017971 : Nat := 3090111687818579394486361

theorem tailTrace_6017971 : CollatzResearch.WordTrace tailWord_6017971 prefixEnd_6017971 3090111687818579394486361 := by
  unfold tailWord_6017971
  simp only [CollatzResearch.WordTrace]
  refine ⟨219493434480926329465557767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146328956320617552977038511 219493434480926329465557767)
  ·
    refine ⟨329240151721389494198336651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219493434480926329465557767 329240151721389494198336651)
    ·
      refine ⟨493860227582084241297504977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329240151721389494198336651 493860227582084241297504977)
      ·
        refine ⟨370395170686563180973128733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 493860227582084241297504977 370395170686563180973128733)
        ·
          refine ⟨138898189007461192864923275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 370395170686563180973128733 138898189007461192864923275)
          ·
            refine ⟨208347283511191789297384913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138898189007461192864923275 208347283511191789297384913)
            ·
              refine ⟨156260462633393841973038685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208347283511191789297384913 156260462633393841973038685)
              ·
                refine ⟨58597673487522690739889507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156260462633393841973038685 58597673487522690739889507)
                ·
                  refine ⟨87896510231284036109834261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58597673487522690739889507 87896510231284036109834261)
                  ·
                    refine ⟨4120148917091439192648481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 87896510231284036109834261 4120148917091439192648481)
                    ·
                      refine ⟨3090111687818579394486361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4120148917091439192648481 3090111687818579394486361)
                      ·
                        rfl

theorem cell23_6017971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 6, 2].length) (baseStart_6017971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017971 prefixEnd_6017971 := by exact prefixLift 6017971
  have htrace : WordTrace (prefixWord ++ tailWord_6017971) baseStart_6017971 baseEnd_6017971 := by
    simpa [prefixWord, tailWord_6017971, baseEnd_6017971] using wordTrace_append hprefix tailTrace_6017971
  have hstable : (prefixWord ++ tailWord_6017971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017971).length < 2 ^ (prefixWord ++ tailWord_6017971).sum := by decide
  have hdescent : baseEnd_6017971 < baseStart_6017971 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6017991 : List Nat := [1, 1, 4, 1, 1, 2, 4, 1, 1, 4, 3]
def baseStart_6017991 : Nat := 118140960795 + 6017991 * 2 ^ 59
def prefixEnd_6017991 : Nat := 4983230072969 + 3 ^ 40 * 6017991 * 2
def baseEnd_6017991 : Nat := 3090121957431669316236269

theorem tailTrace_6017991 : CollatzResearch.WordTrace tailWord_6017991 prefixEnd_6017991 3090121957431669316236269 := by
  unfold tailWord_6017991
  simp only [CollatzResearch.WordTrace]
  refine ⟨219494163940853872881285827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146329442627235915254190551 219494163940853872881285827)
  ·
    refine ⟨329241245911280809321928741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219494163940853872881285827 329241245911280809321928741)
    ·
      refine ⟨61732733608365151747861639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 329241245911280809321928741 61732733608365151747861639)
      ·
        refine ⟨92599100412547727621792459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61732733608365151747861639 92599100412547727621792459)
        ·
          refine ⟨138898650618821591432688689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92599100412547727621792459 138898650618821591432688689)
          ·
            refine ⟨104173987964116193574516517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138898650618821591432688689 104173987964116193574516517)
            ·
              refine ⟨19532622743271786295221847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104173987964116193574516517 19532622743271786295221847)
              ·
                refine ⟨29298934114907679442832771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19532622743271786295221847 29298934114907679442832771)
                ·
                  refine ⟨43948401172361519164249157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29298934114907679442832771 43948401172361519164249157)
                  ·
                    refine ⟨8240325219817784843296717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43948401172361519164249157 8240325219817784843296717)
                    ·
                      refine ⟨3090121957431669316236269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8240325219817784843296717 3090121957431669316236269)
                      ·
                        rfl

theorem cell23_6017991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 4, 3].length) (baseStart_6017991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6017991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6017991 prefixEnd_6017991 := by exact prefixLift 6017991
  have htrace : WordTrace (prefixWord ++ tailWord_6017991) baseStart_6017991 baseEnd_6017991 := by
    simpa [prefixWord, tailWord_6017991, baseEnd_6017991] using wordTrace_append hprefix tailTrace_6017991
  have hstable : (prefixWord ++ tailWord_6017991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6017991).length < 2 ^ (prefixWord ++ tailWord_6017991).sum := by decide
  have hdescent : baseEnd_6017991 < baseStart_6017991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6017991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018008 : List Nat := [2, 1, 2, 2, 2, 4, 1, 2, 2, 2, 3]
def baseStart_6018008 : Nat := 118140960795 + 6018008 * 2 ^ 59
def prefixEnd_6018008 : Nat := 4983230072969 + 3 ^ 40 * 6018008 * 2
def baseEnd_6018008 : Nat := 3090130686602795749723691

theorem tailTrace_6018008 : CollatzResearch.WordTrace tailWord_6018008 prefixEnd_6018008 3090130686602795749723691 := by
  unfold tailWord_6018008
  simp only [CollatzResearch.WordTrace]
  refine ⟨109747391990896142392327339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146329855987861523189769785 109747391990896142392327339)
  ·
    refine ⟨164621087986344213588491009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109747391990896142392327339 164621087986344213588491009)
    ·
      refine ⟨123465815989758160191368257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164621087986344213588491009 123465815989758160191368257)
      ·
        refine ⟨92599361992318620143526193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123465815989758160191368257 92599361992318620143526193)
        ·
          refine ⟨69449521494238965107644645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92599361992318620143526193 69449521494238965107644645)
          ·
            refine ⟨13021785280169805957683371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69449521494238965107644645 13021785280169805957683371)
            ·
              refine ⟨19532677920254708936525057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13021785280169805957683371 19532677920254708936525057)
              ·
                refine ⟨14649508440191031702393793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19532677920254708936525057 14649508440191031702393793)
                ·
                  refine ⟨10987131330143273776795345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14649508440191031702393793 10987131330143273776795345)
                  ·
                    refine ⟨8240348497607455332596509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10987131330143273776795345 8240348497607455332596509)
                    ·
                      refine ⟨3090130686602795749723691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8240348497607455332596509 3090130686602795749723691)
                      ·
                        rfl

theorem cell23_6018008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 2, 2, 3].length) (baseStart_6018008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018008 prefixEnd_6018008 := by exact prefixLift 6018008
  have htrace : WordTrace (prefixWord ++ tailWord_6018008) baseStart_6018008 baseEnd_6018008 := by
    simpa [prefixWord, tailWord_6018008, baseEnd_6018008] using wordTrace_append hprefix tailTrace_6018008
  have hstable : (prefixWord ++ tailWord_6018008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018008).length < 2 ^ (prefixWord ++ tailWord_6018008).sum := by decide
  have hdescent : baseEnd_6018008 < baseStart_6018008 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018015 : List Nat := [1, 1, 2, 3, 5, 2, 1, 1, 3, 4]
def baseStart_6018015 : Nat := 118140960795 + 6018015 * 2 ^ 59
def prefixEnd_6018015 : Nat := 4983230072969 + 3 ^ 40 * 6018015 * 2
def baseEnd_6018015 : Nat := 1030044760322459074112053

theorem tailTrace_6018015 : CollatzResearch.WordTrace tailWord_6018015 prefixEnd_6018015 1030044760322459074112053 := by
  unfold tailWord_6018015
  simp only [CollatzResearch.WordTrace]
  refine ⟨219495039292766924980159499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146330026195177949986772999 219495039292766924980159499)
  ·
    refine ⟨329242558939150387470239249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219495039292766924980159499 329242558939150387470239249)
    ·
      refine ⟨246931919204362790602679437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329242558939150387470239249 246931919204362790602679437)
      ·
        refine ⟨92599469701636046476004789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246931919204362790602679437 92599469701636046476004789)
        ·
          refine ⟨8681200284528379357125449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92599469701636046476004789 8681200284528379357125449)
          ·
            refine ⟨6510900213396284517844087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8681200284528379357125449 6510900213396284517844087)
            ·
              refine ⟨9766350320094426776766131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6510900213396284517844087 9766350320094426776766131)
              ·
                refine ⟨14649525480141640165149197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9766350320094426776766131 14649525480141640165149197)
                ·
                  refine ⟨5493572055053115061930949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14649525480141640165149197 5493572055053115061930949)
                  ·
                    refine ⟨1030044760322459074112053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5493572055053115061930949 1030044760322459074112053)
                    ·
                      rfl

theorem cell23_6018015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 3, 4].length) (baseStart_6018015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018015 prefixEnd_6018015 := by exact prefixLift 6018015
  have htrace : WordTrace (prefixWord ++ tailWord_6018015) baseStart_6018015 baseEnd_6018015 := by
    simpa [prefixWord, tailWord_6018015, baseEnd_6018015] using wordTrace_append hprefix tailTrace_6018015
  have hstable : (prefixWord ++ tailWord_6018015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018015).length < 2 ^ (prefixWord ++ tailWord_6018015).sum := by decide
  have hdescent : baseEnd_6018015 < baseStart_6018015 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018041 : List Nat := [1, 2, 1, 3, 1, 3, 3, 1, 3, 5]
def baseStart_6018041 : Nat := 118140960795 + 6018041 * 2 ^ 59
def prefixEnd_6018041 : Nat := 4983230072969 + 3 ^ 40 * 6018041 * 2
def baseEnd_6018041 : Nat := 1030049210488131373537013

theorem tailTrace_6018041 : CollatzResearch.WordTrace tailWord_6018041 prefixEnd_6018041 1030049210488131373537013 := by
  unfold tailWord_6018041
  simp only [CollatzResearch.WordTrace]
  refine ⟨219495987590672731420605977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146330658393781820947070651 219495987590672731420605977)
  ·
    refine ⟨164621990693004548565454483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219495987590672731420605977 164621990693004548565454483)
    ·
      refine ⟨246932986039506822848181725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164621990693004548565454483 246932986039506822848181725)
      ·
        refine ⟨92599869764815058568068147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246932986039506822848181725 92599869764815058568068147)
        ·
          refine ⟨138899804647222587852102221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92599869764815058568068147 138899804647222587852102221)
          ·
            refine ⟨52087426742708470444538333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138899804647222587852102221 52087426742708470444538333)
            ·
              refine ⟨19532785028515676416701875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52087426742708470444538333 19532785028515676416701875)
              ·
                refine ⟨29299177542773514625052813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19532785028515676416701875 29299177542773514625052813)
                ·
                  refine ⟨10987191578540067984394805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29299177542773514625052813 10987191578540067984394805)
                  ·
                    refine ⟨1030049210488131373537013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10987191578540067984394805 1030049210488131373537013)
                    ·
                      rfl

theorem cell23_6018041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 3, 5].length) (baseStart_6018041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018041 prefixEnd_6018041 := by exact prefixLift 6018041
  have htrace : WordTrace (prefixWord ++ tailWord_6018041) baseStart_6018041 baseEnd_6018041 := by
    simpa [prefixWord, tailWord_6018041, baseEnd_6018041] using wordTrace_append hprefix tailTrace_6018041
  have hstable : (prefixWord ++ tailWord_6018041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018041).length < 2 ^ (prefixWord ++ tailWord_6018041).sum := by decide
  have hdescent : baseEnd_6018041 < baseStart_6018041 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018066 : List Nat := [3, 2, 5, 1, 1, 1, 1, 4, 1, 4]
def baseStart_6018066 : Nat := 118140960795 + 6018066 * 2 ^ 59
def prefixEnd_6018066 : Nat := 4983230072969 + 3 ^ 40 * 6018066 * 2
def baseEnd_6018066 : Nat := 1030053489493585507599475

theorem tailTrace_6018066 : CollatzResearch.WordTrace tailWord_6018066 prefixEnd_6018066 1030053489493585507599475 := by
  unfold tailWord_6018066
  simp only [CollatzResearch.WordTrace]
  refine ⟨54874224853895540172566513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146331266277054773793510701 54874224853895540172566513)
  ·
    refine ⟨41155668640421655129424885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54874224853895540172566513 41155668640421655129424885)
    ·
      refine ⟨3858343935039530168383583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41155668640421655129424885 3858343935039530168383583)
      ·
        refine ⟨5787515902559295252575375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3858343935039530168383583 5787515902559295252575375)
        ·
          refine ⟨8681273853838942878863063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5787515902559295252575375 8681273853838942878863063)
          ·
            refine ⟨13021910780758414318294595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8681273853838942878863063 13021910780758414318294595)
            ·
              refine ⟨19532866171137621477441893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13021910780758414318294595 19532866171137621477441893)
              ·
                refine ⟨3662412407088304027020355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19532866171137621477441893 3662412407088304027020355)
                ·
                  refine ⟨5493618610632456040530533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3662412407088304027020355 5493618610632456040530533)
                  ·
                    refine ⟨1030053489493585507599475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5493618610632456040530533 1030053489493585507599475)
                    ·
                      rfl

theorem cell23_6018066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_6018066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018066 prefixEnd_6018066 := by exact prefixLift 6018066
  have htrace : WordTrace (prefixWord ++ tailWord_6018066) baseStart_6018066 baseEnd_6018066 := by
    simpa [prefixWord, tailWord_6018066, baseEnd_6018066] using wordTrace_append hprefix tailTrace_6018066
  have hstable : (prefixWord ++ tailWord_6018066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018066).length < 2 ^ (prefixWord ++ tailWord_6018066).sum := by decide
  have hdescent : baseEnd_6018066 < baseStart_6018066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018072 : List Nat := [2, 1, 2, 3, 2, 3, 1, 4, 1, 1, 3]
def baseStart_6018072 : Nat := 118140960795 + 6018072 * 2 ^ 59
def prefixEnd_6018072 : Nat := 4983230072969 + 3 ^ 40 * 6018072 * 2
def baseEnd_6018072 : Nat := 3090163549364683499323397

theorem tailTrace_6018072 : CollatzResearch.WordTrace tailWord_6018072 prefixEnd_6018072 3090163549364683499323397 := by
  unfold tailWord_6018072
  simp only [CollatzResearch.WordTrace]
  refine ⟨109748559126780211857492235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146331412169040282476656313 109748559126780211857492235)
  ·
    refine ⟨164622838690170317786238353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109748559126780211857492235 164622838690170317786238353)
    ·
      refine ⟨123467129017627738339678765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164622838690170317786238353 123467129017627738339678765)
      ·
        refine ⟨46300173381610401877379537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123467129017627738339678765 46300173381610401877379537)
        ·
          refine ⟨34725130036207801408034653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46300173381610401877379537 34725130036207801408034653)
          ·
            refine ⟨13021923763577925528012995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34725130036207801408034653 13021923763577925528012995)
            ·
              refine ⟨19532885645366888292019493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13021923763577925528012995 19532885645366888292019493)
              ·
                refine ⟨3662416058506291554753655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19532885645366888292019493 3662416058506291554753655)
                ·
                  refine ⟨5493624087759437332130483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3662416058506291554753655 5493624087759437332130483)
                  ·
                    refine ⟨8240436131639155998195725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5493624087759437332130483 8240436131639155998195725)
                    ·
                      refine ⟨3090163549364683499323397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8240436131639155998195725 3090163549364683499323397)
                      ·
                        rfl

theorem cell23_6018072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 4, 1, 1, 3].length) (baseStart_6018072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018072 prefixEnd_6018072 := by exact prefixLift 6018072
  have htrace : WordTrace (prefixWord ++ tailWord_6018072) baseStart_6018072 baseEnd_6018072 := by
    simpa [prefixWord, tailWord_6018072, baseEnd_6018072] using wordTrace_append hprefix tailTrace_6018072
  have hstable : (prefixWord ++ tailWord_6018072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018072).length < 2 ^ (prefixWord ++ tailWord_6018072).sum := by decide
  have hdescent : baseEnd_6018072 < baseStart_6018072 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018098 : List Nat := [3, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3]
def baseStart_6018098 : Nat := 118140960795 + 6018098 * 2 ^ 59
def prefixEnd_6018098 : Nat := 4983230072969 + 3 ^ 40 * 6018098 * 2
def baseEnd_6018098 : Nat := 3090176899861700397598277

theorem tailTrace_6018098 : CollatzResearch.WordTrace tailWord_6018098 prefixEnd_6018098 3090176899861700397598277 := by
  unfold tailWord_6018098
  simp only [CollatzResearch.WordTrace]
  refine ⟨54874516637866557538857737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146332044367644153436953965 54874516637866557538857737)
  ·
    refine ⟨41155887478399918154143303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54874516637866557538857737 41155887478399918154143303)
    ·
      refine ⟨61733831217599877231214955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41155887478399918154143303 61733831217599877231214955)
      ·
        refine ⟨92600746826399815846822433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61733831217599877231214955 92600746826399815846822433)
        ·
          refine ⟨69450560119799861885116825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92600746826399815846822433 69450560119799861885116825)
          ·
            refine ⟨52087920089849896413837619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69450560119799861885116825 52087920089849896413837619)
            ·
              refine ⟨78131880134774844620756429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52087920089849896413837619 78131880134774844620756429)
              ·
                refine ⟨29299455050540566732783661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78131880134774844620756429 29299455050540566732783661)
                ·
                  refine ⟨10987295643952712524793873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29299455050540566732783661 10987295643952712524793873)
                  ·
                    refine ⟨8240471732964534393595405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10987295643952712524793873 8240471732964534393595405)
                    ·
                      refine ⟨3090176899861700397598277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8240471732964534393595405 3090176899861700397598277)
                      ·
                        rfl

theorem cell23_6018098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3].length) (baseStart_6018098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018098 prefixEnd_6018098 := by exact prefixLift 6018098
  have htrace : WordTrace (prefixWord ++ tailWord_6018098) baseStart_6018098 baseEnd_6018098 := by
    simpa [prefixWord, tailWord_6018098, baseEnd_6018098] using wordTrace_append hprefix tailTrace_6018098
  have hstable : (prefixWord ++ tailWord_6018098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018098).length < 2 ^ (prefixWord ++ tailWord_6018098).sum := by decide
  have hdescent : baseEnd_6018098 < baseStart_6018098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018108 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 4]
def baseStart_6018108 : Nat := 118140960795 + 6018108 * 2 ^ 59
def prefixEnd_6018108 : Nat := 4983230072969 + 3 ^ 40 * 6018108 * 2
def baseEnd_6018108 : Nat := 3090182034668245358473231

theorem tailTrace_6018108 : CollatzResearch.WordTrace tailWord_6018108 prefixEnd_6018108 3090182034668245358473231 := by
  unfold tailWord_6018108
  simp only [CollatzResearch.WordTrace]
  refine ⟨109749215640715000931647489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146332287520953334575529985 109749215640715000931647489)
  ·
    refine ⟨82311911730536250698735617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109749215640715000931647489 82311911730536250698735617)
    ·
      refine ⟨61733933797902188024051713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82311911730536250698735617 61733933797902188024051713)
      ·
        refine ⟨46300450348426641018038785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61733933797902188024051713 46300450348426641018038785)
        ·
          refine ⟨34725337761319980763529089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46300450348426641018038785 34725337761319980763529089)
          ·
            refine ⟨26044003320989985572646817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34725337761319980763529089 26044003320989985572646817)
            ·
              refine ⟨19533002490742489179485113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26044003320989985572646817 19533002490742489179485113)
              ·
                refine ⟨14649751868056866884613835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19533002490742489179485113 14649751868056866884613835)
                ·
                  refine ⟨21974627802085300326920753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14649751868056866884613835 21974627802085300326920753)
                  ·
                    refine ⟨16480970851563975245190565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21974627802085300326920753 16480970851563975245190565)
                    ·
                      refine ⟨3090182034668245358473231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16480970851563975245190565 3090182034668245358473231)
                      ·
                        rfl

theorem cell23_6018108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_6018108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018108 prefixEnd_6018108 := by exact prefixLift 6018108
  have htrace : WordTrace (prefixWord ++ tailWord_6018108) baseStart_6018108 baseEnd_6018108 := by
    simpa [prefixWord, tailWord_6018108, baseEnd_6018108] using wordTrace_append hprefix tailTrace_6018108
  have hstable : (prefixWord ++ tailWord_6018108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018108).length < 2 ^ (prefixWord ++ tailWord_6018108).sum := by decide
  have hdescent : baseEnd_6018108 < baseStart_6018108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018138 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 2, 7, 2]
def baseStart_6018138 : Nat := 118140960795 + 6018138 * 2 ^ 59
def prefixEnd_6018138 : Nat := 4983230072969 + 3 ^ 40 * 6018138 * 2
def baseEnd_6018138 : Nat := 3090197439087880241098093

theorem tailTrace_6018138 : CollatzResearch.WordTrace tailWord_6018138 prefixEnd_6018138 3090197439087880241098093 := by
  unfold tailWord_6018138
  simp only [CollatzResearch.WordTrace]
  refine ⟨54874881367830329246721767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146333016980880877991258045 54874881367830329246721767)
  ·
    refine ⟨82312322051745493870082651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54874881367830329246721767 82312322051745493870082651)
    ·
      refine ⟨123468483077618240805123977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82312322051745493870082651 123468483077618240805123977)
      ·
        refine ⟨92601362308213680603842983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123468483077618240805123977 92601362308213680603842983)
        ·
          refine ⟨138902043462320520905764475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92601362308213680603842983 138902043462320520905764475)
          ·
            refine ⟨208353065193480781358646713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138902043462320520905764475 208353065193480781358646713)
            ·
              refine ⟨156264798895110586018985035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208353065193480781358646713 156264798895110586018985035)
              ·
                refine ⟨234397198342665879028477553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156264798895110586018985035 234397198342665879028477553)
                ·
                  refine ⟨175797898756999409271358165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 234397198342665879028477553 175797898756999409271358165)
                  ·
                    refine ⟨4120263252117173654797457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 175797898756999409271358165 4120263252117173654797457)
                    ·
                      refine ⟨3090197439087880241098093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4120263252117173654797457 3090197439087880241098093)
                      ·
                        rfl

theorem cell23_6018138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 2, 7, 2].length) (baseStart_6018138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018138 prefixEnd_6018138 := by exact prefixLift 6018138
  have htrace : WordTrace (prefixWord ++ tailWord_6018138) baseStart_6018138 baseEnd_6018138 := by
    simpa [prefixWord, tailWord_6018138, baseEnd_6018138] using wordTrace_append hprefix tailTrace_6018138
  have hstable : (prefixWord ++ tailWord_6018138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018138).length < 2 ^ (prefixWord ++ tailWord_6018138).sum := by decide
  have hdescent : baseEnd_6018138 < baseStart_6018138 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018142 : List Nat := [4, 4, 1, 1, 1, 2, 1, 1, 1, 1, 6]
def baseStart_6018142 : Nat := 118140960795 + 6018142 * 2 ^ 59
def prefixEnd_6018142 : Nat := 4983230072969 + 3 ^ 40 * 6018142 * 2
def baseEnd_6018142 : Nat := 3090199493010498225448075

theorem tailTrace_6018142 : CollatzResearch.WordTrace tailWord_6018142 prefixEnd_6018142 3090199493010498225448075 := by
  unfold tailWord_6018142
  simp only [CollatzResearch.WordTrace]
  refine ⟨27437458920413353208754085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146333114242204550446688453 27437458920413353208754085)
  ·
    refine ⟨5144523547577503726641391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27437458920413353208754085 5144523547577503726641391)
    ·
      refine ⟨7716785321366255589962087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5144523547577503726641391 7716785321366255589962087)
      ·
        refine ⟨11575177982049383384943131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7716785321366255589962087 11575177982049383384943131)
        ·
          refine ⟨17362766973074075077414697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11575177982049383384943131 17362766973074075077414697)
          ·
            refine ⟨13022075229805556308061023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17362766973074075077414697 13022075229805556308061023)
            ·
              refine ⟨19533112844708334462091535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13022075229805556308061023 19533112844708334462091535)
              ·
                refine ⟨29299669267062501693137303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19533112844708334462091535 29299669267062501693137303)
                ·
                  refine ⟨43949503900593752539705955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29299669267062501693137303 43949503900593752539705955)
                  ·
                    refine ⟨65924255850890628809558933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43949503900593752539705955 65924255850890628809558933)
                    ·
                      refine ⟨3090199493010498225448075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65924255850890628809558933 3090199493010498225448075)
                      ·
                        rfl

theorem cell23_6018142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_6018142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018142 prefixEnd_6018142 := by exact prefixLift 6018142
  have htrace : WordTrace (prefixWord ++ tailWord_6018142) baseStart_6018142 baseEnd_6018142 := by
    simpa [prefixWord, tailWord_6018142, baseEnd_6018142] using wordTrace_append hprefix tailTrace_6018142
  have hstable : (prefixWord ++ tailWord_6018142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018142).length < 2 ^ (prefixWord ++ tailWord_6018142).sum := by decide
  have hdescent : baseEnd_6018142 < baseStart_6018142 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018145 : List Nat := [1, 2, 3, 1, 1, 2, 2, 5, 2, 1, 3]
def baseStart_6018145 : Nat := 118140960795 + 6018145 * 2 ^ 59
def prefixEnd_6018145 : Nat := 4983230072969 + 3 ^ 40 * 6018145 * 2
def baseEnd_6018145 : Nat := 3090201033452461713710561

theorem tailTrace_6018145 : CollatzResearch.WordTrace tailWord_6018145 prefixEnd_6018145 3090201033452461713710561 := by
  unfold tailWord_6018145
  simp only [CollatzResearch.WordTrace]
  refine ⟨219499780782295957182391889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146333187188197304788261259 219499780782295957182391889)
  ·
    refine ⟨164624835586721967886793917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219499780782295957182391889 164624835586721967886793917)
    ·
      refine ⟨61734313345020737957547719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164624835586721967886793917 61734313345020737957547719)
      ·
        refine ⟨92601470017531106936321579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61734313345020737957547719 92601470017531106936321579)
        ·
          refine ⟨138902205026296660404482369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92601470017531106936321579 138902205026296660404482369)
          ·
            refine ⟨104176653769722495303361777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138902205026296660404482369 104176653769722495303361777)
            ·
              refine ⟨78132490327291871477521333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104176653769722495303361777 78132490327291871477521333)
              ·
                refine ⟨7324920968183612951017625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78132490327291871477521333 7324920968183612951017625)
                ·
                  refine ⟨5493690726137709713263219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7324920968183612951017625 5493690726137709713263219)
                  ·
                    refine ⟨8240536089206564569894829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5493690726137709713263219 8240536089206564569894829)
                    ·
                      refine ⟨3090201033452461713710561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8240536089206564569894829 3090201033452461713710561)
                      ·
                        rfl

theorem cell23_6018145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 5, 2, 1, 3].length) (baseStart_6018145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018145 prefixEnd_6018145 := by exact prefixLift 6018145
  have htrace : WordTrace (prefixWord ++ tailWord_6018145) baseStart_6018145 baseEnd_6018145 := by
    simpa [prefixWord, tailWord_6018145, baseEnd_6018145] using wordTrace_append hprefix tailTrace_6018145
  have hstable : (prefixWord ++ tailWord_6018145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018145).length < 2 ^ (prefixWord ++ tailWord_6018145).sum := by decide
  have hdescent : baseEnd_6018145 < baseStart_6018145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018152 : List Nat := [2, 1, 4, 4, 1, 2, 2, 7]
def baseStart_6018152 : Nat := 118140960795 + 6018152 * 2 ^ 59
def prefixEnd_6018152 : Nat := 4983230072969 + 3 ^ 40 * 6018152 * 2
def baseEnd_6018152 : Nat := 114452023252483080974927

theorem tailTrace_6018152 : CollatzResearch.WordTrace tailWord_6018152 prefixEnd_6018152 114452023252483080974927 := by
  unfold tailWord_6018152
  simp only [CollatzResearch.WordTrace]
  refine ⟨109750018046635298688948355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146333357395513731585264473 109750018046635298688948355)
  ·
    refine ⟨164625027069952948033422533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109750018046635298688948355 164625027069952948033422533)
    ·
      refine ⟨30867192575616177756266725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164625027069952948033422533 30867192575616177756266725)
      ·
        refine ⟨5787598607928033329300011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30867192575616177756266725 5787598607928033329300011)
        ·
          refine ⟨8681397911892049993950017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5787598607928033329300011 8681397911892049993950017)
          ·
            refine ⟨6511048433919037495462513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8681397911892049993950017 6511048433919037495462513)
            ·
              refine ⟨4883286325439278121596885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6511048433919037495462513 4883286325439278121596885)
              ·
                refine ⟨114452023252483080974927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4883286325439278121596885 114452023252483080974927)
                ·
                  rfl

theorem cell23_6018152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 7].length) (baseStart_6018152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018152 prefixEnd_6018152 := by exact prefixLift 6018152
  have htrace : WordTrace (prefixWord ++ tailWord_6018152) baseStart_6018152 baseEnd_6018152 := by
    simpa [prefixWord, tailWord_6018152, baseEnd_6018152] using wordTrace_append hprefix tailTrace_6018152
  have hstable : (prefixWord ++ tailWord_6018152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018152).length < 2 ^ (prefixWord ++ tailWord_6018152).sum := by decide
  have hdescent : baseEnd_6018152 < baseStart_6018152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018158 : List Nat := [4, 1, 2, 2, 1, 2, 1, 1, 2, 2, 5]
def baseStart_6018158 : Nat := 118140960795 + 6018158 * 2 ^ 59
def prefixEnd_6018158 : Nat := 4983230072969 + 3 ^ 40 * 6018158 * 2
def baseEnd_6018158 : Nat := 3090207708700970162848001

theorem tailTrace_6018158 : CollatzResearch.WordTrace tailWord_6018158 prefixEnd_6018158 3090207708700970162848001 := by
  unfold tailWord_6018158
  simp only [CollatzResearch.WordTrace]
  refine ⟨27437531866406107550326891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146333503287499240268410085 27437531866406107550326891)
  ·
    refine ⟨41156297799609161325490337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27437531866406107550326891 41156297799609161325490337)
    ·
      refine ⟨30867223349706870994117753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41156297799609161325490337 30867223349706870994117753)
      ·
        refine ⟨23150417512280153245588315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30867223349706870994117753 23150417512280153245588315)
        ·
          refine ⟨34725626268420229868382473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23150417512280153245588315 34725626268420229868382473)
          ·
            refine ⟨26044219701315172401286855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34725626268420229868382473 26044219701315172401286855)
            ·
              refine ⟨39066329551972758601930283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26044219701315172401286855 39066329551972758601930283)
              ·
                refine ⟨58599494327959137902895425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39066329551972758601930283 58599494327959137902895425)
                ·
                  refine ⟨43949620745969353427171569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58599494327959137902895425 43949620745969353427171569)
                  ·
                    refine ⟨32962215559477015070378677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43949620745969353427171569 32962215559477015070378677)
                    ·
                      refine ⟨3090207708700970162848001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32962215559477015070378677 3090207708700970162848001)
                      ·
                        rfl

theorem cell23_6018158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_6018158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018158 prefixEnd_6018158 := by exact prefixLift 6018158
  have htrace : WordTrace (prefixWord ++ tailWord_6018158) baseStart_6018158 baseEnd_6018158 := by
    simpa [prefixWord, tailWord_6018158, baseEnd_6018158] using wordTrace_append hprefix tailTrace_6018158
  have hstable : (prefixWord ++ tailWord_6018158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018158).length < 2 ^ (prefixWord ++ tailWord_6018158).sum := by decide
  have hdescent : baseEnd_6018158 < baseStart_6018158 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018161 : List Nat := [1, 2, 2, 2, 1, 1, 2, 2, 4, 6]
def baseStart_6018161 : Nat := 118140960795 + 6018161 * 2 ^ 59
def prefixEnd_6018161 : Nat := 4983230072969 + 3 ^ 40 * 6018161 * 2
def baseEnd_6018161 : Nat := 1030069749714311217036829

theorem tailTrace_6018161 : CollatzResearch.WordTrace tailWord_6018161 prefixEnd_6018161 1030069749714311217036829 := by
  unfold tailWord_6018161
  simp only [CollatzResearch.WordTrace]
  refine ⟨219500364350237991914974337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146333576233491994609982891 219500364350237991914974337)
  ·
    refine ⟨164625273262678493936230753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219500364350237991914974337 164625273262678493936230753)
    ·
      refine ⟨123468954947008870452173065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164625273262678493936230753 123468954947008870452173065)
      ·
        refine ⟨92601716210256652839129799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123468954947008870452173065 92601716210256652839129799)
        ·
          refine ⟨138902574315384979258694699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92601716210256652839129799 138902574315384979258694699)
          ·
            refine ⟨208353861473077468888042049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138902574315384979258694699 208353861473077468888042049)
            ·
              refine ⟨156265396104808101666031537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208353861473077468888042049 156265396104808101666031537)
              ·
                refine ⟨117199047078606076249523653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156265396104808101666031537 117199047078606076249523653)
                ·
                  refine ⟨21974821327238639296785685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 117199047078606076249523653 21974821327238639296785685)
                  ·
                    refine ⟨1030069749714311217036829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21974821327238639296785685 1030069749714311217036829)
                    ·
                      rfl

theorem cell23_6018161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 6].length) (baseStart_6018161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018161 prefixEnd_6018161 := by exact prefixLift 6018161
  have htrace : WordTrace (prefixWord ++ tailWord_6018161) baseStart_6018161 baseEnd_6018161 := by
    simpa [prefixWord, tailWord_6018161, baseEnd_6018161] using wordTrace_append hprefix tailTrace_6018161
  have hstable : (prefixWord ++ tailWord_6018161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018161).length < 2 ^ (prefixWord ++ tailWord_6018161).sum := by decide
  have hdescent : baseEnd_6018161 < baseStart_6018161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018206 : List Nat := [4, 3, 1, 1, 2, 3, 1, 2, 1, 3, 2]
def baseStart_6018206 : Nat := 118140960795 + 6018206 * 2 ^ 59
def prefixEnd_6018206 : Nat := 4983230072969 + 3 ^ 40 * 6018206 * 2
def baseEnd_6018206 : Nat := 3090232355772385975047781

theorem tailTrace_6018206 : CollatzResearch.WordTrace tailWord_6018206 prefixEnd_6018206 3090232355772385975047781 := by
  unfold tailWord_6018206
  simp only [CollatzResearch.WordTrace]
  refine ⟨27437750704384370575045309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146334670423383309733574981 27437750704384370575045309)
  ·
    refine ⟨10289156514144138965641991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27437750704384370575045309 10289156514144138965641991)
    ·
      refine ⟨15433734771216208448462987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10289156514144138965641991 15433734771216208448462987)
      ·
        refine ⟨23150602156824312672694481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15433734771216208448462987 23150602156824312672694481)
        ·
          refine ⟨17362951617618234504520861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23150602156824312672694481 17362951617618234504520861)
          ·
            refine ⟨6511106856606837939195323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17362951617618234504520861 6511106856606837939195323)
            ·
              refine ⟨9766660284910256908792985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6511106856606837939195323 9766660284910256908792985)
              ·
                refine ⟨7324995213682692681594739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9766660284910256908792985 7324995213682692681594739)
                ·
                  refine ⟨10987492820524039022392109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7324995213682692681594739 10987492820524039022392109)
                  ·
                    refine ⟨4120309807696514633397041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10987492820524039022392109 4120309807696514633397041)
                    ·
                      refine ⟨3090232355772385975047781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4120309807696514633397041 3090232355772385975047781)
                      ·
                        rfl

theorem cell23_6018206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_6018206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018206 prefixEnd_6018206 := by exact prefixLift 6018206
  have htrace : WordTrace (prefixWord ++ tailWord_6018206) baseStart_6018206 baseEnd_6018206 := by
    simpa [prefixWord, tailWord_6018206, baseEnd_6018206] using wordTrace_append hprefix tailTrace_6018206
  have hstable : (prefixWord ++ tailWord_6018206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018206).length < 2 ^ (prefixWord ++ tailWord_6018206).sum := by decide
  have hdescent : baseEnd_6018206 < baseStart_6018206 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018211 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 8]
def baseStart_6018211 : Nat := 118140960795 + 6018211 * 2 ^ 59
def prefixEnd_6018211 : Nat := 4983230072969 + 3 ^ 40 * 6018211 * 2
def baseEnd_6018211 : Nat := 3090234923175658455485257

theorem tailTrace_6018211 : CollatzResearch.WordTrace tailWord_6018211 prefixEnd_6018211 3090234923175658455485257 := by
  unfold tailWord_6018211
  simp only [CollatzResearch.WordTrace]
  refine ⟨219502188000056850454294487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146334792000037900302862991 219502188000056850454294487)
  ·
    refine ⟨329253282000085275681441731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219502188000056850454294487 329253282000085275681441731)
    ·
      refine ⟨493879923000127913522162597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329253282000085275681441731 493879923000127913522162597)
      ·
        refine ⟨92602485562523983785405487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 493879923000127913522162597 92602485562523983785405487)
        ·
          refine ⟨138903728343785975678108231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92602485562523983785405487 138903728343785975678108231)
          ·
            refine ⟨208355592515678963517162347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138903728343785975678108231 208355592515678963517162347)
            ·
              refine ⟨312533388773518445275743521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208355592515678963517162347 312533388773518445275743521)
              ·
                refine ⟨234400041580138833956807641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 312533388773518445275743521 234400041580138833956807641)
                ·
                  refine ⟨175800031185104125467605731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 234400041580138833956807641 175800031185104125467605731)
                  ·
                    refine ⟨263700046777656188201408597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 175800031185104125467605731 263700046777656188201408597)
                    ·
                      refine ⟨3090234923175658455485257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 263700046777656188201408597 3090234923175658455485257)
                      ·
                        rfl

theorem cell23_6018211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_6018211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018211 prefixEnd_6018211 := by exact prefixLift 6018211
  have htrace : WordTrace (prefixWord ++ tailWord_6018211) baseStart_6018211 baseEnd_6018211 := by
    simpa [prefixWord, tailWord_6018211, baseEnd_6018211] using wordTrace_append hprefix tailTrace_6018211
  have hstable : (prefixWord ++ tailWord_6018211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018211).length < 2 ^ (prefixWord ++ tailWord_6018211).sum := by decide
  have hdescent : baseEnd_6018211 < baseStart_6018211 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018248 : List Nat := [2, 1, 3, 1, 2, 1, 4, 1, 1, 2, 5]
def baseStart_6018248 : Nat := 118140960795 + 6018248 * 2 ^ 59
def prefixEnd_6018248 : Nat := 4983230072969 + 3 ^ 40 * 6018248 * 2
def baseEnd_6018248 : Nat := 3090253921959874810722587

theorem tailTrace_6018248 : CollatzResearch.WordTrace tailWord_6018248 prefixEnd_6018248 3090253921959874810722587 := by
  unfold tailWord_6018248
  simp only [CollatzResearch.WordTrace]
  refine ⟨109751768750461402886695699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146335691667281870515594265 109751768750461402886695699)
  ·
    refine ⟨164627653125692104330043549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109751768750461402886695699 164627653125692104330043549)
    ·
      refine ⟨61735369922134539123766331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164627653125692104330043549 61735369922134539123766331)
      ·
        refine ⟨92603054883201808685649497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61735369922134539123766331 92603054883201808685649497)
        ·
          refine ⟨69452291162401356514237123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92603054883201808685649497 69452291162401356514237123)
          ·
            refine ⟨104178436743602034771355685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69452291162401356514237123 104178436743602034771355685)
            ·
              refine ⟨19533456889425381519629191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104178436743602034771355685 19533456889425381519629191)
              ·
                refine ⟨29300185334138072279443787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19533456889425381519629191 29300185334138072279443787)
                ·
                  refine ⟨43950278001207108419165681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29300185334138072279443787 43950278001207108419165681)
                  ·
                    refine ⟨32962708500905331314374261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43950278001207108419165681 32962708500905331314374261)
                    ·
                      refine ⟨3090253921959874810722587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32962708500905331314374261 3090253921959874810722587)
                      ·
                        rfl

theorem cell23_6018248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_6018248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018248 prefixEnd_6018248 := by exact prefixLift 6018248
  have htrace : WordTrace (prefixWord ++ tailWord_6018248) baseStart_6018248 baseEnd_6018248 := by
    simpa [prefixWord, tailWord_6018248, baseEnd_6018248] using wordTrace_append hprefix tailTrace_6018248
  have hstable : (prefixWord ++ tailWord_6018248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018248).length < 2 ^ (prefixWord ++ tailWord_6018248).sum := by decide
  have hdescent : baseEnd_6018248 < baseStart_6018248 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018298 : List Nat := [3, 1, 1, 1, 1, 4, 3, 1, 8]
def baseStart_6018298 : Nat := 118140960795 + 6018298 * 2 ^ 59
def prefixEnd_6018298 : Nat := 4983230072969 + 3 ^ 40 * 6018298 * 2
def baseEnd_6018298 : Nat := 343364399554733290566373

theorem tailTrace_6018298 : CollatzResearch.WordTrace tailWord_6018298 prefixEnd_6018298 343364399554733290566373 := by
  unfold tailWord_6018298
  simp only [CollatzResearch.WordTrace]
  refine ⟨54876340287685416078177887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146336907433827776208474365 54876340287685416078177887)
  ·
    refine ⟨82314510431528124117266831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54876340287685416078177887 82314510431528124117266831)
    ·
      refine ⟨123471765647292186175900247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82314510431528124117266831 123471765647292186175900247)
      ·
        refine ⟨185207648470938279263850371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123471765647292186175900247 185207648470938279263850371)
        ·
          refine ⟨277811472706407418895775557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185207648470938279263850371 277811472706407418895775557)
          ·
            refine ⟨52089651132451391042957917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 277811472706407418895775557 52089651132451391042957917)
            ·
              refine ⟨19533619174669271641109219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52089651132451391042957917 19533619174669271641109219)
              ·
                refine ⟨29300428762003907461663829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19533619174669271641109219 29300428762003907461663829)
                ·
                  refine ⟨343364399554733290566373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29300428762003907461663829 343364399554733290566373)
                  ·
                    rfl

theorem cell23_6018298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 8].length) (baseStart_6018298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018298 prefixEnd_6018298 := by exact prefixLift 6018298
  have htrace : WordTrace (prefixWord ++ tailWord_6018298) baseStart_6018298 baseEnd_6018298 := by
    simpa [prefixWord, tailWord_6018298, baseEnd_6018298] using wordTrace_append hprefix tailTrace_6018298
  have hstable : (prefixWord ++ tailWord_6018298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018298).length < 2 ^ (prefixWord ++ tailWord_6018298).sum := by decide
  have hdescent : baseEnd_6018298 < baseStart_6018298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018302 : List Nat := [4, 2, 2, 1, 1, 2, 1, 3, 3, 4]
def baseStart_6018302 : Nat := 118140960795 + 6018302 * 2 ^ 59
def prefixEnd_6018302 : Nat := 4983230072969 + 3 ^ 40 * 6018302 * 2
def baseEnd_6018302 : Nat := 1030093883305072533149113

theorem tailTrace_6018302 : CollatzResearch.WordTrace tailWord_6018302 prefixEnd_6018302 1030093883305072533149113 := by
  unfold tailWord_6018302
  simp only [CollatzResearch.WordTrace]
  refine ⟨27438188380340896624482145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146337004695151448663904773 27438188380340896624482145)
  ·
    refine ⟨20578641285255672468361609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27438188380340896624482145 20578641285255672468361609)
    ·
      refine ⟨15433980963941754351271207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20578641285255672468361609 15433980963941754351271207)
      ·
        refine ⟨23150971445912631526906811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15433980963941754351271207 23150971445912631526906811)
        ·
          refine ⟨34726457168868947290360217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23150971445912631526906811 34726457168868947290360217)
          ·
            refine ⟨26044842876651710467770163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34726457168868947290360217 26044842876651710467770163)
            ·
              refine ⟨39067264314977565701655245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26044842876651710467770163 39067264314977565701655245)
              ·
                refine ⟨14650224118116587138120717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39067264314977565701655245 14650224118116587138120717)
                ·
                  refine ⟨5493834044293720176795269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14650224118116587138120717 5493834044293720176795269)
                  ·
                    refine ⟨1030093883305072533149113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5493834044293720176795269 1030093883305072533149113)
                    ·
                      rfl

theorem cell23_6018302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_6018302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018302 prefixEnd_6018302 := by exact prefixLift 6018302
  have htrace : WordTrace (prefixWord ++ tailWord_6018302) baseStart_6018302 baseEnd_6018302 := by
    simpa [prefixWord, tailWord_6018302, baseEnd_6018302] using wordTrace_append hprefix tailTrace_6018302
  have hstable : (prefixWord ++ tailWord_6018302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018302).length < 2 ^ (prefixWord ++ tailWord_6018302).sum := by decide
  have hdescent : baseEnd_6018302 < baseStart_6018302 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018336 : List Nat := [2, 1, 1, 5, 3, 2, 1, 3, 1, 4]
def baseStart_6018336 : Nat := 118140960795 + 6018336 * 2 ^ 59
def prefixEnd_6018336 : Nat := 4983230072969 + 3 ^ 40 * 6018336 * 2
def baseEnd_6018336 : Nat := 1030099702752490155474061

theorem tailTrace_6018336 : CollatzResearch.WordTrace tailWord_6018336 prefixEnd_6018336 1030099702752490155474061 := by
  unfold tailWord_6018336
  simp only [CollatzResearch.WordTrace]
  refine ⟨109753373562301998401297431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146337831416402664535063241 109753373562301998401297431)
  ·
    refine ⟨164630060343452997601946147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109753373562301998401297431 164630060343452997601946147)
    ·
      refine ⟨246945090515179496402919221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164630060343452997601946147 246945090515179496402919221)
      ·
        refine ⟨23151102235798077787773677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 246945090515179496402919221 23151102235798077787773677)
        ·
          refine ⟨8681663338424279170415129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23151102235798077787773677 8681663338424279170415129)
          ·
            refine ⟨6511247503818209377811347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8681663338424279170415129 6511247503818209377811347)
            ·
              refine ⟨9766871255727314066717021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6511247503818209377811347 9766871255727314066717021)
              ·
                refine ⟨3662576720897742775018883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9766871255727314066717021 3662576720897742775018883)
                ·
                  refine ⟨5493865081346614162528325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3662576720897742775018883 5493865081346614162528325)
                  ·
                    refine ⟨1030099702752490155474061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5493865081346614162528325 1030099702752490155474061)
                    ·
                      rfl

theorem cell23_6018336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 3, 1, 4].length) (baseStart_6018336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018336 prefixEnd_6018336 := by exact prefixLift 6018336
  have htrace : WordTrace (prefixWord ++ tailWord_6018336) baseStart_6018336 baseEnd_6018336 := by
    simpa [prefixWord, tailWord_6018336, baseEnd_6018336] using wordTrace_append hprefix tailTrace_6018336
  have hstable : (prefixWord ++ tailWord_6018336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018336).length < 2 ^ (prefixWord ++ tailWord_6018336).sum := by decide
  have hdescent : baseEnd_6018336 < baseStart_6018336 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018352 : List Nat := [2, 1, 1, 1, 2, 2, 5, 2, 2, 3, 2]
def baseStart_6018352 : Nat := 118140960795 + 6018352 * 2 ^ 59
def prefixEnd_6018352 : Nat := 4983230072969 + 3 ^ 40 * 6018352 * 2
def baseEnd_6018352 : Nat := 3090307323947942403822109

theorem tailTrace_6018352 : CollatzResearch.WordTrace tailWord_6018352 prefixEnd_6018352 3090307323947942403822109 := by
  unfold tailWord_6018352
  simp only [CollatzResearch.WordTrace]
  refine ⟨109753665346273015767588655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146338220461697354356784873 109753665346273015767588655)
  ·
    refine ⟨164630498019409523651382983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109753665346273015767588655 164630498019409523651382983)
    ·
      refine ⟨246945747029114285477074475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164630498019409523651382983 246945747029114285477074475)
      ·
        refine ⟨370418620543671428215611713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246945747029114285477074475 370418620543671428215611713)
        ·
          refine ⟨277813965407753571161708785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 370418620543671428215611713 277813965407753571161708785)
          ·
            refine ⟨208360474055815178371281589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277813965407753571161708785 208360474055815178371281589)
            ·
              refine ⟨19533794442732672972307649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 208360474055815178371281589 19533794442732672972307649)
              ·
                refine ⟨14650345832049504729230737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19533794442732672972307649 14650345832049504729230737)
                ·
                  refine ⟨10987759374037128546923053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14650345832049504729230737 10987759374037128546923053)
                  ·
                    refine ⟨4120409765263923205096145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10987759374037128546923053 4120409765263923205096145)
                    ·
                      refine ⟨3090307323947942403822109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4120409765263923205096145 3090307323947942403822109)
                      ·
                        rfl

theorem cell23_6018352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 2, 3, 2].length) (baseStart_6018352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018352 prefixEnd_6018352 := by exact prefixLift 6018352
  have htrace : WordTrace (prefixWord ++ tailWord_6018352) baseStart_6018352 baseEnd_6018352 := by
    simpa [prefixWord, tailWord_6018352, baseEnd_6018352] using wordTrace_append hprefix tailTrace_6018352
  have hstable : (prefixWord ++ tailWord_6018352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018352).length < 2 ^ (prefixWord ++ tailWord_6018352).sum := by decide
  have hdescent : baseEnd_6018352 < baseStart_6018352 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018410 : List Nat := [3, 1, 3, 3, 2, 2, 2, 2, 1, 1, 3]
def baseStart_6018410 : Nat := 118140960795 + 6018410 * 2 ^ 59
def prefixEnd_6018410 : Nat := 4983230072969 + 3 ^ 40 * 6018410 * 2
def baseEnd_6018410 : Nat := 3090337105825903176896843

theorem tailTrace_6018410 : CollatzResearch.WordTrace tailWord_6018410 prefixEnd_6018410 3090337105825903176896843 := by
  unfold tailWord_6018410
  simp only [CollatzResearch.WordTrace]
  refine ⟨54877361531583976860197171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146339630750890604960525789 54877361531583976860197171)
  ·
    refine ⟨82316042297375965290295757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54877361531583976860197171 82316042297375965290295757)
    ·
      refine ⟨30868515861515986983860909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82316042297375965290295757 30868515861515986983860909)
      ·
        refine ⟨11575693448068495118947841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30868515861515986983860909 11575693448068495118947841)
        ·
          refine ⟨8681770086051371339210881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11575693448068495118947841 8681770086051371339210881)
          ·
            refine ⟨6511327564538528504408161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8681770086051371339210881 6511327564538528504408161)
            ·
              refine ⟨4883495673403896378306121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6511327564538528504408161 4883495673403896378306121)
              ·
                refine ⟨3662621755052922283729591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4883495673403896378306121 3662621755052922283729591)
                ·
                  refine ⟨5493932632579383425594387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3662621755052922283729591 5493932632579383425594387)
                  ·
                    refine ⟨8240898948869075138391581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5493932632579383425594387 8240898948869075138391581)
                    ·
                      refine ⟨3090337105825903176896843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8240898948869075138391581 3090337105825903176896843)
                      ·
                        rfl

theorem cell23_6018410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_6018410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018410 prefixEnd_6018410 := by exact prefixLift 6018410
  have htrace : WordTrace (prefixWord ++ tailWord_6018410) baseStart_6018410 baseEnd_6018410 := by
    simpa [prefixWord, tailWord_6018410, baseEnd_6018410] using wordTrace_append hprefix tailTrace_6018410
  have hstable : (prefixWord ++ tailWord_6018410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018410).length < 2 ^ (prefixWord ++ tailWord_6018410).sum := by decide
  have hdescent : baseEnd_6018410 < baseStart_6018410 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018415 : List Nat := [1, 1, 2, 1, 3, 1, 3, 2, 3, 3, 3]
def baseStart_6018415 : Nat := 118140960795 + 6018415 * 2 ^ 59
def prefixEnd_6018415 : Nat := 4983230072969 + 3 ^ 40 * 6018415 * 2
def baseEnd_6018415 : Nat := 3090339673229175657334319

theorem tailTrace_6018415 : CollatzResearch.WordTrace tailWord_6018415 prefixEnd_6018415 3090339673229175657334319 := by
  unfold tailWord_6018415
  simp only [CollatzResearch.WordTrace]
  refine ⟨219509628491317793294720699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146339752327545195529813799 219509628491317793294720699)
  ·
    refine ⟨329264442736976689942081049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219509628491317793294720699 329264442736976689942081049)
    ·
      refine ⟨246948332052732517456560787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329264442736976689942081049 246948332052732517456560787)
      ·
        refine ⟨370422498079098776184841181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246948332052732517456560787 370422498079098776184841181)
        ·
          refine ⟨138908436779662041069315443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 370422498079098776184841181 138908436779662041069315443)
          ·
            refine ⟨208362655169493061603973165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138908436779662041069315443 208362655169493061603973165)
            ·
              refine ⟨78135995688559898101489937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 208362655169493061603973165 78135995688559898101489937)
              ·
                refine ⟨58601996766419923576117453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78135995688559898101489937 58601996766419923576117453)
                ·
                  refine ⟨21975748787407471341044045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58601996766419923576117453 21975748787407471341044045)
                  ·
                    refine ⟨8240905795277801752891517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21975748787407471341044045 8240905795277801752891517)
                    ·
                      refine ⟨3090339673229175657334319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8240905795277801752891517 3090339673229175657334319)
                      ·
                        rfl

theorem cell23_6018415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 3, 3].length) (baseStart_6018415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018415 prefixEnd_6018415 := by exact prefixLift 6018415
  have htrace : WordTrace (prefixWord ++ tailWord_6018415) baseStart_6018415 baseEnd_6018415 := by
    simpa [prefixWord, tailWord_6018415, baseEnd_6018415] using wordTrace_append hprefix tailTrace_6018415
  have hstable : (prefixWord ++ tailWord_6018415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018415).length < 2 ^ (prefixWord ++ tailWord_6018415).sum := by decide
  have hdescent : baseEnd_6018415 < baseStart_6018415 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018416 : List Nat := [2, 1, 1, 1, 4, 2, 3, 4, 1, 2, 2]
def baseStart_6018416 : Nat := 118140960795 + 6018416 * 2 ^ 59
def prefixEnd_6018416 : Nat := 4983230072969 + 3 ^ 40 * 6018416 * 2
def baseEnd_6018416 : Nat := 3090340186709830153421815

theorem tailTrace_6018416 : CollatzResearch.WordTrace tailWord_6018416 prefixEnd_6018416 3090340186709830153421815 := by
  unfold tailWord_6018416
  simp only [CollatzResearch.WordTrace]
  refine ⟨109754832482157085232753551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146339776642876113643671401 109754832482157085232753551)
  ·
    refine ⟨164632248723235627849130327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109754832482157085232753551 164632248723235627849130327)
    ·
      refine ⟨246948373084853441773695491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164632248723235627849130327 246948373084853441773695491)
      ·
        refine ⟨370422559627280162660543237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246948373084853441773695491 370422559627280162660543237)
        ·
          refine ⟨69454229930115030498851857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 370422559627280162660543237 69454229930115030498851857)
          ·
            refine ⟨52090672447586272874138893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69454229930115030498851857 52090672447586272874138893)
            ·
              refine ⟨19534002167844852327802085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52090672447586272874138893 19534002167844852327802085)
              ·
                refine ⟨3662625406470909811462891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19534002167844852327802085 3662625406470909811462891)
                ·
                  refine ⟨5493938109706364717194337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3662625406470909811462891 5493938109706364717194337)
                  ·
                    refine ⟨4120453582279773537895753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5493938109706364717194337 4120453582279773537895753)
                    ·
                      refine ⟨3090340186709830153421815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4120453582279773537895753 3090340186709830153421815)
                      ·
                        rfl

theorem cell23_6018416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 4, 1, 2, 2].length) (baseStart_6018416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018416 prefixEnd_6018416 := by exact prefixLift 6018416
  have htrace : WordTrace (prefixWord ++ tailWord_6018416) baseStart_6018416 baseEnd_6018416 := by
    simpa [prefixWord, tailWord_6018416, baseEnd_6018416] using wordTrace_append hprefix tailTrace_6018416
  have hstable : (prefixWord ++ tailWord_6018416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018416).length < 2 ^ (prefixWord ++ tailWord_6018416).sum := by decide
  have hdescent : baseEnd_6018416 < baseStart_6018416 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018450 : List Nat := [3, 2, 3, 3, 2, 1, 2, 1, 1, 1, 4]
def baseStart_6018450 : Nat := 118140960795 + 6018450 * 2 ^ 59
def prefixEnd_6018450 : Nat := 4983230072969 + 3 ^ 40 * 6018450 * 2
def baseEnd_6018450 : Nat := 3090357645052083020396659

theorem tailTrace_6018450 : CollatzResearch.WordTrace tailWord_6018450 prefixEnd_6018450 3090357645052083020396659 := by
  unfold tailWord_6018450
  simp only [CollatzResearch.WordTrace]
  refine ⟨54877726261547748568061201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146340603364127329514829869 54877726261547748568061201)
  ·
    refine ⟨41158294696160811426045901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54877726261547748568061201 41158294696160811426045901)
    ·
      refine ⟨15434360511060304284767213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41158294696160811426045901 15434360511060304284767213)
      ·
        refine ⟨5787885191647614106787705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15434360511060304284767213 5787885191647614106787705)
        ·
          refine ⟨4340913893735710580090779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5787885191647614106787705 4340913893735710580090779)
          ·
            refine ⟨6511370840603565870136169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4340913893735710580090779 6511370840603565870136169)
            ·
              refine ⟨4883528130452674402602127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6511370840603565870136169 4883528130452674402602127)
              ·
                refine ⟨7325292195679011603903191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4883528130452674402602127 7325292195679011603903191)
                ·
                  refine ⟨10987938293518517405854787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7325292195679011603903191 10987938293518517405854787)
                  ·
                    refine ⟨16481907440277776108782181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10987938293518517405854787 16481907440277776108782181)
                    ·
                      refine ⟨3090357645052083020396659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16481907440277776108782181 3090357645052083020396659)
                      ·
                        rfl

theorem cell23_6018450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_6018450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018450 prefixEnd_6018450 := by exact prefixLift 6018450
  have htrace : WordTrace (prefixWord ++ tailWord_6018450) baseStart_6018450 baseEnd_6018450 := by
    simpa [prefixWord, tailWord_6018450, baseEnd_6018450] using wordTrace_append hprefix tailTrace_6018450
  have hstable : (prefixWord ++ tailWord_6018450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018450).length < 2 ^ (prefixWord ++ tailWord_6018450).sum := by decide
  have hdescent : baseEnd_6018450 < baseStart_6018450 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018466 : List Nat := [3, 3, 1, 2, 1, 2, 3, 2, 2, 1, 3]
def baseStart_6018466 : Nat := 118140960795 + 6018466 * 2 ^ 59
def prefixEnd_6018466 : Nat := 4983230072969 + 3 ^ 40 * 6018466 * 2
def baseEnd_6018466 : Nat := 3090365860742554957796585

theorem tailTrace_6018466 : CollatzResearch.WordTrace tailWord_6018466 prefixEnd_6018466 3090365860742554957796585 := by
  unfold tailWord_6018466
  simp only [CollatzResearch.WordTrace]
  refine ⟨54877872153533257251206813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146340992409422019336551501 54877872153533257251206813)
  ·
    refine ⟨20579202057574971469202555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54877872153533257251206813 20579202057574971469202555)
    ·
      refine ⟨30868803086362457203803833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20579202057574971469202555 30868803086362457203803833)
      ·
        refine ⟨23151602314771842902852875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30868803086362457203803833 23151602314771842902852875)
        ·
          refine ⟨34727403472157764354279313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23151602314771842902852875 34727403472157764354279313)
          ·
            refine ⟨26045552604118323265709485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34727403472157764354279313 26045552604118323265709485)
            ·
              refine ⟨9767082226544371224641057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26045552604118323265709485 9767082226544371224641057)
              ·
                refine ⟨7325311669908278418480793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9767082226544371224641057 7325311669908278418480793)
                ·
                  refine ⟨5493983752431208813860595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7325311669908278418480793 5493983752431208813860595)
                  ·
                    refine ⟨8240975628646813220790893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5493983752431208813860595 8240975628646813220790893)
                    ·
                      refine ⟨3090365860742554957796585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8240975628646813220790893 3090365860742554957796585)
                      ·
                        rfl

theorem cell23_6018466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_6018466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018466 prefixEnd_6018466 := by exact prefixLift 6018466
  have htrace : WordTrace (prefixWord ++ tailWord_6018466) baseStart_6018466 baseEnd_6018466 := by
    simpa [prefixWord, tailWord_6018466, baseEnd_6018466] using wordTrace_append hprefix tailTrace_6018466
  have hstable : (prefixWord ++ tailWord_6018466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018466).length < 2 ^ (prefixWord ++ tailWord_6018466).sum := by decide
  have hdescent : baseEnd_6018466 < baseStart_6018466 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018475 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 6, 4, 3]
def baseStart_6018475 : Nat := 118140960795 + 6018475 * 2 ^ 59
def prefixEnd_6018475 : Nat := 4983230072969 + 3 ^ 40 * 6018475 * 2
def baseEnd_6018475 : Nat := 3090370482068445422584043

theorem tailTrace_6018475 : CollatzResearch.WordTrace tailWord_6018475 prefixEnd_6018475 3090370482068445422584043 := by
  unfold tailWord_6018475
  simp only [CollatzResearch.WordTrace]
  refine ⟨219511816871100423541904879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146341211247400282361269919 219511816871100423541904879)
  ·
    refine ⟨329267725306650635312857319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219511816871100423541904879 329267725306650635312857319)
    ·
      refine ⟨493901587959975952969285979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329267725306650635312857319 493901587959975952969285979)
      ·
        refine ⟨740852381939963929453928969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 493901587959975952969285979 740852381939963929453928969)
        ·
          refine ⟨555639286454972947090446727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 740852381939963929453928969 555639286454972947090446727)
          ·
            refine ⟨833458929682459420635670091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 555639286454972947090446727 833458929682459420635670091)
            ·
              refine ⟨1250188394523689130953505137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 833458929682459420635670091 1250188394523689130953505137)
              ·
                refine ⟨937641295892766848215128853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1250188394523689130953505137 937641295892766848215128853)
                ·
                  refine ⟨43951935744973446010084165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 937641295892766848215128853 43951935744973446010084165)
                  ·
                    refine ⟨8240987952182521126890781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43951935744973446010084165 8240987952182521126890781)
                    ·
                      refine ⟨3090370482068445422584043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8240987952182521126890781 3090370482068445422584043)
                      ·
                        rfl

theorem cell23_6018475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 4, 3].length) (baseStart_6018475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018475 prefixEnd_6018475 := by exact prefixLift 6018475
  have htrace : WordTrace (prefixWord ++ tailWord_6018475) baseStart_6018475 baseEnd_6018475 := by
    simpa [prefixWord, tailWord_6018475, baseEnd_6018475] using wordTrace_append hprefix tailTrace_6018475
  have hstable : (prefixWord ++ tailWord_6018475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018475).length < 2 ^ (prefixWord ++ tailWord_6018475).sum := by decide
  have hdescent : baseEnd_6018475 < baseStart_6018475 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018542 : List Nat := [4, 1, 2, 1, 2, 1, 1, 2, 4, 5]
def baseStart_6018542 : Nat := 118140960795 + 6018542 * 2 ^ 59
def prefixEnd_6018542 : Nat := 4983230072969 + 3 ^ 40 * 6018542 * 2
def baseEnd_6018542 : Nat := 1030134961757432220148745

theorem tailTrace_6018542 : CollatzResearch.WordTrace tailWord_6018542 prefixEnd_6018542 1030134961757432220148745 := by
  unfold tailWord_6018542
  simp only [CollatzResearch.WordTrace]
  refine ⟨27439282570232211748074235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146342840374571795989729253 27439282570232211748074235)
  ·
    refine ⟨41158923855348317622111353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27439282570232211748074235 41158923855348317622111353)
    ·
      refine ⟨30869192891511238216583515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41158923855348317622111353 30869192891511238216583515)
      ·
        refine ⟨46303789337266857324875273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30869192891511238216583515 46303789337266857324875273)
        ·
          refine ⟨34727842002950142993656455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46303789337266857324875273 34727842002950142993656455)
          ·
            refine ⟨52091763004425214490484683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34727842002950142993656455 52091763004425214490484683)
            ·
              refine ⟨78137644506637821735727025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52091763004425214490484683 78137644506637821735727025)
              ·
                refine ⟨58603233379978366301795269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78137644506637821735727025 58603233379978366301795269)
                ·
                  refine ⟨10988106258745943681586613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58603233379978366301795269 10988106258745943681586613)
                  ·
                    refine ⟨1030134961757432220148745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10988106258745943681586613 1030134961757432220148745)
                    ·
                      rfl

theorem cell23_6018542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_6018542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018542 prefixEnd_6018542 := by exact prefixLift 6018542
  have htrace : WordTrace (prefixWord ++ tailWord_6018542) baseStart_6018542 baseEnd_6018542 := by
    simpa [prefixWord, tailWord_6018542, baseEnd_6018542] using wordTrace_append hprefix tailTrace_6018542
  have hstable : (prefixWord ++ tailWord_6018542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018542).length < 2 ^ (prefixWord ++ tailWord_6018542).sum := by decide
  have hdescent : baseEnd_6018542 < baseStart_6018542 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018580 : List Nat := [2, 4, 3, 1, 2, 2, 2, 2, 5]
def baseStart_6018580 : Nat := 118140960795 + 6018580 * 2 ^ 59
def prefixEnd_6018580 : Nat := 4983230072969 + 3 ^ 40 * 6018580 * 2
def baseEnd_6018580 : Nat := 343380488615240834641229

theorem tailTrace_6018580 : CollatzResearch.WordTrace tailWord_6018580 prefixEnd_6018580 343380488615240834641229 := by
  unfold tailWord_6018580
  simp only [CollatzResearch.WordTrace]
  refine ⟨109757823267860013237238597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146343764357146684316318129 109757823267860013237238597)
  ·
    refine ⟨20579591862723752481982237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109757823267860013237238597 20579591862723752481982237)
    ·
      refine ⟨7717346948521407180743339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20579591862723752481982237 7717346948521407180743339)
      ·
        refine ⟨11576020422782110771115009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7717346948521407180743339 11576020422782110771115009)
        ·
          refine ⟨8682015317086583078336257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11576020422782110771115009 8682015317086583078336257)
          ·
            refine ⟨6511511487814937308752193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8682015317086583078336257 6511511487814937308752193)
            ·
              refine ⟨4883633615861202981564145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6511511487814937308752193 4883633615861202981564145)
              ·
                refine ⟨3662725211895902236173109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4883633615861202981564145 3662725211895902236173109)
                ·
                  refine ⟨343380488615240834641229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3662725211895902236173109 343380488615240834641229)
                  ·
                    rfl

theorem cell23_6018580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 2, 5].length) (baseStart_6018580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018580 prefixEnd_6018580 := by exact prefixLift 6018580
  have htrace : WordTrace (prefixWord ++ tailWord_6018580) baseStart_6018580 baseEnd_6018580 := by
    simpa [prefixWord, tailWord_6018580, baseEnd_6018580] using wordTrace_append hprefix tailTrace_6018580
  have hstable : (prefixWord ++ tailWord_6018580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018580).length < 2 ^ (prefixWord ++ tailWord_6018580).sum := by decide
  have hdescent : baseEnd_6018580 < baseStart_6018580 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018589 : List Nat := [1, 4, 2, 2, 1, 1, 2, 3, 3, 4]
def baseStart_6018589 : Nat := 118140960795 + 6018589 * 2 ^ 59
def prefixEnd_6018589 : Nat := 4983230072969 + 3 ^ 40 * 6018589 * 2
def baseEnd_6018589 : Nat := 1030143006287685992186173

theorem tailTrace_6018589 : CollatzResearch.WordTrace tailWord_6018589 prefixEnd_6018589 1030143006287685992186173 := by
  unfold tailWord_6018589
  simp only [CollatzResearch.WordTrace]
  refine ⟨219515974792687421011554821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146343983195124947341036547 219515974792687421011554821)
  ·
    refine ⟨41159245273628891439666529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 219515974792687421011554821 41159245273628891439666529)
    ·
      refine ⟨30869433955221668579749897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41159245273628891439666529 30869433955221668579749897)
      ·
        refine ⟨23152075466416251434812423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30869433955221668579749897 23152075466416251434812423)
        ·
          refine ⟨34728113199624377152218635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23152075466416251434812423 34728113199624377152218635)
          ·
            refine ⟨52092169799436565728327953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34728113199624377152218635 52092169799436565728327953)
            ·
              refine ⟨39069127349577424296245965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52092169799436565728327953 39069127349577424296245965)
              ·
                refine ⟨14650922756091534111092237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39069127349577424296245965 14650922756091534111092237)
                ·
                  refine ⟨5494096033534325291659589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14650922756091534111092237 5494096033534325291659589)
                  ·
                    refine ⟨1030143006287685992186173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5494096033534325291659589 1030143006287685992186173)
                    ·
                      rfl

theorem cell23_6018589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_6018589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018589 prefixEnd_6018589 := by exact prefixLift 6018589
  have htrace : WordTrace (prefixWord ++ tailWord_6018589) baseStart_6018589 baseEnd_6018589 := by
    simpa [prefixWord, tailWord_6018589, baseEnd_6018589] using wordTrace_append hprefix tailTrace_6018589
  have hstable : (prefixWord ++ tailWord_6018589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018589).length < 2 ^ (prefixWord ++ tailWord_6018589).sum := by decide
  have hdescent : baseEnd_6018589 < baseStart_6018589 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018590 : List Nat := [4, 3, 3, 1, 1, 1, 1, 1, 2, 3, 3]
def baseStart_6018590 : Nat := 118140960795 + 6018590 * 2 ^ 59
def prefixEnd_6018590 : Nat := 4983230072969 + 3 ^ 40 * 6018590 * 2
def baseEnd_6018590 : Nat := 3090429532343712472646015

theorem tailTrace_6018590 : CollatzResearch.WordTrace tailWord_6018590 prefixEnd_6018590 3090429532343712472646015 := by
  unfold tailWord_6018590
  simp only [CollatzResearch.WordTrace]
  refine ⟨27439501408210474772792653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146344007510455865454894149 27439501408210474772792653)
  ·
    refine ⟨10289813028078928039797245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27439501408210474772792653 10289813028078928039797245)
    ·
      refine ⟨3858679885529598014923967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10289813028078928039797245 3858679885529598014923967)
      ·
        refine ⟨5788019828294397022385951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3858679885529598014923967 5788019828294397022385951)
        ·
          refine ⟨8682029742441595533578927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5788019828294397022385951 8682029742441595533578927)
          ·
            refine ⟨13023044613662393300368391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8682029742441595533578927 13023044613662393300368391)
            ·
              refine ⟨19534566920493589950552587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13023044613662393300368391 19534566920493589950552587)
              ·
                refine ⟨29301850380740384925828881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19534566920493589950552587 29301850380740384925828881)
                ·
                  refine ⟨21976387785555288694371661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29301850380740384925828881 21976387785555288694371661)
                  ·
                    refine ⟨8241145419583233260389373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21976387785555288694371661 8241145419583233260389373)
                    ·
                      refine ⟨3090429532343712472646015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8241145419583233260389373 3090429532343712472646015)
                      ·
                        rfl

theorem cell23_6018590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_6018590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018590 prefixEnd_6018590 := by exact prefixLift 6018590
  have htrace : WordTrace (prefixWord ++ tailWord_6018590) baseStart_6018590 baseEnd_6018590 := by
    simpa [prefixWord, tailWord_6018590, baseEnd_6018590] using wordTrace_append hprefix tailTrace_6018590
  have hstable : (prefixWord ++ tailWord_6018590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018590).length < 2 ^ (prefixWord ++ tailWord_6018590).sum := by decide
  have hdescent : baseEnd_6018590 < baseStart_6018590 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018606 : List Nat := [4, 1, 3, 1, 2, 2, 1, 2, 3, 4]
def baseStart_6018606 : Nat := 118140960795 + 6018606 * 2 ^ 59
def prefixEnd_6018606 : Nat := 4983230072969 + 3 ^ 40 * 6018606 * 2
def baseEnd_6018606 : Nat := 1030145916011394803348647

theorem tailTrace_6018606 : CollatzResearch.WordTrace tailWord_6018606 prefixEnd_6018606 1030145916011394803348647 := by
  unfold tailWord_6018606
  simp only [CollatzResearch.WordTrace]
  refine ⟨27439574354203229114365459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146344396555750555276615781 27439574354203229114365459)
  ·
    refine ⟨41159361531304843671548189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27439574354203229114365459 41159361531304843671548189)
    ·
      refine ⟨15434760574239316376830571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41159361531304843671548189 15434760574239316376830571)
      ·
        refine ⟨23152140861358974565245857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15434760574239316376830571 23152140861358974565245857)
        ·
          refine ⟨17364105646019230923934393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23152140861358974565245857 17364105646019230923934393)
          ·
            refine ⟨13023079234514423192950795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17364105646019230923934393 13023079234514423192950795)
            ·
              refine ⟨19534618851771634789426193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13023079234514423192950795 19534618851771634789426193)
              ·
                refine ⟨14650964138828726092069645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19534618851771634789426193 14650964138828726092069645)
                ·
                  refine ⟨5494111552060772284526117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14650964138828726092069645 5494111552060772284526117)
                  ·
                    refine ⟨1030145916011394803348647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5494111552060772284526117 1030145916011394803348647)
                    ·
                      rfl

theorem cell23_6018606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_6018606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018606 prefixEnd_6018606 := by exact prefixLift 6018606
  have htrace : WordTrace (prefixWord ++ tailWord_6018606) baseStart_6018606 baseEnd_6018606 := by
    simpa [prefixWord, tailWord_6018606, baseEnd_6018606] using wordTrace_append hprefix tailTrace_6018606
  have hstable : (prefixWord ++ tailWord_6018606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018606).length < 2 ^ (prefixWord ++ tailWord_6018606).sum := by decide
  have hdescent : baseEnd_6018606 < baseStart_6018606 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018616 : List Nat := [2, 1, 2, 1, 4, 4, 1, 1, 2, 2, 3]
def baseStart_6018616 : Nat := 118140960795 + 6018616 * 2 ^ 59
def prefixEnd_6018616 : Nat := 4983230072969 + 3 ^ 40 * 6018616 * 2
def baseEnd_6018616 : Nat := 3090442882840729370920895

theorem tailTrace_6018616 : CollatzResearch.WordTrace tailWord_6018616 prefixEnd_6018616 3090442882840729370920895 := by
  unfold tailWord_6018616
  simp only [CollatzResearch.WordTrace]
  refine ⟨109758479781794802311393851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146344639709059736415191801 109758479781794802311393851)
  ·
    refine ⟨164637719672692203467090777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109758479781794802311393851 164637719672692203467090777)
    ·
      refine ⟨123478289754519152600318083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164637719672692203467090777 123478289754519152600318083)
      ·
        refine ⟨185217434631778728900477125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123478289754519152600318083 185217434631778728900477125)
        ·
          refine ⟨34728268993458511668839461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 185217434631778728900477125 34728268993458511668839461)
          ·
            refine ⟨6511550436273470937907399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34728268993458511668839461 6511550436273470937907399)
            ·
              refine ⟨9767325654410206406861099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6511550436273470937907399 9767325654410206406861099)
              ·
                refine ⟨14650988481615309610291649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9767325654410206406861099 14650988481615309610291649)
                ·
                  refine ⟨10988241361211482207718737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14650988481615309610291649 10988241361211482207718737)
                  ·
                    refine ⟨8241181020908611655789053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10988241361211482207718737 8241181020908611655789053)
                    ·
                      refine ⟨3090442882840729370920895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8241181020908611655789053 3090442882840729370920895)
                      ·
                        rfl

theorem cell23_6018616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 2, 2, 3].length) (baseStart_6018616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018616 prefixEnd_6018616 := by exact prefixLift 6018616
  have htrace : WordTrace (prefixWord ++ tailWord_6018616) baseStart_6018616 baseEnd_6018616 := by
    simpa [prefixWord, tailWord_6018616, baseEnd_6018616] using wordTrace_append hprefix tailTrace_6018616
  have hstable : (prefixWord ++ tailWord_6018616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018616).length < 2 ^ (prefixWord ++ tailWord_6018616).sum := by decide
  have hdescent : baseEnd_6018616 < baseStart_6018616 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018629 : List Nat := [1, 3, 1, 1, 1, 4, 1, 2, 5, 1, 3]
def baseStart_6018629 : Nat := 118140960795 + 6018629 * 2 ^ 59
def prefixEnd_6018629 : Nat := 4983230072969 + 3 ^ 40 * 6018629 * 2
def baseEnd_6018629 : Nat := 3090449558089237820058335

theorem tailTrace_6018629 : CollatzResearch.WordTrace tailWord_6018629 prefixEnd_6018629 3090449558089237820058335 := by
  unfold tailWord_6018629
  simp only [CollatzResearch.WordTrace]
  refine ⟨219517433712542507843010941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146344955808361671895340627 219517433712542507843010941)
  ·
    refine ⟨82319037642203440441129103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219517433712542507843010941 82319037642203440441129103)
    ·
      refine ⟨123478556463305160661693655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82319037642203440441129103 123478556463305160661693655)
      ·
        refine ⟨185217834694957740992540483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123478556463305160661693655 185217834694957740992540483)
        ·
          refine ⟨277826752042436611488810725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185217834694957740992540483 277826752042436611488810725)
          ·
            refine ⟨52092516007956864654152011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 277826752042436611488810725 52092516007956864654152011)
            ·
              refine ⟨78138774011935296981228017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52092516007956864654152011 78138774011935296981228017)
              ·
                refine ⟨58604080508951472735921013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78138774011935296981228017 58604080508951472735921013)
                ·
                  refine ⟨5494132547714200568992595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58604080508951472735921013 5494132547714200568992595)
                  ·
                    refine ⟨8241198821571300853488893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5494132547714200568992595 8241198821571300853488893)
                    ·
                      refine ⟨3090449558089237820058335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8241198821571300853488893 3090449558089237820058335)
                      ·
                        rfl

theorem cell23_6018629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 5, 1, 3].length) (baseStart_6018629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018629 prefixEnd_6018629 := by exact prefixLift 6018629
  have htrace : WordTrace (prefixWord ++ tailWord_6018629) baseStart_6018629 baseEnd_6018629 := by
    simpa [prefixWord, tailWord_6018629, baseEnd_6018629] using wordTrace_append hprefix tailTrace_6018629
  have hstable : (prefixWord ++ tailWord_6018629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018629).length < 2 ^ (prefixWord ++ tailWord_6018629).sum := by decide
  have hdescent : baseEnd_6018629 < baseStart_6018629 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018639 : List Nat := [1, 1, 2, 1, 1, 2, 3, 3, 4, 3, 2]
def baseStart_6018639 : Nat := 118140960795 + 6018639 * 2 ^ 59
def prefixEnd_6018639 : Nat := 4983230072969 + 3 ^ 40 * 6018639 * 2
def baseEnd_6018639 : Nat := 3090454692895782780933289

theorem tailTrace_6018639 : CollatzResearch.WordTrace tailWord_6018639 prefixEnd_6018639 3090454692895782780933289 := by
  unfold tailWord_6018639
  simp only [CollatzResearch.WordTrace]
  refine ⟨219517798442506279550874971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146345198961670853033916647 219517798442506279550874971)
  ·
    refine ⟨329276697663759419326312457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219517798442506279550874971 329276697663759419326312457)
    ·
      refine ⟨246957523247819564494734343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329276697663759419326312457 246957523247819564494734343)
      ·
        refine ⟨370436284871729346742101515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246957523247819564494734343 370436284871729346742101515)
        ·
          refine ⟨555654427307594020113152273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 370436284871729346742101515 555654427307594020113152273)
          ·
            refine ⟨416740820480695515084864205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 555654427307594020113152273 416740820480695515084864205)
            ·
              refine ⟨156277807680260818156824077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 416740820480695515084864205 156277807680260818156824077)
              ·
                refine ⟨58604177880097806808809029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156277807680260818156824077 58604177880097806808809029)
                ·
                  refine ⟨10988283352518338776651693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58604177880097806808809029 10988283352518338776651693)
                  ·
                    refine ⟨4120606257194377041244385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10988283352518338776651693 4120606257194377041244385)
                    ·
                      refine ⟨3090454692895782780933289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4120606257194377041244385 3090454692895782780933289)
                      ·
                        rfl

theorem cell23_6018639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 4, 3, 2].length) (baseStart_6018639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018639 prefixEnd_6018639 := by exact prefixLift 6018639
  have htrace : WordTrace (prefixWord ++ tailWord_6018639) baseStart_6018639 baseEnd_6018639 := by
    simpa [prefixWord, tailWord_6018639, baseEnd_6018639] using wordTrace_append hprefix tailTrace_6018639
  have hstable : (prefixWord ++ tailWord_6018639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018639).length < 2 ^ (prefixWord ++ tailWord_6018639).sum := by decide
  have hdescent : baseEnd_6018639 < baseStart_6018639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018666 : List Nat := [3, 1, 3, 2, 1, 3, 2, 2, 1, 5]
def baseStart_6018666 : Nat := 118140960795 + 6018666 * 2 ^ 59
def prefixEnd_6018666 : Nat := 4983230072969 + 3 ^ 40 * 6018666 * 2
def baseEnd_6018666 : Nat := 1030156185624484725098555

theorem tailTrace_6018666 : CollatzResearch.WordTrace tailWord_6018666 prefixEnd_6018666 1030156185624484725098555 := by
  unfold tailWord_6018666
  simp only [CollatzResearch.WordTrace]
  refine ⟨54879695803352115790526963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146345855475605642108071901 54879695803352115790526963)
  ·
    refine ⟨82319543705028173685790445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54879695803352115790526963 82319543705028173685790445)
    ·
      refine ⟨30869828889385565132171417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82319543705028173685790445 30869828889385565132171417)
      ·
        refine ⟨23152371667039173849128563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30869828889385565132171417 23152371667039173849128563)
        ·
          refine ⟨34728557500558760773692845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23152371667039173849128563 34728557500558760773692845)
          ·
            refine ⟨13023209062709535290134817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34728557500558760773692845 13023209062709535290134817)
            ·
              refine ⟨9767406797032151467601113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13023209062709535290134817 9767406797032151467601113)
              ·
                refine ⟨7325555097774113600700835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9767406797032151467601113 7325555097774113600700835)
                ·
                  refine ⟨10988332646661170401051253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7325555097774113600700835 10988332646661170401051253)
                  ·
                    refine ⟨1030156185624484725098555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10988332646661170401051253 1030156185624484725098555)
                    ·
                      rfl

theorem cell23_6018666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_6018666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018666 prefixEnd_6018666 := by exact prefixLift 6018666
  have htrace : WordTrace (prefixWord ++ tailWord_6018666) baseStart_6018666 baseEnd_6018666 := by
    simpa [prefixWord, tailWord_6018666, baseEnd_6018666] using wordTrace_append hprefix tailTrace_6018666
  have hstable : (prefixWord ++ tailWord_6018666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018666).length < 2 ^ (prefixWord ++ tailWord_6018666).sum := by decide
  have hdescent : baseEnd_6018666 < baseStart_6018666 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018689 : List Nat := [1, 2, 4, 2, 1, 2, 1, 3, 1, 1, 5]
def baseStart_6018689 : Nat := 118140960795 + 6018689 * 2 ^ 59
def prefixEnd_6018689 : Nat := 4983230072969 + 3 ^ 40 * 6018689 * 2
def baseEnd_6018689 : Nat := 3090480366928507585308059

theorem tailTrace_6018689 : CollatzResearch.WordTrace tailWord_6018689 prefixEnd_6018689 3090480366928507585308059 := by
  unfold tailWord_6018689
  simp only [CollatzResearch.WordTrace]
  refine ⟨219519622092325138090195121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146346414728216758726796747 219519622092325138090195121)
  ·
    refine ⟨164639716569243853567646341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219519622092325138090195121 164639716569243853567646341)
    ·
      refine ⟨30869946856733222543933689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164639716569243853567646341 30869946856733222543933689)
      ·
        refine ⟨23152460142549916907950267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30869946856733222543933689 23152460142549916907950267)
        ·
          refine ⟨34728690213824875361925401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23152460142549916907950267 34728690213824875361925401)
          ·
            refine ⟨26046517660368656521444051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34728690213824875361925401 26046517660368656521444051)
            ·
              refine ⟨39069776490552984782166077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26046517660368656521444051 39069776490552984782166077)
              ·
                refine ⟨14651166183957369293312279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39069776490552984782166077 14651166183957369293312279)
                ·
                  refine ⟨21976749275936053939968419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14651166183957369293312279 21976749275936053939968419)
                  ·
                    refine ⟨32965123913904080909952629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21976749275936053939968419 32965123913904080909952629)
                    ·
                      refine ⟨3090480366928507585308059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32965123913904080909952629 3090480366928507585308059)
                      ·
                        rfl

theorem cell23_6018689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_6018689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018689 prefixEnd_6018689 := by exact prefixLift 6018689
  have htrace : WordTrace (prefixWord ++ tailWord_6018689) baseStart_6018689 baseEnd_6018689 := by
    simpa [prefixWord, tailWord_6018689, baseEnd_6018689] using wordTrace_append hprefix tailTrace_6018689
  have hstable : (prefixWord ++ tailWord_6018689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018689).length < 2 ^ (prefixWord ++ tailWord_6018689).sum := by decide
  have hdescent : baseEnd_6018689 < baseStart_6018689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018769 : List Nat := [1, 2, 2, 1, 2, 5, 1, 1, 2, 6]
def baseStart_6018769 : Nat := 118140960795 + 6018769 * 2 ^ 59
def prefixEnd_6018769 : Nat := 4983230072969 + 3 ^ 40 * 6018769 * 2
def baseEnd_6018769 : Nat := 1030173815126955757435897

theorem tailTrace_6018769 : CollatzResearch.WordTrace tailWord_6018769 prefixEnd_6018769 1030173815126955757435897 := by
  unfold tailWord_6018769
  simp only [CollatzResearch.WordTrace]
  refine ⟨219522539932035311753107361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146348359954690207835404907 219522539932035311753107361)
  ·
    refine ⟨164641904949026483814830521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219522539932035311753107361 164641904949026483814830521)
    ·
      refine ⟨123481428711769862861122891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164641904949026483814830521 123481428711769862861122891)
      ·
        refine ⟨185222143067654794291684337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123481428711769862861122891 185222143067654794291684337)
        ·
          refine ⟨138916607300741095718763253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185222143067654794291684337 138916607300741095718763253)
          ·
            refine ⟨13023431934444477723634055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 138916607300741095718763253 13023431934444477723634055)
            ·
              refine ⟨19535147901666716585451083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13023431934444477723634055 19535147901666716585451083)
              ·
                refine ⟨29302721852500074878176625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19535147901666716585451083 29302721852500074878176625)
                ·
                  refine ⟨21977041389375056158632469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29302721852500074878176625 21977041389375056158632469)
                  ·
                    refine ⟨1030173815126955757435897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21977041389375056158632469 1030173815126955757435897)
                    ·
                      rfl

theorem cell23_6018769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 6].length) (baseStart_6018769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018769 prefixEnd_6018769 := by exact prefixLift 6018769
  have htrace : WordTrace (prefixWord ++ tailWord_6018769) baseStart_6018769 baseEnd_6018769 := by
    simpa [prefixWord, tailWord_6018769, baseEnd_6018769] using wordTrace_append hprefix tailTrace_6018769
  have hstable : (prefixWord ++ tailWord_6018769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018769).length < 2 ^ (prefixWord ++ tailWord_6018769).sum := by decide
  have hdescent : baseEnd_6018769 < baseStart_6018769 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018789 : List Nat := [1, 3, 1, 4, 1, 1, 1, 2, 1, 4, 4]
def baseStart_6018789 : Nat := 118140960795 + 6018789 * 2 ^ 59
def prefixEnd_6018789 : Nat := 4983230072969 + 3 ^ 40 * 6018789 * 2
def baseEnd_6018789 : Nat := 3090531714993957194057599

theorem tailTrace_6018789 : CollatzResearch.WordTrace tailWord_6018789 prefixEnd_6018789 3090531714993957194057599 := by
  unfold tailWord_6018789
  simp only [CollatzResearch.WordTrace]
  refine ⟨219523269391962855168835421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146348846261308570112556947 219523269391962855168835421)
  ·
    refine ⟨82321226021986070688313283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219523269391962855168835421 82321226021986070688313283)
    ·
      refine ⟨123481839032979106032469925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82321226021986070688313283 123481839032979106032469925)
      ·
        refine ⟨23152844818683582381088111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123481839032979106032469925 23152844818683582381088111)
        ·
          refine ⟨34729267228025373571632167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23152844818683582381088111 34729267228025373571632167)
          ·
            refine ⟨52093900842038060357448251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34729267228025373571632167 52093900842038060357448251)
            ·
              refine ⟨78140851263057090536172377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52093900842038060357448251 78140851263057090536172377)
              ·
                refine ⟨58605638447292817902129283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78140851263057090536172377 58605638447292817902129283)
                ·
                  refine ⟨87908457670939226853193925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58605638447292817902129283 87908457670939226853193925)
                  ·
                    refine ⟨16482835813301105034973861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 87908457670939226853193925 16482835813301105034973861)
                    ·
                      refine ⟨3090531714993957194057599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16482835813301105034973861 3090531714993957194057599)
                      ·
                        rfl

theorem cell23_6018789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_6018789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018789 prefixEnd_6018789 := by exact prefixLift 6018789
  have htrace : WordTrace (prefixWord ++ tailWord_6018789) baseStart_6018789 baseEnd_6018789 := by
    simpa [prefixWord, tailWord_6018789, baseEnd_6018789] using wordTrace_append hprefix tailTrace_6018789
  have hstable : (prefixWord ++ tailWord_6018789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018789).length < 2 ^ (prefixWord ++ tailWord_6018789).sum := by decide
  have hdescent : baseEnd_6018789 < baseStart_6018789 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018797 : List Nat := [1, 5, 1, 2, 1, 4, 2, 1, 1, 3, 2]
def baseStart_6018797 : Nat := 118140960795 + 6018797 * 2 ^ 59
def prefixEnd_6018797 : Nat := 4983230072969 + 3 ^ 40 * 6018797 * 2
def baseEnd_6018797 : Nat := 3090535822839193162757563

theorem tailTrace_6018797 : CollatzResearch.WordTrace tailWord_6018797 prefixEnd_6018797 3090535822839193162757563 := by
  unfold tailWord_6018797
  simp only [CollatzResearch.WordTrace]
  refine ⟨219523561175933872535126645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146349040783955915023417763 219523561175933872535126645)
  ·
    refine ⟨20580333860243800550168123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 219523561175933872535126645 20580333860243800550168123)
    ·
      refine ⟨30870500790365700825252185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20580333860243800550168123 30870500790365700825252185)
      ·
        refine ⟨23152875592774275618939139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30870500790365700825252185 23152875592774275618939139)
        ·
          refine ⟨34729313389161413428408709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23152875592774275618939139 34729313389161413428408709)
          ·
            refine ⟨6511746260467765017826633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34729313389161413428408709 6511746260467765017826633)
            ·
              refine ⟨4883809695350823763369975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6511746260467765017826633 4883809695350823763369975)
              ·
                refine ⟨7325714543026235645054963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4883809695350823763369975 7325714543026235645054963)
                ·
                  refine ⟨10988571814539353467582445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7325714543026235645054963 10988571814539353467582445)
                  ·
                    refine ⟨4120714430452257550343417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10988571814539353467582445 4120714430452257550343417)
                    ·
                      refine ⟨3090535822839193162757563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4120714430452257550343417 3090535822839193162757563)
                      ·
                        rfl

theorem cell23_6018797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_6018797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018797 prefixEnd_6018797 := by exact prefixLift 6018797
  have htrace : WordTrace (prefixWord ++ tailWord_6018797) baseStart_6018797 baseEnd_6018797 := by
    simpa [prefixWord, tailWord_6018797, baseEnd_6018797] using wordTrace_append hprefix tailTrace_6018797
  have hstable : (prefixWord ++ tailWord_6018797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018797).length < 2 ^ (prefixWord ++ tailWord_6018797).sum := by decide
  have hdescent : baseEnd_6018797 < baseStart_6018797 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018804 : List Nat := [2, 6, 1, 1, 1, 3, 1, 2, 2, 1, 3]
def baseStart_6018804 : Nat := 118140960795 + 6018804 * 2 ^ 59
def prefixEnd_6018804 : Nat := 4983230072969 + 3 ^ 40 * 6018804 * 2
def baseEnd_6018804 : Nat := 3090539417203774635370031

theorem tailTrace_6018804 : CollatzResearch.WordTrace tailWord_6018804 prefixEnd_6018804 3090539417203774635370031 := by
  unfold tailWord_6018804
  simp only [CollatzResearch.WordTrace]
  refine ⟨109761908243454256365315733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146349210991272341820420977 109761908243454256365315733)
  ·
    refine ⟨5145089448911918267124175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 109761908243454256365315733 5145089448911918267124175)
    ·
      refine ⟨7717634173367877400686263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5145089448911918267124175 7717634173367877400686263)
      ·
        refine ⟨11576451260051816101029395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7717634173367877400686263 11576451260051816101029395)
        ·
          refine ⟨17364676890077724151544093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11576451260051816101029395 17364676890077724151544093)
          ·
            refine ⟨6511753833779146556829035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17364676890077724151544093 6511753833779146556829035)
            ·
              refine ⟨9767630750668719835243553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6511753833779146556829035 9767630750668719835243553)
              ·
                refine ⟨7325723063001539876432665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9767630750668719835243553 7325723063001539876432665)
                ·
                  refine ⟨5494292297251154907324499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7325723063001539876432665 5494292297251154907324499)
                  ·
                    refine ⟨8241438445876732360986749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5494292297251154907324499 8241438445876732360986749)
                    ·
                      refine ⟨3090539417203774635370031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8241438445876732360986749 3090539417203774635370031)
                      ·
                        rfl

theorem cell23_6018804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_6018804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018804 prefixEnd_6018804 := by exact prefixLift 6018804
  have htrace : WordTrace (prefixWord ++ tailWord_6018804) baseStart_6018804 baseEnd_6018804 := by
    simpa [prefixWord, tailWord_6018804, baseEnd_6018804] using wordTrace_append hprefix tailTrace_6018804
  have hstable : (prefixWord ++ tailWord_6018804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018804).length < 2 ^ (prefixWord ++ tailWord_6018804).sum := by decide
  have hdescent : baseEnd_6018804 < baseStart_6018804 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018806 : List Nat := [5, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4]
def baseStart_6018806 : Nat := 118140960795 + 6018806 * 2 ^ 59
def prefixEnd_6018806 : Nat := 4983230072969 + 3 ^ 40 * 6018806 * 2
def baseEnd_6018806 : Nat := 3090540444165083627545021

theorem tailTrace_6018806 : CollatzResearch.WordTrace tailWord_6018806 prefixEnd_6018806 3090540444165083627545021 := by
  unfold tailWord_6018806
  simp only [CollatzResearch.WordTrace]
  refine ⟨13720243089556329192012767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 146349259621934178048136181 13720243089556329192012767)
  ·
    refine ⟨20580364634334493788019151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13720243089556329192012767 20580364634334493788019151)
    ·
      refine ⟨30870546951501740682028727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20580364634334493788019151 30870546951501740682028727)
      ·
        refine ⟨46305820427252611023043091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30870546951501740682028727 46305820427252611023043091)
        ·
          refine ⟨69458730640878916534564637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46305820427252611023043091 69458730640878916534564637)
          ·
            refine ⟨26047023990329593700461739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69458730640878916534564637 26047023990329593700461739)
            ·
              refine ⟨39070535985494390550692609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26047023990329593700461739 39070535985494390550692609)
              ·
                refine ⟨29302901989120792913019457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39070535985494390550692609 29302901989120792913019457)
                ·
                  refine ⟨21977176491840594684764593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29302901989120792913019457 21977176491840594684764593)
                  ·
                    refine ⟨16482882368880446013573445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21977176491840594684764593 16482882368880446013573445)
                    ·
                      refine ⟨3090540444165083627545021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16482882368880446013573445 3090540444165083627545021)
                      ·
                        rfl

theorem cell23_6018806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_6018806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018806 prefixEnd_6018806 := by exact prefixLift 6018806
  have htrace : WordTrace (prefixWord ++ tailWord_6018806) baseStart_6018806 baseEnd_6018806 := by
    simpa [prefixWord, tailWord_6018806, baseEnd_6018806] using wordTrace_append hprefix tailTrace_6018806
  have hstable : (prefixWord ++ tailWord_6018806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018806).length < 2 ^ (prefixWord ++ tailWord_6018806).sum := by decide
  have hdescent : baseEnd_6018806 < baseStart_6018806 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018826 : List Nat := [3, 1, 2, 2, 1, 3, 2, 1, 2, 3, 3]
def baseStart_6018826 : Nat := 118140960795 + 6018826 * 2 ^ 59
def prefixEnd_6018826 : Nat := 4983230072969 + 3 ^ 40 * 6018826 * 2
def baseEnd_6018826 : Nat := 3090550713778173549294929

theorem tailTrace_6018826 : CollatzResearch.WordTrace tailWord_6018826 prefixEnd_6018826 3090550713778173549294929 := by
  unfold tailWord_6018826
  simp only [CollatzResearch.WordTrace]
  refine ⟨54881154723207202621983083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146349745928552540325288221 54881154723207202621983083)
  ·
    refine ⟨82321732084810803932974625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54881154723207202621983083 82321732084810803932974625)
    ·
      refine ⟨61741299063608102949730969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82321732084810803932974625 61741299063608102949730969)
      ·
        refine ⟨46305974297706077212298227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61741299063608102949730969 46305974297706077212298227)
        ·
          refine ⟨69458961446559115818447341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46305974297706077212298227 69458961446559115818447341)
          ·
            refine ⟨26047110542459668431917753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69458961446559115818447341 26047110542459668431917753)
            ·
              refine ⟨19535332906844751323938315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26047110542459668431917753 19535332906844751323938315)
              ·
                refine ⟨29302999360267126985907473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19535332906844751323938315 29302999360267126985907473)
                ·
                  refine ⟨21977249520200345239430605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29302999360267126985907473 21977249520200345239430605)
                  ·
                    refine ⟨8241468570075129464786477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21977249520200345239430605 8241468570075129464786477)
                    ·
                      refine ⟨3090550713778173549294929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8241468570075129464786477 3090550713778173549294929)
                      ·
                        rfl

theorem cell23_6018826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_6018826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018826 prefixEnd_6018826 := by exact prefixLift 6018826
  have htrace : WordTrace (prefixWord ++ tailWord_6018826) baseStart_6018826 baseEnd_6018826 := by
    simpa [prefixWord, tailWord_6018826, baseEnd_6018826] using wordTrace_append hprefix tailTrace_6018826
  have hstable : (prefixWord ++ tailWord_6018826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018826).length < 2 ^ (prefixWord ++ tailWord_6018826).sum := by decide
  have hdescent : baseEnd_6018826 < baseStart_6018826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018866 : List Nat := [3, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4]
def baseStart_6018866 : Nat := 118140960795 + 6018866 * 2 ^ 59
def prefixEnd_6018866 : Nat := 4983230072969 + 3 ^ 40 * 6018866 * 2
def baseEnd_6018866 : Nat := 3090571253004353392794745

theorem tailTrace_6018866 : CollatzResearch.WordTrace tailWord_6018866 prefixEnd_6018866 3090571253004353392794745 := by
  unfold tailWord_6018866
  simp only [CollatzResearch.WordTrace]
  refine ⟨54881519453170974329847113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146350718541789264879592301 54881519453170974329847113)
  ·
    refine ⟨41161139589878230747385335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54881519453170974329847113 41161139589878230747385335)
    ·
      refine ⟨61741709384817346121078003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41161139589878230747385335 61741709384817346121078003)
      ·
        refine ⟨92612564077226019181617005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61741709384817346121078003 92612564077226019181617005)
        ·
          refine ⟨34729711528959757193106377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92612564077226019181617005 34729711528959757193106377)
          ·
            refine ⟨26047283646719817894829783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34729711528959757193106377 26047283646719817894829783)
            ·
              refine ⟨39070925470079726842244675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26047283646719817894829783 39070925470079726842244675)
              ·
                refine ⟨58606388205119590263367013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39070925470079726842244675 58606388205119590263367013)
                ·
                  refine ⟨10988697788459923174381315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58606388205119590263367013 10988697788459923174381315)
                  ·
                    refine ⟨16483046682689884761571973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10988697788459923174381315 16483046682689884761571973)
                    ·
                      refine ⟨3090571253004353392794745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16483046682689884761571973 3090571253004353392794745)
                      ·
                        rfl

theorem cell23_6018866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_6018866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018866 prefixEnd_6018866 := by exact prefixLift 6018866
  have htrace : WordTrace (prefixWord ++ tailWord_6018866) baseStart_6018866 baseEnd_6018866 := by
    simpa [prefixWord, tailWord_6018866, baseEnd_6018866] using wordTrace_append hprefix tailTrace_6018866
  have hstable : (prefixWord ++ tailWord_6018866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018866).length < 2 ^ (prefixWord ++ tailWord_6018866).sum := by decide
  have hdescent : baseEnd_6018866 < baseStart_6018866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018873 : List Nat := [1, 2, 1, 7, 1, 1, 1, 1, 1, 2, 5]
def baseStart_6018873 : Nat := 118140960795 + 6018873 * 2 ^ 59
def prefixEnd_6018873 : Nat := 4983230072969 + 3 ^ 40 * 6018873 * 2
def baseEnd_6018873 : Nat := 3090574847368934865407213

theorem tailTrace_6018873 : CollatzResearch.WordTrace tailWord_6018873 prefixEnd_6018873 3090574847368934865407213 := by
  unfold tailWord_6018873
  simp only [CollatzResearch.WordTrace]
  refine ⟨219526333123658537514893273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146350888749105691676595515 219526333123658537514893273)
  ·
    refine ⟨164644749842743903136169955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219526333123658537514893273 164644749842743903136169955)
    ·
      refine ⟨246967124764115854704254933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164644749842743903136169955 246967124764115854704254933)
      ·
        refine ⟨5788291986658965344630975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 246967124764115854704254933 5788291986658965344630975)
        ·
          refine ⟨8682437979988448016946463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5788291986658965344630975 8682437979988448016946463)
          ·
            refine ⟨13023656969982672025419695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8682437979988448016946463 13023656969982672025419695)
            ·
              refine ⟨19535485454974008038129543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13023656969982672025419695 19535485454974008038129543)
              ·
                refine ⟨29303228182461012057194315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19535485454974008038129543 29303228182461012057194315)
                ·
                  refine ⟨43954842273691518085791473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29303228182461012057194315 43954842273691518085791473)
                  ·
                    refine ⟨32966131705268638564343605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43954842273691518085791473 32966131705268638564343605)
                    ·
                      refine ⟨3090574847368934865407213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32966131705268638564343605 3090574847368934865407213)
                      ·
                        rfl

theorem cell23_6018873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_6018873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018873 prefixEnd_6018873 := by exact prefixLift 6018873
  have htrace : WordTrace (prefixWord ++ tailWord_6018873) baseStart_6018873 baseEnd_6018873 := by
    simpa [prefixWord, tailWord_6018873, baseEnd_6018873] using wordTrace_append hprefix tailTrace_6018873
  have hstable : (prefixWord ++ tailWord_6018873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018873).length < 2 ^ (prefixWord ++ tailWord_6018873).sum := by decide
  have hdescent : baseEnd_6018873 < baseStart_6018873 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018967 : List Nat := [1, 1, 3, 3, 1, 4, 2, 3, 1, 1, 3]
def baseStart_6018967 : Nat := 118140960795 + 6018967 * 2 ^ 59
def prefixEnd_6018967 : Nat := 4983230072969 + 3 ^ 40 * 6018967 * 2
def baseEnd_6018967 : Nat := 3090623114550457497631781

theorem tailTrace_6018967 : CollatzResearch.WordTrace tailWord_6018967 prefixEnd_6018967 3090623114550457497631781 := by
  unfold tailWord_6018967
  simp only [CollatzResearch.WordTrace]
  refine ⟨219529761585317991568815155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146353174390211994379210103 219529761585317991568815155)
  ·
    refine ⟨329294642377976987353222733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219529761585317991568815155 329294642377976987353222733)
    ·
      refine ⟨123485490891741370257458525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 329294642377976987353222733 123485490891741370257458525)
      ·
        refine ⟨46307059084403013846546947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123485490891741370257458525 46307059084403013846546947)
        ·
          refine ⟨69460588626604520769820421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46307059084403013846546947 69460588626604520769820421)
          ·
            refine ⟨13023860367488347644341329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69460588626604520769820421 13023860367488347644341329)
            ·
              refine ⟨9767895275616260733255997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13023860367488347644341329 9767895275616260733255997)
              ·
                refine ⟨3662960728356097774970999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9767895275616260733255997 3662960728356097774970999)
                ·
                  refine ⟨5494441092534146662456499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3662960728356097774970999 5494441092534146662456499)
                  ·
                    refine ⟨8241661638801219993684749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5494441092534146662456499 8241661638801219993684749)
                    ·
                      refine ⟨3090623114550457497631781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8241661638801219993684749 3090623114550457497631781)
                      ·
                        rfl

theorem cell23_6018967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 3, 1, 1, 3].length) (baseStart_6018967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018967 prefixEnd_6018967 := by exact prefixLift 6018967
  have htrace : WordTrace (prefixWord ++ tailWord_6018967) baseStart_6018967 baseEnd_6018967 := by
    simpa [prefixWord, tailWord_6018967, baseEnd_6018967] using wordTrace_append hprefix tailTrace_6018967
  have hstable : (prefixWord ++ tailWord_6018967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018967).length < 2 ^ (prefixWord ++ tailWord_6018967).sum := by decide
  have hdescent : baseEnd_6018967 < baseStart_6018967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018970 : List Nat := [3, 1, 1, 4, 2, 1, 4, 1, 1, 5]
def baseStart_6018970 : Nat := 118140960795 + 6018970 * 2 ^ 59
def prefixEnd_6018970 : Nat := 4983230072969 + 3 ^ 40 * 6018970 * 2
def baseEnd_6018970 : Nat := 1030208218330806995298089

theorem tailTrace_6018970 : CollatzResearch.WordTrace tailWord_6018970 prefixEnd_6018970 1030208218330806995298089 := by
  unfold tailWord_6018970
  simp only [CollatzResearch.WordTrace]
  refine ⟨54882467751076780770293591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146353247336204748720782909 54882467751076780770293591)
  ·
    refine ⟨82323701626615171155440387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54882467751076780770293591 82323701626615171155440387)
    ·
      refine ⟨123485552439922756733160581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82323701626615171155440387 123485552439922756733160581)
      ·
        refine ⟨23153541082485516887467609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123485552439922756733160581 23153541082485516887467609)
        ·
          refine ⟨17365155811864137665600707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23153541082485516887467609 17365155811864137665600707)
          ·
            refine ⟨26047733717796206498401061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17365155811864137665600707 26047733717796206498401061)
            ·
              refine ⟨4883950072086788718450199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26047733717796206498401061 4883950072086788718450199)
              ·
                refine ⟨7325925108130183077675299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4883950072086788718450199 7325925108130183077675299)
                ·
                  refine ⟨10988887662195274616512949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7325925108130183077675299 10988887662195274616512949)
                  ·
                    refine ⟨1030208218330806995298089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10988887662195274616512949 1030208218330806995298089)
                    ·
                      rfl

theorem cell23_6018970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 1, 1, 5].length) (baseStart_6018970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018970 prefixEnd_6018970 := by exact prefixLift 6018970
  have htrace : WordTrace (prefixWord ++ tailWord_6018970) baseStart_6018970 baseEnd_6018970 := by
    simpa [prefixWord, tailWord_6018970, baseEnd_6018970] using wordTrace_append hprefix tailTrace_6018970
  have hstable : (prefixWord ++ tailWord_6018970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018970).length < 2 ^ (prefixWord ++ tailWord_6018970).sum := by decide
  have hdescent : baseEnd_6018970 < baseStart_6018970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018974 : List Nat := [4, 3, 1, 3, 2, 1, 1, 2, 6]
def baseStart_6018974 : Nat := 118140960795 + 6018974 * 2 ^ 59
def prefixEnd_6018974 : Nat := 4983230072969 + 3 ^ 40 * 6018974 * 2
def baseEnd_6018974 : Nat := 343402967657226552249361

theorem tailTrace_6018974 : CollatzResearch.WordTrace tailWord_6018974 prefixEnd_6018974 343402967657226552249361 := by
  unfold tailWord_6018974
  simp only [CollatzResearch.WordTrace]
  refine ⟨27441252112036578970539997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146353344597528421176213317 27441252112036578970539997)
  ·
    refine ⟨10290469542013717113952499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27441252112036578970539997 10290469542013717113952499)
    ·
      refine ⟨15435704313020575670928749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10290469542013717113952499 15435704313020575670928749)
      ·
        refine ⟨5788389117382715876598281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15435704313020575670928749 5788389117382715876598281)
        ·
          refine ⟨4341291838037036907448711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5788389117382715876598281 4341291838037036907448711)
          ·
            refine ⟨6511937757055555361173067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4341291838037036907448711 6511937757055555361173067)
            ·
              refine ⟨9767906635583333041759601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6511937757055555361173067 9767906635583333041759601)
              ·
                refine ⟨7325929976687499781319701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9767906635583333041759601 7325929976687499781319701)
                ·
                  refine ⟨343402967657226552249361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7325929976687499781319701 343402967657226552249361)
                  ·
                    rfl

theorem cell23_6018974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_6018974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018974 prefixEnd_6018974 := by exact prefixLift 6018974
  have htrace : WordTrace (prefixWord ++ tailWord_6018974) baseStart_6018974 baseEnd_6018974 := by
    simpa [prefixWord, tailWord_6018974, baseEnd_6018974] using wordTrace_append hprefix tailTrace_6018974
  have hstable : (prefixWord ++ tailWord_6018974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018974).length < 2 ^ (prefixWord ++ tailWord_6018974).sum := by decide
  have hdescent : baseEnd_6018974 < baseStart_6018974 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018976 : List Nat := [2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 5]
def baseStart_6018976 : Nat := 118140960795 + 6018976 * 2 ^ 59
def prefixEnd_6018976 : Nat := 4983230072969 + 3 ^ 40 * 6018976 * 2
def baseEnd_6018976 : Nat := 3090627735876347962419239

theorem tailTrace_6018976 : CollatzResearch.WordTrace tailWord_6018976 prefixEnd_6018976 3090627735876347962419239 := by
  unfold tailWord_6018976
  simp only [CollatzResearch.WordTrace]
  refine ⟨109765044921142693052946391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146353393228190257403928521 109765044921142693052946391)
  ·
    refine ⟨164647567381714039579419587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109765044921142693052946391 164647567381714039579419587)
    ·
      refine ⟨246971351072571059369129381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164647567381714039579419587 246971351072571059369129381)
      ·
        refine ⟨46307128326107073631711759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 246971351072571059369129381 46307128326107073631711759)
        ·
          refine ⟨69460692489160610447567639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46307128326107073631711759 69460692489160610447567639)
          ·
            refine ⟨104191038733740915671351459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69460692489160610447567639 104191038733740915671351459)
            ·
              refine ⟨156286558100611373507027189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104191038733740915671351459 156286558100611373507027189)
              ·
                refine ⟨14651864821932316266283799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 156286558100611373507027189 14651864821932316266283799)
                ·
                  refine ⟨21977797232898474399425699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14651864821932316266283799 21977797232898474399425699)
                  ·
                    refine ⟨32966695849347711599138549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21977797232898474399425699 32966695849347711599138549)
                    ·
                      refine ⟨3090627735876347962419239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32966695849347711599138549 3090627735876347962419239)
                      ·
                        rfl

theorem cell23_6018976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_6018976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018976 prefixEnd_6018976 := by exact prefixLift 6018976
  have htrace : WordTrace (prefixWord ++ tailWord_6018976) baseStart_6018976 baseEnd_6018976 := by
    simpa [prefixWord, tailWord_6018976, baseEnd_6018976] using wordTrace_append hprefix tailTrace_6018976
  have hstable : (prefixWord ++ tailWord_6018976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018976).length < 2 ^ (prefixWord ++ tailWord_6018976).sum := by decide
  have hdescent : baseEnd_6018976 < baseStart_6018976 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018984 : List Nat := [2, 1, 6, 2, 1, 1, 2, 1, 3, 1, 3]
def baseStart_6018984 : Nat := 118140960795 + 6018984 * 2 ^ 59
def prefixEnd_6018984 : Nat := 4983230072969 + 3 ^ 40 * 6018984 * 2
def baseEnd_6018984 : Nat := 3090631843721583931119203

theorem tailTrace_6018984 : CollatzResearch.WordTrace tailWord_6018984 prefixEnd_6018984 3090631843721583931119203 := by
  unfold tailWord_6018984
  simp only [CollatzResearch.WordTrace]
  refine ⟨109765190813128201736092003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146353587750837602314789337 109765190813128201736092003)
  ·
    refine ⟨164647786219692302604138005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109765190813128201736092003 164647786219692302604138005)
    ·
      refine ⟨7717864979048076684568969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 164647786219692302604138005 7717864979048076684568969)
      ·
        refine ⟨5788398734286057513426727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7717864979048076684568969 5788398734286057513426727)
        ·
          refine ⟨8682598101429086270140091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5788398734286057513426727 8682598101429086270140091)
          ·
            refine ⟨13023897152143629405210137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8682598101429086270140091 13023897152143629405210137)
            ·
              refine ⟨9767922864107722053907603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13023897152143629405210137 9767922864107722053907603)
              ·
                refine ⟨14651884296161583080861405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9767922864107722053907603 14651884296161583080861405)
                ·
                  refine ⟨5494456611060593655323027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14651884296161583080861405 5494456611060593655323027)
                  ·
                    refine ⟨8241684916590890482984541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5494456611060593655323027 8241684916590890482984541)
                    ·
                      refine ⟨3090631843721583931119203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8241684916590890482984541 3090631843721583931119203)
                      ·
                        rfl

theorem cell23_6018984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_6018984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018984 prefixEnd_6018984 := by exact prefixLift 6018984
  have htrace : WordTrace (prefixWord ++ tailWord_6018984) baseStart_6018984 baseEnd_6018984 := by
    simpa [prefixWord, tailWord_6018984, baseEnd_6018984] using wordTrace_append hprefix tailTrace_6018984
  have hstable : (prefixWord ++ tailWord_6018984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018984).length < 2 ^ (prefixWord ++ tailWord_6018984).sum := by decide
  have hdescent : baseEnd_6018984 < baseStart_6018984 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6018993 : List Nat := [1, 2, 2, 4, 2, 2, 1, 2, 1, 1, 5]
def baseStart_6018993 : Nat := 118140960795 + 6018993 * 2 ^ 59
def prefixEnd_6018993 : Nat := 4983230072969 + 3 ^ 40 * 6018993 * 2
def baseEnd_6018993 : Nat := 3090636465047474395906661

theorem tailTrace_6018993 : CollatzResearch.WordTrace tailWord_6018993 prefixEnd_6018993 3090636465047474395906661 := by
  unfold tailWord_6018993
  simp only [CollatzResearch.WordTrace]
  refine ⟨219530709883223798009261633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146353806588815865339507755 219530709883223798009261633)
  ·
    refine ⟨164648032412417848506946225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219530709883223798009261633 164648032412417848506946225)
    ·
      refine ⟨123486024309313386380209669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164648032412417848506946225 123486024309313386380209669)
      ·
        refine ⟨23153629557996259946289313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123486024309313386380209669 23153629557996259946289313)
        ·
          refine ⟨17365222168497194959716985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23153629557996259946289313 17365222168497194959716985)
          ·
            refine ⟨13023916626372896219787739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17365222168497194959716985 13023916626372896219787739)
            ·
              refine ⟨19535874939559344329681609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13023916626372896219787739 19535874939559344329681609)
              ·
                refine ⟨14651906204669508247261207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19535874939559344329681609 14651906204669508247261207)
                ·
                  refine ⟨21977859307004262370891811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14651906204669508247261207 21977859307004262370891811)
                  ·
                    refine ⟨32966788960506393556337717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21977859307004262370891811 32966788960506393556337717)
                    ·
                      refine ⟨3090636465047474395906661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32966788960506393556337717 3090636465047474395906661)
                      ·
                        rfl

theorem cell23_6018993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_6018993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6018993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6018993 prefixEnd_6018993 := by exact prefixLift 6018993
  have htrace : WordTrace (prefixWord ++ tailWord_6018993) baseStart_6018993 baseEnd_6018993 := by
    simpa [prefixWord, tailWord_6018993, baseEnd_6018993] using wordTrace_append hprefix tailTrace_6018993
  have hstable : (prefixWord ++ tailWord_6018993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6018993).length < 2 ^ (prefixWord ++ tailWord_6018993).sum := by decide
  have hdescent : baseEnd_6018993 < baseStart_6018993 := by decide
  rcases family_descends (prefixWord ++ tailWord_6018993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019000 : List Nat := [2, 1, 2, 1, 2, 3, 5, 1, 2, 4]
def baseStart_6019000 : Nat := 118140960795 + 6019000 * 2 ^ 59
def prefixEnd_6019000 : Nat := 4983230072969 + 3 ^ 40 * 6019000 * 2
def baseEnd_6019000 : Nat := 1030213353137351956173043

theorem tailTrace_6019000 : CollatzResearch.WordTrace tailWord_6019000 prefixEnd_6019000 1030213353137351956173043 := by
  unfold tailWord_6019000
  simp only [CollatzResearch.WordTrace]
  refine ⟨109765482597099219102383227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146353976796132292136510969 109765482597099219102383227)
  ·
    refine ⟨164648223895648828653574841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109765482597099219102383227 164648223895648828653574841)
    ·
      refine ⟨123486167921736621490181131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164648223895648828653574841 123486167921736621490181131)
      ·
        refine ⟨185229251882604932235271697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123486167921736621490181131 185229251882604932235271697)
        ·
          refine ⟨138921938911953699176453773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185229251882604932235271697 138921938911953699176453773)
          ·
            refine ⟨52095727091982637191170165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138921938911953699176453773 52095727091982637191170165)
            ·
              refine ⟨4883974414873372236672203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52095727091982637191170165 4883974414873372236672203)
              ·
                refine ⟨7325961622310058355008305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4883974414873372236672203 7325961622310058355008305)
                ·
                  refine ⟨5494471216732543766256229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7325961622310058355008305 5494471216732543766256229)
                  ·
                    refine ⟨1030213353137351956173043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5494471216732543766256229 1030213353137351956173043)
                    ·
                      rfl

theorem cell23_6019000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 1, 2, 4].length) (baseStart_6019000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019000 prefixEnd_6019000 := by exact prefixLift 6019000
  have htrace : WordTrace (prefixWord ++ tailWord_6019000) baseStart_6019000 baseEnd_6019000 := by
    simpa [prefixWord, tailWord_6019000, baseEnd_6019000] using wordTrace_append hprefix tailTrace_6019000
  have hstable : (prefixWord ++ tailWord_6019000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019000).length < 2 ^ (prefixWord ++ tailWord_6019000).sum := by decide
  have hdescent : baseEnd_6019000 < baseStart_6019000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019023 : List Nat := [1, 1, 2, 1, 1, 5, 1, 1, 6, 1, 3]
def baseStart_6019023 : Nat := 118140960795 + 6019023 * 2 ^ 59
def prefixEnd_6019023 : Nat := 4983230072969 + 3 ^ 40 * 6019023 * 2
def baseEnd_6019023 : Nat := 3090651869467109278531523

theorem tailTrace_6019023 : CollatzResearch.WordTrace tailWord_6019023 prefixEnd_6019023 3090651869467109278531523 := by
  unfold tailWord_6019023
  simp only [CollatzResearch.WordTrace]
  refine ⟨219531804073115113132853723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146354536048743408755235815 219531804073115113132853723)
  ·
    refine ⟨329297706109672669699280585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219531804073115113132853723 329297706109672669699280585)
    ·
      refine ⟨246973279582254502274460439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329297706109672669699280585 246973279582254502274460439)
      ·
        refine ⟨370459919373381753411690659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246973279582254502274460439 370459919373381753411690659)
        ·
          refine ⟨555689879060072630117535989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 370459919373381753411690659 555689879060072630117535989)
          ·
            refine ⟨52095926161881809073518999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 555689879060072630117535989 52095926161881809073518999)
            ·
              refine ⟨78143889242822713610278499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52095926161881809073518999 78143889242822713610278499)
              ·
                refine ⟨117215833864234070415417749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78143889242822713610278499 117215833864234070415417749)
                ·
                  refine ⟨5494492212385972050722707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 117215833864234070415417749 5494492212385972050722707)
                  ·
                    refine ⟨8241738318578958076084061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5494492212385972050722707 8241738318578958076084061)
                    ·
                      refine ⟨3090651869467109278531523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8241738318578958076084061 3090651869467109278531523)
                      ·
                        rfl

theorem cell23_6019023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 6, 1, 3].length) (baseStart_6019023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019023 prefixEnd_6019023 := by exact prefixLift 6019023
  have htrace : WordTrace (prefixWord ++ tailWord_6019023) baseStart_6019023 baseEnd_6019023 := by
    simpa [prefixWord, tailWord_6019023, baseEnd_6019023] using wordTrace_append hprefix tailTrace_6019023
  have hstable : (prefixWord ++ tailWord_6019023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019023).length < 2 ^ (prefixWord ++ tailWord_6019023).sum := by decide
  have hdescent : baseEnd_6019023 < baseStart_6019023 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019030 : List Nat := [5, 2, 1, 1, 3, 2, 9]
def baseStart_6019030 : Nat := 118140960795 + 6019030 * 2 ^ 59
def prefixEnd_6019030 : Nat := 4983230072969 + 3 ^ 40 * 6019030 * 2
def baseEnd_6019030 : Nat := 38156240294218404335111

theorem tailTrace_6019030 : CollatzResearch.WordTrace tailWord_6019030 prefixEnd_6019030 38156240294218404335111 := by
  unfold tailWord_6019030
  simp only [CollatzResearch.WordTrace]
  refine ⟨13720753711505609583022409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 146354706256059835552239029 13720753711505609583022409)
  ·
    refine ⟨10290565283629207187266807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13720753711505609583022409 10290565283629207187266807)
    ·
      refine ⟨15435847925443810780900211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10290565283629207187266807 15435847925443810780900211)
      ·
        refine ⟨23153771888165716171350317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15435847925443810780900211 23153771888165716171350317)
        ·
          refine ⟨8682664458062143564256369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23153771888165716171350317 8682664458062143564256369)
          ·
            refine ⟨6511998343546607673192277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8682664458062143564256369 6511998343546607673192277)
            ·
              refine ⟨38156240294218404335111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6511998343546607673192277 38156240294218404335111)
              ·
                rfl

theorem cell23_6019030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 9].length) (baseStart_6019030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019030 prefixEnd_6019030 := by exact prefixLift 6019030
  have htrace : WordTrace (prefixWord ++ tailWord_6019030) baseStart_6019030 baseEnd_6019030 := by
    simpa [prefixWord, tailWord_6019030, baseEnd_6019030] using wordTrace_append hprefix tailTrace_6019030
  have hstable : (prefixWord ++ tailWord_6019030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019030).length < 2 ^ (prefixWord ++ tailWord_6019030).sum := by decide
  have hdescent : baseEnd_6019030 < baseStart_6019030 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019050 : List Nat := [3, 1, 3, 1, 2, 1, 2, 2, 3, 3, 2]
def baseStart_6019050 : Nat := 118140960795 + 6019050 * 2 ^ 59
def prefixEnd_6019050 : Nat := 4983230072969 + 3 ^ 40 * 6019050 * 2
def baseEnd_6019050 : Nat := 3090665733444780672893899

theorem tailTrace_6019050 : CollatzResearch.WordTrace tailWord_6019050 prefixEnd_6019050 3090665733444780672893899 := by
  unfold tailWord_6019050
  simp only [CollatzResearch.WordTrace]
  refine ⟨54883197211004324186021651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146355192562678197829391069 54883197211004324186021651)
  ·
    refine ⟨82324795816506486279032477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54883197211004324186021651 82324795816506486279032477)
    ·
      refine ⟨30871798431189932354637179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82324795816506486279032477 30871798431189932354637179)
      ·
        refine ⟨46307697646784898531955769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30871798431189932354637179 46307697646784898531955769)
        ·
          refine ⟨34730773235088673898966827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46307697646784898531955769 34730773235088673898966827)
          ·
            refine ⟨52096159852633010848450241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34730773235088673898966827 52096159852633010848450241)
            ·
              refine ⟨39072119889474758136337681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52096159852633010848450241 39072119889474758136337681)
              ·
                refine ⟨29304089917106068602253261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39072119889474758136337681 29304089917106068602253261)
                ·
                  refine ⟨10989033718914775725844973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29304089917106068602253261 10989033718914775725844973)
                  ·
                    refine ⟨4120887644593040897191865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10989033718914775725844973 4120887644593040897191865)
                    ·
                      refine ⟨3090665733444780672893899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4120887644593040897191865 3090665733444780672893899)
                      ·
                        rfl

theorem cell23_6019050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 3, 3, 2].length) (baseStart_6019050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019050 prefixEnd_6019050 := by exact prefixLift 6019050
  have htrace : WordTrace (prefixWord ++ tailWord_6019050) baseStart_6019050 baseEnd_6019050 := by
    simpa [prefixWord, tailWord_6019050, baseEnd_6019050] using wordTrace_append hprefix tailTrace_6019050
  have hstable : (prefixWord ++ tailWord_6019050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019050).length < 2 ^ (prefixWord ++ tailWord_6019050).sum := by decide
  have hdescent : baseEnd_6019050 < baseStart_6019050 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019056 : List Nat := [2, 1, 1, 1, 3, 2, 2, 3, 2, 6]
def baseStart_6019056 : Nat := 118140960795 + 6019056 * 2 ^ 59
def prefixEnd_6019056 : Nat := 4983230072969 + 3 ^ 40 * 6019056 * 2
def baseEnd_6019056 : Nat := 1030222938109569216472957

theorem tailTrace_6019056 : CollatzResearch.WordTrace tailWord_6019056 prefixEnd_6019056 1030222938109569216472957 := by
  unfold tailWord_6019056
  simp only [CollatzResearch.WordTrace]
  refine ⟨109766503840997779884402511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146355338454663706512536681 109766503840997779884402511)
  ·
    refine ⟨164649755761496669826603767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109766503840997779884402511 164649755761496669826603767)
    ·
      refine ⟨246974633642245004739905651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164649755761496669826603767 246974633642245004739905651)
      ·
        refine ⟨370461950463367507109858477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246974633642245004739905651 370461950463367507109858477)
        ·
          refine ⟨138923231423762815166196929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 370461950463367507109858477 138923231423762815166196929)
          ·
            refine ⟨104192423567822111374647697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138923231423762815166196929 104192423567822111374647697)
            ·
              refine ⟨78144317675866583530985773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104192423567822111374647697 78144317675866583530985773)
              ·
                refine ⟨29304119128449968824119665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78144317675866583530985773 29304119128449968824119665)
                ·
                  refine ⟨21978089346337476618089749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29304119128449968824119665 21978089346337476618089749)
                  ·
                    refine ⟨1030222938109569216472957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21978089346337476618089749 1030222938109569216472957)
                    ·
                      rfl

theorem cell23_6019056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 2, 6].length) (baseStart_6019056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019056 prefixEnd_6019056 := by exact prefixLift 6019056
  have htrace : WordTrace (prefixWord ++ tailWord_6019056) baseStart_6019056 baseEnd_6019056 := by
    simpa [prefixWord, tailWord_6019056, baseEnd_6019056] using wordTrace_append hprefix tailTrace_6019056
  have hstable : (prefixWord ++ tailWord_6019056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019056).length < 2 ^ (prefixWord ++ tailWord_6019056).sum := by decide
  have hdescent : baseEnd_6019056 < baseStart_6019056 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019057 : List Nat := [1, 2, 2, 2, 5, 1, 1, 3, 2, 1, 3]
def baseStart_6019057 : Nat := 118140960795 + 6019057 * 2 ^ 59
def prefixEnd_6019057 : Nat := 4983230072969 + 3 ^ 40 * 6019057 * 2
def baseEnd_6019057 : Nat := 3090669327809362145506367

theorem tailTrace_6019057 : CollatzResearch.WordTrace tailWord_6019057 prefixEnd_6019057 3090669327809362145506367 := by
  unfold tailWord_6019057
  simp only [CollatzResearch.WordTrace]
  refine ⟨219533044154991936939591425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146355362769994624626394283 219533044154991936939591425)
  ·
    refine ⟨164649783116243952704693569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219533044154991936939591425 164649783116243952704693569)
    ·
      refine ⟨123487337337182964528520177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164649783116243952704693569 123487337337182964528520177)
      ·
        refine ⟨92615503002887223396390133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123487337337182964528520177 92615503002887223396390133)
        ·
          refine ⟨8682703406520677193411575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92615503002887223396390133 8682703406520677193411575)
          ·
            refine ⟨13024055109781015790117363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8682703406520677193411575 13024055109781015790117363)
            ·
              refine ⟨19536082664671523685176045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13024055109781015790117363 19536082664671523685176045)
              ·
                refine ⟨7326030999251821381941017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19536082664671523685176045 7326030999251821381941017)
                ·
                  refine ⟨5494523249438866036455763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7326030999251821381941017 5494523249438866036455763)
                  ·
                    refine ⟨8241784874158299054683645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5494523249438866036455763 8241784874158299054683645)
                    ·
                      refine ⟨3090669327809362145506367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8241784874158299054683645 3090669327809362145506367)
                      ·
                        rfl

theorem cell23_6019057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 3, 2, 1, 3].length) (baseStart_6019057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019057 prefixEnd_6019057 := by exact prefixLift 6019057
  have htrace : WordTrace (prefixWord ++ tailWord_6019057) baseStart_6019057 baseEnd_6019057 := by
    simpa [prefixWord, tailWord_6019057, baseEnd_6019057] using wordTrace_append hprefix tailTrace_6019057
  have hstable : (prefixWord ++ tailWord_6019057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019057).length < 2 ^ (prefixWord ++ tailWord_6019057).sum := by decide
  have hdescent : baseEnd_6019057 < baseStart_6019057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019063 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 7, 4, 2]
def baseStart_6019063 : Nat := 118140960795 + 6019063 * 2 ^ 59
def prefixEnd_6019063 : Nat := 4983230072969 + 3 ^ 40 * 6019063 * 2
def baseEnd_6019063 : Nat := 3090672408693289122031339

theorem tailTrace_6019063 : CollatzResearch.WordTrace tailWord_6019063 prefixEnd_6019063 3090672408693289122031339 := by
  unfold tailWord_6019063
  simp only [CollatzResearch.WordTrace]
  refine ⟨219533262992970199964309843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146355508661980133309539895 219533262992970199964309843)
  ·
    refine ⟨329299894489455299946464765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219533262992970199964309843 329299894489455299946464765)
    ·
      refine ⟨123487460433545737479924287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 329299894489455299946464765 123487460433545737479924287)
      ·
        refine ⟨185231190650318606219886431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123487460433545737479924287 185231190650318606219886431)
        ·
          refine ⟨277846785975477909329829647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185231190650318606219886431 277846785975477909329829647)
          ·
            refine ⟨416770178963216863994744471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277846785975477909329829647 416770178963216863994744471)
            ·
              refine ⟨625155268444825295992116707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 416770178963216863994744471 625155268444825295992116707)
              ·
                refine ⟨937732902667237943988175061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 625155268444825295992116707 937732902667237943988175061)
                ·
                  refine ⟨21978114906263389312222853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 937732902667237943988175061 21978114906263389312222853)
                  ·
                    refine ⟨4120896544924385496041785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21978114906263389312222853 4120896544924385496041785)
                    ·
                      refine ⟨3090672408693289122031339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4120896544924385496041785 3090672408693289122031339)
                      ·
                        rfl

theorem cell23_6019063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 4, 2].length) (baseStart_6019063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019063 prefixEnd_6019063 := by exact prefixLift 6019063
  have htrace : WordTrace (prefixWord ++ tailWord_6019063) baseStart_6019063 baseEnd_6019063 := by
    simpa [prefixWord, tailWord_6019063, baseEnd_6019063] using wordTrace_append hprefix tailTrace_6019063
  have hstable : (prefixWord ++ tailWord_6019063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019063).length < 2 ^ (prefixWord ++ tailWord_6019063).sum := by decide
  have hdescent : baseEnd_6019063 < baseStart_6019063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019078 : List Nat := [6, 2, 1, 2, 2, 1, 1, 1, 1, 1, 5]
def baseStart_6019078 : Nat := 118140960795 + 6019078 * 2 ^ 59
def prefixEnd_6019078 : Nat := 4983230072969 + 3 ^ 40 * 6019078 * 2
def baseEnd_6019078 : Nat := 3090680110903106563343771

theorem tailTrace_6019078 : CollatzResearch.WordTrace tailWord_6019078 prefixEnd_6019078 3090680110903106563343771 := by
  unfold tailWord_6019078
  simp only [CollatzResearch.WordTrace]
  refine ⟨6860431565247370547690809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 146355873391943905017403925 6860431565247370547690809)
  ·
    refine ⟨5145323673935527910768107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6860431565247370547690809 5145323673935527910768107)
    ·
      refine ⟨7717985510903291866152161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5145323673935527910768107 7717985510903291866152161)
      ·
        refine ⟨5788489133177468899614121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7717985510903291866152161 5788489133177468899614121)
        ·
          refine ⟨4341366849883101674710591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5788489133177468899614121 4341366849883101674710591)
          ·
            refine ⟨6512050274824652512065887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4341366849883101674710591 6512050274824652512065887)
            ·
              refine ⟨9768075412236978768098831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6512050274824652512065887 9768075412236978768098831)
              ·
                refine ⟨14652113118355468152148247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9768075412236978768098831 14652113118355468152148247)
                ·
                  refine ⟨21978169677533202228222371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14652113118355468152148247 21978169677533202228222371)
                  ·
                    refine ⟨32967254516299803342333557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21978169677533202228222371 32967254516299803342333557)
                    ·
                      refine ⟨3090680110903106563343771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32967254516299803342333557 3090680110903106563343771)
                      ·
                        rfl

theorem cell23_6019078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_6019078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019078 prefixEnd_6019078 := by exact prefixLift 6019078
  have htrace : WordTrace (prefixWord ++ tailWord_6019078) baseStart_6019078 baseEnd_6019078 := by
    simpa [prefixWord, tailWord_6019078, baseEnd_6019078] using wordTrace_append hprefix tailTrace_6019078
  have hstable : (prefixWord ++ tailWord_6019078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019078).length < 2 ^ (prefixWord ++ tailWord_6019078).sum := by decide
  have hdescent : baseEnd_6019078 < baseStart_6019078 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019080 : List Nat := [2, 1, 3, 2, 1, 2, 3, 2, 1, 4, 2]
def baseStart_6019080 : Nat := 118140960795 + 6019080 * 2 ^ 59
def prefixEnd_6019080 : Nat := 4983230072969 + 3 ^ 40 * 6019080 * 2
def baseEnd_6019080 : Nat := 3090681137864415555518761

theorem tailTrace_6019080 : CollatzResearch.WordTrace tailWord_6019080 prefixEnd_6019080 3090681137864415555518761 := by
  unfold tailWord_6019080
  simp only [CollatzResearch.WordTrace]
  refine ⟨109766941516954305933839347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146355922022605741245119129 109766941516954305933839347)
  ·
    refine ⟨164650412275431458900759021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109766941516954305933839347 164650412275431458900759021)
    ·
      refine ⟨61743904603286797087784633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164650412275431458900759021 61743904603286797087784633)
      ·
        refine ⟨46307928452465097815838475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61743904603286797087784633 46307928452465097815838475)
        ·
          refine ⟨69461892678697646723757713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46307928452465097815838475 69461892678697646723757713)
          ·
            refine ⟨52096419509023235042818285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69461892678697646723757713 52096419509023235042818285)
            ·
              refine ⟨19536157315883713141056857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52096419509023235042818285 19536157315883713141056857)
              ·
                refine ⟨14652117986912784855792643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19536157315883713141056857 14652117986912784855792643)
                ·
                  refine ⟨21978176980369177283688965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14652117986912784855792643 21978176980369177283688965)
                  ·
                    refine ⟨4120908183819220740691681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21978176980369177283688965 4120908183819220740691681)
                    ·
                      refine ⟨3090681137864415555518761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4120908183819220740691681 3090681137864415555518761)
                      ·
                        rfl

theorem cell23_6019080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 1, 4, 2].length) (baseStart_6019080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019080 prefixEnd_6019080 := by exact prefixLift 6019080
  have htrace : WordTrace (prefixWord ++ tailWord_6019080) baseStart_6019080 baseEnd_6019080 := by
    simpa [prefixWord, tailWord_6019080, baseEnd_6019080] using wordTrace_append hprefix tailTrace_6019080
  have hstable : (prefixWord ++ tailWord_6019080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019080).length < 2 ^ (prefixWord ++ tailWord_6019080).sum := by decide
  have hdescent : baseEnd_6019080 < baseStart_6019080 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019092 : List Nat := [2, 4, 3, 2, 2, 1, 2, 2, 1, 2, 2]
def baseStart_6019092 : Nat := 118140960795 + 6019092 * 2 ^ 59
def prefixEnd_6019092 : Nat := 4983230072969 + 3 ^ 40 * 6019092 * 2
def baseEnd_6019092 : Nat := 3090687299632269508568707

theorem tailTrace_6019092 : CollatzResearch.WordTrace tailWord_6019092 prefixEnd_6019092 3090687299632269508568707 := by
  unfold tailWord_6019092
  simp only [CollatzResearch.WordTrace]
  refine ⟨109767160354932568958557765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146356213806576758611410353 109767160354932568958557765)
  ·
    refine ⟨20581342566549856679729581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109767160354932568958557765 20581342566549856679729581)
    ·
      refine ⟨7718003462456196254898593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20581342566549856679729581 7718003462456196254898593)
      ·
        refine ⟨5788502596842147191173945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7718003462456196254898593 5788502596842147191173945)
        ·
          refine ⟨4341376947631610393380459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5788502596842147191173945 4341376947631610393380459)
          ·
            refine ⟨6512065421447415590070689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4341376947631610393380459 6512065421447415590070689)
            ·
              refine ⟨4884049066085561692553017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6512065421447415590070689 4884049066085561692553017)
              ·
                refine ⟨3663036799564171269414763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4884049066085561692553017 3663036799564171269414763)
                ·
                  refine ⟨5494555199346256904122145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3663036799564171269414763 5494555199346256904122145)
                  ·
                    refine ⟨4120916399509692678091609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5494555199346256904122145 4120916399509692678091609)
                    ·
                      refine ⟨3090687299632269508568707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4120916399509692678091609 3090687299632269508568707)
                      ·
                        rfl

theorem cell23_6019092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_6019092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019092 prefixEnd_6019092 := by exact prefixLift 6019092
  have htrace : WordTrace (prefixWord ++ tailWord_6019092) baseStart_6019092 baseEnd_6019092 := by
    simpa [prefixWord, tailWord_6019092, baseEnd_6019092] using wordTrace_append hprefix tailTrace_6019092
  have hstable : (prefixWord ++ tailWord_6019092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019092).length < 2 ^ (prefixWord ++ tailWord_6019092).sum := by decide
  have hdescent : baseEnd_6019092 < baseStart_6019092 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019114 : List Nat := [3, 1, 4, 1, 2, 1, 2, 3, 2, 2, 2]
def baseStart_6019114 : Nat := 118140960795 + 6019114 * 2 ^ 59
def prefixEnd_6019114 : Nat := 4983230072969 + 3 ^ 40 * 6019114 * 2
def baseEnd_6019114 : Nat := 3090698596206668422493605

theorem tailTrace_6019114 : CollatzResearch.WordTrace tailWord_6019114 prefixEnd_6019114 3090698596206668422493605 := by
  unfold tailWord_6019114
  simp only [CollatzResearch.WordTrace]
  refine ⟨54883780778946358918604099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146356748743856957116277597 54883780778946358918604099)
  ·
    refine ⟨82325671168419538377906149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54883780778946358918604099 82325671168419538377906149)
    ·
      refine ⟨15436063344078663445857403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82325671168419538377906149 15436063344078663445857403)
      ·
        refine ⟨23154095016117995168786105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15436063344078663445857403 23154095016117995168786105)
        ·
          refine ⟨17365571262088496376589579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23154095016117995168786105 17365571262088496376589579)
          ·
            refine ⟨26048356893132744564884369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17365571262088496376589579 26048356893132744564884369)
            ·
              refine ⟨19536267669849558423663277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26048356893132744564884369 19536267669849558423663277)
              ·
                refine ⟨7326100376193584408873729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19536267669849558423663277 7326100376193584408873729)
                ·
                  refine ⟨5494575282145188306655297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7326100376193584408873729 5494575282145188306655297)
                  ·
                    refine ⟨4120931461608891229991473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5494575282145188306655297 4120931461608891229991473)
                    ·
                      refine ⟨3090698596206668422493605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4120931461608891229991473 3090698596206668422493605)
                      ·
                        rfl

theorem cell23_6019114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_6019114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019114 prefixEnd_6019114 := by exact prefixLift 6019114
  have htrace : WordTrace (prefixWord ++ tailWord_6019114) baseStart_6019114 baseEnd_6019114 := by
    simpa [prefixWord, tailWord_6019114, baseEnd_6019114] using wordTrace_append hprefix tailTrace_6019114
  have hstable : (prefixWord ++ tailWord_6019114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019114).length < 2 ^ (prefixWord ++ tailWord_6019114).sum := by decide
  have hdescent : baseEnd_6019114 < baseStart_6019114 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019133 : List Nat := [1, 4, 1, 3, 1, 1, 3, 1, 1, 7]
def baseStart_6019133 : Nat := 118140960795 + 6019133 * 2 ^ 59
def prefixEnd_6019133 : Nat := 4983230072969 + 3 ^ 40 * 6019133 * 2
def baseEnd_6019133 : Nat := 1030236117446367949385339

theorem tailTrace_6019133 : CollatzResearch.WordTrace tailWord_6019133 prefixEnd_6019133 1030236117446367949385339 := by
  unfold tailWord_6019133
  simp only [CollatzResearch.WordTrace]
  refine ⟨219535816102716601919358053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146357210735144401279572035 219535816102716601919358053)
  ·
    refine ⟨41162965519259362859879635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 219535816102716601919358053 41162965519259362859879635)
    ·
      refine ⟨61744448278889044289819453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41162965519259362859879635 61744448278889044289819453)
      ·
        refine ⟨23154168104583391608682295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61744448278889044289819453 23154168104583391608682295)
        ·
          refine ⟨34731252156875087413023443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23154168104583391608682295 34731252156875087413023443)
          ·
            refine ⟨52096878235312631119535165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34731252156875087413023443 52096878235312631119535165)
            ·
              refine ⟨19536329338242236669825687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52096878235312631119535165 19536329338242236669825687)
              ·
                refine ⟨29304494007363355004738531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19536329338242236669825687 29304494007363355004738531)
                ·
                  refine ⟨43956741011045032507107797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29304494007363355004738531 43956741011045032507107797)
                  ·
                    refine ⟨1030236117446367949385339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43956741011045032507107797 1030236117446367949385339)
                    ·
                      rfl

theorem cell23_6019133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 7].length) (baseStart_6019133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019133 prefixEnd_6019133 := by exact prefixLift 6019133
  have htrace : WordTrace (prefixWord ++ tailWord_6019133) baseStart_6019133 baseEnd_6019133 := by
    simpa [prefixWord, tailWord_6019133, baseEnd_6019133] using wordTrace_append hprefix tailTrace_6019133
  have hstable : (prefixWord ++ tailWord_6019133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019133).length < 2 ^ (prefixWord ++ tailWord_6019133).sum := by decide
  have hdescent : baseEnd_6019133 < baseStart_6019133 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019137 : List Nat := [1, 2, 5, 1, 2, 2, 2, 3, 5]
def baseStart_6019137 : Nat := 118140960795 + 6019137 * 2 ^ 59
def prefixEnd_6019137 : Nat := 4983230072969 + 3 ^ 40 * 6019137 * 2
def baseEnd_6019137 : Nat := 343412267362413536945111

theorem tailTrace_6019137 : CollatzResearch.WordTrace tailWord_6019137 prefixEnd_6019137 343412267362413536945111 := by
  unfold tailWord_6019137
  simp only [CollatzResearch.WordTrace]
  refine ⟨219535961994702110602503665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146357307996468073735002443 219535961994702110602503665)
  ·
    refine ⟨164651971496026582951877749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219535961994702110602503665 164651971496026582951877749)
    ·
      refine ⟨15436122327752492151738539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 164651971496026582951877749 15436122327752492151738539)
      ·
        refine ⟨23154183491628738227607809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15436122327752492151738539 23154183491628738227607809)
        ·
          refine ⟨17365637618721553670705857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23154183491628738227607809 17365637618721553670705857)
          ·
            refine ⟨13024228214041165253029393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17365637618721553670705857 13024228214041165253029393)
            ·
              refine ⟨9768171160530873939772045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13024228214041165253029393 9768171160530873939772045)
              ·
                refine ⟨3663064185199077727414517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9768171160530873939772045 3663064185199077727414517)
                ·
                  refine ⟨343412267362413536945111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3663064185199077727414517 343412267362413536945111)
                  ·
                    rfl

theorem cell23_6019137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 3, 5].length) (baseStart_6019137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019137 prefixEnd_6019137 := by exact prefixLift 6019137
  have htrace : WordTrace (prefixWord ++ tailWord_6019137) baseStart_6019137 baseEnd_6019137 := by
    simpa [prefixWord, tailWord_6019137, baseEnd_6019137] using wordTrace_append hprefix tailTrace_6019137
  have hstable : (prefixWord ++ tailWord_6019137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019137).length < 2 ^ (prefixWord ++ tailWord_6019137).sum := by decide
  have hdescent : baseEnd_6019137 < baseStart_6019137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019153 : List Nat := [1, 2, 2, 1, 3, 1, 1, 3, 4, 1, 4]
def baseStart_6019153 : Nat := 118140960795 + 6019153 * 2 ^ 59
def prefixEnd_6019153 : Nat := 4983230072969 + 3 ^ 40 * 6019153 * 2
def baseEnd_6019153 : Nat := 3090718621952193769905925

theorem tailTrace_6019153 : CollatzResearch.WordTrace tailWord_6019153 prefixEnd_6019153 3090718621952193769905925 := by
  unfold tailWord_6019153
  simp only [CollatzResearch.WordTrace]
  refine ⟨219536545562644145335086113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146357697041762763556724075 219536545562644145335086113)
  ·
    refine ⟨164652409171983109001314585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219536545562644145335086113 164652409171983109001314585)
    ·
      refine ⟨123489306878987331750985939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164652409171983109001314585 123489306878987331750985939)
      ·
        refine ⟨185233960318480997626478909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123489306878987331750985939 185233960318480997626478909)
        ·
          refine ⟨69462735119430374109929591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185233960318480997626478909 69462735119430374109929591)
          ·
            refine ⟨104194102679145561164894387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69462735119430374109929591 104194102679145561164894387)
            ·
              refine ⟨156291154018718341747341581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104194102679145561164894387 156291154018718341747341581)
              ·
                refine ⟨58609182757019378155253093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156291154018718341747341581 58609182757019378155253093)
                ·
                  refine ⟨10989221766941133404109955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58609182757019378155253093 10989221766941133404109955)
                  ·
                    refine ⟨16483832650411700106164933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10989221766941133404109955 16483832650411700106164933)
                    ·
                      refine ⟨3090718621952193769905925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16483832650411700106164933 3090718621952193769905925)
                      ·
                        rfl

theorem cell23_6019153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 4, 1, 4].length) (baseStart_6019153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019153 prefixEnd_6019153 := by exact prefixLift 6019153
  have htrace : WordTrace (prefixWord ++ tailWord_6019153) baseStart_6019153 baseEnd_6019153 := by
    simpa [prefixWord, tailWord_6019153, baseEnd_6019153] using wordTrace_append hprefix tailTrace_6019153
  have hstable : (prefixWord ++ tailWord_6019153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019153).length < 2 ^ (prefixWord ++ tailWord_6019153).sum := by decide
  have hdescent : baseEnd_6019153 < baseStart_6019153 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019180 : List Nat := [2, 2, 1, 1, 3, 3, 2, 2, 3, 4]
def baseStart_6019180 : Nat := 118140960795 + 6019180 * 2 ^ 59
def prefixEnd_6019180 : Nat := 4983230072969 + 3 ^ 40 * 6019180 * 2
def baseEnd_6019180 : Nat := 1030244161976621721422767

theorem tailTrace_6019180 : CollatzResearch.WordTrace tailWord_6019180 prefixEnd_6019180 1030244161976621721422767 := by
  unfold tailWord_6019180
  simp only [CollatzResearch.WordTrace]
  refine ⟨109768765166773164473159497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146358353555697552630879329 109768765166773164473159497)
  ·
    refine ⟨82326573875079873354869623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109768765166773164473159497 82326573875079873354869623)
    ·
      refine ⟨123489860812619810032304435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82326573875079873354869623 123489860812619810032304435)
      ·
        refine ⟨185234791218929715048456653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123489860812619810032304435 185234791218929715048456653)
        ·
          refine ⟨69463046707098643143171245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185234791218929715048456653 69463046707098643143171245)
          ·
            refine ⟨26048642515161991178689217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69463046707098643143171245 26048642515161991178689217)
            ·
              refine ⟨19536481886371493384016913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26048642515161991178689217 19536481886371493384016913)
              ·
                refine ⟨14652361414778620038012685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19536481886371493384016913 14652361414778620038012685)
                ·
                  refine ⟨5494635530541982514254757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14652361414778620038012685 5494635530541982514254757)
                  ·
                    refine ⟨1030244161976621721422767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5494635530541982514254757 1030244161976621721422767)
                    ·
                      rfl

theorem cell23_6019180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 4].length) (baseStart_6019180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019180 prefixEnd_6019180 := by exact prefixLift 6019180
  have htrace : WordTrace (prefixWord ++ tailWord_6019180) baseStart_6019180 baseEnd_6019180 := by
    simpa [prefixWord, tailWord_6019180, baseEnd_6019180] using wordTrace_append hprefix tailTrace_6019180
  have hstable : (prefixWord ++ tailWord_6019180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019180).length < 2 ^ (prefixWord ++ tailWord_6019180).sum := by decide
  have hdescent : baseEnd_6019180 < baseStart_6019180 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019193 : List Nat := [1, 2, 1, 3, 4, 1, 1, 2, 8]
def baseStart_6019193 : Nat := 118140960795 + 6019193 * 2 ^ 59
def prefixEnd_6019193 : Nat := 4983230072969 + 3 ^ 40 * 6019193 * 2
def baseEnd_6019193 : Nat := 343415462353152623711749

theorem tailTrace_6019193 : CollatzResearch.WordTrace tailWord_6019193 prefixEnd_6019193 343415462353152623711749 := by
  unfold tailWord_6019193
  simp only [CollatzResearch.WordTrace]
  refine ⟨219538004482499232166542233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146358669654999488111028155 219538004482499232166542233)
  ·
    refine ⟨164653503361874424124906675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219538004482499232166542233 164653503361874424124906675)
    ·
      refine ⟨246980255042811636187360013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164653503361874424124906675 246980255042811636187360013)
      ·
        refine ⟨92617595641054363570260005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246980255042811636187360013 92617595641054363570260005)
        ·
          refine ⟨17365799182697693169423751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92617595641054363570260005 17365799182697693169423751)
          ·
            refine ⟨26048698774046539754135627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17365799182697693169423751 26048698774046539754135627)
            ·
              refine ⟨39073048161069809631203441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26048698774046539754135627 39073048161069809631203441)
              ·
                refine ⟨29304786120802357223402581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39073048161069809631203441 29304786120802357223402581)
                ·
                  refine ⟨343415462353152623711749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29304786120802357223402581 343415462353152623711749)
                  ·
                    rfl

theorem cell23_6019193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 8].length) (baseStart_6019193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019193 prefixEnd_6019193 := by exact prefixLift 6019193
  have htrace : WordTrace (prefixWord ++ tailWord_6019193) baseStart_6019193 baseEnd_6019193 := by
    simpa [prefixWord, tailWord_6019193, baseEnd_6019193] using wordTrace_append hprefix tailTrace_6019193
  have hstable : (prefixWord ++ tailWord_6019193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019193).length < 2 ^ (prefixWord ++ tailWord_6019193).sum := by decide
  have hdescent : baseEnd_6019193 < baseStart_6019193 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019214 : List Nat := [4, 1, 1, 3, 3, 2, 1, 1, 3, 4]
def baseStart_6019214 : Nat := 118140960795 + 6019214 * 2 ^ 59
def prefixEnd_6019214 : Nat := 4983230072969 + 3 ^ 40 * 6019214 * 2
def baseEnd_6019214 : Nat := 1030249981424039343747715

theorem tailTrace_6019214 : CollatzResearch.WordTrace tailWord_6019214 prefixEnd_6019214 1030249981424039343747715 := by
  unfold tailWord_6019214
  simp only [CollatzResearch.WordTrace]
  refine ⟨27442346301927894094132087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146359180276948768502037797 27442346301927894094132087)
  ·
    refine ⟨41163519452891841141198131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27442346301927894094132087 41163519452891841141198131)
    ·
      refine ⟨61745279179337761711797197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41163519452891841141198131 61745279179337761711797197)
      ·
        refine ⟨23154479692251660641923949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61745279179337761711797197 23154479692251660641923949)
        ·
          refine ⟨8682929884594372740721481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23154479692251660641923949 8682929884594372740721481)
          ·
            refine ⟨6512197413445779555541111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8682929884594372740721481 6512197413445779555541111)
            ·
              refine ⟨9768296120168669333311667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6512197413445779555541111 9768296120168669333311667)
              ·
                refine ⟨14652444180253003999967501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9768296120168669333311667 14652444180253003999967501)
                ·
                  refine ⟨5494666567594876499987813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14652444180253003999967501 5494666567594876499987813)
                  ·
                    refine ⟨1030249981424039343747715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5494666567594876499987813 1030249981424039343747715)
                    ·
                      rfl

theorem cell23_6019214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 3, 4].length) (baseStart_6019214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019214 prefixEnd_6019214 := by exact prefixLift 6019214
  have htrace : WordTrace (prefixWord ++ tailWord_6019214) baseStart_6019214 baseEnd_6019214 := by
    simpa [prefixWord, tailWord_6019214, baseEnd_6019214] using wordTrace_append hprefix tailTrace_6019214
  have hstable : (prefixWord ++ tailWord_6019214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019214).length < 2 ^ (prefixWord ++ tailWord_6019214).sum := by decide
  have hdescent : baseEnd_6019214 < baseStart_6019214 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019257 : List Nat := [1, 2, 1, 4, 1, 2, 5, 1, 1, 5]
def baseStart_6019257 : Nat := 118140960795 + 6019257 * 2 ^ 59
def prefixEnd_6019257 : Nat := 4983230072969 + 3 ^ 40 * 6019257 * 2
def baseEnd_6019257 : Nat := 1030257341313420454335149

theorem tailTrace_6019257 : CollatzResearch.WordTrace tailWord_6019257 prefixEnd_6019257 1030257341313420454335149 := by
  unfold tailWord_6019257
  simp only [CollatzResearch.WordTrace]
  refine ⟨219540338754267371096872025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146360225836178247397914683 219540338754267371096872025)
  ·
    refine ⟨164655254065700528322654019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219540338754267371096872025 164655254065700528322654019)
    ·
      refine ⟨246982881098550792483981029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164655254065700528322654019 246982881098550792483981029)
      ·
        refine ⟨46309290205978273590746443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 246982881098550792483981029 46309290205978273590746443)
        ·
          refine ⟨69463935308967410386119665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46309290205978273590746443 69463935308967410386119665)
          ·
            refine ⟨52097951481725557789589749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69463935308967410386119665 52097951481725557789589749)
            ·
              refine ⟨4884182951411771042774039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52097951481725557789589749 4884182951411771042774039)
              ·
                refine ⟨7326274427117656564161059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4884182951411771042774039 7326274427117656564161059)
                ·
                  refine ⟨10989411640676484846241589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7326274427117656564161059 10989411640676484846241589)
                  ·
                    refine ⟨1030257341313420454335149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10989411640676484846241589 1030257341313420454335149)
                    ·
                      rfl

theorem cell23_6019257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 1, 1, 5].length) (baseStart_6019257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019257 prefixEnd_6019257 := by exact prefixLift 6019257
  have htrace : WordTrace (prefixWord ++ tailWord_6019257) baseStart_6019257 baseEnd_6019257 := by
    simpa [prefixWord, tailWord_6019257, baseEnd_6019257] using wordTrace_append hprefix tailTrace_6019257
  have hstable : (prefixWord ++ tailWord_6019257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019257).length < 2 ^ (prefixWord ++ tailWord_6019257).sum := by decide
  have hdescent : baseEnd_6019257 < baseStart_6019257 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019265 : List Nat := [1, 2, 6, 1, 3, 1, 2, 2, 1, 4]
def baseStart_6019265 : Nat := 118140960795 + 6019265 * 2 ^ 59
def prefixEnd_6019265 : Nat := 4983230072969 + 3 ^ 40 * 6019265 * 2
def baseEnd_6019265 : Nat := 1030258710595165777235137

theorem tailTrace_6019265 : CollatzResearch.WordTrace tailWord_6019265 prefixEnd_6019265 1030258710595165777235137 := by
  unfold tailWord_6019265
  simp only [CollatzResearch.WordTrace]
  refine ⟨219540630538238388463163249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146360420358825592308775499 219540630538238388463163249)
  ·
    refine ⟨164655472903678791347372437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219540630538238388463163249 164655472903678791347372437)
    ·
      refine ⟨7718225292359943344408083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 164655472903678791347372437 7718225292359943344408083)
      ·
        refine ⟨11577337938539915016612125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7718225292359943344408083 11577337938539915016612125)
        ·
          refine ⟨4341501726952468131229547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11577337938539915016612125 4341501726952468131229547)
          ·
            refine ⟨6512252590428702196844321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4341501726952468131229547 6512252590428702196844321)
            ·
              refine ⟨4884189442821526647633241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6512252590428702196844321 4884189442821526647633241)
              ·
                refine ⟨3663142082116144985724931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4884189442821526647633241 3663142082116144985724931)
                ·
                  refine ⟨5494713123174217478587397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3663142082116144985724931 5494713123174217478587397)
                  ·
                    refine ⟨1030258710595165777235137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5494713123174217478587397 1030258710595165777235137)
                    ·
                      rfl

theorem cell23_6019265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_6019265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019265 prefixEnd_6019265 := by exact prefixLift 6019265
  have htrace : WordTrace (prefixWord ++ tailWord_6019265) baseStart_6019265 baseEnd_6019265 := by
    simpa [prefixWord, tailWord_6019265, baseEnd_6019265] using wordTrace_append hprefix tailTrace_6019265
  have hstable : (prefixWord ++ tailWord_6019265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019265).length < 2 ^ (prefixWord ++ tailWord_6019265).sum := by decide
  have hdescent : baseEnd_6019265 < baseStart_6019265 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019273 : List Nat := [1, 2, 1, 1, 2, 1, 1, 6, 1, 1, 6]
def baseStart_6019273 : Nat := 118140960795 + 6019273 * 2 ^ 59
def prefixEnd_6019273 : Nat := 4983230072969 + 3 ^ 40 * 6019273 * 2
def baseEnd_6019273 : Nat := 3090780239630733300405373

theorem tailTrace_6019273 : CollatzResearch.WordTrace tailWord_6019273 prefixEnd_6019273 3090780239630733300405373 := by
  unfold tailWord_6019273
  simp only [CollatzResearch.WordTrace]
  refine ⟨219540922322209405829454473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146360614881472937219636315 219540922322209405829454473)
  ·
    refine ⟨164655691741657054372090855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219540922322209405829454473 164655691741657054372090855)
    ·
      refine ⟨246983537612485581558136283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164655691741657054372090855 246983537612485581558136283)
      ·
        refine ⟨370475306418728372337204425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246983537612485581558136283 370475306418728372337204425)
        ·
          refine ⟨277856479814046279252903319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 370475306418728372337204425 277856479814046279252903319)
          ·
            refine ⟨416784719721069418879354979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277856479814046279252903319 416784719721069418879354979)
            ·
              refine ⟨625177079581604128319032469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 416784719721069418879354979 625177079581604128319032469)
              ·
                refine ⟨29305175605387693514954647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 625177079581604128319032469 29305175605387693514954647)
                ·
                  refine ⟨43957763408081540272431971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29305175605387693514954647 43957763408081540272431971)
                  ·
                    refine ⟨65936645112122310408647957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43957763408081540272431971 65936645112122310408647957)
                    ·
                      refine ⟨3090780239630733300405373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65936645112122310408647957 3090780239630733300405373)
                      ·
                        rfl

theorem cell23_6019273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 1, 6].length) (baseStart_6019273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019273 prefixEnd_6019273 := by exact prefixLift 6019273
  have htrace : WordTrace (prefixWord ++ tailWord_6019273) baseStart_6019273 baseEnd_6019273 := by
    simpa [prefixWord, tailWord_6019273, baseEnd_6019273] using wordTrace_append hprefix tailTrace_6019273
  have hstable : (prefixWord ++ tailWord_6019273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019273).length < 2 ^ (prefixWord ++ tailWord_6019273).sum := by decide
  have hdescent : baseEnd_6019273 < baseStart_6019273 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019290 : List Nat := [3, 1, 1, 2, 2, 1, 3, 3, 1, 2, 4]
def baseStart_6019290 : Nat := 118140960795 + 6019290 * 2 ^ 59
def prefixEnd_6019290 : Nat := 4983230072969 + 3 ^ 40 * 6019290 * 2
def baseEnd_6019290 : Nat := 3090788968801859733892795

theorem tailTrace_6019290 : CollatzResearch.WordTrace tailWord_6019290 prefixEnd_6019290 3090788968801859733892795 := by
  unfold tailWord_6019290
  simp only [CollatzResearch.WordTrace]
  refine ⟨54885385590786954433205831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146361028242098545155215549 54885385590786954433205831)
  ·
    refine ⟨82328078386180431649808747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54885385590786954433205831 82328078386180431649808747)
    ·
      refine ⟨123492117579270647474713121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82328078386180431649808747 123492117579270647474713121)
      ·
        refine ⟨92619088184452985606034841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123492117579270647474713121 92619088184452985606034841)
        ·
          refine ⟨69464316138339739204526131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92619088184452985606034841 69464316138339739204526131)
          ·
            refine ⟨104196474207509608806789197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69464316138339739204526131 104196474207509608806789197)
            ·
              refine ⟨39073677827816103302545949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104196474207509608806789197 39073677827816103302545949)
              ·
                refine ⟨14652629185431038738454731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39073677827816103302545949 14652629185431038738454731)
                ·
                  refine ⟨21978943778146558107682097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14652629185431038738454731 21978943778146558107682097)
                  ·
                    refine ⟨16484207833609918580761573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21978943778146558107682097 16484207833609918580761573)
                    ·
                      refine ⟨3090788968801859733892795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16484207833609918580761573 3090788968801859733892795)
                      ·
                        rfl

theorem cell23_6019290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_6019290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019290 prefixEnd_6019290 := by exact prefixLift 6019290
  have htrace : WordTrace (prefixWord ++ tailWord_6019290) baseStart_6019290 baseEnd_6019290 := by
    simpa [prefixWord, tailWord_6019290, baseEnd_6019290] using wordTrace_append hprefix tailTrace_6019290
  have hstable : (prefixWord ++ tailWord_6019290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019290).length < 2 ^ (prefixWord ++ tailWord_6019290).sum := by decide
  have hdescent : baseEnd_6019290 < baseStart_6019290 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019297 : List Nat := [1, 2, 3, 1, 3, 1, 2, 4, 1, 2, 3]
def baseStart_6019297 : Nat := 118140960795 + 6019297 * 2 ^ 59
def prefixEnd_6019297 : Nat := 4983230072969 + 3 ^ 40 * 6019297 * 2
def baseEnd_6019297 : Nat := 3090792563166441206505263

theorem tailTrace_6019297 : CollatzResearch.WordTrace tailWord_6019297 prefixEnd_6019297 3090792563166441206505263 := by
  unfold tailWord_6019297
  simp only [CollatzResearch.WordTrace]
  refine ⟨219541797674122457928328145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146361198449414971952218763 219541797674122457928328145)
  ·
    refine ⟨164656348255591843446246109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219541797674122457928328145 164656348255591843446246109)
    ·
      refine ⟨61746130595846941292342291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164656348255591843446246109 61746130595846941292342291)
      ·
        refine ⟨92619195893770411938513437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61746130595846941292342291 92619195893770411938513437)
        ·
          refine ⟨34732198460163904476942539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92619195893770411938513437 34732198460163904476942539)
          ·
            refine ⟨52098297690245856715413809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34732198460163904476942539 52098297690245856715413809)
            ·
              refine ⟨39073723267684392536560357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52098297690245856715413809 39073723267684392536560357)
              ·
                refine ⟨7326323112690823600605067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39073723267684392536560357 7326323112690823600605067)
                ·
                  refine ⟨10989484669036235400907601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7326323112690823600605067 10989484669036235400907601)
                  ·
                    refine ⟨8242113501777176550680701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10989484669036235400907601 8242113501777176550680701)
                    ·
                      refine ⟨3090792563166441206505263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8242113501777176550680701 3090792563166441206505263)
                      ·
                        rfl

theorem cell23_6019297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 4, 1, 2, 3].length) (baseStart_6019297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019297 prefixEnd_6019297 := by exact prefixLift 6019297
  have htrace : WordTrace (prefixWord ++ tailWord_6019297) baseStart_6019297 baseEnd_6019297 := by
    simpa [prefixWord, tailWord_6019297, baseEnd_6019297] using wordTrace_append hprefix tailTrace_6019297
  have hstable : (prefixWord ++ tailWord_6019297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019297).length < 2 ^ (prefixWord ++ tailWord_6019297).sum := by decide
  have hdescent : baseEnd_6019297 < baseStart_6019297 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019298 : List Nat := [3, 3, 4, 1, 1, 1, 1, 1, 1, 5, 2]
def baseStart_6019298 : Nat := 118140960795 + 6019298 * 2 ^ 59
def prefixEnd_6019298 : Nat := 4983230072969 + 3 ^ 40 * 6019298 * 2
def baseEnd_6019298 : Nat := 3090793076647095702592759

theorem tailTrace_6019298 : CollatzResearch.WordTrace tailWord_6019298 prefixEnd_6019298 3090793076647095702592759 := by
  unfold tailWord_6019298
  simp only [CollatzResearch.WordTrace]
  refine ⟨54885458536779708774778637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146361222764745890066076365 54885458536779708774778637)
  ·
    refine ⟨20582046951292390790541989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54885458536779708774778637 20582046951292390790541989)
    ·
      refine ⟨3859133803367323273226623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20582046951292390790541989 3859133803367323273226623)
      ·
        refine ⟨5788700705050984909839935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3859133803367323273226623 5788700705050984909839935)
        ·
          refine ⟨8683051057576477364759903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5788700705050984909839935 8683051057576477364759903)
          ·
            refine ⟨13024576586364716047139855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8683051057576477364759903 13024576586364716047139855)
            ·
              refine ⟨19536864879547074070709783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13024576586364716047139855 19536864879547074070709783)
              ·
                refine ⟨29305297319320611106064675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19536864879547074070709783 29305297319320611106064675)
                ·
                  refine ⟨43957945978980916659097013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29305297319320611106064675 43957945978980916659097013)
                  ·
                    refine ⟨4121057435529460936790345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43957945978980916659097013 4121057435529460936790345)
                    ·
                      refine ⟨3090793076647095702592759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4121057435529460936790345 3090793076647095702592759)
                      ·
                        rfl

theorem cell23_6019298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_6019298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019298 prefixEnd_6019298 := by exact prefixLift 6019298
  have htrace : WordTrace (prefixWord ++ tailWord_6019298) baseStart_6019298 baseEnd_6019298 := by
    simpa [prefixWord, tailWord_6019298, baseEnd_6019298] using wordTrace_append hprefix tailTrace_6019298
  have hstable : (prefixWord ++ tailWord_6019298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019298).length < 2 ^ (prefixWord ++ tailWord_6019298).sum := by decide
  have hdescent : baseEnd_6019298 < baseStart_6019298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019311 : List Nat := [1, 1, 2, 1, 6, 1, 1, 5, 1, 2, 2]
def baseStart_6019311 : Nat := 118140960795 + 6019311 * 2 ^ 59
def prefixEnd_6019311 : Nat := 4983230072969 + 3 ^ 40 * 6019311 * 2
def baseEnd_6019311 : Nat := 3090799751895604151730199

theorem tailTrace_6019311 : CollatzResearch.WordTrace tailWord_6019311 prefixEnd_6019311 3090799751895604151730199 := by
  unfold tailWord_6019311
  simp only [CollatzResearch.WordTrace]
  refine ⟨219542308296071738319337787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146361538864047825546225191 219542308296071738319337787)
  ·
    refine ⟨329313462444107607479006681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219542308296071738319337787 329313462444107607479006681)
    ·
      refine ⟨246985096833080705609255011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329313462444107607479006681 246985096833080705609255011)
      ·
        refine ⟨370477645249621058413882517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246985096833080705609255011 370477645249621058413882517)
        ·
          refine ⟨17366139621075987113150743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 370477645249621058413882517 17366139621075987113150743)
          ·
            refine ⟨26049209431613980669726115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17366139621075987113150743 26049209431613980669726115)
            ·
              refine ⟨39073814147420971004589173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26049209431613980669726115 39073814147420971004589173)
              ·
                refine ⟨3663170076320716031680235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39073814147420971004589173 3663170076320716031680235)
                ·
                  refine ⟨5494755114481074047520353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3663170076320716031680235 5494755114481074047520353)
                  ·
                    refine ⟨4121066335860805535640265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5494755114481074047520353 4121066335860805535640265)
                    ·
                      refine ⟨3090799751895604151730199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4121066335860805535640265 3090799751895604151730199)
                      ·
                        rfl

theorem cell23_6019311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 5, 1, 2, 2].length) (baseStart_6019311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019311 prefixEnd_6019311 := by exact prefixLift 6019311
  have htrace : WordTrace (prefixWord ++ tailWord_6019311) baseStart_6019311 baseEnd_6019311 := by
    simpa [prefixWord, tailWord_6019311, baseEnd_6019311] using wordTrace_append hprefix tailTrace_6019311
  have hstable : (prefixWord ++ tailWord_6019311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019311).length < 2 ^ (prefixWord ++ tailWord_6019311).sum := by decide
  have hdescent : baseEnd_6019311 < baseStart_6019311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019314 : List Nat := [3, 2, 1, 3, 2, 2, 1, 3, 1, 2, 3]
def baseStart_6019314 : Nat := 118140960795 + 6019314 * 2 ^ 59
def prefixEnd_6019314 : Nat := 4983230072969 + 3 ^ 40 * 6019314 * 2
def baseEnd_6019314 : Nat := 3090801292337567639992685

theorem tailTrace_6019314 : CollatzResearch.WordTrace tailWord_6019314 prefixEnd_6019314 3090801292337567639992685 := by
  unfold tailWord_6019314
  simp only [CollatzResearch.WordTrace]
  refine ⟨54885604428765217457924249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146361611810040579887797997 54885604428765217457924249)
  ·
    refine ⟨41164203321573913093443187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54885604428765217457924249 41164203321573913093443187)
    ·
      refine ⟨61746304982360869640164781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41164203321573913093443187 61746304982360869640164781)
      ·
        refine ⟨23154864368385326115061793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61746304982360869640164781 23154864368385326115061793)
        ·
          refine ⟨17366148276288994586296345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23154864368385326115061793 17366148276288994586296345)
          ·
            refine ⟨13024611207216745939722259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17366148276288994586296345 13024611207216745939722259)
            ·
              refine ⟨19536916810825118909583389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13024611207216745939722259 19536916810825118909583389)
              ·
                refine ⟨7326343804059419591093771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19536916810825118909583389 7326343804059419591093771)
                ·
                  refine ⟨10989515706089129386640657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7326343804059419591093771 10989515706089129386640657)
                  ·
                    refine ⟨8242136779566847039980493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10989515706089129386640657 8242136779566847039980493)
                    ·
                      refine ⟨3090801292337567639992685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8242136779566847039980493 3090801292337567639992685)
                      ·
                        rfl

theorem cell23_6019314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_6019314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019314 prefixEnd_6019314 := by exact prefixLift 6019314
  have htrace : WordTrace (prefixWord ++ tailWord_6019314) baseStart_6019314 baseEnd_6019314 := by
    simpa [prefixWord, tailWord_6019314, baseEnd_6019314] using wordTrace_append hprefix tailTrace_6019314
  have hstable : (prefixWord ++ tailWord_6019314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019314).length < 2 ^ (prefixWord ++ tailWord_6019314).sum := by decide
  have hdescent : baseEnd_6019314 < baseStart_6019314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019327 : List Nat := [1, 1, 2, 2, 1, 4, 3, 1, 4, 1, 3]
def baseStart_6019327 : Nat := 118140960795 + 6019327 * 2 ^ 59
def prefixEnd_6019327 : Nat := 4983230072969 + 3 ^ 40 * 6019327 * 2
def baseEnd_6019327 : Nat := 3090807967586076089130125

theorem tailTrace_6019327 : CollatzResearch.WordTrace tailWord_6019327 prefixEnd_6019327 3090807967586076089130125 := by
  unfold tailWord_6019327
  simp only [CollatzResearch.WordTrace]
  refine ⟨219542891864013773051920235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146361927909342515367946823 219542891864013773051920235)
  ·
    refine ⟨329314337796020659577880353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219542891864013773051920235 329314337796020659577880353)
    ·
      refine ⟨246985753347015494683410265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329314337796020659577880353 246985753347015494683410265)
      ·
        refine ⟨185239315010261621012557699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246985753347015494683410265 185239315010261621012557699)
        ·
          refine ⟨277858972515392431518836549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185239315010261621012557699 277858972515392431518836549)
          ·
            refine ⟨52098557346636080909781853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 277858972515392431518836549 52098557346636080909781853)
            ·
              refine ⟨19536959004988530341168195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52098557346636080909781853 19536959004988530341168195)
              ·
                refine ⟨29305438507482795511752293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19536959004988530341168195 29305438507482795511752293)
                ·
                  refine ⟨5494769720153024158453555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29305438507482795511752293 5494769720153024158453555)
                  ·
                    refine ⟨8242154580229536237680333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5494769720153024158453555 8242154580229536237680333)
                    ·
                      refine ⟨3090807967586076089130125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8242154580229536237680333 3090807967586076089130125)
                      ·
                        rfl

theorem cell23_6019327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 4, 1, 3].length) (baseStart_6019327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019327 prefixEnd_6019327 := by exact prefixLift 6019327
  have htrace : WordTrace (prefixWord ++ tailWord_6019327) baseStart_6019327 baseEnd_6019327 := by
    simpa [prefixWord, tailWord_6019327, baseEnd_6019327] using wordTrace_append hprefix tailTrace_6019327
  have hstable : (prefixWord ++ tailWord_6019327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019327).length < 2 ^ (prefixWord ++ tailWord_6019327).sum := by decide
  have hdescent : baseEnd_6019327 < baseStart_6019327 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019384 : List Nat := [2, 1, 2, 1, 3, 1, 4, 1, 4, 2, 2]
def baseStart_6019384 : Nat := 118140960795 + 6019384 * 2 ^ 59
def prefixEnd_6019384 : Nat := 4983230072969 + 3 ^ 40 * 6019384 * 2
def baseEnd_6019384 : Nat := 3090837235983382366117363

theorem tailTrace_6019384 : CollatzResearch.WordTrace tailWord_6019384 prefixEnd_6019384 3090837235983382366117363 := by
  unfold tailWord_6019384
  simp only [CollatzResearch.WordTrace]
  refine ⟨109772485412403635893372603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146363313883204847857830137 109772485412403635893372603)
  ·
    refine ⟨164658728118605453840058905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109772485412403635893372603 164658728118605453840058905)
    ·
      refine ⟨123494046088954090380044179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164658728118605453840058905 123494046088954090380044179)
      ·
        refine ⟨185241069133431135570066269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123494046088954090380044179 185241069133431135570066269)
        ·
          refine ⟨69465400925036675838774851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185241069133431135570066269 69465400925036675838774851)
          ·
            refine ⟨104198101387555013758162277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69465400925036675838774851 104198101387555013758162277)
            ·
              refine ⟨19537144010166565079655427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104198101387555013758162277 19537144010166565079655427)
              ·
                refine ⟨29305716015249847619483141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19537144010166565079655427 29305716015249847619483141)
                ·
                  refine ⟨5494821752859346428653089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29305716015249847619483141 5494821752859346428653089)
                  ·
                    refine ⟨4121116314644509821489817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5494821752859346428653089 4121116314644509821489817)
                    ·
                      refine ⟨3090837235983382366117363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4121116314644509821489817 3090837235983382366117363)
                      ·
                        rfl

theorem cell23_6019384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 4, 2, 2].length) (baseStart_6019384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019384 prefixEnd_6019384 := by exact prefixLift 6019384
  have htrace : WordTrace (prefixWord ++ tailWord_6019384) baseStart_6019384 baseEnd_6019384 := by
    simpa [prefixWord, tailWord_6019384, baseEnd_6019384] using wordTrace_append hprefix tailTrace_6019384
  have hstable : (prefixWord ++ tailWord_6019384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019384).length < 2 ^ (prefixWord ++ tailWord_6019384).sum := by decide
  have hdescent : baseEnd_6019384 < baseStart_6019384 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019437 : List Nat := [1, 5, 1, 1, 1, 2, 1, 4, 2, 5]
def baseStart_6019437 : Nat := 118140960795 + 6019437 * 2 ^ 59
def prefixEnd_6019437 : Nat := 4983230072969 + 3 ^ 40 * 6019437 * 2
def baseEnd_6019437 : Nat := 1030288150152690219584873

theorem tailTrace_6019437 : CollatzResearch.WordTrace tailWord_6019437 prefixEnd_6019437 1030288150152690219584873 := by
  unfold tailWord_6019437
  simp only [CollatzResearch.WordTrace]
  refine ⟨219546903893615261838424565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146364602595743507892283043 219546903893615261838424565)
  ·
    refine ⟨20582522240026430797352303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 219546903893615261838424565 20582522240026430797352303)
    ·
      refine ⟨30873783360039646196028455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20582522240026430797352303 30873783360039646196028455)
      ·
        refine ⟨46310675040059469294042683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30873783360039646196028455 46310675040059469294042683)
        ·
          refine ⟨69466012560089203941064025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46310675040059469294042683 69466012560089203941064025)
          ·
            refine ⟨52099509420066902955798019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69466012560089203941064025 52099509420066902955798019)
            ·
              refine ⟨78149264130100354433697029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52099509420066902955798019 78149264130100354433697029)
              ·
                refine ⟨14652987024393816456318193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78149264130100354433697029 14652987024393816456318193)
                ·
                  refine ⟨10989740268295362342238645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14652987024393816456318193 10989740268295362342238645)
                  ·
                    refine ⟨1030288150152690219584873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10989740268295362342238645 1030288150152690219584873)
                    ·
                      rfl

theorem cell23_6019437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_6019437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019437 prefixEnd_6019437 := by exact prefixLift 6019437
  have htrace : WordTrace (prefixWord ++ tailWord_6019437) baseStart_6019437 baseEnd_6019437 := by
    simpa [prefixWord, tailWord_6019437, baseEnd_6019437] using wordTrace_append hprefix tailTrace_6019437
  have hstable : (prefixWord ++ tailWord_6019437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019437).length < 2 ^ (prefixWord ++ tailWord_6019437).sum := by decide
  have hdescent : baseEnd_6019437 < baseStart_6019437 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019467 : List Nat := [1, 1, 1, 1, 4, 4, 1, 1, 5, 4]
def baseStart_6019467 : Nat := 118140960795 + 6019467 * 2 ^ 59
def prefixEnd_6019467 : Nat := 4983230072969 + 3 ^ 40 * 6019467 * 2
def baseEnd_6019467 : Nat := 1030293284959235180459827

theorem tailTrace_6019467 : CollatzResearch.WordTrace tailWord_6019467 prefixEnd_6019467 1030293284959235180459827 := by
  unfold tailWord_6019467
  simp only [CollatzResearch.WordTrace]
  refine ⟨219547998083506576962016655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146365332055671051308011103 219547998083506576962016655)
  ·
    refine ⟨329321997125259865443024983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219547998083506576962016655 329321997125259865443024983)
    ·
      refine ⟨493982995687889798164537475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329321997125259865443024983 493982995687889798164537475)
      ·
        refine ⟨740974493531834697246806213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 493982995687889798164537475 740974493531834697246806213)
        ·
          refine ⟨138932717537219005733776165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 740974493531834697246806213 138932717537219005733776165)
          ·
            refine ⟨26049884538228563575083031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 138932717537219005733776165 26049884538228563575083031)
            ·
              refine ⟨39074826807342845362624547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26049884538228563575083031 39074826807342845362624547)
              ·
                refine ⟨58612240211014268043936821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39074826807342845362624547 58612240211014268043936821)
                ·
                  refine ⟨5494897519782587629119077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58612240211014268043936821 5494897519782587629119077)
                  ·
                    refine ⟨1030293284959235180459827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5494897519782587629119077 1030293284959235180459827)
                    ·
                      rfl

theorem cell23_6019467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 5, 4].length) (baseStart_6019467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019467 prefixEnd_6019467 := by exact prefixLift 6019467
  have htrace : WordTrace (prefixWord ++ tailWord_6019467) baseStart_6019467 baseEnd_6019467 := by
    simpa [prefixWord, tailWord_6019467, baseEnd_6019467] using wordTrace_append hprefix tailTrace_6019467
  have hstable : (prefixWord ++ tailWord_6019467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019467).length < 2 ^ (prefixWord ++ tailWord_6019467).sum := by decide
  have hdescent : baseEnd_6019467 < baseStart_6019467 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019551 : List Nat := [1, 1, 2, 3, 3, 3, 1, 2, 2, 3, 2]
def baseStart_6019551 : Nat := 118140960795 + 6019551 * 2 ^ 59
def prefixEnd_6019551 : Nat := 4983230072969 + 3 ^ 40 * 6019551 * 2
def baseEnd_6019551 : Nat := 3090922987252683212729095

theorem tailTrace_6019551 : CollatzResearch.WordTrace tailWord_6019551 prefixEnd_6019551 3090922987252683212729095 := by
  unfold tailWord_6019551
  simp only [CollatzResearch.WordTrace]
  refine ⟨219551061815202259308074507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146367374543468172872049671 219551061815202259308074507)
  ·
    refine ⟨329326592722803388962111761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219551061815202259308074507 329326592722803388962111761)
    ·
      refine ⟨246994944542102541721583821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329326592722803388962111761 246994944542102541721583821)
      ·
        refine ⟨92623104203288453145593933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246994944542102541721583821 92623104203288453145593933)
        ·
          refine ⟨34733664076233169929597725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92623104203288453145593933 34733664076233169929597725)
          ·
            refine ⟨13025124028587438723599147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34733664076233169929597725 13025124028587438723599147)
            ·
              refine ⟨19537686042881158085398721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13025124028587438723599147 19537686042881158085398721)
              ·
                refine ⟨14653264532160868564049041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19537686042881158085398721 14653264532160868564049041)
                ·
                  refine ⟨10989948399120651423036781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14653264532160868564049041 10989948399120651423036781)
                  ·
                    refine ⟨4121230649670244283638793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10989948399120651423036781 4121230649670244283638793)
                    ·
                      refine ⟨3090922987252683212729095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4121230649670244283638793 3090922987252683212729095)
                      ·
                        rfl

theorem cell23_6019551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 2, 3, 2].length) (baseStart_6019551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019551 prefixEnd_6019551 := by exact prefixLift 6019551
  have htrace : WordTrace (prefixWord ++ tailWord_6019551) baseStart_6019551 baseEnd_6019551 := by
    simpa [prefixWord, tailWord_6019551, baseEnd_6019551] using wordTrace_append hprefix tailTrace_6019551
  have hstable : (prefixWord ++ tailWord_6019551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019551).length < 2 ^ (prefixWord ++ tailWord_6019551).sum := by decide
  have hdescent : baseEnd_6019551 < baseStart_6019551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019567 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 2, 6, 3]
def baseStart_6019567 : Nat := 118140960795 + 6019567 * 2 ^ 59
def prefixEnd_6019567 : Nat := 4983230072969 + 3 ^ 40 * 6019567 * 2
def baseEnd_6019567 : Nat := 3090931202943155150129021

theorem tailTrace_6019567 : CollatzResearch.WordTrace tailWord_6019567 prefixEnd_6019567 3090931202943155150129021 := by
  unfold tailWord_6019567
  simp only [CollatzResearch.WordTrace]
  refine ⟨219551645383144294040656955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146367763588762862693771303 219551645383144294040656955)
  ·
    refine ⟨329327468074716441060985433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219551645383144294040656955 329327468074716441060985433)
    ·
      refine ⟨246995601056037330795739075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329327468074716441060985433 246995601056037330795739075)
      ·
        refine ⟨370493401584055996193608613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246995601056037330795739075 370493401584055996193608613)
        ·
          refine ⟨69467512797010499286301615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 370493401584055996193608613 69467512797010499286301615)
          ·
            refine ⟨104201269195515748929452423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69467512797010499286301615 104201269195515748929452423)
            ·
              refine ⟨156301903793273623394178635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104201269195515748929452423 156301903793273623394178635)
              ·
                refine ⟨234452855689910435091267953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156301903793273623394178635 234452855689910435091267953)
                ·
                  refine ⟨175839641767432826318450965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 234452855689910435091267953 175839641767432826318450965)
                  ·
                    refine ⟨8242483207848413733677389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 175839641767432826318450965 8242483207848413733677389)
                    ·
                      refine ⟨3090931202943155150129021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8242483207848413733677389 3090931202943155150129021)
                      ·
                        rfl

theorem cell23_6019567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 6, 3].length) (baseStart_6019567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019567 prefixEnd_6019567 := by exact prefixLift 6019567
  have htrace : WordTrace (prefixWord ++ tailWord_6019567) baseStart_6019567 baseEnd_6019567 := by
    simpa [prefixWord, tailWord_6019567, baseEnd_6019567] using wordTrace_append hprefix tailTrace_6019567
  have hstable : (prefixWord ++ tailWord_6019567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019567).length < 2 ^ (prefixWord ++ tailWord_6019567).sum := by decide
  have hdescent : baseEnd_6019567 < baseStart_6019567 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019574 : List Nat := [5, 1, 1, 1, 2, 1, 2, 3, 1, 6]
def baseStart_6019574 : Nat := 118140960795 + 6019574 * 2 ^ 59
def prefixEnd_6019574 : Nat := 4983230072969 + 3 ^ 40 * 6019574 * 2
def baseEnd_6019574 : Nat := 1030311599102578874247163

theorem tailTrace_6019574 : CollatzResearch.WordTrace tailWord_6019574 prefixEnd_6019574 1030311599102578874247163 := by
  unfold tailWord_6019574
  simp only [CollatzResearch.WordTrace]
  refine ⟨13721993793382433389760111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 146367933796079289490774517 13721993793382433389760111)
  ·
    refine ⟨20582990690073650084640167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13721993793382433389760111 20582990690073650084640167)
    ·
      refine ⟨30874486035110475126960251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20582990690073650084640167 30874486035110475126960251)
      ·
        refine ⟨46311729052665712690440377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30874486035110475126960251 46311729052665712690440377)
        ·
          refine ⟨34733796789499284517830283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46311729052665712690440377 34733796789499284517830283)
          ·
            refine ⟨52100695184248926776745425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34733796789499284517830283 52100695184248926776745425)
            ·
              refine ⟨39075521388186695082559069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52100695184248926776745425 39075521388186695082559069)
              ·
                refine ⟨14653320520570010655959651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39075521388186695082559069 14653320520570010655959651)
                ·
                  refine ⟨21979980780855015983939477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14653320520570010655959651 21979980780855015983939477)
                  ·
                    refine ⟨1030311599102578874247163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21979980780855015983939477 1030311599102578874247163)
                    ·
                      rfl

theorem cell23_6019574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_6019574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019574 prefixEnd_6019574 := by exact prefixLift 6019574
  have htrace : WordTrace (prefixWord ++ tailWord_6019574) baseStart_6019574 baseEnd_6019574 := by
    simpa [prefixWord, tailWord_6019574, baseEnd_6019574] using wordTrace_append hprefix tailTrace_6019574
  have hstable : (prefixWord ++ tailWord_6019574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019574).length < 2 ^ (prefixWord ++ tailWord_6019574).sum := by decide
  have hdescent : baseEnd_6019574 < baseStart_6019574 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019577 : List Nat := [1, 2, 1, 3, 1, 2, 4, 1, 1, 1, 6]
def baseStart_6019577 : Nat := 118140960795 + 6019577 * 2 ^ 59
def prefixEnd_6019577 : Nat := 4983230072969 + 3 ^ 40 * 6019577 * 2
def baseEnd_6019577 : Nat := 3090936337749700111003975

theorem tailTrace_6019577 : CollatzResearch.WordTrace tailWord_6019577 prefixEnd_6019577 3090936337749700111003975 := by
  unfold tailWord_6019577
  simp only [CollatzResearch.WordTrace]
  refine ⟨219552010113108065748520985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146368006742072043832347323 219552010113108065748520985)
  ·
    refine ⟨164664007584831049311390739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219552010113108065748520985 164664007584831049311390739)
    ·
      refine ⟨246996011377246573967086109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164664007584831049311390739 246996011377246573967086109)
      ·
        refine ⟨92623504266467465237657291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246996011377246573967086109 92623504266467465237657291)
        ·
          refine ⟨138935256399701197856485937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92623504266467465237657291 138935256399701197856485937)
          ·
            refine ⟨104201442299775898392364453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138935256399701197856485937 104201442299775898392364453)
            ·
              refine ⟨19537770431207980948568335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104201442299775898392364453 19537770431207980948568335)
              ·
                refine ⟨29306655646811971422852503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19537770431207980948568335 29306655646811971422852503)
                ·
                  refine ⟨43959983470217957134278755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29306655646811971422852503 43959983470217957134278755)
                  ·
                    refine ⟨65939975205326935701418133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43959983470217957134278755 65939975205326935701418133)
                    ·
                      refine ⟨3090936337749700111003975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 65939975205326935701418133 3090936337749700111003975)
                      ·
                        rfl

theorem cell23_6019577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_6019577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019577 prefixEnd_6019577 := by exact prefixLift 6019577
  have htrace : WordTrace (prefixWord ++ tailWord_6019577) baseStart_6019577 baseEnd_6019577 := by
    simpa [prefixWord, tailWord_6019577, baseEnd_6019577] using wordTrace_append hprefix tailTrace_6019577
  have hstable : (prefixWord ++ tailWord_6019577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019577).length < 2 ^ (prefixWord ++ tailWord_6019577).sum := by decide
  have hdescent : baseEnd_6019577 < baseStart_6019577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019581 : List Nat := [1, 4, 1, 1, 1, 3, 2, 1, 5, 2, 2]
def baseStart_6019581 : Nat := 118140960795 + 6019581 * 2 ^ 59
def prefixEnd_6019581 : Nat := 4983230072969 + 3 ^ 40 * 6019581 * 2
def baseEnd_6019581 : Nat := 3090938391672318095353957

theorem tailTrace_6019581 : CollatzResearch.WordTrace tailWord_6019581 prefixEnd_6019581 3090938391672318095353957 := by
  unfold tailWord_6019581
  simp only [CollatzResearch.WordTrace]
  refine ⟨219552156005093574431666597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146368104003395716287777731 219552156005093574431666597)
  ·
    refine ⟨41166029250955045205937487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 219552156005093574431666597 41166029250955045205937487)
    ·
      refine ⟨61749043876432567808906231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41166029250955045205937487 61749043876432567808906231)
      ·
        refine ⟨92623565814648851713359347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61749043876432567808906231 92623565814648851713359347)
        ·
          refine ⟨138935348721973277570039021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92623565814648851713359347 138935348721973277570039021)
          ·
            refine ⟨52100755770739979088764633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138935348721973277570039021 52100755770739979088764633)
            ·
              refine ⟨39075566828054984316573475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52100755770739979088764633 39075566828054984316573475)
              ·
                refine ⟨58613350242082476474860213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39075566828054984316573475 58613350242082476474860213)
                ·
                  refine ⟨5495001585195232169518145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58613350242082476474860213 5495001585195232169518145)
                  ·
                    refine ⟨4121251188896424127138609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5495001585195232169518145 4121251188896424127138609)
                    ·
                      refine ⟨3090938391672318095353957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4121251188896424127138609 3090938391672318095353957)
                      ·
                        rfl

theorem cell23_6019581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 5, 2, 2].length) (baseStart_6019581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019581 prefixEnd_6019581 := by exact prefixLift 6019581
  have htrace : WordTrace (prefixWord ++ tailWord_6019581) baseStart_6019581 baseEnd_6019581 := by
    simpa [prefixWord, tailWord_6019581, baseEnd_6019581] using wordTrace_append hprefix tailTrace_6019581
  have hstable : (prefixWord ++ tailWord_6019581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019581).length < 2 ^ (prefixWord ++ tailWord_6019581).sum := by decide
  have hdescent : baseEnd_6019581 < baseStart_6019581 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019594 : List Nat := [3, 1, 2, 2, 2, 1, 3, 2, 1, 2, 4]
def baseStart_6019594 : Nat := 118140960795 + 6019594 * 2 ^ 59
def prefixEnd_6019594 : Nat := 4983230072969 + 3 ^ 40 * 6019594 * 2
def baseEnd_6019594 : Nat := 3090945066920826544491397

theorem tailTrace_6019594 : CollatzResearch.WordTrace tailWord_6019594 prefixEnd_6019594 3090945066920826544491397 := by
  unfold tailWord_6019594
  simp only [CollatzResearch.WordTrace]
  refine ⟨54888157538511619412972459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146368420102697651767926557 54888157538511619412972459)
  ·
    refine ⟨82332236307767429119458689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54888157538511619412972459 82332236307767429119458689)
    ·
      refine ⟨61749177230825571839594017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82332236307767429119458689 61749177230825571839594017)
      ·
        refine ⟨46311882923119178879695513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61749177230825571839594017 46311882923119178879695513)
        ·
          refine ⟨34733912192339384159771635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46311882923119178879695513 34733912192339384159771635)
          ·
            refine ⟨52100868288509076239657453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34733912192339384159771635 52100868288509076239657453)
            ·
              refine ⟨19537825608190903589871545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52100868288509076239657453 19537825608190903589871545)
              ·
                refine ⟨14653369206143177692403659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19537825608190903589871545 14653369206143177692403659)
                ·
                  refine ⟨21980053809214766538605489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14653369206143177692403659 21980053809214766538605489)
                  ·
                    refine ⟨16485040356911074903954117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21980053809214766538605489 16485040356911074903954117)
                    ·
                      refine ⟨3090945066920826544491397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16485040356911074903954117 3090945066920826544491397)
                      ·
                        rfl

theorem cell23_6019594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_6019594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019594 prefixEnd_6019594 := by exact prefixLift 6019594
  have htrace : WordTrace (prefixWord ++ tailWord_6019594) baseStart_6019594 baseEnd_6019594 := by
    simpa [prefixWord, tailWord_6019594, baseEnd_6019594] using wordTrace_append hprefix tailTrace_6019594
  have hstable : (prefixWord ++ tailWord_6019594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019594).length < 2 ^ (prefixWord ++ tailWord_6019594).sum := by decide
  have hdescent : baseEnd_6019594 < baseStart_6019594 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019598 : List Nat := [4, 1, 1, 2, 3, 2, 3, 1, 1, 1, 4]
def baseStart_6019598 : Nat := 118140960795 + 6019598 * 2 ^ 59
def prefixEnd_6019598 : Nat := 4983230072969 + 3 ^ 40 * 6019598 * 2
def baseEnd_6019598 : Nat := 3090947120843444528841379

theorem tailTrace_6019598 : CollatzResearch.WordTrace tailWord_6019598 prefixEnd_6019598 3090947120843444528841379 := by
  unfold tailWord_6019598
  simp only [CollatzResearch.WordTrace]
  refine ⟨27444097005753998291879431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146368517364021324223356965 27444097005753998291879431)
  ·
    refine ⟨41166145508630997437819147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27444097005753998291879431 41166145508630997437819147)
    ·
      refine ⟨61749218262946496156728721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41166145508630997437819147 61749218262946496156728721)
      ·
        refine ⟨46311913697209872117546541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61749218262946496156728721 46311913697209872117546541)
        ·
          refine ⟨17366967636453702044079953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46311913697209872117546541 17366967636453702044079953)
          ·
            refine ⟨13025225727340276533059965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17366967636453702044079953 13025225727340276533059965)
            ·
              refine ⟨4884459647752603699897487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13025225727340276533059965 4884459647752603699897487)
              ·
                refine ⟨7326689471628905549846231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4884459647752603699897487 7326689471628905549846231)
                ·
                  refine ⟨10990034207443358324769347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7326689471628905549846231 10990034207443358324769347)
                  ·
                    refine ⟨16485051311165037487154021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10990034207443358324769347 16485051311165037487154021)
                    ·
                      refine ⟨3090947120843444528841379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16485051311165037487154021 3090947120843444528841379)
                      ·
                        rfl

theorem cell23_6019598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 1, 1, 1, 4].length) (baseStart_6019598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019598 prefixEnd_6019598 := by exact prefixLift 6019598
  have htrace : WordTrace (prefixWord ++ tailWord_6019598) baseStart_6019598 baseEnd_6019598 := by
    simpa [prefixWord, tailWord_6019598, baseEnd_6019598] using wordTrace_append hprefix tailTrace_6019598
  have hstable : (prefixWord ++ tailWord_6019598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019598).length < 2 ^ (prefixWord ++ tailWord_6019598).sum := by decide
  have hdescent : baseEnd_6019598 < baseStart_6019598 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019604 : List Nat := [2, 4, 3, 1, 1, 12]
def baseStart_6019604 : Nat := 118140960795 + 6019604 * 2 ^ 59
def prefixEnd_6019604 : Nat := 4983230072969 + 3 ^ 40 * 6019604 * 2
def baseEnd_6019604 : Nat := 12719959677890417717557

theorem tailTrace_6019604 : CollatzResearch.WordTrace tailWord_6019604 prefixEnd_6019604 12719959677890417717557 := by
  unfold tailWord_6019604
  simp only [CollatzResearch.WordTrace]
  refine ⟨109776497442005124679876933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146368663256006832906502577 109776497442005124679876933)
  ·
    refine ⟨20583093270375960877476925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109776497442005124679876933 20583093270375960877476925)
    ·
      refine ⟨7718659976390985329053847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20583093270375960877476925 7718659976390985329053847)
      ·
        refine ⟨11577989964586477993580771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7718659976390985329053847 11577989964586477993580771)
        ·
          refine ⟨17366984946879716990371157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11577989964586477993580771 17366984946879716990371157)
          ·
            refine ⟨12719959677890417717557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 17366984946879716990371157 12719959677890417717557)
            ·
              rfl

theorem cell23_6019604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 12].length) (baseStart_6019604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019604 prefixEnd_6019604 := by exact prefixLift 6019604
  have htrace : WordTrace (prefixWord ++ tailWord_6019604) baseStart_6019604 baseEnd_6019604 := by
    simpa [prefixWord, tailWord_6019604, baseEnd_6019604] using wordTrace_append hprefix tailTrace_6019604
  have hstable : (prefixWord ++ tailWord_6019604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019604).length < 2 ^ (prefixWord ++ tailWord_6019604).sum := by decide
  have hdescent : baseEnd_6019604 < baseStart_6019604 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019617 : List Nat := [1, 2, 3, 2, 2, 1, 1, 1, 1, 9]
def baseStart_6019617 : Nat := 118140960795 + 6019617 * 2 ^ 59
def prefixEnd_6019617 : Nat := 4983230072969 + 3 ^ 40 * 6019617 * 2
def baseEnd_6019617 : Nat := 1030318958991959984834597

theorem tailTrace_6019617 : CollatzResearch.WordTrace tailWord_6019617 prefixEnd_6019617 1030318958991959984834597 := by
  unfold tailWord_6019617
  simp only [CollatzResearch.WordTrace]
  refine ⟨219553469032963152579977105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146368979355308768386651403 219553469032963152579977105)
  ·
    refine ⟨164665101774722364434982829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219553469032963152579977105 164665101774722364434982829)
    ·
      refine ⟨61749413165520886663118561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164665101774722364434982829 61749413165520886663118561)
      ·
        refine ⟨46312059874140664997338921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61749413165520886663118561 46312059874140664997338921)
        ·
          refine ⟨34734044905605498748004191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46312059874140664997338921 34734044905605498748004191)
          ·
            refine ⟨52101067358408248122006287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34734044905605498748004191 52101067358408248122006287)
            ·
              refine ⟨78151601037612372183009431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52101067358408248122006287 78151601037612372183009431)
              ·
                refine ⟨117227401556418558274514147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78151601037612372183009431 117227401556418558274514147)
                ·
                  refine ⟨175841102334627837411771221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117227401556418558274514147 175841102334627837411771221)
                  ·
                    refine ⟨1030318958991959984834597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 175841102334627837411771221 1030318958991959984834597)
                    ·
                      rfl

theorem cell23_6019617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 9].length) (baseStart_6019617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019617 prefixEnd_6019617 := by exact prefixLift 6019617
  have htrace : WordTrace (prefixWord ++ tailWord_6019617) baseStart_6019617 baseEnd_6019617 := by
    simpa [prefixWord, tailWord_6019617, baseEnd_6019617] using wordTrace_append hprefix tailTrace_6019617
  have hstable : (prefixWord ++ tailWord_6019617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019617).length < 2 ^ (prefixWord ++ tailWord_6019617).sum := by decide
  have hdescent : baseEnd_6019617 < baseStart_6019617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019641 : List Nat := [1, 2, 1, 5, 1, 1, 1, 3, 3, 3, 2]
def baseStart_6019641 : Nat := 118140960795 + 6019641 * 2 ^ 59
def prefixEnd_6019641 : Nat := 4983230072969 + 3 ^ 40 * 6019641 * 2
def baseEnd_6019641 : Nat := 3090969200511587860603681

theorem tailTrace_6019641 : CollatzResearch.WordTrace tailWord_6019641 prefixEnd_6019641 3090969200511587860603681 := by
  unfold tailWord_6019641
  simp only [CollatzResearch.WordTrace]
  refine ⟨219554344384876204678850777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146369562923250803119233851 219554344384876204678850777)
  ·
    refine ⟨164665758288657153509138083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219554344384876204678850777 164665758288657153509138083)
    ·
      refine ⟨246998637432985730263707125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164665758288657153509138083 246998637432985730263707125)
      ·
        refine ⟨23156122259342412212222543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 246998637432985730263707125 23156122259342412212222543)
        ·
          refine ⟨34734183389013618318333815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23156122259342412212222543 34734183389013618318333815)
          ·
            refine ⟨52101275083520427477500723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34734183389013618318333815 52101275083520427477500723)
            ·
              refine ⟨78151912625280641216251085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52101275083520427477500723 78151912625280641216251085)
              ·
                refine ⟨29306967234480240456094157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78151912625280641216251085 29306967234480240456094157)
                ·
                  refine ⟨10990112712930090171035309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29306967234480240456094157 10990112712930090171035309)
                  ·
                    refine ⟨4121292267348783814138241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10990112712930090171035309 4121292267348783814138241)
                    ·
                      refine ⟨3090969200511587860603681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4121292267348783814138241 3090969200511587860603681)
                      ·
                        rfl

theorem cell23_6019641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_6019641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019641 prefixEnd_6019641 := by exact prefixLift 6019641
  have htrace : WordTrace (prefixWord ++ tailWord_6019641) baseStart_6019641 baseEnd_6019641 := by
    simpa [prefixWord, tailWord_6019641, baseEnd_6019641] using wordTrace_append hprefix tailTrace_6019641
  have hstable : (prefixWord ++ tailWord_6019641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019641).length < 2 ^ (prefixWord ++ tailWord_6019641).sum := by decide
  have hdescent : baseEnd_6019641 < baseStart_6019641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019647 : List Nat := [1, 1, 2, 2, 3, 2, 1, 2, 1, 8]
def baseStart_6019647 : Nat := 118140960795 + 6019647 * 2 ^ 59
def prefixEnd_6019647 : Nat := 4983230072969 + 3 ^ 40 * 6019647 * 2
def baseEnd_6019647 : Nat := 1030324093798504945709551

theorem tailTrace_6019647 : CollatzResearch.WordTrace tailWord_6019647 prefixEnd_6019647 1030324093798504945709551 := by
  unfold tailWord_6019647
  simp only [CollatzResearch.WordTrace]
  refine ⟨219554563222854467703569195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146369708815236311802379463 219554563222854467703569195)
  ·
    refine ⟨329331844834281701555353793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219554563222854467703569195 329331844834281701555353793)
    ·
      refine ⟨246998883625711276166515345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 329331844834281701555353793 246998883625711276166515345)
      ·
        refine ⟨185249162719283457124886509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246998883625711276166515345 185249162719283457124886509)
        ·
          refine ⟨69468436019731296421832441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185249162719283457124886509 69468436019731296421832441)
          ·
            refine ⟨52101327014798472316374331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69468436019731296421832441 52101327014798472316374331)
            ·
              refine ⟨78151990522197708474561497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52101327014798472316374331 78151990522197708474561497)
              ·
                refine ⟨58613992891648281355921123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78151990522197708474561497 58613992891648281355921123)
                ·
                  refine ⟨87920989337472422033881685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58613992891648281355921123 87920989337472422033881685)
                  ·
                    refine ⟨1030324093798504945709551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 87920989337472422033881685 1030324093798504945709551)
                    ·
                      rfl

theorem cell23_6019647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 8].length) (baseStart_6019647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019647 prefixEnd_6019647 := by exact prefixLift 6019647
  have htrace : WordTrace (prefixWord ++ tailWord_6019647) baseStart_6019647 baseEnd_6019647 := by
    simpa [prefixWord, tailWord_6019647, baseEnd_6019647] using wordTrace_append hprefix tailTrace_6019647
  have hstable : (prefixWord ++ tailWord_6019647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019647).length < 2 ^ (prefixWord ++ tailWord_6019647).sum := by decide
  have hdescent : baseEnd_6019647 < baseStart_6019647 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019652 : List Nat := [2, 3, 5, 1, 1, 1, 1, 3, 1, 2, 3]
def baseStart_6019652 : Nat := 118140960795 + 6019652 * 2 ^ 59
def prefixEnd_6019652 : Nat := 4983230072969 + 3 ^ 40 * 6019652 * 2
def baseEnd_6019652 : Nat := 3090974848798787317566131

theorem tailTrace_6019652 : CollatzResearch.WordTrace tailWord_6019652 prefixEnd_6019652 3090974848798787317566131 := by
  unfold tailWord_6019652
  simp only [CollatzResearch.WordTrace]
  refine ⟨109777372793918176778750605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146369830391890902371667473 109777372793918176778750605)
  ·
    refine ⟨41166514797719316292031477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109777372793918176778750605 41166514797719316292031477)
    ·
      refine ⟨3859360762286185902377951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41166514797719316292031477 3859360762286185902377951)
      ·
        refine ⟨5789041143429278853566927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3859360762286185902377951 5789041143429278853566927)
        ·
          refine ⟨8683561715143918280350391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5789041143429278853566927 8683561715143918280350391)
          ·
            refine ⟨13025342572715877420525587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8683561715143918280350391 13025342572715877420525587)
            ·
              refine ⟨19538013859073816130788381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13025342572715877420525587 19538013859073816130788381)
              ·
                refine ⟨7326755197152681049045643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19538013859073816130788381 7326755197152681049045643)
                ·
                  refine ⟨10990132795729021573568465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7326755197152681049045643 10990132795729021573568465)
                  ·
                    refine ⟨8242599596796766180176349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10990132795729021573568465 8242599596796766180176349)
                    ·
                      refine ⟨3090974848798787317566131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8242599596796766180176349 3090974848798787317566131)
                      ·
                        rfl

theorem cell23_6019652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_6019652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019652 prefixEnd_6019652 := by exact prefixLift 6019652
  have htrace : WordTrace (prefixWord ++ tailWord_6019652) baseStart_6019652 baseEnd_6019652 := by
    simpa [prefixWord, tailWord_6019652, baseEnd_6019652] using wordTrace_append hprefix tailTrace_6019652
  have hstable : (prefixWord ++ tailWord_6019652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019652).length < 2 ^ (prefixWord ++ tailWord_6019652).sum := by decide
  have hdescent : baseEnd_6019652 < baseStart_6019652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019658 : List Nat := [3, 1, 2, 1, 1, 5, 1, 3, 1, 3, 2]
def baseStart_6019658 : Nat := 118140960795 + 6019658 * 2 ^ 59
def prefixEnd_6019658 : Nat := 4983230072969 + 3 ^ 40 * 6019658 * 2
def baseEnd_6019658 : Nat := 3090977929682714294091103

theorem tailTrace_6019658 : CollatzResearch.WordTrace tailWord_6019658 prefixEnd_6019658 3090977929682714294091103 := by
  unfold tailWord_6019658
  simp only [CollatzResearch.WordTrace]
  refine ⟨54888741106453654145554907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146369976283876411054813085 54888741106453654145554907)
  ·
    refine ⟨82333111659680481218332361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54888741106453654145554907 82333111659680481218332361)
    ·
      refine ⟨61749833744760360913749271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82333111659680481218332361 61749833744760360913749271)
      ·
        refine ⟨92624750617140541370623907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61749833744760360913749271 92624750617140541370623907)
        ·
          refine ⟨138937125925710812055935861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92624750617140541370623907 138937125925710812055935861)
          ·
            refine ⟨13025355555535388630243987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 138937125925710812055935861 13025355555535388630243987)
            ·
              refine ⟨19538033333303082945365981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13025355555535388630243987 19538033333303082945365981)
              ·
                refine ⟨7326762499988656104512243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19538033333303082945365981 7326762499988656104512243)
                ·
                  refine ⟨10990143749982984156768365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7326762499988656104512243 10990143749982984156768365)
                  ·
                    refine ⟨4121303906243619058788137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10990143749982984156768365 4121303906243619058788137)
                    ·
                      refine ⟨3090977929682714294091103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4121303906243619058788137 3090977929682714294091103)
                      ·
                        rfl

theorem cell23_6019658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 3, 1, 3, 2].length) (baseStart_6019658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019658 prefixEnd_6019658 := by exact prefixLift 6019658
  have htrace : WordTrace (prefixWord ++ tailWord_6019658) baseStart_6019658 baseEnd_6019658 := by
    simpa [prefixWord, tailWord_6019658, baseEnd_6019658] using wordTrace_append hprefix tailTrace_6019658
  have hstable : (prefixWord ++ tailWord_6019658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019658).length < 2 ^ (prefixWord ++ tailWord_6019658).sum := by decide
  have hdescent : baseEnd_6019658 < baseStart_6019658 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019682 : List Nat := [3, 3, 2, 3, 2, 1, 1, 1, 1, 3, 3]
def baseStart_6019682 : Nat := 118140960795 + 6019682 * 2 ^ 59
def prefixEnd_6019682 : Nat := 4983230072969 + 3 ^ 40 * 6019682 * 2
def baseEnd_6019682 : Nat := 3090990253218422200190993

theorem tailTrace_6019682 : CollatzResearch.WordTrace tailWord_6019682 prefixEnd_6019682 3090990253218422200190993 := by
  unfold tailWord_6019682
  simp only [CollatzResearch.WordTrace]
  refine ⟨54888959944431917170273325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146370559851818445787395533 54888959944431917170273325)
  ·
    refine ⟨20583359979161968938852497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54888959944431917170273325 20583359979161968938852497)
    ·
      refine ⟨15437519984371476704139373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20583359979161968938852497 15437519984371476704139373)
      ·
        refine ⟨5789069994139303764052265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15437519984371476704139373 5789069994139303764052265)
        ·
          refine ⟨4341802495604477823039199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5789069994139303764052265 4341802495604477823039199)
          ·
            refine ⟨6512703743406716734558799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4341802495604477823039199 6512703743406716734558799)
            ·
              refine ⟨9769055615110075101838199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6512703743406716734558799 9769055615110075101838199)
              ·
                refine ⟨14653583422665112652757299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9769055615110075101838199 14653583422665112652757299)
                ·
                  refine ⟨21980375133997668979135949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14653583422665112652757299 21980375133997668979135949)
                  ·
                    refine ⟨8242640675249125867175981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21980375133997668979135949 8242640675249125867175981)
                    ·
                      refine ⟨3090990253218422200190993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8242640675249125867175981 3090990253218422200190993)
                      ·
                        rfl

theorem cell23_6019682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_6019682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019682 prefixEnd_6019682 := by exact prefixLift 6019682
  have htrace : WordTrace (prefixWord ++ tailWord_6019682) baseStart_6019682 baseEnd_6019682 := by
    simpa [prefixWord, tailWord_6019682, baseEnd_6019682] using wordTrace_append hprefix tailTrace_6019682
  have hstable : (prefixWord ++ tailWord_6019682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019682).length < 2 ^ (prefixWord ++ tailWord_6019682).sum := by decide
  have hdescent : baseEnd_6019682 < baseStart_6019682 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019684 : List Nat := [2, 3, 1, 1, 2, 2, 1, 3, 2, 2, 4]
def baseStart_6019684 : Nat := 118140960795 + 6019684 * 2 ^ 59
def prefixEnd_6019684 : Nat := 4983230072969 + 3 ^ 40 * 6019684 * 2
def baseEnd_6019684 : Nat := 3090991280179731192365983

theorem tailTrace_6019684 : CollatzResearch.WordTrace tailWord_6019684 prefixEnd_6019684 3090991280179731192365983 := by
  unfold tailWord_6019684
  simp only [CollatzResearch.WordTrace]
  refine ⟨109777956361860211511333053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146370608482480282015110737 109777956361860211511333053)
  ·
    refine ⟨41166733635697579316749895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109777956361860211511333053 41166733635697579316749895)
    ·
      refine ⟨61750100453546368975124843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41166733635697579316749895 61750100453546368975124843)
      ·
        refine ⟨92625150680319553462687265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61750100453546368975124843 92625150680319553462687265)
        ·
          refine ⟨69468863010239665097015449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92625150680319553462687265 69468863010239665097015449)
          ·
            refine ⟨52101647257679748822761587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69468863010239665097015449 52101647257679748822761587)
            ·
              refine ⟨78152470886519623234142381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52101647257679748822761587 78152470886519623234142381)
              ·
                refine ⟨29307176582444858712803393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78152470886519623234142381 29307176582444858712803393)
                ·
                  refine ⟨21980382436833644034602545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29307176582444858712803393 21980382436833644034602545)
                  ·
                    refine ⟨16485286827625233025951909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21980382436833644034602545 16485286827625233025951909)
                    ·
                      refine ⟨3090991280179731192365983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16485286827625233025951909 3090991280179731192365983)
                      ·
                        rfl

theorem cell23_6019684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_6019684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019684 prefixEnd_6019684 := by exact prefixLift 6019684
  have htrace : WordTrace (prefixWord ++ tailWord_6019684) baseStart_6019684 baseEnd_6019684 := by
    simpa [prefixWord, tailWord_6019684, baseEnd_6019684] using wordTrace_append hprefix tailTrace_6019684
  have hstable : (prefixWord ++ tailWord_6019684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019684).length < 2 ^ (prefixWord ++ tailWord_6019684).sum := by decide
  have hdescent : baseEnd_6019684 < baseStart_6019684 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019758 : List Nat := [4, 1, 4, 1, 1, 1, 1, 3, 2, 5]
def baseStart_6019758 : Nat := 118140960795 + 6019758 * 2 ^ 59
def prefixEnd_6019758 : Nat := 4983230072969 + 3 ^ 40 * 6019758 * 2
def baseEnd_6019758 : Nat := 1030343092582721300946881

theorem tailTrace_6019758 : CollatzResearch.WordTrace tailWord_6019758 prefixEnd_6019758 1030343092582721300946881 := by
  unfold tailWord_6019758
  simp only [CollatzResearch.WordTrace]
  refine ⟨27444826465681541707607491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146372407816968222440573285 27444826465681541707607491)
  ·
    refine ⟨41167239698522312561411237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27444826465681541707607491 41167239698522312561411237)
    ·
      refine ⟨7718857443472933605264607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41167239698522312561411237 7718857443472933605264607)
      ·
        refine ⟨11578286165209400407896911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7718857443472933605264607 11578286165209400407896911)
        ·
          refine ⟨17367429247814100611845367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11578286165209400407896911 17367429247814100611845367)
          ·
            refine ⟨26051143871721150917768051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17367429247814100611845367 26051143871721150917768051)
            ·
              refine ⟨39076715807581726376652077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26051143871721150917768051 39076715807581726376652077)
              ·
                refine ⟨14653768427843147391244529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39076715807581726376652077 14653768427843147391244529)
                ·
                  refine ⟨10990326320882360543433397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14653768427843147391244529 10990326320882360543433397)
                  ·
                    refine ⟨1030343092582721300946881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10990326320882360543433397 1030343092582721300946881)
                    ·
                      rfl

theorem cell23_6019758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_6019758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019758 prefixEnd_6019758 := by exact prefixLift 6019758
  have htrace : WordTrace (prefixWord ++ tailWord_6019758) baseStart_6019758 baseEnd_6019758 := by
    simpa [prefixWord, tailWord_6019758, baseEnd_6019758] using wordTrace_append hprefix tailTrace_6019758
  have hstable : (prefixWord ++ tailWord_6019758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019758).length < 2 ^ (prefixWord ++ tailWord_6019758).sum := by decide
  have hdescent : baseEnd_6019758 < baseStart_6019758 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019868 : List Nat := [2, 2, 3, 1, 1, 3, 1, 4, 1, 1, 4]
def baseStart_6019868 : Nat := 118140960795 + 6019868 * 2 ^ 59
def prefixEnd_6019868 : Nat := 4983230072969 + 3 ^ 40 * 6019868 * 2
def baseEnd_6019868 : Nat := 3091085760620158472465137

theorem tailTrace_6019868 : CollatzResearch.WordTrace tailWord_6019868 prefixEnd_6019868 3091085760620158472465137 := by
  unfold tailWord_6019868
  simp only [CollatzResearch.WordTrace]
  refine ⟨109781311877526911223682129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146375082503369214964909505 109781311877526911223682129)
  ·
    refine ⟨82335983908145183417761597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109781311877526911223682129 82335983908145183417761597)
    ·
      refine ⟨30875993965554443781660599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82335983908145183417761597 30875993965554443781660599)
      ·
        refine ⟨46313990948331665672490899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30875993965554443781660599 46313990948331665672490899)
        ·
          refine ⟨69470986422497498508736349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46313990948331665672490899 69470986422497498508736349)
          ·
            refine ⟨26051619908436561940776131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69470986422497498508736349 26051619908436561940776131)
            ·
              refine ⟨39077429862654842911164197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26051619908436561940776131 39077429862654842911164197)
              ·
                refine ⟨7327018099247783045843287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39077429862654842911164197 7327018099247783045843287)
                ·
                  refine ⟨10990527148871674568764931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7327018099247783045843287 10990527148871674568764931)
                  ·
                    refine ⟨16485790723307511853147397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10990527148871674568764931 16485790723307511853147397)
                    ·
                      refine ⟨3091085760620158472465137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16485790723307511853147397 3091085760620158472465137)
                      ·
                        rfl

theorem cell23_6019868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_6019868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019868 prefixEnd_6019868 := by exact prefixLift 6019868
  have htrace : WordTrace (prefixWord ++ tailWord_6019868) baseStart_6019868 baseEnd_6019868 := by
    simpa [prefixWord, tailWord_6019868, baseEnd_6019868] using wordTrace_append hprefix tailTrace_6019868
  have hstable : (prefixWord ++ tailWord_6019868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019868).length < 2 ^ (prefixWord ++ tailWord_6019868).sum := by decide
  have hdescent : baseEnd_6019868 < baseStart_6019868 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019891 : List Nat := [1, 1, 1, 2, 6, 3, 9]
def baseStart_6019891 : Nat := 118140960795 + 6019891 * 2 ^ 59
def prefixEnd_6019891 : Nat := 4983230072969 + 3 ^ 40 * 6019891 * 2
def baseEnd_6019891 : Nat := 38161698403397677561451

theorem tailTrace_6019891 : CollatzResearch.WordTrace tailWord_6019891 prefixEnd_6019891 38161698403397677561451 := by
  unfold tailWord_6019891
  simp only [CollatzResearch.WordTrace]
  refine ⟨219563462633970497375451527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146375641755980331583634351 219563462633970497375451527)
  ·
    refine ⟨329345193950955746063177291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219563462633970497375451527 329345193950955746063177291)
    ·
      refine ⟨494017790926433619094765937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329345193950955746063177291 494017790926433619094765937)
      ·
        refine ⟨370513343194825214321074453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 494017790926433619094765937 370513343194825214321074453)
        ·
          refine ⟨17367812962257431921300365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 370513343194825214321074453 17367812962257431921300365)
          ·
            refine ⟨6512929860846536970487637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17367812962257431921300365 6512929860846536970487637)
            ·
              refine ⟨38161698403397677561451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6512929860846536970487637 38161698403397677561451)
              ·
                rfl

theorem cell23_6019891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 9].length) (baseStart_6019891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019891 prefixEnd_6019891 := by exact prefixLift 6019891
  have htrace : WordTrace (prefixWord ++ tailWord_6019891) baseStart_6019891 baseEnd_6019891 := by
    simpa [prefixWord, tailWord_6019891, baseEnd_6019891] using wordTrace_append hprefix tailTrace_6019891
  have hstable : (prefixWord ++ tailWord_6019891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019891).length < 2 ^ (prefixWord ++ tailWord_6019891).sum := by decide
  have hdescent : baseEnd_6019891 < baseStart_6019891 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019975 : List Nat := [1, 1, 4, 2, 3, 1, 1, 3, 1, 4, 2]
def baseStart_6019975 : Nat := 118140960795 + 6019975 * 2 ^ 59
def prefixEnd_6019975 : Nat := 4983230072969 + 3 ^ 40 * 6019975 * 2
def baseEnd_6019975 : Nat := 3091140703050189553827145

theorem tailTrace_6019975 : CollatzResearch.WordTrace tailWord_6019975 prefixEnd_6019975 3091140703050189553827145 := by
  unfold tailWord_6019975
  simp only [CollatzResearch.WordTrace]
  refine ⟨219566526365666179721509379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146377684243777453147672919 219566526365666179721509379)
  ·
    refine ⟨329349789548499269582264069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219566526365666179721509379 329349789548499269582264069)
    ·
      refine ⟨61753085540343613046674513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 329349789548499269582264069 61753085540343613046674513)
      ·
        refine ⟨46314814155257709785005885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61753085540343613046674513 46314814155257709785005885)
        ·
          refine ⟨17368055308221641169377207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46314814155257709785005885 17368055308221641169377207)
          ·
            refine ⟨26052082962332461754065811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17368055308221641169377207 26052082962332461754065811)
            ·
              refine ⟨39078124443498692631098717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26052082962332461754065811 39078124443498692631098717)
              ·
                refine ⟨14654296666312009736662019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39078124443498692631098717 14654296666312009736662019)
                ·
                  refine ⟨21981444999468014604993029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14654296666312009736662019 21981444999468014604993029)
                  ·
                    refine ⟨4121520937400252738436193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21981444999468014604993029 4121520937400252738436193)
                    ·
                      refine ⟨3091140703050189553827145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4121520937400252738436193 3091140703050189553827145)
                      ·
                        rfl

theorem cell23_6019975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 4, 2].length) (baseStart_6019975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019975 prefixEnd_6019975 := by exact prefixLift 6019975
  have htrace : WordTrace (prefixWord ++ tailWord_6019975) baseStart_6019975 baseEnd_6019975 := by
    simpa [prefixWord, tailWord_6019975, baseEnd_6019975] using wordTrace_append hprefix tailTrace_6019975
  have hstable : (prefixWord ++ tailWord_6019975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019975).length < 2 ^ (prefixWord ++ tailWord_6019975).sum := by decide
  have hdescent : baseEnd_6019975 < baseStart_6019975 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019988 : List Nat := [2, 4, 2, 1, 1, 1, 1, 2, 1, 4, 4]
def baseStart_6019988 : Nat := 118140960795 + 6019988 * 2 ^ 59
def prefixEnd_6019988 : Nat := 4983230072969 + 3 ^ 40 * 6019988 * 2
def baseEnd_6019988 : Nat := 3091147378298698002964585

theorem tailTrace_6019988 : CollatzResearch.WordTrace tailWord_6019988 prefixEnd_6019988 3091147378298698002964585 := by
  unfold tailWord_6019988
  simp only [CollatzResearch.WordTrace]
  refine ⟨109783500257309541470866309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146378000343079388627821745 109783500257309541470866309)
  ·
    refine ⟨20584406298245539025787433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109783500257309541470866309 20584406298245539025787433)
    ·
      refine ⟨15438304723684154269340575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20584406298245539025787433 15438304723684154269340575)
      ·
        refine ⟨23157457085526231404010863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15438304723684154269340575 23157457085526231404010863)
        ·
          refine ⟨34736185628289347106016295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23157457085526231404010863 34736185628289347106016295)
          ·
            refine ⟨52104278442434020659024443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34736185628289347106016295 52104278442434020659024443)
            ·
              refine ⟨78156417663651030988536665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52104278442434020659024443 78156417663651030988536665)
              ·
                refine ⟨58617313247738273241402499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78156417663651030988536665 58617313247738273241402499)
                ·
                  refine ⟨87925969871607409862103749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58617313247738273241402499 87925969871607409862103749)
                  ·
                    refine ⟨16486119350926389349144453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 87925969871607409862103749 16486119350926389349144453)
                    ·
                      refine ⟨3091147378298698002964585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16486119350926389349144453 3091147378298698002964585)
                      ·
                        rfl

theorem cell23_6019988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_6019988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019988 prefixEnd_6019988 := by exact prefixLift 6019988
  have htrace : WordTrace (prefixWord ++ tailWord_6019988) baseStart_6019988 baseEnd_6019988 := by
    simpa [prefixWord, tailWord_6019988, baseEnd_6019988] using wordTrace_append hprefix tailTrace_6019988
  have hstable : (prefixWord ++ tailWord_6019988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019988).length < 2 ^ (prefixWord ++ tailWord_6019988).sum := by decide
  have hdescent : baseEnd_6019988 < baseStart_6019988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6019996 : List Nat := [2, 2, 3, 3, 2, 2, 2, 1, 1, 3, 2]
def baseStart_6019996 : Nat := 118140960795 + 6019996 * 2 ^ 59
def prefixEnd_6019996 : Nat := 4983230072969 + 3 ^ 40 * 6019996 * 2
def baseEnd_6019996 : Nat := 3091151486143933971664549

theorem tailTrace_6019996 : CollatzResearch.WordTrace tailWord_6019996 prefixEnd_6019996 3091151486143933971664549 := by
  unfold tailWord_6019996
  simp only [CollatzResearch.WordTrace]
  refine ⟨109783646149295050154011921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146378194865726733538682561 109783646149295050154011921)
  ·
    refine ⟨82337734611971287615508941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109783646149295050154011921 82337734611971287615508941)
    ·
      refine ⟨30876650479489232855815853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82337734611971287615508941 30876650479489232855815853)
      ·
        refine ⟨11578743929808462320930945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30876650479489232855815853 11578743929808462320930945)
        ·
          refine ⟨8684057947356346740698209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11578743929808462320930945 8684057947356346740698209)
          ·
            refine ⟨6513043460517260055523657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8684057947356346740698209 6513043460517260055523657)
            ·
              refine ⟨4884782595387945041642743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6513043460517260055523657 4884782595387945041642743)
              ·
                refine ⟨7327173893081917562464115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4884782595387945041642743 7327173893081917562464115)
                ·
                  refine ⟨10990760839622876343696173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7327173893081917562464115 10990760839622876343696173)
                  ·
                    refine ⟨4121535314858578628886065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10990760839622876343696173 4121535314858578628886065)
                    ·
                      refine ⟨3091151486143933971664549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4121535314858578628886065 3091151486143933971664549)
                      ·
                        rfl

theorem cell23_6019996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_6019996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6019996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6019996 prefixEnd_6019996 := by exact prefixLift 6019996
  have htrace : WordTrace (prefixWord ++ tailWord_6019996) baseStart_6019996 baseEnd_6019996 := by
    simpa [prefixWord, tailWord_6019996, baseEnd_6019996] using wordTrace_append hprefix tailTrace_6019996
  have hstable : (prefixWord ++ tailWord_6019996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6019996).length < 2 ^ (prefixWord ++ tailWord_6019996).sum := by decide
  have hdescent : baseEnd_6019996 < baseStart_6019996 := by decide
  rcases family_descends (prefixWord ++ tailWord_6019996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6020048 : List Nat := [2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 4]
def baseStart_6020048 : Nat := 118140960795 + 6020048 * 2 ^ 59
def prefixEnd_6020048 : Nat := 4983230072969 + 3 ^ 40 * 6020048 * 2
def baseEnd_6020048 : Nat := 3091178187137967768214309

theorem tailTrace_6020048 : CollatzResearch.WordTrace tailWord_6020048 prefixEnd_6020048 3091178187137967768214309 := by
  unfold tailWord_6020048
  simp only [CollatzResearch.WordTrace]
  refine ⟨109784594447200856594458399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146379459262934475459277865 109784594447200856594458399)
  ·
    refine ⟨164676891670801284891687599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109784594447200856594458399 164676891670801284891687599)
    ·
      refine ⟨247015337506201927337531399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164676891670801284891687599 247015337506201927337531399)
      ·
        refine ⟨370523006259302891006297099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247015337506201927337531399 370523006259302891006297099)
        ·
          refine ⟨555784509388954336509445649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 370523006259302891006297099 555784509388954336509445649)
          ·
            refine ⟨416838382041715752382084237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 555784509388954336509445649 416838382041715752382084237)
            ·
              refine ⟨156314393265643407143281589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 416838382041715752382084237 156314393265643407143281589)
              ·
                refine ⟨14654474368654069419682649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 156314393265643407143281589 14654474368654069419682649)
                ·
                  refine ⟨10990855776490552064761987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14654474368654069419682649 10990855776490552064761987)
                  ·
                    refine ⟨16486283664735828097142981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10990855776490552064761987 16486283664735828097142981)
                    ·
                      refine ⟨3091178187137967768214309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16486283664735828097142981 3091178187137967768214309)
                      ·
                        rfl

theorem cell23_6020048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 4].length) (baseStart_6020048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6020048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6020048 prefixEnd_6020048 := by exact prefixLift 6020048
  have htrace : WordTrace (prefixWord ++ tailWord_6020048) baseStart_6020048 baseEnd_6020048 := by
    simpa [prefixWord, tailWord_6020048, baseEnd_6020048] using wordTrace_append hprefix tailTrace_6020048
  have hstable : (prefixWord ++ tailWord_6020048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6020048).length < 2 ^ (prefixWord ++ tailWord_6020048).sum := by decide
  have hdescent : baseEnd_6020048 < baseStart_6020048 := by decide
  rcases family_descends (prefixWord ++ tailWord_6020048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6020068 : List Nat := [2, 3, 1, 1, 1, 1, 2, 2, 3, 4, 3]
def baseStart_6020068 : Nat := 118140960795 + 6020068 * 2 ^ 59
def prefixEnd_6020068 : Nat := 4983230072969 + 3 ^ 40 * 6020068 * 2
def baseEnd_6020068 : Nat := 3091188456751057689964217

theorem tailTrace_6020068 : CollatzResearch.WordTrace tailWord_6020068 prefixEnd_6020068 3091188456751057689964217 := by
  unfold tailWord_6020068
  simp only [CollatzResearch.WordTrace]
  refine ⟨109784959177164628302322429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146379945569552837736429905 109784959177164628302322429)
  ·
    refine ⟨41169359691436735613370911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109784959177164628302322429 41169359691436735613370911)
    ·
      refine ⟨61754039537155103420056367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41169359691436735613370911 61754039537155103420056367)
      ·
        refine ⟨92631059305732655130084551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61754039537155103420056367 92631059305732655130084551)
        ·
          refine ⟨138946588958598982695126827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92631059305732655130084551 138946588958598982695126827)
          ·
            refine ⟨208419883437898474042690241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138946588958598982695126827 208419883437898474042690241)
            ·
              refine ⟨156314912578423855532017681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208419883437898474042690241 156314912578423855532017681)
              ·
                refine ⟨117236184433817891649013261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156314912578423855532017681 117236184433817891649013261)
                ·
                  refine ⟨43963569162681709368379973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117236184433817891649013261 43963569162681709368379973)
                  ·
                    refine ⟨8243169218002820506571245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43963569162681709368379973 8243169218002820506571245)
                    ·
                      refine ⟨3091188456751057689964217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8243169218002820506571245 3091188456751057689964217)
                      ·
                        rfl

theorem cell23_6020068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 3, 4, 3].length) (baseStart_6020068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6020068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6020068 prefixEnd_6020068 := by exact prefixLift 6020068
  have htrace : WordTrace (prefixWord ++ tailWord_6020068) baseStart_6020068 baseEnd_6020068 := by
    simpa [prefixWord, tailWord_6020068, baseEnd_6020068] using wordTrace_append hprefix tailTrace_6020068
  have hstable : (prefixWord ++ tailWord_6020068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6020068).length < 2 ^ (prefixWord ++ tailWord_6020068).sum := by decide
  have hdescent : baseEnd_6020068 < baseStart_6020068 := by decide
  rcases family_descends (prefixWord ++ tailWord_6020068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6020142 : List Nat := [4, 1, 3, 1, 1, 1, 2, 2, 1, 5, 2]
def baseStart_6020142 : Nat := 118140960795 + 6020142 * 2 ^ 59
def prefixEnd_6020142 : Nat := 4983230072969 + 3 ^ 40 * 6020142 * 2
def baseEnd_6020142 : Nat := 3091226454319490400438877

theorem tailTrace_6020142 : CollatzResearch.WordTrace tailWord_6020142 prefixEnd_6020142 3091226454319490400438877 := by
  unfold tailWord_6020142
  simp only [CollatzResearch.WordTrace]
  refine ⟨27446577169507645905354835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146381744904040778161892453 27446577169507645905354835)
  ·
    refine ⟨41169865754261468858032253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27446577169507645905354835 41169865754261468858032253)
    ·
      refine ⟨15438699657848050821762095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41169865754261468858032253 15438699657848050821762095)
      ·
        refine ⟨23158049486772076232643143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15438699657848050821762095 23158049486772076232643143)
        ·
          refine ⟨34737074230158114348964715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23158049486772076232643143 34737074230158114348964715)
          ·
            refine ⟨52105611345237171523447073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34737074230158114348964715 52105611345237171523447073)
            ·
              refine ⟨39079208508927878642585305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52105611345237171523447073 39079208508927878642585305)
              ·
                refine ⟨29309406381695908981938979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39079208508927878642585305 29309406381695908981938979)
                ·
                  refine ⟨43964109572543863472908469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29309406381695908981938979 43964109572543863472908469)
                  ·
                    refine ⟨4121635272425987200585169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43964109572543863472908469 4121635272425987200585169)
                    ·
                      refine ⟨3091226454319490400438877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4121635272425987200585169 3091226454319490400438877)
                      ·
                        rfl

theorem cell23_6020142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_6020142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6020142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6020142 prefixEnd_6020142 := by exact prefixLift 6020142
  have htrace : WordTrace (prefixWord ++ tailWord_6020142) baseStart_6020142 baseEnd_6020142 := by
    simpa [prefixWord, tailWord_6020142, baseEnd_6020142] using wordTrace_append hprefix tailTrace_6020142
  have hstable : (prefixWord ++ tailWord_6020142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6020142).length < 2 ^ (prefixWord ++ tailWord_6020142).sum := by decide
  have hdescent : baseEnd_6020142 < baseStart_6020142 := by decide
  rcases family_descends (prefixWord ++ tailWord_6020142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6020172 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 7, 2, 2]
def baseStart_6020172 : Nat := 118140960795 + 6020172 * 2 ^ 59
def prefixEnd_6020172 : Nat := 4983230072969 + 3 ^ 40 * 6020172 * 2
def baseEnd_6020172 : Nat := 3091241858739125283063739

theorem tailTrace_6020172 : CollatzResearch.WordTrace tailWord_6020172 prefixEnd_6020172 3091241858739125283063739 := by
  unfold tailWord_6020172
  simp only [CollatzResearch.WordTrace]
  refine ⟨109786855772976241183215385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146382474363968321577620513 109786855772976241183215385)
  ·
    refine ⟨82340141829732180887411539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109786855772976241183215385 82340141829732180887411539)
    ·
      refine ⟨123510212744598271331117309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82340141829732180887411539 123510212744598271331117309)
      ·
        refine ⟨46316329779224351749168991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123510212744598271331117309 46316329779224351749168991)
        ·
          refine ⟨69474494668836527623753487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46316329779224351749168991 69474494668836527623753487)
          ·
            refine ⟨104211742003254791435630231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69474494668836527623753487 104211742003254791435630231)
            ·
              refine ⟨156317613004882187153445347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104211742003254791435630231 156317613004882187153445347)
              ·
                refine ⟨234476419507323280730168021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156317613004882187153445347 234476419507323280730168021)
                ·
                  refine ⟨5495541082202889392113313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 234476419507323280730168021 5495541082202889392113313)
                  ·
                    refine ⟨4121655811652167044084985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5495541082202889392113313 4121655811652167044084985)
                    ·
                      refine ⟨3091241858739125283063739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4121655811652167044084985 3091241858739125283063739)
                      ·
                        rfl

theorem cell23_6020172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 7, 2, 2].length) (baseStart_6020172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6020172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6020172 prefixEnd_6020172 := by exact prefixLift 6020172
  have htrace : WordTrace (prefixWord ++ tailWord_6020172) baseStart_6020172 baseEnd_6020172 := by
    simpa [prefixWord, tailWord_6020172, baseEnd_6020172] using wordTrace_append hprefix tailTrace_6020172
  have hstable : (prefixWord ++ tailWord_6020172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6020172).length < 2 ^ (prefixWord ++ tailWord_6020172).sum := by decide
  have hdescent : baseEnd_6020172 < baseStart_6020172 := by decide
  rcases family_descends (prefixWord ++ tailWord_6020172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6020199 : List Nat := [1, 1, 5, 1, 1, 4, 3, 1, 2, 4]
def baseStart_6020199 : Nat := 118140960795 + 6020199 * 2 ^ 59
def prefixEnd_6020199 : Nat := 4983230072969 + 3 ^ 40 * 6020199 * 2
def baseEnd_6020199 : Nat := 1030418574238932225808705

theorem tailTrace_6020199 : CollatzResearch.WordTrace tailWord_6020199 prefixEnd_6020199 1030418574238932225808705 := by
  unfold tailWord_6020199
  simp only [CollatzResearch.WordTrace]
  refine ⟨219574696316854665977663651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146383130877903110651775767 219574696316854665977663651)
  ·
    refine ⟨329362044475281998966495477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219574696316854665977663651 329362044475281998966495477)
    ·
      refine ⟨30877691669557687403108951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 329362044475281998966495477 30877691669557687403108951)
      ·
        refine ⟨46316537504336531104663427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30877691669557687403108951 46316537504336531104663427)
        ·
          refine ⟨69474806256504796656995141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46316537504336531104663427 69474806256504796656995141)
          ·
            refine ⟨13026526173094649373186589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69474806256504796656995141 13026526173094649373186589)
            ·
              refine ⟨4884947314910493514944971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13026526173094649373186589 4884947314910493514944971)
              ·
                refine ⟨7327420972365740272417457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4884947314910493514944971 7327420972365740272417457)
                ·
                  refine ⟨5495565729274305204313093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7327420972365740272417457 5495565729274305204313093)
                  ·
                    refine ⟨1030418574238932225808705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5495565729274305204313093 1030418574238932225808705)
                    ·
                      rfl

theorem cell23_6020199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_6020199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6020199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6020199 prefixEnd_6020199 := by exact prefixLift 6020199
  have htrace : WordTrace (prefixWord ++ tailWord_6020199) baseStart_6020199 baseEnd_6020199 := by
    simpa [prefixWord, tailWord_6020199, baseEnd_6020199] using wordTrace_append hprefix tailTrace_6020199
  have hstable : (prefixWord ++ tailWord_6020199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6020199).length < 2 ^ (prefixWord ++ tailWord_6020199).sum := by decide
  have hdescent : baseEnd_6020199 < baseStart_6020199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6020199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6020202 : List Nat := [3, 1, 3, 2, 2, 1, 3, 1, 1, 2, 4]
def baseStart_6020202 : Nat := 118140960795 + 6020202 * 2 ^ 59
def prefixEnd_6020202 : Nat := 4983230072969 + 3 ^ 40 * 6020202 * 2
def baseEnd_6020202 : Nat := 3091257263158760165688601

theorem tailTrace_6020202 : CollatzResearch.WordTrace tailWord_6020202 prefixEnd_6020202 3091257263158760165688601 := by
  unfold tailWord_6020202
  simp only [CollatzResearch.WordTrace]
  refine ⟨54893701433960949372505715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146383203823895864993348573 54893701433960949372505715)
  ·
    refine ⟨82340552150941424058758573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54893701433960949372505715 82340552150941424058758573)
    ·
      refine ⟨30877707056603034022034465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82340552150941424058758573 30877707056603034022034465)
      ·
        refine ⟨23158280292452275516525849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30877707056603034022034465 23158280292452275516525849)
        ·
          refine ⟨17368710219339206637394387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23158280292452275516525849 17368710219339206637394387)
          ·
            refine ⟨26053065329008809956091581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17368710219339206637394387 26053065329008809956091581)
            ·
              refine ⟨9769899498378303733534343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26053065329008809956091581 9769899498378303733534343)
              ·
                refine ⟨14654849247567455600301515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9769899498378303733534343 14654849247567455600301515)
                ·
                  refine ⟨21982273871351183400452273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14654849247567455600301515 21982273871351183400452273)
                  ·
                    refine ⟨16486705403513387550339205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21982273871351183400452273 16486705403513387550339205)
                    ·
                      refine ⟨3091257263158760165688601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16486705403513387550339205 3091257263158760165688601)
                      ·
                        rfl

theorem cell23_6020202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_6020202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6020202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6020202 prefixEnd_6020202 := by exact prefixLift 6020202
  have htrace : WordTrace (prefixWord ++ tailWord_6020202) baseStart_6020202 baseEnd_6020202 := by
    simpa [prefixWord, tailWord_6020202, baseEnd_6020202] using wordTrace_append hprefix tailTrace_6020202
  have hstable : (prefixWord ++ tailWord_6020202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6020202).length < 2 ^ (prefixWord ++ tailWord_6020202).sum := by decide
  have hdescent : baseEnd_6020202 < baseStart_6020202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6020202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6020266 : List Nat := [3, 1, 5, 1, 1, 2, 1, 1, 3, 3, 2]
def baseStart_6020266 : Nat := 118140960795 + 6020266 * 2 ^ 59
def prefixEnd_6020266 : Nat := 4983230072969 + 3 ^ 40 * 6020266 * 2
def baseEnd_6020266 : Nat := 3091290125920647915288307

theorem tailTrace_6020266 : CollatzResearch.WordTrace tailWord_6020266 prefixEnd_6020266 3091290125920647915288307 := by
  unfold tailWord_6020266
  simp only [CollatzResearch.WordTrace]
  refine ⟨54894285001902984105088163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146384760005074624280235101 54894285001902984105088163)
  ·
    refine ⟨82341427502854476157632245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54894285001902984105088163 82341427502854476157632245)
    ·
      refine ⟨7719508828392607139778023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82341427502854476157632245 7719508828392607139778023)
      ·
        refine ⟨11579263242588910709667035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7719508828392607139778023 11579263242588910709667035)
        ·
          refine ⟨17368894863883366064500553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11579263242588910709667035 17368894863883366064500553)
          ·
            refine ⟨13026671147912524548375415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17368894863883366064500553 13026671147912524548375415)
            ·
              refine ⟨19540006721868786822563123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13026671147912524548375415 19540006721868786822563123)
              ·
                refine ⟨29310010082803180233844685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19540006721868786822563123 29310010082803180233844685)
                ·
                  refine ⟨10991253781051192587691757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29310010082803180233844685 10991253781051192587691757)
                  ·
                    refine ⟨4121720167894197220384409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10991253781051192587691757 4121720167894197220384409)
                    ·
                      refine ⟨3091290125920647915288307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4121720167894197220384409 3091290125920647915288307)
                      ·
                        rfl

theorem cell23_6020266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_6020266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6020266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6020266 prefixEnd_6020266 := by exact prefixLift 6020266
  have htrace : WordTrace (prefixWord ++ tailWord_6020266) baseStart_6020266 baseEnd_6020266 := by
    simpa [prefixWord, tailWord_6020266, baseEnd_6020266] using wordTrace_append hprefix tailTrace_6020266
  have hstable : (prefixWord ++ tailWord_6020266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6020266).length < 2 ^ (prefixWord ++ tailWord_6020266).sum := by decide
  have hdescent : baseEnd_6020266 < baseStart_6020266 := by decide
  rcases family_descends (prefixWord ++ tailWord_6020266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6020290 : List Nat := [3, 5, 1, 1, 2, 1, 2, 2, 2, 1, 3]
def baseStart_6020290 : Nat := 118140960795 + 6020290 * 2 ^ 59
def prefixEnd_6020290 : Nat := 4983230072969 + 3 ^ 40 * 6020290 * 2
def baseEnd_6020290 : Nat := 3091302449456355821388197

theorem tailTrace_6020290 : CollatzResearch.WordTrace tailWord_6020290 prefixEnd_6020290 3091302449456355821388197 := by
  unfold tailWord_6020290
  simp only [CollatzResearch.WordTrace]
  refine ⟨54894503839881247129806581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146385343573016659012817549 54894503839881247129806581)
  ·
    refine ⟨5146359734988866918419367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54894503839881247129806581 5146359734988866918419367)
    ·
      refine ⟨7719539602483300377629051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5146359734988866918419367 7719539602483300377629051)
      ·
        refine ⟨11579309403724950566443577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7719539602483300377629051 11579309403724950566443577)
        ·
          refine ⟨8684482052793712924832683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11579309403724950566443577 8684482052793712924832683)
          ·
            refine ⟨13026723079190569387249025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8684482052793712924832683 13026723079190569387249025)
            ·
              refine ⟨9770042309392927040436769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13026723079190569387249025 9770042309392927040436769)
              ·
                refine ⟨7327531732044695280327577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9770042309392927040436769 7327531732044695280327577)
                ·
                  refine ⟨5495648799033521460245683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7327531732044695280327577 5495648799033521460245683)
                  ·
                    refine ⟨8243473198550282190368525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5495648799033521460245683 8243473198550282190368525)
                    ·
                      refine ⟨3091302449456355821388197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8243473198550282190368525 3091302449456355821388197)
                      ·
                        rfl

theorem cell23_6020290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_6020290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6020290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6020290 prefixEnd_6020290 := by exact prefixLift 6020290
  have htrace : WordTrace (prefixWord ++ tailWord_6020290) baseStart_6020290 baseEnd_6020290 := by
    simpa [prefixWord, tailWord_6020290, baseEnd_6020290] using wordTrace_append hprefix tailTrace_6020290
  have hstable : (prefixWord ++ tailWord_6020290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6020290).length < 2 ^ (prefixWord ++ tailWord_6020290).sum := by decide
  have hdescent : baseEnd_6020290 < baseStart_6020290 := by decide
  rcases family_descends (prefixWord ++ tailWord_6020290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6020295 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 3, 5, 3]
def baseStart_6020295 : Nat := 118140960795 + 6020295 * 2 ^ 59
def prefixEnd_6020295 : Nat := 4983230072969 + 3 ^ 40 * 6020295 * 2
def baseEnd_6020295 : Nat := 3091305016859628301825673

theorem tailTrace_6020295 : CollatzResearch.WordTrace tailWord_6020295 prefixEnd_6020295 3091305016859628301825673 := by
  unfold tailWord_6020295
  simp only [CollatzResearch.WordTrace]
  refine ⟨219578197724506874373158339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146385465149671249582105559 219578197724506874373158339)
  ·
    refine ⟨329367296586760311559737509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219578197724506874373158339 329367296586760311559737509)
    ·
      refine ⟨61756368110017558417450783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 329367296586760311559737509 61756368110017558417450783)
      ·
        refine ⟨92634552165026337626176175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61756368110017558417450783 92634552165026337626176175)
        ·
          refine ⟨138951828247539506439264263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92634552165026337626176175 138951828247539506439264263)
          ·
            refine ⟨208427742371309259658896395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138951828247539506439264263 208427742371309259658896395)
            ·
              refine ⟨312641613556963889488344593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208427742371309259658896395 312641613556963889488344593)
              ·
                refine ⟨234481210167722917116258445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 312641613556963889488344593 234481210167722917116258445)
                ·
                  refine ⟨87930453812896093918596917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 234481210167722917116258445 87930453812896093918596917)
                  ·
                    refine ⟨8243480044959008804868461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 87930453812896093918596917 8243480044959008804868461)
                    ·
                      refine ⟨3091305016859628301825673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8243480044959008804868461 3091305016859628301825673)
                      ·
                        rfl

theorem cell23_6020295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 5, 3].length) (baseStart_6020295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6020295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6020295 prefixEnd_6020295 := by exact prefixLift 6020295
  have htrace : WordTrace (prefixWord ++ tailWord_6020295) baseStart_6020295 baseEnd_6020295 := by
    simpa [prefixWord, tailWord_6020295, baseEnd_6020295] using wordTrace_append hprefix tailTrace_6020295
  have hstable : (prefixWord ++ tailWord_6020295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6020295).length < 2 ^ (prefixWord ++ tailWord_6020295).sum := by decide
  have hdescent : baseEnd_6020295 < baseStart_6020295 := by decide
  rcases family_descends (prefixWord ++ tailWord_6020295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6020332 : List Nat := [2, 2, 1, 1, 2, 4, 3, 1, 2, 5]
def baseStart_6020332 : Nat := 118140960795 + 6020332 * 2 ^ 59
def prefixEnd_6020332 : Nat := 4983230072969 + 3 ^ 40 * 6020332 * 2
def baseEnd_6020332 : Nat := 1030441338547948219021001

theorem tailTrace_6020332 : CollatzResearch.WordTrace tailWord_6020332 prefixEnd_6020332 1030441338547948219021001 := by
  unfold tailWord_6020332
  simp only [CollatzResearch.WordTrace]
  refine ⟨109789773612686414846127625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146386364816915219794836833 109789773612686414846127625)
  ·
    refine ⟨82342330209514811134595719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109789773612686414846127625 82342330209514811134595719)
    ·
      refine ⟨123513495314272216701893579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82342330209514811134595719 123513495314272216701893579)
      ·
        refine ⟨185270242971408325052840369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123513495314272216701893579 185270242971408325052840369)
        ·
          refine ⟨138952682228556243789630277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185270242971408325052840369 138952682228556243789630277)
          ·
            refine ⟨26053627917854295710555677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 138952682228556243789630277 26053627917854295710555677)
            ·
              refine ⟨9770110469195360891458379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26053627917854295710555677 9770110469195360891458379)
              ·
                refine ⟨14655165703793041337187569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9770110469195360891458379 14655165703793041337187569)
                ·
                  refine ⟨10991374277844781002890677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14655165703793041337187569 10991374277844781002890677)
                  ·
                    refine ⟨1030441338547948219021001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10991374277844781002890677 1030441338547948219021001)
                    ·
                      rfl

theorem cell23_6020332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 5].length) (baseStart_6020332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6020332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6020332 prefixEnd_6020332 := by exact prefixLift 6020332
  have htrace : WordTrace (prefixWord ++ tailWord_6020332) baseStart_6020332 baseEnd_6020332 := by
    simpa [prefixWord, tailWord_6020332, baseEnd_6020332] using wordTrace_append hprefix tailTrace_6020332
  have hstable : (prefixWord ++ tailWord_6020332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6020332).length < 2 ^ (prefixWord ++ tailWord_6020332).sum := by decide
  have hdescent : baseEnd_6020332 < baseStart_6020332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6020332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6020392 : List Nat := [2, 1, 5, 1, 2, 1, 1, 2, 8]
def baseStart_6020392 : Nat := 118140960795 + 6020392 * 2 ^ 59
def prefixEnd_6020392 : Nat := 4983230072969 + 3 ^ 40 * 6020392 * 2
def baseEnd_6020392 : Nat := 343483869387012713590303

theorem tailTrace_6020392 : CollatzResearch.WordTrace tailWord_6020392 prefixEnd_6020392 343483869387012713590303 := by
  unfold tailWord_6020392
  simp only [CollatzResearch.WordTrace]
  refine ⟨109790867802577729969719715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146387823736770306626292953 109790867802577729969719715)
  ·
    refine ⟨164686301703866594954579573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109790867802577729969719715 164686301703866594954579573)
    ·
      refine ⟨15439340784737493276991835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 164686301703866594954579573 15439340784737493276991835)
      ·
        refine ⟨23159011177106239915487753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15439340784737493276991835 23159011177106239915487753)
        ·
          refine ⟨17369258382829679936615815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23159011177106239915487753 17369258382829679936615815)
          ·
            refine ⟨26053887574244519904923723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17369258382829679936615815 26053887574244519904923723)
            ·
              refine ⟨39080831361366779857385585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26053887574244519904923723 39080831361366779857385585)
              ·
                refine ⟨29310623521025084893039189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39080831361366779857385585 29310623521025084893039189)
                ·
                  refine ⟨343483869387012713590303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29310623521025084893039189 343483869387012713590303)
                  ·
                    rfl

theorem cell23_6020392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 8].length) (baseStart_6020392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6020392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6020392 prefixEnd_6020392 := by exact prefixLift 6020392
  have htrace : WordTrace (prefixWord ++ tailWord_6020392) baseStart_6020392 baseEnd_6020392 := by
    simpa [prefixWord, tailWord_6020392, baseEnd_6020392] using wordTrace_append hprefix tailTrace_6020392
  have hstable : (prefixWord ++ tailWord_6020392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6020392).length < 2 ^ (prefixWord ++ tailWord_6020392).sum := by decide
  have hdescent : baseEnd_6020392 < baseStart_6020392 := by decide
  rcases family_descends (prefixWord ++ tailWord_6020392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6020413 : List Nat := [1, 4, 1, 5, 1, 2, 1, 1, 3, 4]
def baseStart_6020413 : Nat := 118140960795 + 6020413 * 2 ^ 59
def prefixEnd_6020413 : Nat := 4983230072969 + 3 ^ 40 * 6020413 * 2
def baseEnd_6020413 : Nat := 1030455202525619613383377

theorem tailTrace_6020413 : CollatzResearch.WordTrace tailWord_6020413 prefixEnd_6020413 1030455202525619613383377 := by
  unfold tailWord_6020413
  simp only [CollatzResearch.WordTrace]
  refine ⟨219582501538079380525953893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146388334358719587017302595 219582501538079380525953893)
  ·
    refine ⟨41171719038389883848616355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 219582501538079380525953893 41171719038389883848616355)
    ·
      refine ⟨61757578557584825772924533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41171719038389883848616355 61757578557584825772924533)
      ·
        refine ⟨5789772989773577416211675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61757578557584825772924533 5789772989773577416211675)
        ·
          refine ⟨8684659484660366124317513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5789772989773577416211675 8684659484660366124317513)
          ·
            refine ⟨6513494613495274593238135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8684659484660366124317513 6513494613495274593238135)
            ·
              refine ⟨9770241920242911889857203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6513494613495274593238135 9770241920242911889857203)
              ·
                refine ⟨14655362880364367834785805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9770241920242911889857203 14655362880364367834785805)
                ·
                  refine ⟨5495761080136637938044677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14655362880364367834785805 5495761080136637938044677)
                  ·
                    refine ⟨1030455202525619613383377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5495761080136637938044677 1030455202525619613383377)
                    ·
                      rfl

theorem cell23_6020413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 3, 4].length) (baseStart_6020413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6020413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6020413 prefixEnd_6020413 := by exact prefixLift 6020413
  have htrace : WordTrace (prefixWord ++ tailWord_6020413) baseStart_6020413 baseEnd_6020413 := by
    simpa [prefixWord, tailWord_6020413, baseEnd_6020413] using wordTrace_append hprefix tailTrace_6020413
  have hstable : (prefixWord ++ tailWord_6020413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6020413).length < 2 ^ (prefixWord ++ tailWord_6020413).sum := by decide
  have hdescent : baseEnd_6020413 < baseStart_6020413 := by decide
  rcases family_descends (prefixWord ++ tailWord_6020413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6020439 : List Nat := [1, 1, 3, 2, 3, 2, 3, 2, 1, 5]
def baseStart_6020439 : Nat := 118140960795 + 6020439 * 2 ^ 59
def prefixEnd_6020439 : Nat := 4983230072969 + 3 ^ 40 * 6020439 * 2
def baseEnd_6020439 : Nat := 1030459652691291912808337

theorem tailTrace_6020439 : CollatzResearch.WordTrace tailWord_6020439 prefixEnd_6020439 1030459652691291912808337 := by
  unfold tailWord_6020439
  simp only [CollatzResearch.WordTrace]
  refine ⟨219583449835985186966400371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146388966557323457977600247 219583449835985186966400371)
  ·
    refine ⟨329375174753977780449600557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219583449835985186966400371 329375174753977780449600557)
    ·
      refine ⟨123515690532741667668600209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 329375174753977780449600557 123515690532741667668600209)
      ·
        refine ⟨92636767899556250751450157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123515690532741667668600209 92636767899556250751450157)
        ·
          refine ⟨34738787962333594031793809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92636767899556250751450157 34738787962333594031793809)
          ·
            refine ⟨26054090971750195523845357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34738787962333594031793809 26054090971750195523845357)
            ·
              refine ⟨9770284114406323321442009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26054090971750195523845357 9770284114406323321442009)
              ·
                refine ⟨7327713085804742491081507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9770284114406323321442009 7327713085804742491081507)
                ·
                  refine ⟨10991569628707113736622261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7327713085804742491081507 10991569628707113736622261)
                  ·
                    refine ⟨1030459652691291912808337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10991569628707113736622261 1030459652691291912808337)
                    ·
                      rfl

theorem cell23_6020439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 2, 1, 5].length) (baseStart_6020439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6020439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6020439 prefixEnd_6020439 := by exact prefixLift 6020439
  have htrace : WordTrace (prefixWord ++ tailWord_6020439) baseStart_6020439 baseEnd_6020439 := by
    simpa [prefixWord, tailWord_6020439, baseEnd_6020439] using wordTrace_append hprefix tailTrace_6020439
  have hstable : (prefixWord ++ tailWord_6020439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6020439).length < 2 ^ (prefixWord ++ tailWord_6020439).sum := by decide
  have hdescent : baseEnd_6020439 < baseStart_6020439 := by decide
  rcases family_descends (prefixWord ++ tailWord_6020439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6020452 : List Nat := [2, 3, 1, 1, 3, 2, 1, 1, 3, 6]
def baseStart_6020452 : Nat := 118140960795 + 6020452 * 2 ^ 59
def prefixEnd_6020452 : Nat := 4983230072969 + 3 ^ 40 * 6020452 * 2
def baseEnd_6020452 : Nat := 1030461877774128062520817

theorem tailTrace_6020452 : CollatzResearch.WordTrace tailWord_6020452 prefixEnd_6020452 1030461877774128062520817 := by
  unfold tailWord_6020452
  simp only [CollatzResearch.WordTrace]
  refine ⟨109791961992469045093311805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146389282656625393457749073 109791961992469045093311805)
  ·
    refine ⟨41171985747175891909991927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109791961992469045093311805 41171985747175891909991927)
    ·
      refine ⟨61757978620763837864987891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41171985747175891909991927 61757978620763837864987891)
      ·
        refine ⟨92636967931145756797481837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61757978620763837864987891 92636967931145756797481837)
        ·
          refine ⟨34738862974179658799055689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92636967931145756797481837 34738862974179658799055689)
          ·
            refine ⟨26054147230634744099291767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34738862974179658799055689 26054147230634744099291767)
            ·
              refine ⟨39081220845952116148937651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26054147230634744099291767 39081220845952116148937651)
              ·
                refine ⟨58621831268928174223406477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39081220845952116148937651 58621831268928174223406477)
                ·
                  refine ⟨21983186725848065333777429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58621831268928174223406477 21983186725848065333777429)
                  ·
                    refine ⟨1030461877774128062520817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21983186725848065333777429 1030461877774128062520817)
                    ·
                      rfl

theorem cell23_6020452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 3, 6].length) (baseStart_6020452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6020452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6020452 prefixEnd_6020452 := by exact prefixLift 6020452
  have htrace : WordTrace (prefixWord ++ tailWord_6020452) baseStart_6020452 baseEnd_6020452 := by
    simpa [prefixWord, tailWord_6020452, baseEnd_6020452] using wordTrace_append hprefix tailTrace_6020452
  have hstable : (prefixWord ++ tailWord_6020452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6020452).length < 2 ^ (prefixWord ++ tailWord_6020452).sum := by decide
  have hdescent : baseEnd_6020452 < baseStart_6020452 := by decide
  rcases family_descends (prefixWord ++ tailWord_6020452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6020476 : List Nat := [2, 2, 2, 1, 1, 1, 4, 3, 3, 2, 2]
def baseStart_6020476 : Nat := 118140960795 + 6020476 * 2 ^ 59
def prefixEnd_6020476 : Nat := 4983230072969 + 3 ^ 40 * 6020476 * 2
def baseEnd_6020476 : Nat := 3091397956858092093662341

theorem tailTrace_6020476 : CollatzResearch.WordTrace tailWord_6020476 prefixEnd_6020476 3091397956858092093662341 := by
  unfold tailWord_6020476
  simp only [CollatzResearch.WordTrace]
  refine ⟨109792399668425571142748641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146389866224567428190331521 109792399668425571142748641)
  ·
    refine ⟨82344299751319178357061481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109792399668425571142748641 82344299751319178357061481)
    ·
      refine ⟨61758224813489383767796111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82344299751319178357061481 61758224813489383767796111)
      ·
        refine ⟨92637337220234075651694167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61758224813489383767796111 92637337220234075651694167)
        ·
          refine ⟨138956005830351113477541251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92637337220234075651694167 138956005830351113477541251)
          ·
            refine ⟨208434008745526670216311877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138956005830351113477541251 208434008745526670216311877)
            ·
              refine ⟨39081376639786250665558477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 208434008745526670216311877 39081376639786250665558477)
              ·
                refine ⟨14655516239919843999584429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39081376639786250665558477 14655516239919843999584429)
                ·
                  refine ⟨5495818589969941499844161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14655516239919843999584429 5495818589969941499844161)
                  ·
                    refine ⟨4121863942477456124883121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5495818589969941499844161 4121863942477456124883121)
                    ·
                      refine ⟨3091397956858092093662341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4121863942477456124883121 3091397956858092093662341)
                      ·
                        rfl

theorem cell23_6020476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 3, 2, 2].length) (baseStart_6020476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6020476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6020476 prefixEnd_6020476 := by exact prefixLift 6020476
  have htrace : WordTrace (prefixWord ++ tailWord_6020476) baseStart_6020476 baseEnd_6020476 := by
    simpa [prefixWord, tailWord_6020476, baseEnd_6020476] using wordTrace_append hprefix tailTrace_6020476
  have hstable : (prefixWord ++ tailWord_6020476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6020476).length < 2 ^ (prefixWord ++ tailWord_6020476).sum := by decide
  have hdescent : baseEnd_6020476 < baseStart_6020476 := by decide
  rcases family_descends (prefixWord ++ tailWord_6020476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6020520 : List Nat := [2, 1, 6, 1, 2, 2, 1, 2, 2, 4]
def baseStart_6020520 : Nat := 118140960795 + 6020520 * 2 ^ 59
def prefixEnd_6020520 : Nat := 4983230072969 + 3 ^ 40 * 6020520 * 2
def baseEnd_6020520 : Nat := 1030473516668963307170713

theorem tailTrace_6020520 : CollatzResearch.WordTrace tailWord_6020520 prefixEnd_6020520 1030473516668963307170713 := by
  unfold tailWord_6020520
  simp only [CollatzResearch.WordTrace]
  refine ⟨109793202074345868900049507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146390936099127825200066009 109793202074345868900049507)
  ·
    refine ⟨164689803111518803350074261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109793202074345868900049507 164689803111518803350074261)
    ·
      refine ⟨7719834520852443907034731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 164689803111518803350074261 7719834520852443907034731)
      ·
        refine ⟨11579751781278665860552097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7719834520852443907034731 11579751781278665860552097)
        ·
          refine ⟨8684813835958999395414073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11579751781278665860552097 8684813835958999395414073)
          ·
            refine ⟨6513610376969249546560555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8684813835958999395414073 6513610376969249546560555)
            ·
              refine ⟨9770415565453874319840833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6513610376969249546560555 9770415565453874319840833)
              ·
                refine ⟨7327811674090405739880625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9770415565453874319840833 7327811674090405739880625)
                ·
                  refine ⟨5495858755567804304910469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7327811674090405739880625 5495858755567804304910469)
                  ·
                    refine ⟨1030473516668963307170713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5495858755567804304910469 1030473516668963307170713)
                    ·
                      rfl

theorem cell23_6020520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_6020520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6020520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6020520 prefixEnd_6020520 := by exact prefixLift 6020520
  have htrace : WordTrace (prefixWord ++ tailWord_6020520) baseStart_6020520 baseEnd_6020520 := by
    simpa [prefixWord, tailWord_6020520, baseEnd_6020520] using wordTrace_append hprefix tailTrace_6020520
  have hstable : (prefixWord ++ tailWord_6020520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6020520).length < 2 ^ (prefixWord ++ tailWord_6020520).sum := by decide
  have hdescent : baseEnd_6020520 < baseStart_6020520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6020520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6020569 : List Nat := [1, 2, 1, 2, 4, 3, 1, 1, 2, 1, 5]
def baseStart_6020569 : Nat := 118140960795 + 6020569 * 2 ^ 59
def prefixEnd_6020569 : Nat := 4983230072969 + 3 ^ 40 * 6020569 * 2
def baseEnd_6020569 : Nat := 3091445710558960229799413

theorem tailTrace_6020569 : CollatzResearch.WordTrace tailWord_6020569 prefixEnd_6020569 3091445710558960229799413 := by
  unfold tailWord_6020569
  simp only [CollatzResearch.WordTrace]
  refine ⟨219588191325514219168632761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146392127550342812779088507 219588191325514219168632761)
  ·
    refine ⟨164691143494135664376474571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219588191325514219168632761 164691143494135664376474571)
    ·
      refine ⟨247036715241203496564711857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164691143494135664376474571 247036715241203496564711857)
      ·
        refine ⟨185277536430902622423533893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247036715241203496564711857 185277536430902622423533893)
        ·
          refine ⟨34739538080794241704412605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 185277536430902622423533893 34739538080794241704412605)
          ·
            refine ⟨13027326780297840639154727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34739538080794241704412605 13027326780297840639154727)
            ·
              refine ⟨19540990170446760958732091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13027326780297840639154727 19540990170446760958732091)
              ·
                refine ⟨29311485255670141438098137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19540990170446760958732091 29311485255670141438098137)
                ·
                  refine ⟨21983613941752606078573603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29311485255670141438098137 21983613941752606078573603)
                  ·
                    refine ⟨32975420912628909117860405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21983613941752606078573603 32975420912628909117860405)
                    ·
                      refine ⟨3091445710558960229799413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32975420912628909117860405 3091445710558960229799413)
                      ·
                        rfl

theorem cell23_6020569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 1, 5].length) (baseStart_6020569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6020569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6020569 prefixEnd_6020569 := by exact prefixLift 6020569
  have htrace : WordTrace (prefixWord ++ tailWord_6020569) baseStart_6020569 baseEnd_6020569 := by
    simpa [prefixWord, tailWord_6020569, baseEnd_6020569] using wordTrace_append hprefix tailTrace_6020569
  have hstable : (prefixWord ++ tailWord_6020569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6020569).length < 2 ^ (prefixWord ++ tailWord_6020569).sum := by decide
  have hdescent : baseEnd_6020569 < baseStart_6020569 := by decide
  rcases family_descends (prefixWord ++ tailWord_6020569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6020583 : List Nat := [1, 1, 5, 2, 1, 2, 2, 1, 4, 2, 2]
def baseStart_6020583 : Nat := 118140960795 + 6020583 * 2 ^ 59
def prefixEnd_6020583 : Nat := 4983230072969 + 3 ^ 40 * 6020583 * 2
def baseEnd_6020583 : Nat := 3091452899288123175024349

theorem tailTrace_6020583 : CollatzResearch.WordTrace tailWord_6020583 prefixEnd_6020583 3091452899288123175024349 := by
  unfold tailWord_6020583
  simp only [CollatzResearch.WordTrace]
  refine ⟨219588701947463499559642403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146392467964975666373094935 219588701947463499559642403)
  ·
    refine ⟨329383052921195249339463605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219588701947463499559642403 329383052921195249339463605)
    ·
      refine ⟨30879661211362054625574713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 329383052921195249339463605 30879661211362054625574713)
      ·
        refine ⟨23159745908521540969181035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30879661211362054625574713 23159745908521540969181035)
        ·
          refine ⟨34739618862782311453771553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23159745908521540969181035 34739618862782311453771553)
          ·
            refine ⟨26054714147086733590328665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34739618862782311453771553 26054714147086733590328665)
            ·
              refine ⟨19541035610315050192746499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26054714147086733590328665 19541035610315050192746499)
              ·
                refine ⟨29311553415472575289119749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19541035610315050192746499 29311553415472575289119749)
                ·
                  refine ⟨5495916265401107866709953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29311553415472575289119749 5495916265401107866709953)
                  ·
                    refine ⟨4121937199050830900032465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5495916265401107866709953 4121937199050830900032465)
                    ·
                      refine ⟨3091452899288123175024349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4121937199050830900032465 3091452899288123175024349)
                      ·
                        rfl

theorem cell23_6020583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_6020583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6020583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6020583 prefixEnd_6020583 := by exact prefixLift 6020583
  have htrace : WordTrace (prefixWord ++ tailWord_6020583) baseStart_6020583 baseEnd_6020583 := by
    simpa [prefixWord, tailWord_6020583, baseEnd_6020583] using wordTrace_append hprefix tailTrace_6020583
  have hstable : (prefixWord ++ tailWord_6020583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6020583).length < 2 ^ (prefixWord ++ tailWord_6020583).sum := by decide
  have hdescent : baseEnd_6020583 < baseStart_6020583 := by decide
  rcases family_descends (prefixWord ++ tailWord_6020583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6020600 : List Nat := [2, 1, 2, 1, 1, 5, 4, 1, 2, 2, 2]
def baseStart_6020600 : Nat := 118140960795 + 6020600 * 2 ^ 59
def prefixEnd_6020600 : Nat := 4983230072969 + 3 ^ 40 * 6020600 * 2
def baseEnd_6020600 : Nat := 3091461628459249608511771

theorem tailTrace_6020600 : CollatzResearch.WordTrace tailWord_6020600 prefixEnd_6020600 3091461628459249608511771 := by
  unfold tailWord_6020600
  simp only [CollatzResearch.WordTrace]
  refine ⟨109794660994200955731505627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146392881325601274308674169 109794660994200955731505627)
  ·
    refine ⟨164691991491301433597258441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109794660994200955731505627 164691991491301433597258441)
    ·
      refine ⟨123518993618476075197943831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164691991491301433597258441 123518993618476075197943831)
      ·
        refine ⟨185278490427714112796915747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123518993618476075197943831 185278490427714112796915747)
        ·
          refine ⟨277917735641571169195373621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185278490427714112796915747 277917735641571169195373621)
          ·
            refine ⟨26054787716397297112066277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 277917735641571169195373621 26054787716397297112066277)
            ·
              refine ⟨4885272696824493208512427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26054787716397297112066277 4885272696824493208512427)
              ·
                refine ⟨7327909045236739812768641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4885272696824493208512427 7327909045236739812768641)
                ·
                  refine ⟨5495931783927554859576481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7327909045236739812768641 5495931783927554859576481)
                  ·
                    refine ⟨4121948837945666144682361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5495931783927554859576481 4121948837945666144682361)
                    ·
                      refine ⟨3091461628459249608511771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4121948837945666144682361 3091461628459249608511771)
                      ·
                        rfl

theorem cell23_6020600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 1, 2, 2, 2].length) (baseStart_6020600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6020600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6020600 prefixEnd_6020600 := by exact prefixLift 6020600
  have htrace : WordTrace (prefixWord ++ tailWord_6020600) baseStart_6020600 baseEnd_6020600 := by
    simpa [prefixWord, tailWord_6020600, baseEnd_6020600] using wordTrace_append hprefix tailTrace_6020600
  have hstable : (prefixWord ++ tailWord_6020600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6020600).length < 2 ^ (prefixWord ++ tailWord_6020600).sum := by decide
  have hdescent : baseEnd_6020600 < baseStart_6020600 := by decide
  rcases family_descends (prefixWord ++ tailWord_6020600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6020629 : List Nat := [1, 3, 2, 1, 3, 2, 1, 2, 1, 2, 5]
def baseStart_6020629 : Nat := 118140960795 + 6020629 * 2 ^ 59
def prefixEnd_6020629 : Nat := 4983230072969 + 3 ^ 40 * 6020629 * 2
def baseEnd_6020629 : Nat := 3091476519398229995049137

theorem tailTrace_6020629 : CollatzResearch.WordTrace tailWord_6020629 prefixEnd_6020629 3091476519398229995049137 := by
  unfold tailWord_6020629
  simp only [CollatzResearch.WordTrace]
  refine ⟨219590379705296849415816941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146393586470197899610544627 219590379705296849415816941)
  ·
    refine ⟨82346392389486318530931353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 219590379705296849415816941 82346392389486318530931353)
    ·
      refine ⟨61759794292114738898198515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82346392389486318530931353 61759794292114738898198515)
      ·
        refine ⟨92639691438172108347297773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61759794292114738898198515 92639691438172108347297773)
        ·
          refine ⟨34739884289314540630236665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92639691438172108347297773 34739884289314540630236665)
          ·
            refine ⟨26054913216985905472677499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34739884289314540630236665 26054913216985905472677499)
            ·
              refine ⟨39082369825478858209016249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26054913216985905472677499 39082369825478858209016249)
              ·
                refine ⟨29311777369109143656762187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39082369825478858209016249 29311777369109143656762187)
                ·
                  refine ⟨43967666053663715485143281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29311777369109143656762187 43967666053663715485143281)
                  ·
                    refine ⟨32975749540247786613857461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43967666053663715485143281 32975749540247786613857461)
                    ·
                      refine ⟨3091476519398229995049137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32975749540247786613857461 3091476519398229995049137)
                      ·
                        rfl

theorem cell23_6020629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_6020629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6020629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6020629 prefixEnd_6020629 := by exact prefixLift 6020629
  have htrace : WordTrace (prefixWord ++ tailWord_6020629) baseStart_6020629 baseEnd_6020629 := by
    simpa [prefixWord, tailWord_6020629, baseEnd_6020629] using wordTrace_append hprefix tailTrace_6020629
  have hstable : (prefixWord ++ tailWord_6020629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6020629).length < 2 ^ (prefixWord ++ tailWord_6020629).sum := by decide
  have hdescent : baseEnd_6020629 < baseStart_6020629 := by decide
  rcases family_descends (prefixWord ++ tailWord_6020629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6020640 : List Nat := [2, 1, 1, 6, 1, 3, 2, 2, 5]
def baseStart_6020640 : Nat := 118140960795 + 6020640 * 2 ^ 59
def prefixEnd_6020640 : Nat := 4983230072969 + 3 ^ 40 * 6020640 * 2
def baseEnd_6020640 : Nat := 343498018631714383556843

theorem tailTrace_6020640 : CollatzResearch.WordTrace tailWord_6020640 prefixEnd_6020640 343498018631714383556843 := by
  unfold tailWord_6020640
  simp only [CollatzResearch.WordTrace]
  refine ⟨109795390454128499147233687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146393853938837998862978249 109795390454128499147233687)
  ·
    refine ⟨164693085681192748720850531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109795390454128499147233687 164693085681192748720850531)
    ·
      refine ⟨247039628521789123081275797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164693085681192748720850531 247039628521789123081275797)
      ·
        refine ⟨11579982586958865144434803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 247039628521789123081275797 11579982586958865144434803)
        ·
          refine ⟨17369973880438297716652205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11579982586958865144434803 17369973880438297716652205)
          ·
            refine ⟨6513740205164361643744577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17369973880438297716652205 6513740205164361643744577)
            ·
              refine ⟨4885305153873271232808433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6513740205164361643744577 4885305153873271232808433)
              ·
                refine ⟨3663978865404953424606325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4885305153873271232808433 3663978865404953424606325)
                ·
                  refine ⟨343498018631714383556843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3663978865404953424606325 343498018631714383556843)
                  ·
                    rfl

theorem cell23_6020640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 2, 5].length) (baseStart_6020640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6020640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6020640 prefixEnd_6020640 := by exact prefixLift 6020640
  have htrace : WordTrace (prefixWord ++ tailWord_6020640) baseStart_6020640 baseEnd_6020640 := by
    simpa [prefixWord, tailWord_6020640, baseEnd_6020640] using wordTrace_append hprefix tailTrace_6020640
  have hstable : (prefixWord ++ tailWord_6020640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6020640).length < 2 ^ (prefixWord ++ tailWord_6020640).sum := by decide
  have hdescent : baseEnd_6020640 < baseStart_6020640 := by decide
  rcases family_descends (prefixWord ++ tailWord_6020640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6020666 : List Nat := [3, 1, 1, 1, 3, 2, 3, 2, 3, 4]
def baseStart_6020666 : Nat := 118140960795 + 6020666 * 2 ^ 59
def prefixEnd_6020666 : Nat := 4983230072969 + 3 ^ 40 * 6020666 * 2
def baseEnd_6020666 : Nat := 1030498506060815450095489

theorem tailTrace_6020666 : CollatzResearch.WordTrace tailWord_6020666 prefixEnd_6020666 1030498506060815450095489 := by
  unfold tailWord_6020666
  simp only [CollatzResearch.WordTrace]
  refine ⟨54897932301540701183728463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146394486137441869823275901 54897932301540701183728463)
  ·
    refine ⟨82346898452311051775592695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54897932301540701183728463 82346898452311051775592695)
    ·
      refine ⟨123520347678466577663389043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82346898452311051775592695 123520347678466577663389043)
      ·
        refine ⟨185280521517699866495083565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123520347678466577663389043 185280521517699866495083565)
        ·
          refine ⟨69480195569137449935656337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185280521517699866495083565 69480195569137449935656337)
          ·
            refine ⟨52110146676853087451742253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69480195569137449935656337 52110146676853087451742253)
            ·
              refine ⟨19541305003819907794403345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52110146676853087451742253 19541305003819907794403345)
              ·
                refine ⟨14655978752864930845802509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19541305003819907794403345 14655978752864930845802509)
                ·
                  refine ⟨5495992032324349067175941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14655978752864930845802509 5495992032324349067175941)
                  ·
                    refine ⟨1030498506060815450095489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5495992032324349067175941 1030498506060815450095489)
                    ·
                      rfl

theorem cell23_6020666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 3, 4].length) (baseStart_6020666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6020666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6020666 prefixEnd_6020666 := by exact prefixLift 6020666
  have htrace : WordTrace (prefixWord ++ tailWord_6020666) baseStart_6020666 baseEnd_6020666 := by
    simpa [prefixWord, tailWord_6020666, baseEnd_6020666] using wordTrace_append hprefix tailTrace_6020666
  have hstable : (prefixWord ++ tailWord_6020666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6020666).length < 2 ^ (prefixWord ++ tailWord_6020666).sum := by decide
  have hdescent : baseEnd_6020666 < baseStart_6020666 := by decide
  rcases family_descends (prefixWord ++ tailWord_6020666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6020700 : List Nat := [2, 2, 4, 1, 2, 1, 2, 4, 1, 4]
def baseStart_6020700 : Nat := 118140960795 + 6020700 * 2 ^ 59
def prefixEnd_6020700 : Nat := 4983230072969 + 3 ^ 40 * 6020700 * 2
def baseEnd_6020700 : Nat := 1030504325508233072420437

theorem tailTrace_6020700 : CollatzResearch.WordTrace tailWord_6020700 prefixEnd_6020700 1030504325508233072420437 := by
  unfold tailWord_6020700
  simp only [CollatzResearch.WordTrace]
  refine ⟨109796484644019814270825777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146395312858693085694434369 109796484644019814270825777)
  ·
    refine ⟨82347363483014860703119333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109796484644019814270825777 82347363483014860703119333)
    ·
      refine ⟨15440130653065286381834875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82347363483014860703119333 15440130653065286381834875)
      ·
        refine ⟨23160195979597929572752313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15440130653065286381834875 23160195979597929572752313)
        ·
          refine ⟨17370146984698447179564235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23160195979597929572752313 17370146984698447179564235)
          ·
            refine ⟨26055220477047670769346353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17370146984698447179564235 26055220477047670769346353)
            ·
              refine ⟨19541415357785753077009765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26055220477047670769346353 19541415357785753077009765)
              ·
                refine ⟨3664015379584828701939331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19541415357785753077009765 3664015379584828701939331)
                ·
                  refine ⟨5496023069377243052908997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3664015379584828701939331 5496023069377243052908997)
                  ·
                    refine ⟨1030504325508233072420437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5496023069377243052908997 1030504325508233072420437)
                    ·
                      rfl

theorem cell23_6020700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_6020700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6020700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6020700 prefixEnd_6020700 := by exact prefixLift 6020700
  have htrace : WordTrace (prefixWord ++ tailWord_6020700) baseStart_6020700 baseEnd_6020700 := by
    simpa [prefixWord, tailWord_6020700, baseEnd_6020700] using wordTrace_append hprefix tailTrace_6020700
  have hstable : (prefixWord ++ tailWord_6020700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6020700).length < 2 ^ (prefixWord ++ tailWord_6020700).sum := by decide
  have hdescent : baseEnd_6020700 < baseStart_6020700 := by decide
  rcases family_descends (prefixWord ++ tailWord_6020700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6020733 : List Nat := [1, 4, 1, 1, 4, 1, 2, 1, 1, 5, 2]
def baseStart_6020733 : Nat := 118140960795 + 6020733 * 2 ^ 59
def prefixEnd_6020733 : Nat := 4983230072969 + 3 ^ 40 * 6020733 * 2
def baseEnd_6020733 : Nat := 3091529921386297588148659

theorem tailTrace_6020733 : CollatzResearch.WordTrace tailWord_6020733 prefixEnd_6020733 3091529921386297588148659 := by
  unfold tailWord_6020733
  simp only [CollatzResearch.WordTrace]
  refine ⟨219594172896920075177602853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146396115264613383451735235 219594172896920075177602853)
  ·
    refine ⟨41173907418172514095800535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 219594172896920075177602853 41173907418172514095800535)
    ·
      refine ⟨61760861127258771143700803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41173907418172514095800535 61760861127258771143700803)
      ·
        refine ⟨92641291690888156715551205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61760861127258771143700803 92641291690888156715551205)
        ·
          refine ⟨17370242192041529384165851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92641291690888156715551205 17370242192041529384165851)
          ·
            refine ⟨26055363288062294076248777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17370242192041529384165851 26055363288062294076248777)
            ·
              refine ⟨19541522466046720557186583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26055363288062294076248777 19541522466046720557186583)
              ·
                refine ⟨29312283699070080835779875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19541522466046720557186583 29312283699070080835779875)
                ·
                  refine ⟨43968425548605121253669813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29312283699070080835779875 43968425548605121253669813)
                  ·
                    refine ⟨4122039895181730117531545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43968425548605121253669813 4122039895181730117531545)
                    ·
                      refine ⟨3091529921386297588148659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4122039895181730117531545 3091529921386297588148659)
                      ·
                        rfl

theorem cell23_6020733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 5, 2].length) (baseStart_6020733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6020733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6020733 prefixEnd_6020733 := by exact prefixLift 6020733
  have htrace : WordTrace (prefixWord ++ tailWord_6020733) baseStart_6020733 baseEnd_6020733 := by
    simpa [prefixWord, tailWord_6020733, baseEnd_6020733] using wordTrace_append hprefix tailTrace_6020733
  have hstable : (prefixWord ++ tailWord_6020733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6020733).length < 2 ^ (prefixWord ++ tailWord_6020733).sum := by decide
  have hdescent : baseEnd_6020733 < baseStart_6020733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6020733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6020739 : List Nat := [1, 1, 1, 3, 3, 1, 1, 3, 3, 6]
def baseStart_6020739 : Nat := 118140960795 + 6020739 * 2 ^ 59
def prefixEnd_6020739 : Nat := 4983230072969 + 3 ^ 40 * 6020739 * 2
def baseEnd_6020739 : Nat := 1030511000756741521557877

theorem tailTrace_6020739 : CollatzResearch.WordTrace tailWord_6020739 prefixEnd_6020739 1030511000756741521557877 := by
  unfold tailWord_6020739
  simp only [CollatzResearch.WordTrace]
  refine ⟨219594391734898338202321271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146396261156598892134880847 219594391734898338202321271)
  ·
    refine ⟨329391587602347507303481907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219594391734898338202321271 329391587602347507303481907)
    ·
      refine ⟨494087381403521260955222861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329391587602347507303481907 494087381403521260955222861)
      ·
        refine ⟨185282768026320472858208573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 494087381403521260955222861 185282768026320472858208573)
        ·
          refine ⟨69481038009870177321828215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185282768026320472858208573 69481038009870177321828215)
          ·
            refine ⟨104221557014805265982742323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69481038009870177321828215 104221557014805265982742323)
            ·
              refine ⟨156332335522207898974113485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104221557014805265982742323 156332335522207898974113485)
              ·
                refine ⟨58624625820827962115292557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156332335522207898974113485 58624625820827962115292557)
                ·
                  refine ⟨21984234682810485793234709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58624625820827962115292557 21984234682810485793234709)
                  ·
                    refine ⟨1030511000756741521557877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21984234682810485793234709 1030511000756741521557877)
                    ·
                      rfl

theorem cell23_6020739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 6].length) (baseStart_6020739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6020739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6020739 prefixEnd_6020739 := by exact prefixLift 6020739
  have htrace : WordTrace (prefixWord ++ tailWord_6020739) baseStart_6020739 baseEnd_6020739 := by
    simpa [prefixWord, tailWord_6020739, baseEnd_6020739] using wordTrace_append hprefix tailTrace_6020739
  have hstable : (prefixWord ++ tailWord_6020739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6020739).length < 2 ^ (prefixWord ++ tailWord_6020739).sum := by decide
  have hdescent : baseEnd_6020739 < baseStart_6020739 := by decide
  rcases family_descends (prefixWord ++ tailWord_6020739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6020750 : List Nat := [4, 1, 1, 3, 1, 3, 1, 2, 2, 3, 2]
def baseStart_6020750 : Nat := 118140960795 + 6020750 * 2 ^ 59
def prefixEnd_6020750 : Nat := 4983230072969 + 3 ^ 40 * 6020750 * 2
def baseEnd_6020750 : Nat := 3091538650557424021636081

theorem tailTrace_6020750 : CollatzResearch.WordTrace tailWord_6020750 prefixEnd_6020750 3091538650557424021636081 := by
  unfold tailWord_6020750
  simp only [CollatzResearch.WordTrace]
  refine ⟨27449349117232310885121463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146396528625238991387314469 27449349117232310885121463)
  ·
    refine ⟨41174023675848466327682195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27449349117232310885121463 41174023675848466327682195)
    ·
      refine ⟨61761035513772699491523293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41174023675848466327682195 61761035513772699491523293)
      ·
        refine ⟨23160388317664762309321235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61761035513772699491523293 23160388317664762309321235)
        ·
          refine ⟨34740582476497143463981853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23160388317664762309321235 34740582476497143463981853)
          ·
            refine ⟨13027718428686428798993195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34740582476497143463981853 13027718428686428798993195)
            ·
              refine ⟨19541577643029643198489793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13027718428686428798993195 19541577643029643198489793)
              ·
                refine ⟨14656183232272232398867345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19541577643029643198489793 14656183232272232398867345)
                ·
                  refine ⟨10992137424204174299150509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14656183232272232398867345 10992137424204174299150509)
                  ·
                    refine ⟨4122051534076565362181441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10992137424204174299150509 4122051534076565362181441)
                    ·
                      refine ⟨3091538650557424021636081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4122051534076565362181441 3091538650557424021636081)
                      ·
                        rfl

theorem cell23_6020750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_6020750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6020750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6020750 prefixEnd_6020750 := by exact prefixLift 6020750
  have htrace : WordTrace (prefixWord ++ tailWord_6020750) baseStart_6020750 baseEnd_6020750 := by
    simpa [prefixWord, tailWord_6020750, baseEnd_6020750] using wordTrace_append hprefix tailTrace_6020750
  have hstable : (prefixWord ++ tailWord_6020750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6020750).length < 2 ^ (prefixWord ++ tailWord_6020750).sum := by decide
  have hdescent : baseEnd_6020750 < baseStart_6020750 := by decide
  rcases family_descends (prefixWord ++ tailWord_6020750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6020790 : List Nat := [5, 1, 3, 1, 1, 2, 1, 2, 1, 6]
def baseStart_6020790 : Nat := 118140960795 + 6020790 * 2 ^ 59
def prefixEnd_6020790 : Nat := 4983230072969 + 3 ^ 40 * 6020790 * 2
def baseEnd_6020790 : Nat := 1030519729927867955045299

theorem tailTrace_6020790 : CollatzResearch.WordTrace tailWord_6020790 prefixEnd_6020790 1030519729927867955045299 := by
  unfold tailWord_6020790
  simp only [CollatzResearch.WordTrace]
  refine ⟨13724765741107098369526739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 146397501238475715941618549 13724765741107098369526739)
  ·
    refine ⟨20587148611660647554290109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13724765741107098369526739 20587148611660647554290109)
    ·
      refine ⟨7720180729372742832858791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20587148611660647554290109 7720180729372742832858791)
      ·
        refine ⟨11580271094059114249288187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7720180729372742832858791 11580271094059114249288187)
        ·
          refine ⟨17370406641088671373932281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11580271094059114249288187 17370406641088671373932281)
          ·
            refine ⟨13027804980816503530449211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17370406641088671373932281 13027804980816503530449211)
            ·
              refine ⟨19541707471224755295673817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13027804980816503530449211 19541707471224755295673817)
              ·
                refine ⟨14656280603418566471755363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19541707471224755295673817 14656280603418566471755363)
                ·
                  refine ⟨21984420905127849707633045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14656280603418566471755363 21984420905127849707633045)
                  ·
                    refine ⟨1030519729927867955045299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21984420905127849707633045 1030519729927867955045299)
                    ·
                      rfl

theorem cell23_6020790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_6020790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6020790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6020790 prefixEnd_6020790 := by exact prefixLift 6020790
  have htrace : WordTrace (prefixWord ++ tailWord_6020790) baseStart_6020790 baseEnd_6020790 := by
    simpa [prefixWord, tailWord_6020790, baseEnd_6020790] using wordTrace_append hprefix tailTrace_6020790
  have hstable : (prefixWord ++ tailWord_6020790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6020790).length < 2 ^ (prefixWord ++ tailWord_6020790).sum := by decide
  have hdescent : baseEnd_6020790 < baseStart_6020790 := by decide
  rcases family_descends (prefixWord ++ tailWord_6020790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6020797 : List Nat := [1, 4, 1, 2, 1, 2, 2, 5, 1, 2, 2]
def baseStart_6020797 : Nat := 118140960795 + 6020797 * 2 ^ 59
def prefixEnd_6020797 : Nat := 4983230072969 + 3 ^ 40 * 6020797 * 2
def baseEnd_6020797 : Nat := 3091562784148185337748365

theorem tailTrace_6020797 : CollatzResearch.WordTrace tailWord_6020797 prefixEnd_6020797 3091562784148185337748365 := by
  unfold tailWord_6020797
  simp only [CollatzResearch.WordTrace]
  refine ⟨219596507168688214107932645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146397671445792142738621763 219596507168688214107932645)
  ·
    refine ⟨41174345094129040145237371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 219596507168688214107932645 41174345094129040145237371)
    ·
      refine ⟨61761517641193560217856057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41174345094129040145237371 61761517641193560217856057)
      ·
        refine ⟨46321138230895170163392043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61761517641193560217856057 46321138230895170163392043)
        ·
          refine ⟨69481707346342755245088065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46321138230895170163392043 69481707346342755245088065)
          ·
            refine ⟨52111280509757066433816049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69481707346342755245088065 52111280509757066433816049)
            ·
              refine ⟨39083460382317799825362037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52111280509757066433816049 39083460382317799825362037)
              ·
                refine ⟨3664074410842293733627691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39083460382317799825362037 3664074410842293733627691)
                ·
                  refine ⟨5496111616263440600441537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3664074410842293733627691 5496111616263440600441537)
                  ·
                    refine ⟨4122083712197580450331153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5496111616263440600441537 4122083712197580450331153)
                    ·
                      refine ⟨3091562784148185337748365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4122083712197580450331153 3091562784148185337748365)
                      ·
                        rfl

theorem cell23_6020797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 5, 1, 2, 2].length) (baseStart_6020797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6020797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6020797 prefixEnd_6020797 := by exact prefixLift 6020797
  have htrace : WordTrace (prefixWord ++ tailWord_6020797) baseStart_6020797 baseEnd_6020797 := by
    simpa [prefixWord, tailWord_6020797, baseEnd_6020797] using wordTrace_append hprefix tailTrace_6020797
  have hstable : (prefixWord ++ tailWord_6020797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6020797).length < 2 ^ (prefixWord ++ tailWord_6020797).sum := by decide
  have hdescent : baseEnd_6020797 < baseStart_6020797 := by decide
  rcases family_descends (prefixWord ++ tailWord_6020797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6020800 : List Nat := [2, 1, 1, 2, 4, 1, 5, 1, 1, 2, 3]
def baseStart_6020800 : Nat := 118140960795 + 6020800 * 2 ^ 59
def prefixEnd_6020800 : Nat := 4983230072969 + 3 ^ 40 * 6020800 * 2
def baseEnd_6020800 : Nat := 3091564324590148826010851

theorem tailTrace_6020800 : CollatzResearch.WordTrace tailWord_6020800 prefixEnd_6020800 3091564324590148826010851 := by
  unfold tailWord_6020800
  simp only [CollatzResearch.WordTrace]
  refine ⟨109798308293838672810145927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146397744391784897080194569 109798308293838672810145927)
  ·
    refine ⟨164697462440758009215218891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109798308293838672810145927 164697462440758009215218891)
    ·
      refine ⟨247046193661137013822828337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164697462440758009215218891 247046193661137013822828337)
      ·
        refine ⟨185284645245852760367121253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247046193661137013822828337 185284645245852760367121253)
        ·
          refine ⟨34740870983597392568835235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 185284645245852760367121253 34740870983597392568835235)
          ·
            refine ⟨52111306475396088853252853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34740870983597392568835235 52111306475396088853252853)
            ·
              refine ⟨4885434982068383329992455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52111306475396088853252853 4885434982068383329992455)
              ·
                refine ⟨7328152473102574994988683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4885434982068383329992455 7328152473102574994988683)
                ·
                  refine ⟨10992228709653862492483025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7328152473102574994988683 10992228709653862492483025)
                  ·
                    refine ⟨8244171532240396869362269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10992228709653862492483025 8244171532240396869362269)
                    ·
                      refine ⟨3091564324590148826010851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8244171532240396869362269 3091564324590148826010851)
                      ·
                        rfl

theorem cell23_6020800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 1, 1, 2, 3].length) (baseStart_6020800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6020800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6020800 prefixEnd_6020800 := by exact prefixLift 6020800
  have htrace : WordTrace (prefixWord ++ tailWord_6020800) baseStart_6020800 baseEnd_6020800 := by
    simpa [prefixWord, tailWord_6020800, baseEnd_6020800] using wordTrace_append hprefix tailTrace_6020800
  have hstable : (prefixWord ++ tailWord_6020800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6020800).length < 2 ^ (prefixWord ++ tailWord_6020800).sum := by decide
  have hdescent : baseEnd_6020800 < baseStart_6020800 := by decide
  rcases family_descends (prefixWord ++ tailWord_6020800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6020809 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 1, 5, 7]
def baseStart_6020809 : Nat := 118140960795 + 6020809 * 2 ^ 59
def prefixEnd_6020809 : Nat := 4983230072969 + 3 ^ 40 * 6020809 * 2
def baseEnd_6020809 : Nat := 3091568945916039290798309

theorem tailTrace_6020809 : CollatzResearch.WordTrace tailWord_6020809 prefixEnd_6020809 3091568945916039290798309 := by
  unfold tailWord_6020809
  simp only [CollatzResearch.WordTrace]
  refine ⟨219596944844644740157369481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146397963229763160104912987 219596944844644740157369481)
  ·
    refine ⟨164697708633483555118027111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219596944844644740157369481 164697708633483555118027111)
    ·
      refine ⟨247046562950225332677040667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164697708633483555118027111 247046562950225332677040667)
      ·
        refine ⟨370569844425337999015561001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247046562950225332677040667 370569844425337999015561001)
        ·
          refine ⟨277927383319003499261670751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 370569844425337999015561001 277927383319003499261670751)
          ·
            refine ⟨416891074978505248892506127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277927383319003499261670751 416891074978505248892506127)
            ·
              refine ⟨625336612467757873338759191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 416891074978505248892506127 625336612467757873338759191)
              ·
                refine ⟨938004918701636810008138787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 625336612467757873338759191 938004918701636810008138787)
                ·
                  refine ⟨1407007378052455215012208181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 938004918701636810008138787 1407007378052455215012208181)
                  ·
                    refine ⟨131906941692417676407394517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1407007378052455215012208181 131906941692417676407394517)
                    ·
                      refine ⟨3091568945916039290798309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 131906941692417676407394517 3091568945916039290798309)
                      ·
                        rfl

theorem cell23_6020809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 5, 7].length) (baseStart_6020809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6020809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6020809 prefixEnd_6020809 := by exact prefixLift 6020809
  have htrace : WordTrace (prefixWord ++ tailWord_6020809) baseStart_6020809 baseEnd_6020809 := by
    simpa [prefixWord, tailWord_6020809, baseEnd_6020809] using wordTrace_append hprefix tailTrace_6020809
  have hstable : (prefixWord ++ tailWord_6020809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6020809).length < 2 ^ (prefixWord ++ tailWord_6020809).sum := by decide
  have hdescent : baseEnd_6020809 < baseStart_6020809 := by decide
  rcases family_descends (prefixWord ++ tailWord_6020809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6020819 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 8]
def baseStart_6020819 : Nat := 118140960795 + 6020819 * 2 ^ 59
def prefixEnd_6020819 : Nat := 4983230072969 + 3 ^ 40 * 6020819 * 2
def baseEnd_6020819 : Nat := 3091574080722584251673263

theorem tailTrace_6020819 : CollatzResearch.WordTrace tailWord_6020819 prefixEnd_6020819 3091574080722584251673263 := by
  unfold tailWord_6020819
  simp only [CollatzResearch.WordTrace]
  refine ⟨219597309574608511865233511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146398206383072341243489007 219597309574608511865233511)
  ·
    refine ⟨329395964361912767797850267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219597309574608511865233511 329395964361912767797850267)
    ·
      refine ⟨494093946542869151696775401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 329395964361912767797850267 494093946542869151696775401)
      ·
        refine ⟨370570459907151863772581551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 494093946542869151696775401 370570459907151863772581551)
        ·
          refine ⟨555855689860727795658872327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 370570459907151863772581551 555855689860727795658872327)
          ·
            refine ⟨833783534791091693488308491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 555855689860727795658872327 833783534791091693488308491)
            ·
              refine ⟨1250675302186637540232462737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 833783534791091693488308491 1250675302186637540232462737)
              ·
                refine ⟨938006476639978155174347053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1250675302186637540232462737 938006476639978155174347053)
                ·
                  refine ⟨351752428739991808190380145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 938006476639978155174347053 351752428739991808190380145)
                  ·
                    refine ⟨263814321554993856142785109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 351752428739991808190380145 263814321554993856142785109)
                    ·
                      refine ⟨3091574080722584251673263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 263814321554993856142785109 3091574080722584251673263)
                      ·
                        rfl

theorem cell23_6020819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 8].length) (baseStart_6020819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6020819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6020819 prefixEnd_6020819 := by exact prefixLift 6020819
  have htrace : WordTrace (prefixWord ++ tailWord_6020819) baseStart_6020819 baseEnd_6020819 := by
    simpa [prefixWord, tailWord_6020819, baseEnd_6020819] using wordTrace_append hprefix tailTrace_6020819
  have hstable : (prefixWord ++ tailWord_6020819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6020819).length < 2 ^ (prefixWord ++ tailWord_6020819).sum := by decide
  have hdescent : baseEnd_6020819 < baseStart_6020819 := by decide
  rcases family_descends (prefixWord ++ tailWord_6020819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6020823 : List Nat := [1, 1, 3, 2, 1, 3, 1, 1, 5, 3, 2]
def baseStart_6020823 : Nat := 118140960795 + 6020823 * 2 ^ 59
def prefixEnd_6020823 : Nat := 4983230072969 + 3 ^ 40 * 6020823 * 2
def baseEnd_6020823 : Nat := 3091576134645202236023245

theorem tailTrace_6020823 : CollatzResearch.WordTrace tailWord_6020823 prefixEnd_6020823 3091576134645202236023245 := by
  unfold tailWord_6020823
  simp only [CollatzResearch.WordTrace]
  refine ⟨219597455466594020548379123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146398303644396013698919415 219597455466594020548379123)
  ·
    refine ⟨329396183199891030822568685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 219597455466594020548379123 329396183199891030822568685)
    ·
      refine ⟨123523568699959136558463257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 329396183199891030822568685 123523568699959136558463257)
      ·
        refine ⟨92642676524969352418847443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123523568699959136558463257 92642676524969352418847443)
        ·
          refine ⟨138964014787454028628271165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92642676524969352418847443 138964014787454028628271165)
          ·
            refine ⟨52111505545295260735601687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138964014787454028628271165 52111505545295260735601687)
            ·
              refine ⟨78167258317942891103402531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52111505545295260735601687 78167258317942891103402531)
              ·
                refine ⟨117250887476914336655103797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78167258317942891103402531 117250887476914336655103797)
                ·
                  refine ⟨10992270700960719061415981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 117250887476914336655103797 10992270700960719061415981)
                  ·
                    refine ⟨4122101512860269648030993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10992270700960719061415981 4122101512860269648030993)
                    ·
                      refine ⟨3091576134645202236023245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4122101512860269648030993 3091576134645202236023245)
                      ·
                        rfl

theorem cell23_6020823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 5, 3, 2].length) (baseStart_6020823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6020823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6020823 prefixEnd_6020823 := by exact prefixLift 6020823
  have htrace : WordTrace (prefixWord ++ tailWord_6020823) baseStart_6020823 baseEnd_6020823 := by
    simpa [prefixWord, tailWord_6020823, baseEnd_6020823] using wordTrace_append hprefix tailTrace_6020823
  have hstable : (prefixWord ++ tailWord_6020823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6020823).length < 2 ^ (prefixWord ++ tailWord_6020823).sum := by decide
  have hdescent : baseEnd_6020823 < baseStart_6020823 := by decide
  rcases family_descends (prefixWord ++ tailWord_6020823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6020836 : List Nat := [2, 3, 1, 1, 1, 3, 1, 2, 2, 3, 4]
def baseStart_6020836 : Nat := 118140960795 + 6020836 * 2 ^ 59
def prefixEnd_6020836 : Nat := 4983230072969 + 3 ^ 40 * 6020836 * 2
def baseEnd_6020836 : Nat := 3091582809893710685160685

theorem tailTrace_6020836 : CollatzResearch.WordTrace tailWord_6020836 prefixEnd_6020836 3091582809893710685160685 := by
  unfold tailWord_6020836
  simp only [CollatzResearch.WordTrace]
  refine ⟨109798964807773461884301181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146398619743697949179068241 109798964807773461884301181)
  ·
    refine ⟨41174611802915048206612943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109798964807773461884301181 41174611802915048206612943)
    ·
      refine ⟨61761917704372572309919415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41174611802915048206612943 61761917704372572309919415)
      ·
        refine ⟨92642876556558858464879123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61761917704372572309919415 92642876556558858464879123)
        ·
          refine ⟨138964314834838287697318685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92642876556558858464879123 138964314834838287697318685)
          ·
            refine ⟨52111618063064357886494507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138964314834838287697318685 52111618063064357886494507)
            ·
              refine ⟨78167427094596536829741761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52111618063064357886494507 78167427094596536829741761)
              ·
                refine ⟨58625570320947402622306321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78167427094596536829741761 58625570320947402622306321)
                ·
                  refine ⟨43969177740710551966729741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58625570320947402622306321 43969177740710551966729741)
                  ·
                    refine ⟨16488441652766456987523653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43969177740710551966729741 16488441652766456987523653)
                    ·
                      refine ⟨3091582809893710685160685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16488441652766456987523653 3091582809893710685160685)
                      ·
                        rfl

theorem cell23_6020836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_6020836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6020836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6020836 prefixEnd_6020836 := by exact prefixLift 6020836
  have htrace : WordTrace (prefixWord ++ tailWord_6020836) baseStart_6020836 baseEnd_6020836 := by
    simpa [prefixWord, tailWord_6020836, baseEnd_6020836] using wordTrace_append hprefix tailTrace_6020836
  have hstable : (prefixWord ++ tailWord_6020836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6020836).length < 2 ^ (prefixWord ++ tailWord_6020836).sum := by decide
  have hdescent : baseEnd_6020836 < baseStart_6020836 := by decide
  rcases family_descends (prefixWord ++ tailWord_6020836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6020840 : List Nat := [2, 1, 4, 1, 3, 1, 2, 1, 3, 3, 2]
def baseStart_6020840 : Nat := 118140960795 + 6020840 * 2 ^ 59
def prefixEnd_6020840 : Nat := 4983230072969 + 3 ^ 40 * 6020840 * 2
def baseEnd_6020840 : Nat := 3091584863816328669510667

theorem tailTrace_6020840 : CollatzResearch.WordTrace tailWord_6020840 prefixEnd_6020840 3091584863816328669510667 := by
  unfold tailWord_6020840
  simp only [CollatzResearch.WordTrace]
  refine ⟨109799037753766216225873987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146398717005021621634498649 109799037753766216225873987)
  ·
    refine ⟨164698556630649324338810981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109799037753766216225873987 164698556630649324338810981)
    ·
      refine ⟨30880979368246748313527059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164698556630649324338810981 30880979368246748313527059)
      ·
        refine ⟨46321469052370122470290589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30880979368246748313527059 46321469052370122470290589)
        ·
          refine ⟨17370550894638795926358971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46321469052370122470290589 17370550894638795926358971)
          ·
            refine ⟨26055826341958193889538457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17370550894638795926358971 26055826341958193889538457)
            ·
              refine ⟨19541869756468645417153843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26055826341958193889538457 19541869756468645417153843)
              ·
                refine ⟨29312804634702968125730765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19541869756468645417153843 29312804634702968125730765)
                ·
                  refine ⟨10992301738013613047149037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29312804634702968125730765 10992301738013613047149037)
                  ·
                    refine ⟨4122113151755104892680889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10992301738013613047149037 4122113151755104892680889)
                    ·
                      refine ⟨3091584863816328669510667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4122113151755104892680889 3091584863816328669510667)
                      ·
                        rfl

theorem cell23_6020840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 3, 3, 2].length) (baseStart_6020840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6020840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6020840 prefixEnd_6020840 := by exact prefixLift 6020840
  have htrace : WordTrace (prefixWord ++ tailWord_6020840) baseStart_6020840 baseEnd_6020840 := by
    simpa [prefixWord, tailWord_6020840, baseEnd_6020840] using wordTrace_append hprefix tailTrace_6020840
  have hstable : (prefixWord ++ tailWord_6020840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6020840).length < 2 ^ (prefixWord ++ tailWord_6020840).sum := by decide
  have hdescent : baseEnd_6020840 < baseStart_6020840 := by decide
  rcases family_descends (prefixWord ++ tailWord_6020840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6020846 : List Nat := [4, 1, 2, 1, 1, 2, 1, 2, 1, 8]
def baseStart_6020846 : Nat := 118140960795 + 6020846 * 2 ^ 59
def prefixEnd_6020846 : Nat := 4983230072969 + 3 ^ 40 * 6020846 * 2
def baseEnd_6020846 : Nat := 1030529314900085215345213

theorem tailTrace_6020846 : CollatzResearch.WordTrace tailWord_6020846 prefixEnd_6020846 1030529314900085215345213 := by
  unfold tailWord_6020846
  simp only [CollatzResearch.WordTrace]
  refine ⟨27449786793188836934558299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146398862897007130317644261 27449786793188836934558299)
  ·
    refine ⟨41174680189783255401837449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27449786793188836934558299 41174680189783255401837449)
    ·
      refine ⟨30881010142337441551378087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41174680189783255401837449 30881010142337441551378087)
      ·
        refine ⟨46321515213506162327067131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30881010142337441551378087 46321515213506162327067131)
        ·
          refine ⟨69482272820259243490600697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46321515213506162327067131 69482272820259243490600697)
          ·
            refine ⟨52111704615194432617950523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69482272820259243490600697 52111704615194432617950523)
            ·
              refine ⟨78167556922791648926925785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52111704615194432617950523 78167556922791648926925785)
              ·
                refine ⟨58625667692093736695194339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78167556922791648926925785 58625667692093736695194339)
                ·
                  refine ⟨87938501538140605042791509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58625667692093736695194339 87938501538140605042791509)
                  ·
                    refine ⟨1030529314900085215345213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 87938501538140605042791509 1030529314900085215345213)
                    ·
                      rfl

theorem cell23_6020846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_6020846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6020846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6020846 prefixEnd_6020846 := by exact prefixLift 6020846
  have htrace : WordTrace (prefixWord ++ tailWord_6020846) baseStart_6020846 baseEnd_6020846 := by
    simpa [prefixWord, tailWord_6020846, baseEnd_6020846] using wordTrace_append hprefix tailTrace_6020846
  have hstable : (prefixWord ++ tailWord_6020846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6020846).length < 2 ^ (prefixWord ++ tailWord_6020846).sum := by decide
  have hdescent : baseEnd_6020846 < baseStart_6020846 := by decide
  rcases family_descends (prefixWord ++ tailWord_6020846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
