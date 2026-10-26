import V185TrunkScan22Chunk105

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_951220 : List Nat := [2, 5, 2, 1, 1, 3, 2, 1, 2, 3]
def baseStart_951220 : Nat := 118140960795 + 951220 * 2 ^ 59
def prefixEnd_951220 : Nat := 4983230072969 + 3 ^ 40 * 951220 * 2
def baseEnd_951220 : Nat := 325622045446582387383617

theorem tailTrace_951220 : CollatzResearch.WordTrace tailWord_951220 prefixEnd_951220 325622045446582387383617 := by
  unfold tailWord_951220
  simp only [CollatzResearch.WordTrace]
  refine ⟨17346921806949935143685557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23129229075933246858247409 17346921806949935143685557)
  ·
    refine ⟨1626273919401556419720521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17346921806949935143685557 1626273919401556419720521)
    ·
      refine ⟨1219705439551167314790391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1626273919401556419720521 1219705439551167314790391)
      ·
        refine ⟨1829558159326750972185587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1219705439551167314790391 1829558159326750972185587)
        ·
          refine ⟨2744337238990126458278381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1829558159326750972185587 2744337238990126458278381)
          ·
            refine ⟨1029126464621297421854393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2744337238990126458278381 1029126464621297421854393)
            ·
              refine ⟨771844848465973066390795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1029126464621297421854393 771844848465973066390795)
              ·
                refine ⟨1157767272698959599586193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 771844848465973066390795 1157767272698959599586193)
                ·
                  refine ⟨868325454524219699689645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1157767272698959599586193 868325454524219699689645)
                  ·
                    refine ⟨325622045446582387383617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 868325454524219699689645 325622045446582387383617)
                    ·
                      rfl

theorem cell22_951220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_951220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_951220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_951220 prefixEnd_951220 := by exact prefixLift 951220
  have htrace : WordTrace (prefixWord ++ tailWord_951220) baseStart_951220 baseEnd_951220 := by
    simpa [prefixWord, tailWord_951220, baseEnd_951220] using wordTrace_append hprefix tailTrace_951220
  have hstable : (prefixWord ++ tailWord_951220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951220).length < 2 ^ (prefixWord ++ tailWord_951220).sum := by decide
  have hdescent : baseEnd_951220 < baseStart_951220 := by decide
  rcases family_descends (prefixWord ++ tailWord_951220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951255 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 10]
def baseStart_951255 : Nat := 118140960795 + 951255 * 2 ^ 59
def prefixEnd_951255 : Nat := 4983230072969 + 3 ^ 40 * 951255 * 2
def baseEnd_951255 : Nat := 108544675553951320919503

theorem tailTrace_951255 : CollatzResearch.WordTrace tailWord_951255 prefixEnd_951255 108544675553951320919503 := by
  unfold tailWord_951255
  simp only [CollatzResearch.WordTrace]
  refine ⟨34695120168773071264895219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23130080112515380843263479 34695120168773071264895219)
  ·
    refine ⟨52042680253159606897342829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34695120168773071264895219 52042680253159606897342829)
    ·
      refine ⟨19516005094934852586503561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52042680253159606897342829 19516005094934852586503561)
      ·
        refine ⟨14637003821201139439877671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19516005094934852586503561 14637003821201139439877671)
        ·
          refine ⟨21955505731801709159816507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14637003821201139439877671 21955505731801709159816507)
          ·
            refine ⟨32933258597702563739724761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21955505731801709159816507 32933258597702563739724761)
            ·
              refine ⟨24699943948276922804793571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32933258597702563739724761 24699943948276922804793571)
              ·
                refine ⟨37049915922415384207190357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24699943948276922804793571 37049915922415384207190357)
                ·
                  refine ⟨108544675553951320919503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 37049915922415384207190357 108544675553951320919503)
                  ·
                    rfl

theorem cell22_951255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 10].length) (baseStart_951255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_951255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_951255 prefixEnd_951255 := by exact prefixLift 951255
  have htrace : WordTrace (prefixWord ++ tailWord_951255) baseStart_951255 baseEnd_951255 := by
    simpa [prefixWord, tailWord_951255, baseEnd_951255] using wordTrace_append hprefix tailTrace_951255
  have hstable : (prefixWord ++ tailWord_951255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951255).length < 2 ^ (prefixWord ++ tailWord_951255).sum := by decide
  have hdescent : baseEnd_951255 < baseStart_951255 := by decide
  rcases family_descends (prefixWord ++ tailWord_951255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951306 : List Nat := [3, 1, 2, 2, 3, 2, 2, 3, 4]
def baseStart_951306 : Nat := 118140960795 + 951306 * 2 ^ 59
def prefixEnd_951306 : Nat := 4983230072969 + 3 ^ 40 * 951306 * 2
def baseEnd_951306 : Nat := 108550495001368943244451

theorem tailTrace_951306 : CollatzResearch.WordTrace tailWord_951306 prefixEnd_951306 108550495001368943244451 := by
  unfold tailWord_951306
  simp only [CollatzResearch.WordTrace]
  refine ⟨8674245072897076743750443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23131320194392204650001181 8674245072897076743750443)
  ·
    refine ⟨13011367609345615115625665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8674245072897076743750443 13011367609345615115625665)
    ·
      refine ⟨9758525707009211336719249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13011367609345615115625665 9758525707009211336719249)
      ·
        refine ⟨7318894280256908502539437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9758525707009211336719249 7318894280256908502539437)
        ·
          refine ⟨2744585355096340688452289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7318894280256908502539437 2744585355096340688452289)
          ·
            refine ⟨2058439016322255516339217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2744585355096340688452289 2058439016322255516339217)
            ·
              refine ⟨1543829262241691637254413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2058439016322255516339217 1543829262241691637254413)
              ·
                refine ⟨578935973340634363970405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1543829262241691637254413 578935973340634363970405)
                ·
                  refine ⟨108550495001368943244451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 578935973340634363970405 108550495001368943244451)
                  ·
                    rfl

theorem cell22_951306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 3, 4].length) (baseStart_951306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_951306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_951306 prefixEnd_951306 := by exact prefixLift 951306
  have htrace : WordTrace (prefixWord ++ tailWord_951306) baseStart_951306 baseEnd_951306 := by
    simpa [prefixWord, tailWord_951306, baseEnd_951306] using wordTrace_append hprefix tailTrace_951306
  have hstable : (prefixWord ++ tailWord_951306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951306).length < 2 ^ (prefixWord ++ tailWord_951306).sum := by decide
  have hdescent : baseEnd_951306 < baseStart_951306 := by decide
  rcases family_descends (prefixWord ++ tailWord_951306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951317 : List Nat := [1, 3, 2, 1, 4, 2, 9]
def baseStart_951317 : Nat := 118140960795 + 951317 * 2 ^ 59
def prefixEnd_951317 : Nat := 4983230072969 + 3 ^ 40 * 951317 * 2
def baseEnd_951317 : Nat := 12061305575144683989197

theorem tailTrace_951317 : CollatzResearch.WordTrace tailWord_951317 prefixEnd_951317 12061305575144683989197 := by
  unfold tailWord_951317
  simp only [CollatzResearch.WordTrace]
  refine ⟨34697381494548455853652205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23131587663032303902434803 34697381494548455853652205)
  ·
    refine ⟨13011518060455670945119577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34697381494548455853652205 13011518060455670945119577)
    ·
      refine ⟨9758638545341753208839683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13011518060455670945119577 9758638545341753208839683)
      ·
        refine ⟨14637957818012629813259525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9758638545341753208839683 14637957818012629813259525)
        ·
          refine ⟨2744617090877368089986161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14637957818012629813259525 2744617090877368089986161)
          ·
            refine ⟨2058462818158026067489621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2744617090877368089986161 2058462818158026067489621)
            ·
              refine ⟨12061305575144683989197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2058462818158026067489621 12061305575144683989197)
              ·
                rfl

theorem cell22_951317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 9].length) (baseStart_951317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_951317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_951317 prefixEnd_951317 := by exact prefixLift 951317
  have htrace : WordTrace (prefixWord ++ tailWord_951317) baseStart_951317 baseEnd_951317 := by
    simpa [prefixWord, tailWord_951317, baseEnd_951317] using wordTrace_append hprefix tailTrace_951317
  have hstable : (prefixWord ++ tailWord_951317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951317).length < 2 ^ (prefixWord ++ tailWord_951317).sum := by decide
  have hdescent : baseEnd_951317 < baseStart_951317 := by decide
  rcases family_descends (prefixWord ++ tailWord_951317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951338 : List Nat := [3, 1, 4, 1, 4, 1, 1, 1, 1, 5]
def baseStart_951338 : Nat := 118140960795 + 951338 * 2 ^ 59
def prefixEnd_951338 : Nat := 4983230072969 + 3 ^ 40 * 951338 * 2
def baseEnd_951338 : Nat := 325662439258069412933255

theorem tailTrace_951338 : CollatzResearch.WordTrace tailWord_951338 prefixEnd_951338 325662439258069412933255 := by
  unfold tailWord_951338
  simp only [CollatzResearch.WordTrace]
  refine ⟨8674536856868094110041667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23132098284981584293444445 8674536856868094110041667)
  ·
    refine ⟨13011805285302141165062501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8674536856868094110041667 13011805285302141165062501)
    ·
      refine ⟨2439713490994151468449219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13011805285302141165062501 2439713490994151468449219)
      ·
        refine ⟨3659570236491227202673829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2439713490994151468449219 3659570236491227202673829)
        ·
          refine ⟨686169419342105100501343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3659570236491227202673829 686169419342105100501343)
          ·
            refine ⟨1029254129013157650752015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 686169419342105100501343 1029254129013157650752015)
            ·
              refine ⟨1543881193519736476128023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1029254129013157650752015 1543881193519736476128023)
              ·
                refine ⟨2315821790279604714192035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1543881193519736476128023 2315821790279604714192035)
                ·
                  refine ⟨3473732685419407071288053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2315821790279604714192035 3473732685419407071288053)
                  ·
                    refine ⟨325662439258069412933255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3473732685419407071288053 325662439258069412933255)
                    ·
                      rfl

theorem cell22_951338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_951338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_951338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_951338 prefixEnd_951338 := by exact prefixLift 951338
  have htrace : WordTrace (prefixWord ++ tailWord_951338) baseStart_951338 baseEnd_951338 := by
    simpa [prefixWord, tailWord_951338, baseEnd_951338] using wordTrace_append hprefix tailTrace_951338
  have hstable : (prefixWord ++ tailWord_951338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951338).length < 2 ^ (prefixWord ++ tailWord_951338).sum := by decide
  have hdescent : baseEnd_951338 < baseStart_951338 := by decide
  rcases family_descends (prefixWord ++ tailWord_951338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951377 : List Nat := [1, 2, 2, 1, 3, 1, 2, 1, 4, 5]
def baseStart_951377 : Nat := 118140960795 + 951377 * 2 ^ 59
def prefixEnd_951377 : Nat := 4983230072969 + 3 ^ 40 * 951377 * 2
def baseEnd_951377 : Nat := 325675789755086311208135

theorem tailTrace_951377 : CollatzResearch.WordTrace tailWord_951377 prefixEnd_951377 325675789755086311208135 := by
  unfold tailWord_951377
  simp only [CollatzResearch.WordTrace]
  refine ⟨34699569874331086100836385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23133046582887390733890923 34699569874331086100836385)
  ·
    refine ⟨26024677405748314575627289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34699569874331086100836385 26024677405748314575627289)
    ·
      refine ⟨19518508054311235931720467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26024677405748314575627289 19518508054311235931720467)
      ·
        refine ⟨29277762081466853897580701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19518508054311235931720467 29277762081466853897580701)
        ·
          refine ⟨10979160780550070211592763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29277762081466853897580701 10979160780550070211592763)
          ·
            refine ⟨16468741170825105317389145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10979160780550070211592763 16468741170825105317389145)
            ·
              refine ⟨12351555878118828988041859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16468741170825105317389145 12351555878118828988041859)
              ·
                refine ⟨18527333817178243482062789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12351555878118828988041859 18527333817178243482062789)
                ·
                  refine ⟨3473875090720920652886773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18527333817178243482062789 3473875090720920652886773)
                  ·
                    refine ⟨325675789755086311208135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3473875090720920652886773 325675789755086311208135)
                    ·
                      rfl

theorem cell22_951377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 5].length) (baseStart_951377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_951377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_951377 prefixEnd_951377 := by exact prefixLift 951377
  have htrace : WordTrace (prefixWord ++ tailWord_951377) baseStart_951377 baseEnd_951377 := by
    simpa [prefixWord, tailWord_951377, baseEnd_951377] using wordTrace_append hprefix tailTrace_951377
  have hstable : (prefixWord ++ tailWord_951377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951377).length < 2 ^ (prefixWord ++ tailWord_951377).sum := by decide
  have hdescent : baseEnd_951377 < baseStart_951377 := by decide
  rcases family_descends (prefixWord ++ tailWord_951377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951407 : List Nat := [1, 1, 2, 1, 3, 3, 2, 1, 8]
def baseStart_951407 : Nat := 118140960795 + 951407 * 2 ^ 59
def prefixEnd_951407 : Nat := 4983230072969 + 3 ^ 40 * 951407 * 2
def baseEnd_951407 : Nat := 108562019789392077652681

theorem tailTrace_951407 : CollatzResearch.WordTrace tailWord_951407 prefixEnd_951407 108562019789392077652681 := by
  unfold tailWord_951407
  simp only [CollatzResearch.WordTrace]
  refine ⟨34700664064222401224428475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23133776042814934149618983 34700664064222401224428475)
  ·
    refine ⟨52050996096333601836642713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34700664064222401224428475 52050996096333601836642713)
    ·
      refine ⟨39038247072250201377482035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52050996096333601836642713 39038247072250201377482035)
      ·
        refine ⟨58557370608375302066223053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39038247072250201377482035 58557370608375302066223053)
        ·
          refine ⟨21959013978140738274833645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58557370608375302066223053 21959013978140738274833645)
          ·
            refine ⟨8234630241802776853062617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21959013978140738274833645 8234630241802776853062617)
            ·
              refine ⟨6175972681352082639796963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8234630241802776853062617 6175972681352082639796963)
              ·
                refine ⟨9263959022028123959695445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6175972681352082639796963 9263959022028123959695445)
                ·
                  refine ⟨108562019789392077652681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9263959022028123959695445 108562019789392077652681)
                  ·
                    rfl

theorem cell22_951407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 8].length) (baseStart_951407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_951407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_951407 prefixEnd_951407 := by exact prefixLift 951407
  have htrace : WordTrace (prefixWord ++ tailWord_951407) baseStart_951407 baseEnd_951407 := by
    simpa [prefixWord, tailWord_951407, baseEnd_951407] using wordTrace_append hprefix tailTrace_951407
  have hstable : (prefixWord ++ tailWord_951407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951407).length < 2 ^ (prefixWord ++ tailWord_951407).sum := by decide
  have hdescent : baseEnd_951407 < baseStart_951407 := by decide
  rcases family_descends (prefixWord ++ tailWord_951407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951409 : List Nat := [1, 2, 2, 2, 1, 1, 2, 6, 1, 4]
def baseStart_951409 : Nat := 118140960795 + 951409 * 2 ^ 59
def prefixEnd_951409 : Nat := 4983230072969 + 3 ^ 40 * 951409 * 2
def baseEnd_951409 : Nat := 325686744009048894408037

theorem tailTrace_951409 : CollatzResearch.WordTrace tailWord_951409 prefixEnd_951409 325686744009048894408037 := by
  unfold tailWord_951409
  simp only [CollatzResearch.WordTrace]
  refine ⟨34700737010215155566001281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23133824673476770377334187 34700737010215155566001281)
  ·
    refine ⟨26025552757661366674500961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34700737010215155566001281 26025552757661366674500961)
    ·
      refine ⟨19519164568246025005875721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26025552757661366674500961 19519164568246025005875721)
      ·
        refine ⟨14639373426184518754406791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19519164568246025005875721 14639373426184518754406791)
        ·
          refine ⟨21959060139276778131610187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14639373426184518754406791 21959060139276778131610187)
          ·
            refine ⟨32938590208915167197415281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21959060139276778131610187 32938590208915167197415281)
            ·
              refine ⟨24703942656686375398061461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32938590208915167197415281 24703942656686375398061461)
              ·
                refine ⟨1157997312032173846784131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24703942656686375398061461 1157997312032173846784131)
                ·
                  refine ⟨1736995968048260770176197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1157997312032173846784131 1736995968048260770176197)
                  ·
                    refine ⟨325686744009048894408037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1736995968048260770176197 325686744009048894408037)
                    ·
                      rfl

theorem cell22_951409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 6, 1, 4].length) (baseStart_951409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_951409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_951409 prefixEnd_951409 := by exact prefixLift 951409
  have htrace : WordTrace (prefixWord ++ tailWord_951409) baseStart_951409 baseEnd_951409 := by
    simpa [prefixWord, tailWord_951409, baseEnd_951409] using wordTrace_append hprefix tailTrace_951409
  have hstable : (prefixWord ++ tailWord_951409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951409).length < 2 ^ (prefixWord ++ tailWord_951409).sum := by decide
  have hdescent : baseEnd_951409 < baseStart_951409 := by decide
  rcases family_descends (prefixWord ++ tailWord_951409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951456 : List Nat := [2, 1, 1, 4, 2, 1, 1, 5, 2, 3]
def baseStart_951456 : Nat := 118140960795 + 951456 * 2 ^ 59
def prefixEnd_951456 : Nat := 4983230072969 + 3 ^ 40 * 951456 * 2
def baseEnd_951456 : Nat := 325702833069556438482893

theorem tailTrace_951456 : CollatzResearch.WordTrace tailWord_951456 prefixEnd_951456 325702833069556438482893 := by
  unfold tailWord_951456
  simp only [CollatzResearch.WordTrace]
  refine ⟨17351225620522441296481111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23134967494029921728641481 17351225620522441296481111)
  ·
    refine ⟨26026838430783661944721667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17351225620522441296481111 26026838430783661944721667)
    ·
      refine ⟨39040257646175492917082501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26026838430783661944721667 39040257646175492917082501)
      ·
        refine ⟨7320048308657904921952969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39040257646175492917082501 7320048308657904921952969)
        ·
          refine ⟨5490036231493428691464727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7320048308657904921952969 5490036231493428691464727)
          ·
            refine ⟨8235054347240143037197091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5490036231493428691464727 8235054347240143037197091)
            ·
              refine ⟨12352581520860214555795637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8235054347240143037197091 12352581520860214555795637)
              ·
                refine ⟨1158054517580645114605841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12352581520860214555795637 1158054517580645114605841)
                ·
                  refine ⟨868540888185483835954381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1158054517580645114605841 868540888185483835954381)
                  ·
                    refine ⟨325702833069556438482893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 868540888185483835954381 325702833069556438482893)
                    ·
                      rfl

theorem cell22_951456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 5, 2, 3].length) (baseStart_951456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_951456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_951456 prefixEnd_951456 := by exact prefixLift 951456
  have htrace : WordTrace (prefixWord ++ tailWord_951456) baseStart_951456 baseEnd_951456 := by
    simpa [prefixWord, tailWord_951456, baseEnd_951456] using wordTrace_append hprefix tailTrace_951456
  have hstable : (prefixWord ++ tailWord_951456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951456).length < 2 ^ (prefixWord ++ tailWord_951456).sum := by decide
  have hdescent : baseEnd_951456 < baseStart_951456 := by decide
  rcases family_descends (prefixWord ++ tailWord_951456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951544 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 7, 4]
def baseStart_951544 : Nat := 118140960795 + 951544 * 2 ^ 59
def prefixEnd_951544 : Nat := 4983230072969 + 3 ^ 40 * 951544 * 2
def baseEnd_951544 : Nat := 325732957267953542282623

theorem tailTrace_951544 : CollatzResearch.WordTrace tailWord_951544 prefixEnd_951544 325732957267953542282623 := by
  unfold tailWord_951544
  simp only [CollatzResearch.WordTrace]
  refine ⟨17352830432363036811082843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23137107243150715748110457 17352830432363036811082843)
  ·
    refine ⟨26029245648544555216624265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17352830432363036811082843 26029245648544555216624265)
    ·
      refine ⟨19521934236408416412468199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26029245648544555216624265 19521934236408416412468199)
      ·
        refine ⟨29282901354612624618702299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19521934236408416412468199 29282901354612624618702299)
        ·
          refine ⟨43924352031918936928053449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29282901354612624618702299 43924352031918936928053449)
          ·
            refine ⟨32943264023939202696040087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43924352031918936928053449 32943264023939202696040087)
            ·
              refine ⟨49414896035908804044060131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32943264023939202696040087 49414896035908804044060131)
              ·
                refine ⟨74122344053863206066090197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49414896035908804044060131 74122344053863206066090197)
                ·
                  refine ⟨1737242438762418892173989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 74122344053863206066090197 1737242438762418892173989)
                  ·
                    refine ⟨325732957267953542282623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1737242438762418892173989 325732957267953542282623)
                    ·
                      rfl

theorem cell22_951544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 7, 4].length) (baseStart_951544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_951544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_951544 prefixEnd_951544 := by exact prefixLift 951544
  have htrace : WordTrace (prefixWord ++ tailWord_951544) baseStart_951544 baseEnd_951544 := by
    simpa [prefixWord, tailWord_951544, baseEnd_951544] using wordTrace_append hprefix tailTrace_951544
  have hstable : (prefixWord ++ tailWord_951544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951544).length < 2 ^ (prefixWord ++ tailWord_951544).sum := by decide
  have hdescent : baseEnd_951544 < baseStart_951544 := by decide
  rcases family_descends (prefixWord ++ tailWord_951544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951578 : List Nat := [3, 1, 1, 3, 3, 1, 3, 2, 1, 4]
def baseStart_951578 : Nat := 118140960795 + 951578 * 2 ^ 59
def prefixEnd_951578 : Nat := 4983230072969 + 3 ^ 40 * 951578 * 2
def baseEnd_951578 : Nat := 325744596162788786932519

theorem tailTrace_951578 : CollatzResearch.WordTrace tailWord_951578 prefixEnd_951578 325744596162788786932519 := by
  unfold tailWord_951578
  simp only [CollatzResearch.WordTrace]
  refine ⟨8676725236650724357225847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23137933964401931619268925 8676725236650724357225847)
  ·
    refine ⟨13015087854976086535838771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8676725236650724357225847 13015087854976086535838771)
    ·
      refine ⟨19522631782464129803758157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13015087854976086535838771 19522631782464129803758157)
      ·
        refine ⟨7320986918424048676409309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19522631782464129803758157 7320986918424048676409309)
        ·
          refine ⟨2745370094409018253653491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7320986918424048676409309 2745370094409018253653491)
          ·
            refine ⟨4118055141613527380480237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2745370094409018253653491 4118055141613527380480237)
            ·
              refine ⟨1544270678105072767680089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4118055141613527380480237 1544270678105072767680089)
              ·
                refine ⟨1158203008578804575760067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1544270678105072767680089 1158203008578804575760067)
                ·
                  refine ⟨1737304512868206863640101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1158203008578804575760067 1737304512868206863640101)
                  ·
                    refine ⟨325744596162788786932519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1737304512868206863640101 325744596162788786932519)
                    ·
                      rfl

theorem cell22_951578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 2, 1, 4].length) (baseStart_951578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_951578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_951578 prefixEnd_951578 := by exact prefixLift 951578
  have htrace : WordTrace (prefixWord ++ tailWord_951578) baseStart_951578 baseEnd_951578 := by
    simpa [prefixWord, tailWord_951578, baseEnd_951578] using wordTrace_append hprefix tailTrace_951578
  have hstable : (prefixWord ++ tailWord_951578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951578).length < 2 ^ (prefixWord ++ tailWord_951578).sum := by decide
  have hdescent : baseEnd_951578 < baseStart_951578 := by decide
  rcases family_descends (prefixWord ++ tailWord_951578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951619 : List Nat := [1, 1, 1, 3, 1, 3, 1, 2, 2, 7]
def baseStart_951619 : Nat := 118140960795 + 951619 * 2 ^ 59
def prefixEnd_951619 : Nat := 4983230072969 + 3 ^ 40 * 951619 * 2
def baseEnd_951619 : Nat := 325758631300678346657393

theorem tailTrace_951619 : CollatzResearch.WordTrace tailWord_951619 prefixEnd_951619 325758631300678346657393 := by
  unfold tailWord_951619
  simp only [CollatzResearch.WordTrace]
  refine ⟨34708396339454361431145911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23138930892969574287430607 34708396339454361431145911)
  ·
    refine ⟨52062594509181542146718867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34708396339454361431145911 52062594509181542146718867)
    ·
      refine ⟨78093891763772313220078301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52062594509181542146718867 78093891763772313220078301)
      ·
        refine ⟨29285209411414617457529363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78093891763772313220078301 29285209411414617457529363)
        ·
          refine ⟨43927814117121926186294045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29285209411414617457529363 43927814117121926186294045)
          ·
            refine ⟨16472930293920722319860267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43927814117121926186294045 16472930293920722319860267)
            ·
              refine ⟨24709395440881083479790401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16472930293920722319860267 24709395440881083479790401)
              ·
                refine ⟨18532046580660812609842801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24709395440881083479790401 18532046580660812609842801)
                ·
                  refine ⟨13899034935495609457382101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18532046580660812609842801 13899034935495609457382101)
                  ·
                    refine ⟨325758631300678346657393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13899034935495609457382101 325758631300678346657393)
                    ·
                      rfl

theorem cell22_951619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 7].length) (baseStart_951619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_951619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_951619 prefixEnd_951619 := by exact prefixLift 951619
  have htrace : WordTrace (prefixWord ++ tailWord_951619) baseStart_951619 baseEnd_951619 := by
    simpa [prefixWord, tailWord_951619, baseEnd_951619] using wordTrace_append hprefix tailTrace_951619
  have hstable : (prefixWord ++ tailWord_951619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951619).length < 2 ^ (prefixWord ++ tailWord_951619).sum := by decide
  have hdescent : baseEnd_951619 < baseStart_951619 := by decide
  rcases family_descends (prefixWord ++ tailWord_951619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951666 : List Nat := [3, 2, 1, 2, 1, 2, 3, 1, 7]
def baseStart_951666 : Nat := 118140960795 + 951666 * 2 ^ 59
def prefixEnd_951666 : Nat := 4983230072969 + 3 ^ 40 * 951666 * 2
def baseEnd_951666 : Nat := 108591573453728630244083

theorem tailTrace_951666 : CollatzResearch.WordTrace tailWord_951666 prefixEnd_951666 108591573453728630244083 := by
  unfold tailWord_951666
  simp only [CollatzResearch.WordTrace]
  refine ⟨8677527642571022114526713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23140073713522725638737901 8677527642571022114526713)
  ·
    refine ⟨6508145731928266585895035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8677527642571022114526713 6508145731928266585895035)
    ·
      refine ⟨9762218597892399878842553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6508145731928266585895035 9762218597892399878842553)
      ·
        refine ⟨7321663948419299909131915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9762218597892399878842553 7321663948419299909131915)
        ·
          refine ⟨10982495922628949863697873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7321663948419299909131915 10982495922628949863697873)
          ·
            refine ⟨8236871941971712397773405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10982495922628949863697873 8236871941971712397773405)
            ·
              refine ⟨3088826978239392149165027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8236871941971712397773405 3088826978239392149165027)
              ·
                refine ⟨4633240467359088223747541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3088826978239392149165027 4633240467359088223747541)
                ·
                  refine ⟨108591573453728630244083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4633240467359088223747541 108591573453728630244083)
                  ·
                    rfl

theorem cell22_951666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 7].length) (baseStart_951666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_951666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_951666 prefixEnd_951666 := by exact prefixLift 951666
  have htrace : WordTrace (prefixWord ++ tailWord_951666) baseStart_951666 baseEnd_951666 := by
    simpa [prefixWord, tailWord_951666, baseEnd_951666] using wordTrace_append hprefix tailTrace_951666
  have hstable : (prefixWord ++ tailWord_951666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951666).length < 2 ^ (prefixWord ++ tailWord_951666).sum := by decide
  have hdescent : baseEnd_951666 < baseStart_951666 := by decide
  rcases family_descends (prefixWord ++ tailWord_951666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951704 : List Nat := [2, 1, 2, 5, 2, 2, 1, 3, 1, 3]
def baseStart_951704 : Nat := 118140960795 + 951704 * 2 ^ 59
def prefixEnd_951704 : Nat := 4983230072969 + 3 ^ 40 * 951704 * 2
def baseEnd_951704 : Nat := 325787728537766458282133

theorem tailTrace_951704 : CollatzResearch.WordTrace tailWord_951704 prefixEnd_951704 325787728537766458282133 := by
  unfold tailWord_951704
  simp only [CollatzResearch.WordTrace]
  refine ⟨17355748272073210473995083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23140997696097613965326777 17355748272073210473995083)
  ·
    refine ⟨26033622408109815710992625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17355748272073210473995083 26033622408109815710992625)
    ·
      refine ⟨19525216806082361783244469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26033622408109815710992625 19525216806082361783244469)
      ·
        refine ⟨1830489075570221417179169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19525216806082361783244469 1830489075570221417179169)
        ·
          refine ⟨1372866806677666062884377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1830489075570221417179169 1372866806677666062884377)
          ·
            refine ⟨1029650105008249547163283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1372866806677666062884377 1029650105008249547163283)
            ·
              refine ⟨1544475157512374320744925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1029650105008249547163283 1544475157512374320744925)
              ·
                refine ⟨579178184067140370279347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1544475157512374320744925 579178184067140370279347)
                ·
                  refine ⟨868767276100710555419021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 579178184067140370279347 868767276100710555419021)
                  ·
                    refine ⟨325787728537766458282133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 868767276100710555419021 325787728537766458282133)
                    ·
                      rfl

theorem cell22_951704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 3, 1, 3].length) (baseStart_951704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_951704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_951704 prefixEnd_951704 := by exact prefixLift 951704
  have htrace : WordTrace (prefixWord ++ tailWord_951704) baseStart_951704 baseEnd_951704 := by
    simpa [prefixWord, tailWord_951704, baseEnd_951704] using wordTrace_append hprefix tailTrace_951704
  have hstable : (prefixWord ++ tailWord_951704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951704).length < 2 ^ (prefixWord ++ tailWord_951704).sum := by decide
  have hdescent : baseEnd_951704 < baseStart_951704 := by decide
  rcases family_descends (prefixWord ++ tailWord_951704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951758 : List Nat := [4, 1, 1, 1, 2, 1, 3, 3, 2, 4]
def baseStart_951758 : Nat := 118140960795 + 951758 * 2 ^ 59
def prefixEnd_951758 : Nat := 4983230072969 + 3 ^ 40 * 951758 * 2
def baseEnd_951758 : Nat := 325806213841328317431967

theorem tailTrace_951758 : CollatzResearch.WordTrace tailWord_951758 prefixEnd_951758 325806213841328317431967 := by
  unfold tailWord_951758
  simp only [CollatzResearch.WordTrace]
  refine ⟨4339183260743848521306991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23142310723967192113637285 4339183260743848521306991)
  ·
    refine ⟨6508774891115772781960487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4339183260743848521306991 6508774891115772781960487)
    ·
      refine ⟨9763162336673659172940731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6508774891115772781960487 9763162336673659172940731)
      ·
        refine ⟨14644743505010488759411097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9763162336673659172940731 14644743505010488759411097)
        ·
          refine ⟨10983557628757866569558323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14644743505010488759411097 10983557628757866569558323)
          ·
            refine ⟨16475336443136799854337485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10983557628757866569558323 16475336443136799854337485)
            ·
              refine ⟨6178251166176299945376557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16475336443136799854337485 6178251166176299945376557)
              ·
                refine ⟨2316844187316112479516209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6178251166176299945376557 2316844187316112479516209)
                ·
                  refine ⟨1737633140487084359637157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2316844187316112479516209 1737633140487084359637157)
                  ·
                    refine ⟨325806213841328317431967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1737633140487084359637157 325806213841328317431967)
                    ·
                      rfl

theorem cell22_951758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_951758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_951758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_951758 prefixEnd_951758 := by exact prefixLift 951758
  have htrace : WordTrace (prefixWord ++ tailWord_951758) baseStart_951758 baseEnd_951758 := by
    simpa [prefixWord, tailWord_951758, baseEnd_951758] using wordTrace_append hprefix tailTrace_951758
  have hstable : (prefixWord ++ tailWord_951758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951758).length < 2 ^ (prefixWord ++ tailWord_951758).sum := by decide
  have hdescent : baseEnd_951758 < baseStart_951758 := by decide
  rcases family_descends (prefixWord ++ tailWord_951758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951801 : List Nat := [1, 2, 1, 3, 1, 2, 1, 2, 9]
def baseStart_951801 : Nat := 118140960795 + 951801 * 2 ^ 59
def prefixEnd_951801 : Nat := 4983230072969 + 3 ^ 40 * 951801 * 2
def baseEnd_951801 : Nat := 108606977873363512868945

theorem tailTrace_951801 : CollatzResearch.WordTrace tailWord_951801 prefixEnd_951801 108606977873363512868945 := by
  unfold tailWord_951801
  simp only [CollatzResearch.WordTrace]
  refine ⟨34715034424795006514271257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23143356283196671009514171 34715034424795006514271257)
  ·
    refine ⟨26036275818596254885703443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34715034424795006514271257 26036275818596254885703443)
    ·
      refine ⟨39054413727894382328555165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26036275818596254885703443 39054413727894382328555165)
      ·
        refine ⟨14645405147960393373208187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39054413727894382328555165 14645405147960393373208187)
        ·
          refine ⟨21968107721940590059812281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14645405147960393373208187 21968107721940590059812281)
          ·
            refine ⟨16476080791455442544859211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21968107721940590059812281 16476080791455442544859211)
            ·
              refine ⟨24714121187183163817288817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16476080791455442544859211 24714121187183163817288817)
              ·
                refine ⟨18535590890387372862966613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24714121187183163817288817 18535590890387372862966613)
                ·
                  refine ⟨108606977873363512868945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 18535590890387372862966613 108606977873363512868945)
                  ·
                    rfl

theorem cell22_951801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 9].length) (baseStart_951801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_951801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_951801 prefixEnd_951801 := by exact prefixLift 951801
  have htrace : WordTrace (prefixWord ++ tailWord_951801) baseStart_951801 baseEnd_951801 := by
    simpa [prefixWord, tailWord_951801, baseEnd_951801] using wordTrace_append hprefix tailTrace_951801
  have hstable : (prefixWord ++ tailWord_951801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951801).length < 2 ^ (prefixWord ++ tailWord_951801).sum := by decide
  have hdescent : baseEnd_951801 < baseStart_951801 := by decide
  rcases family_descends (prefixWord ++ tailWord_951801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951805 : List Nat := [1, 4, 1, 1, 1, 5, 1, 2, 3, 3]
def baseStart_951805 : Nat := 118140960795 + 951805 * 2 ^ 59
def prefixEnd_951805 : Nat := 4983230072969 + 3 ^ 40 * 951805 * 2
def baseEnd_951805 : Nat := 325822302901835861506823

theorem tailTrace_951805 : CollatzResearch.WordTrace tailWord_951805 prefixEnd_951805 325822302901835861506823 := by
  unfold tailWord_951805
  simp only [CollatzResearch.WordTrace]
  refine ⟨34715180316780515197416869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23143453544520343464944579 34715180316780515197416869)
  ·
    refine ⟨6509096309396346599515663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34715180316780515197416869 6509096309396346599515663)
    ·
      refine ⟨9763644464094519899273495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6509096309396346599515663 9763644464094519899273495)
      ·
        refine ⟨14645466696141779848910243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9763644464094519899273495 14645466696141779848910243)
        ·
          refine ⟨21968200044212669773365365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14645466696141779848910243 21968200044212669773365365)
          ·
            refine ⟨2059518754144937791253003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21968200044212669773365365 2059518754144937791253003)
            ·
              refine ⟨3089278131217406686879505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2059518754144937791253003 3089278131217406686879505)
              ·
                refine ⟨2316958598413055015159629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3089278131217406686879505 2316958598413055015159629)
                ·
                  refine ⟨868859474404895630684861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2316958598413055015159629 868859474404895630684861)
                  ·
                    refine ⟨325822302901835861506823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 868859474404895630684861 325822302901835861506823)
                    ·
                      rfl

theorem cell22_951805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 3, 3].length) (baseStart_951805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_951805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_951805 prefixEnd_951805 := by exact prefixLift 951805
  have htrace : WordTrace (prefixWord ++ tailWord_951805) baseStart_951805 baseEnd_951805 := by
    simpa [prefixWord, tailWord_951805, baseEnd_951805] using wordTrace_append hprefix tailTrace_951805
  have hstable : (prefixWord ++ tailWord_951805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951805).length < 2 ^ (prefixWord ++ tailWord_951805).sum := by decide
  have hdescent : baseEnd_951805 < baseStart_951805 := by decide
  rcases family_descends (prefixWord ++ tailWord_951805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951863 : List Nat := [1, 1, 3, 1, 2, 4, 2, 2, 6]
def baseStart_951863 : Nat := 118140960795 + 951863 * 2 ^ 59
def prefixEnd_951863 : Nat := 4983230072969 + 3 ^ 40 * 951863 * 2
def baseEnd_951863 : Nat := 108614052495714347852215

theorem tailTrace_951863 : CollatzResearch.WordTrace tailWord_951863 prefixEnd_951863 108614052495714347852215 := by
  unfold tailWord_951863
  simp only [CollatzResearch.WordTrace]
  refine ⟨34717295750570391103028243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23144863833713594068685495 34717295750570391103028243)
  ·
    refine ⟨52075943625855586654542365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34717295750570391103028243 52075943625855586654542365)
    ·
      refine ⟨19528478859695844995453387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52075943625855586654542365 19528478859695844995453387)
      ·
        refine ⟨29292718289543767493180081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19528478859695844995453387 29292718289543767493180081)
        ·
          refine ⟨21969538717157825619885061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29292718289543767493180081 21969538717157825619885061)
          ·
            refine ⟨4119288509467092303728449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21969538717157825619885061 4119288509467092303728449)
            ·
              refine ⟨3089466382100319227796337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4119288509467092303728449 3089466382100319227796337)
              ·
                refine ⟨2317099786575239420847253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3089466382100319227796337 2317099786575239420847253)
                ·
                  refine ⟨108614052495714347852215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2317099786575239420847253 108614052495714347852215)
                  ·
                    rfl

theorem cell22_951863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 6].length) (baseStart_951863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_951863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_951863 prefixEnd_951863 := by exact prefixLift 951863
  have htrace : WordTrace (prefixWord ++ tailWord_951863) baseStart_951863 baseEnd_951863 := by
    simpa [prefixWord, tailWord_951863, baseEnd_951863] using wordTrace_append hprefix tailTrace_951863
  have hstable : (prefixWord ++ tailWord_951863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951863).length < 2 ^ (prefixWord ++ tailWord_951863).sum := by decide
  have hdescent : baseEnd_951863 < baseStart_951863 := by decide
  rcases family_descends (prefixWord ++ tailWord_951863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951865 : List Nat := [1, 2, 1, 5, 1, 2, 1, 4, 1, 4]
def baseStart_951865 : Nat := 118140960795 + 951865 * 2 ^ 59
def prefixEnd_951865 : Nat := 4983230072969 + 3 ^ 40 * 951865 * 2
def baseEnd_951865 : Nat := 325842842128015705006639

theorem tailTrace_951865 : CollatzResearch.WordTrace tailWord_951865 prefixEnd_951865 325842842128015705006639 := by
  unfold tailWord_951865
  simp only [CollatzResearch.WordTrace]
  refine ⟨34717368696563145444601049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23144912464375430296400699 34717368696563145444601049)
  ·
    refine ⟨26038026522422359083450787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34717368696563145444601049 26038026522422359083450787)
    ·
      refine ⟨39057039783633538625176181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26038026522422359083450787 39057039783633538625176181)
      ·
        refine ⟨3661597479715644246110267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39057039783633538625176181 3661597479715644246110267)
        ·
          refine ⟨5492396219573466369165401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3661597479715644246110267 5492396219573466369165401)
          ·
            refine ⟨4119297164680099776874051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5492396219573466369165401 4119297164680099776874051)
            ·
              refine ⟨6178945747020149665311077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4119297164680099776874051 6178945747020149665311077)
              ·
                refine ⟨1158552327566278062245827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6178945747020149665311077 1158552327566278062245827)
                ·
                  refine ⟨1737828491349417093368741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1158552327566278062245827 1737828491349417093368741)
                  ·
                    refine ⟨325842842128015705006639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1737828491349417093368741 325842842128015705006639)
                    ·
                      rfl

theorem cell22_951865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 4, 1, 4].length) (baseStart_951865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_951865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_951865 prefixEnd_951865 := by exact prefixLift 951865
  have htrace : WordTrace (prefixWord ++ tailWord_951865) baseStart_951865 baseEnd_951865 := by
    simpa [prefixWord, tailWord_951865, baseEnd_951865] using wordTrace_append hprefix tailTrace_951865
  have hstable : (prefixWord ++ tailWord_951865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951865).length < 2 ^ (prefixWord ++ tailWord_951865).sum := by decide
  have hdescent : baseEnd_951865 < baseStart_951865 := by decide
  rcases family_descends (prefixWord ++ tailWord_951865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951895 : List Nat := [1, 1, 3, 2, 2, 3, 2, 1, 4, 3]
def baseStart_951895 : Nat := 118140960795 + 951895 * 2 ^ 59
def prefixEnd_951895 : Nat := 4983230072969 + 3 ^ 40 * 951895 * 2
def baseEnd_951895 : Nat := 325853111741105626756547

theorem tailTrace_951895 : CollatzResearch.WordTrace tailWord_951895 prefixEnd_951895 325853111741105626756547 := by
  unfold tailWord_951895
  simp only [CollatzResearch.WordTrace]
  refine ⟨34718462886454460568193139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23145641924302973712128759 34718462886454460568193139)
  ·
    refine ⟨52077694329681690852289709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34718462886454460568193139 52077694329681690852289709)
    ·
      refine ⟨19529135373630634069608641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52077694329681690852289709 19529135373630634069608641)
      ·
        refine ⟨14646851530222975552206481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19529135373630634069608641 14646851530222975552206481)
        ·
          refine ⟨10985138647667231664154861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14646851530222975552206481 10985138647667231664154861)
          ·
            refine ⟨4119426992875211874058073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10985138647667231664154861 4119426992875211874058073)
            ·
              refine ⟨3089570244656408905543555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4119426992875211874058073 3089570244656408905543555)
              ·
                refine ⟨4634355366984613358315333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3089570244656408905543555 4634355366984613358315333)
                ·
                  refine ⟨868941631309615004684125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4634355366984613358315333 868941631309615004684125)
                  ·
                    refine ⟨325853111741105626756547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 868941631309615004684125 325853111741105626756547)
                    ·
                      rfl

theorem cell22_951895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 4, 3].length) (baseStart_951895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_951895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_951895 prefixEnd_951895 := by exact prefixLift 951895
  have htrace : WordTrace (prefixWord ++ tailWord_951895) baseStart_951895 baseEnd_951895 := by
    simpa [prefixWord, tailWord_951895, baseEnd_951895] using wordTrace_append hprefix tailTrace_951895
  have hstable : (prefixWord ++ tailWord_951895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951895).length < 2 ^ (prefixWord ++ tailWord_951895).sum := by decide
  have hdescent : baseEnd_951895 < baseStart_951895 := by decide
  rcases family_descends (prefixWord ++ tailWord_951895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951908 : List Nat := [2, 3, 1, 1, 2, 3, 1, 9]
def baseStart_951908 : Nat := 118140960795 + 951908 * 2 ^ 59
def prefixEnd_951908 : Nat := 4983230072969 + 3 ^ 40 * 951908 * 2
def baseEnd_951908 : Nat := 36206395767419769575723

theorem tailTrace_951908 : CollatzResearch.WordTrace tailWord_951908 prefixEnd_951908 36206395767419769575723 := by
  unfold tailWord_951908
  simp only [CollatzResearch.WordTrace]
  refine ⟨17359468517703681894208189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23145958023604909192277585 17359468517703681894208189)
  ·
    refine ⟨6509800694138880710328071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17359468517703681894208189 6509800694138880710328071)
    ·
      refine ⟨9764701041208321065492107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6509800694138880710328071 9764701041208321065492107)
      ·
        refine ⟨14647051561812481598238161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9764701041208321065492107 14647051561812481598238161)
        ·
          refine ⟨10985288671359361198678621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14647051561812481598238161 10985288671359361198678621)
          ·
            refine ⟨4119483251759760449504483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10985288671359361198678621 4119483251759760449504483)
            ·
              refine ⟨6179224877639640674256725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4119483251759760449504483 6179224877639640674256725)
              ·
                refine ⟨36206395767419769575723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6179224877639640674256725 36206395767419769575723)
                ·
                  rfl

theorem cell22_951908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 9].length) (baseStart_951908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_951908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_951908 prefixEnd_951908 := by exact prefixLift 951908
  have htrace : WordTrace (prefixWord ++ tailWord_951908) baseStart_951908 baseEnd_951908 := by
    simpa [prefixWord, tailWord_951908, baseEnd_951908] using wordTrace_append hprefix tailTrace_951908
  have hstable : (prefixWord ++ tailWord_951908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951908).length < 2 ^ (prefixWord ++ tailWord_951908).sum := by decide
  have hdescent : baseEnd_951908 < baseStart_951908 := by decide
  rcases family_descends (prefixWord ++ tailWord_951908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951925 : List Nat := [1, 3, 4, 2, 1, 1, 2, 8]
def baseStart_951925 : Nat := 118140960795 + 951925 * 2 ^ 59
def prefixEnd_951925 : Nat := 4983230072969 + 3 ^ 40 * 951925 * 2
def baseEnd_951925 : Nat := 36207042372688394278495

theorem tailTrace_951925 : CollatzResearch.WordTrace tailWord_951925 prefixEnd_951925 36207042372688394278495 := by
  unfold tailWord_951925
  simp only [CollatzResearch.WordTrace]
  refine ⟨34719557076345775691785229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23146371384230517127856819 34719557076345775691785229)
  ·
    refine ⟨13019833903629665884419461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34719557076345775691785229 13019833903629665884419461)
    ·
      refine ⟨2441218856930562353328649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13019833903629665884419461 2441218856930562353328649)
      ·
        refine ⟨1830914142697921764996487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2441218856930562353328649 1830914142697921764996487)
        ·
          refine ⟨2746371214046882647494731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1830914142697921764996487 2746371214046882647494731)
          ·
            refine ⟨4119556821070323971242097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2746371214046882647494731 4119556821070323971242097)
            ·
              refine ⟨3089667615802742978431573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4119556821070323971242097 3089667615802742978431573)
              ·
                refine ⟨36207042372688394278495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3089667615802742978431573 36207042372688394278495)
                ·
                  rfl

theorem cell22_951925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 8].length) (baseStart_951925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_951925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_951925 prefixEnd_951925 := by exact prefixLift 951925
  have htrace : WordTrace (prefixWord ++ tailWord_951925) baseStart_951925 baseEnd_951925 := by
    simpa [prefixWord, tailWord_951925, baseEnd_951925] using wordTrace_append hprefix tailTrace_951925
  have hstable : (prefixWord ++ tailWord_951925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951925).length < 2 ^ (prefixWord ++ tailWord_951925).sum := by decide
  have hdescent : baseEnd_951925 < baseStart_951925 := by decide
  rcases family_descends (prefixWord ++ tailWord_951925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951976 : List Nat := [2, 1, 7, 1, 1, 1, 3, 6]
def baseStart_951976 : Nat := 118140960795 + 951976 * 2 ^ 59
def prefixEnd_951976 : Nat := 4983230072969 + 3 ^ 40 * 951976 * 2
def baseEnd_951976 : Nat := 36208982188494268386811

theorem tailTrace_951976 : CollatzResearch.WordTrace tailWord_951976 prefixEnd_951976 36208982188494268386811 := by
  unfold tailWord_951976
  simp only [CollatzResearch.WordTrace]
  refine ⟨17360708599580505700945891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23147611466107340934594521 17360708599580505700945891)
  ·
    refine ⟨26041062899370758551418837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17360708599580505700945891 26041062899370758551418837)
    ·
      refine ⟨610337411704002153548879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 26041062899370758551418837 610337411704002153548879)
      ·
        refine ⟨915506117556003230323319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610337411704002153548879 915506117556003230323319)
        ·
          refine ⟨1373259176334004845484979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 915506117556003230323319 1373259176334004845484979)
          ·
            refine ⟨2059888764501007268227469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1373259176334004845484979 2059888764501007268227469)
            ·
              refine ⟨772458286687877725585301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2059888764501007268227469 772458286687877725585301)
              ·
                refine ⟨36208982188494268386811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 772458286687877725585301 36208982188494268386811)
                ·
                  rfl

theorem cell22_951976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 6].length) (baseStart_951976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_951976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_951976 prefixEnd_951976 := by exact prefixLift 951976
  have htrace : WordTrace (prefixWord ++ tailWord_951976) baseStart_951976 baseEnd_951976 := by
    simpa [prefixWord, tailWord_951976, baseEnd_951976] using wordTrace_append hprefix tailTrace_951976
  have hstable : (prefixWord ++ tailWord_951976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951976).length < 2 ^ (prefixWord ++ tailWord_951976).sum := by decide
  have hdescent : baseEnd_951976 < baseStart_951976 := by decide
  rcases family_descends (prefixWord ++ tailWord_951976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952049 : List Nat := [1, 2, 2, 2, 2, 5, 1, 3, 4]
def baseStart_952049 : Nat := 118140960795 + 952049 * 2 ^ 59
def prefixEnd_952049 : Nat := 4983230072969 + 3 ^ 40 * 952049 * 2
def baseEnd_952049 : Nat := 108635276362766852802025

theorem tailTrace_952049 : CollatzResearch.WordTrace tailWord_952049 prefixEnd_952049 108635276362766852802025 := by
  unfold tailWord_952049
  simp only [CollatzResearch.WordTrace]
  refine ⟨34724079727896544869299201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23149386485264363246199467 34724079727896544869299201)
  ·
    refine ⟨26043059795922408651974401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34724079727896544869299201 26043059795922408651974401)
    ·
      refine ⟨19532294846941806488980801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26043059795922408651974401 19532294846941806488980801)
      ·
        refine ⟨14649221135206354866735601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19532294846941806488980801 14649221135206354866735601)
        ·
          refine ⟨10986915851404766150051701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14649221135206354866735601 10986915851404766150051701)
          ·
            refine ⟨1030023361069196826567347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10986915851404766150051701 1030023361069196826567347)
            ·
              refine ⟨1545035041603795239851021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1030023361069196826567347 1545035041603795239851021)
              ·
                refine ⟨579388140601423214944133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1545035041603795239851021 579388140601423214944133)
                ·
                  refine ⟨108635276362766852802025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 579388140601423214944133 108635276362766852802025)
                  ·
                    rfl

theorem cell22_952049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 3, 4].length) (baseStart_952049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_952049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_952049 prefixEnd_952049 := by exact prefixLift 952049
  have htrace : WordTrace (prefixWord ++ tailWord_952049) baseStart_952049 baseEnd_952049 := by
    simpa [prefixWord, tailWord_952049, baseEnd_952049] using wordTrace_append hprefix tailTrace_952049
  have hstable : (prefixWord ++ tailWord_952049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952049).length < 2 ^ (prefixWord ++ tailWord_952049).sum := by decide
  have hdescent : baseEnd_952049 < baseStart_952049 := by decide
  rcases family_descends (prefixWord ++ tailWord_952049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952066 : List Nat := [3, 4, 1, 1, 1, 1, 5, 2, 4]
def baseStart_952066 : Nat := 118140960795 + 952066 * 2 ^ 59
def prefixEnd_952066 : Nat := 4983230072969 + 3 ^ 40 * 952066 * 2
def baseEnd_952066 : Nat := 108637216178572726910341

theorem tailTrace_952066 : CollatzResearch.WordTrace tailWord_952066 prefixEnd_952066 108637216178572726910341 := by
  unfold tailWord_952066
  simp only [CollatzResearch.WordTrace]
  refine ⟨8681174942208739193167013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23149799845889971181778701 8681174942208739193167013)
  ·
    refine ⟨1627720301664138598718815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8681174942208739193167013 1627720301664138598718815)
    ·
      refine ⟨2441580452496207898078223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1627720301664138598718815 2441580452496207898078223)
      ·
        refine ⟨3662370678744311847117335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2441580452496207898078223 3662370678744311847117335)
        ·
          refine ⟨5493556018116467770676003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3662370678744311847117335 5493556018116467770676003)
          ·
            refine ⟨8240334027174701656014005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5493556018116467770676003 8240334027174701656014005)
            ·
              refine ⟨772531315047628280251313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8240334027174701656014005 772531315047628280251313)
              ·
                refine ⟨579398486285721210188485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 772531315047628280251313 579398486285721210188485)
                ·
                  refine ⟨108637216178572726910341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 579398486285721210188485 108637216178572726910341)
                  ·
                    rfl

theorem cell22_952066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_952066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_952066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_952066 prefixEnd_952066 := by exact prefixLift 952066
  have htrace : WordTrace (prefixWord ++ tailWord_952066) baseStart_952066 baseEnd_952066 := by
    simpa [prefixWord, tailWord_952066, baseEnd_952066] using wordTrace_append hprefix tailTrace_952066
  have hstable : (prefixWord ++ tailWord_952066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952066).length < 2 ^ (prefixWord ++ tailWord_952066).sum := by decide
  have hdescent : baseEnd_952066 < baseStart_952066 := by decide
  rcases family_descends (prefixWord ++ tailWord_952066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952092 : List Nat := [2, 2, 3, 1, 1, 2, 2, 1, 5, 3]
def baseStart_952092 : Nat := 118140960795 + 952092 * 2 ^ 59
def prefixEnd_952092 : Nat := 4983230072969 + 3 ^ 40 * 952092 * 2
def baseEnd_952092 : Nat := 325920548867062779580943

theorem tailTrace_952092 : CollatzResearch.WordTrace tailWord_952092 prefixEnd_952092 325920548867062779580943 := by
  unfold tailWord_952092
  simp only [CollatzResearch.WordTrace]
  refine ⟨17362824033370381606557265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23150432044493842142076353 17362824033370381606557265)
  ·
    refine ⟨13022118025027786204917949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17362824033370381606557265 13022118025027786204917949)
    ·
      refine ⟨4883294259385419826844231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13022118025027786204917949 4883294259385419826844231)
      ·
        refine ⟨7324941389078129740266347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4883294259385419826844231 7324941389078129740266347)
        ·
          refine ⟨10987412083617194610399521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7324941389078129740266347 10987412083617194610399521)
          ·
            refine ⟨8240559062712895957799641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10987412083617194610399521 8240559062712895957799641)
            ·
              refine ⟨6180419297034671968349731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8240559062712895957799641 6180419297034671968349731)
              ·
                refine ⟨9270628945552007952524597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6180419297034671968349731 9270628945552007952524597)
                ·
                  refine ⟨869121463645500745549181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9270628945552007952524597 869121463645500745549181)
                  ·
                    refine ⟨325920548867062779580943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 869121463645500745549181 325920548867062779580943)
                    ·
                      rfl

theorem cell22_952092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_952092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_952092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_952092 prefixEnd_952092 := by exact prefixLift 952092
  have htrace : WordTrace (prefixWord ++ tailWord_952092) baseStart_952092 baseEnd_952092 := by
    simpa [prefixWord, tailWord_952092, baseEnd_952092] using wordTrace_append hprefix tailTrace_952092
  have hstable : (prefixWord ++ tailWord_952092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952092).length < 2 ^ (prefixWord ++ tailWord_952092).sum := by decide
  have hdescent : baseEnd_952092 < baseStart_952092 := by decide
  rcases family_descends (prefixWord ++ tailWord_952092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952122 : List Nat := [3, 1, 1, 1, 5, 1, 1, 4, 5]
def baseStart_952122 : Nat := 118140960795 + 952122 * 2 ^ 59
def prefixEnd_952122 : Nat := 4983230072969 + 3 ^ 40 * 952122 * 2
def baseEnd_952122 : Nat := 108643606160050900443617

theorem tailTrace_952122 : CollatzResearch.WordTrace tailWord_952122 prefixEnd_952122 108643606160050900443617 := by
  unfold tailWord_952122
  simp only [CollatzResearch.WordTrace]
  refine ⟨8681685564158019584176655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23151161504421385557804413 8681685564158019584176655)
  ·
    refine ⟨13022528346237029376264983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8681685564158019584176655 13022528346237029376264983)
    ·
      refine ⟨19533792519355544064397475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13022528346237029376264983 19533792519355544064397475)
      ·
        refine ⟨29300688779033316096596213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19533792519355544064397475 29300688779033316096596213)
        ·
          refine ⟨2746939573034373384055895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29300688779033316096596213 2746939573034373384055895)
          ·
            refine ⟨4120409359551560076083843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2746939573034373384055895 4120409359551560076083843)
            ·
              refine ⟨6180614039327340114125765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4120409359551560076083843 6180614039327340114125765)
              ·
                refine ⟨1158865132373876271398581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6180614039327340114125765 1158865132373876271398581)
                ·
                  refine ⟨108643606160050900443617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1158865132373876271398581 108643606160050900443617)
                  ·
                    rfl

theorem cell22_952122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 4, 5].length) (baseStart_952122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_952122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_952122 prefixEnd_952122 := by exact prefixLift 952122
  have htrace : WordTrace (prefixWord ++ tailWord_952122) baseStart_952122 baseEnd_952122 := by
    simpa [prefixWord, tailWord_952122, baseEnd_952122] using wordTrace_append hprefix tailTrace_952122
  have hstable : (prefixWord ++ tailWord_952122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952122).length < 2 ^ (prefixWord ++ tailWord_952122).sum := by decide
  have hdescent : baseEnd_952122 < baseStart_952122 := by decide
  rcases family_descends (prefixWord ++ tailWord_952122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952334 : List Nat := [4, 1, 1, 2, 2, 1, 1, 4, 1, 5]
def baseStart_952334 : Nat := 118140960795 + 952334 * 2 ^ 59
def prefixEnd_952334 : Nat := 4983230072969 + 3 ^ 40 * 952334 * 2
def baseEnd_952334 : Nat := 326003390412654815030201

theorem tailTrace_952334 : CollatzResearch.WordTrace tailWord_952334 prefixEnd_952334 326003390412654815030201 := by
  unfold tailWord_952334
  simp only [CollatzResearch.WordTrace]
  refine ⟨4341809316483004817928007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23156316354576025695616037 4341809316483004817928007)
  ·
    refine ⟨6512713974724507226892011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4341809316483004817928007 6512713974724507226892011)
    ·
      refine ⟨9769070962086760840338017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6512713974724507226892011 9769070962086760840338017)
      ·
        refine ⟨7326803221565070630253513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9769070962086760840338017 7326803221565070630253513)
        ·
          refine ⟨5495102416173802972690135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7326803221565070630253513 5495102416173802972690135)
          ·
            refine ⟨8242653624260704459035203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5495102416173802972690135 8242653624260704459035203)
            ·
              refine ⟨12363980436391056688552805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8242653624260704459035203 12363980436391056688552805)
              ·
                refine ⟨2318246331823323129103651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12363980436391056688552805 2318246331823323129103651)
                ·
                  refine ⟨3477369497734984693655477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2318246331823323129103651 3477369497734984693655477)
                  ·
                    refine ⟨326003390412654815030201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3477369497734984693655477 326003390412654815030201)
                    ·
                      rfl

theorem cell22_952334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_952334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_952334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_952334 prefixEnd_952334 := by exact prefixLift 952334
  have htrace : WordTrace (prefixWord ++ tailWord_952334) baseStart_952334 baseEnd_952334 := by
    simpa [prefixWord, tailWord_952334, baseEnd_952334] using wordTrace_append hprefix tailTrace_952334
  have hstable : (prefixWord ++ tailWord_952334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952334).length < 2 ^ (prefixWord ++ tailWord_952334).sum := by decide
  have hdescent : baseEnd_952334 < baseStart_952334 := by decide
  rcases family_descends (prefixWord ++ tailWord_952334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952368 : List Nat := [2, 1, 1, 1, 2, 6, 3, 1, 2, 3]
def baseStart_952368 : Nat := 118140960795 + 952368 * 2 ^ 59
def prefixEnd_952368 : Nat := 4983230072969 + 3 ^ 40 * 952368 * 2
def baseEnd_952368 : Nat := 326015029307490059680097

theorem tailTrace_952368 : CollatzResearch.WordTrace tailWord_952368 prefixEnd_952368 326015029307490059680097 := by
  unfold tailWord_952368
  simp only [CollatzResearch.WordTrace]
  refine ⟨17367857306870431175080879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23157143075827241566774505 17367857306870431175080879)
  ·
    refine ⟨26051785960305646762621319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17367857306870431175080879 26051785960305646762621319)
    ·
      refine ⟨39077678940458470143931979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26051785960305646762621319 39077678940458470143931979)
      ·
        refine ⟨58616518410687705215897969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39077678940458470143931979 58616518410687705215897969)
        ·
          refine ⟨43962388808015778911923477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58616518410687705215897969 43962388808015778911923477)
          ·
            refine ⟨2060736975375739636496413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 43962388808015778911923477 2060736975375739636496413)
            ·
              refine ⟨772776365765902363686155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2060736975375739636496413 772776365765902363686155)
              ·
                refine ⟨1159164548648853545529233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 772776365765902363686155 1159164548648853545529233)
                ·
                  refine ⟨869373411486640159146925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1159164548648853545529233 869373411486640159146925)
                  ·
                    refine ⟨326015029307490059680097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 869373411486640159146925 326015029307490059680097)
                    ·
                      rfl

theorem cell22_952368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 1, 2, 3].length) (baseStart_952368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_952368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_952368 prefixEnd_952368 := by exact prefixLift 952368
  have htrace : WordTrace (prefixWord ++ tailWord_952368) baseStart_952368 baseEnd_952368 := by
    simpa [prefixWord, tailWord_952368, baseEnd_952368] using wordTrace_append hprefix tailTrace_952368
  have hstable : (prefixWord ++ tailWord_952368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952368).length < 2 ^ (prefixWord ++ tailWord_952368).sum := by decide
  have hdescent : baseEnd_952368 < baseStart_952368 := by decide
  rcases family_descends (prefixWord ++ tailWord_952368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952409 : List Nat := [1, 2, 1, 2, 2, 1, 4, 4, 5]
def baseStart_952409 : Nat := 118140960795 + 952409 * 2 ^ 59
def prefixEnd_952409 : Nat := 4983230072969 + 3 ^ 40 * 952409 * 2
def baseEnd_952409 : Nat := 108676354815126539801657

theorem tailTrace_952409 : CollatzResearch.WordTrace tailWord_952409 prefixEnd_952409 108676354815126539801657 := by
  unfold tailWord_952409
  simp only [CollatzResearch.WordTrace]
  refine ⟨34737210006592326352404281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23158140004394884234936187 34737210006592326352404281)
  ·
    refine ⟨26052907504944244764303211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34737210006592326352404281 26052907504944244764303211)
    ·
      refine ⟨39079361257416367146454817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26052907504944244764303211 39079361257416367146454817)
      ·
        refine ⟨29309520943062275359841113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39079361257416367146454817 29309520943062275359841113)
        ·
          refine ⟨21982140707296706519880835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29309520943062275359841113 21982140707296706519880835)
          ·
            refine ⟨32973211060945059779821253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21982140707296706519880835 32973211060945059779821253)
            ·
              refine ⟨6182477073927198708716485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32973211060945059779821253 6182477073927198708716485)
              ·
                refine ⟨1159214451361349757884341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6182477073927198708716485 1159214451361349757884341)
                ·
                  refine ⟨108676354815126539801657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1159214451361349757884341 108676354815126539801657)
                  ·
                    rfl

theorem cell22_952409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 4, 5].length) (baseStart_952409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_952409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_952409 prefixEnd_952409 := by exact prefixLift 952409
  have htrace : WordTrace (prefixWord ++ tailWord_952409) baseStart_952409 baseEnd_952409 := by
    simpa [prefixWord, tailWord_952409, baseEnd_952409] using wordTrace_append hprefix tailTrace_952409
  have hstable : (prefixWord ++ tailWord_952409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952409).length < 2 ^ (prefixWord ++ tailWord_952409).sum := by decide
  have hdescent : baseEnd_952409 < baseStart_952409 := by decide
  rcases family_descends (prefixWord ++ tailWord_952409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952469 : List Nat := [1, 3, 2, 1, 1, 1, 3, 2, 3, 5]
def baseStart_952469 : Nat := 118140960795 + 952469 * 2 ^ 59
def prefixEnd_952469 : Nat := 4983230072969 + 3 ^ 40 * 952469 * 2
def baseEnd_952469 : Nat := 326049603671559462904787

theorem tailTrace_952469 : CollatzResearch.WordTrace tailWord_952469 prefixEnd_952469 326049603671559462904787 := by
  unfold tailWord_952469
  simp only [CollatzResearch.WordTrace]
  refine ⟨34739398386374956599588461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23159598924249971066392307 34739398386374956599588461)
  ·
    refine ⟨13027274394890608724845673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34739398386374956599588461 13027274394890608724845673)
    ·
      refine ⟨9770455796167956543634255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13027274394890608724845673 9770455796167956543634255)
      ·
        refine ⟨14655683694251934815451383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9770455796167956543634255 14655683694251934815451383)
        ·
          refine ⟨21983525541377902223177075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14655683694251934815451383 21983525541377902223177075)
          ·
            refine ⟨32975288312066853334765613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21983525541377902223177075 32975288312066853334765613)
            ·
              refine ⟨12365733117025070000537105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32975288312066853334765613 12365733117025070000537105)
              ·
                refine ⟨9274299837768802500402829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12365733117025070000537105 9274299837768802500402829)
                ·
                  refine ⟨3477862439163300937651061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9274299837768802500402829 3477862439163300937651061)
                  ·
                    refine ⟨326049603671559462904787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3477862439163300937651061 326049603671559462904787)
                    ·
                      rfl

theorem cell22_952469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_952469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_952469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_952469 prefixEnd_952469 := by exact prefixLift 952469
  have htrace : WordTrace (prefixWord ++ tailWord_952469) baseStart_952469 baseEnd_952469 := by
    simpa [prefixWord, tailWord_952469, baseEnd_952469] using wordTrace_append hprefix tailTrace_952469
  have hstable : (prefixWord ++ tailWord_952469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952469).length < 2 ^ (prefixWord ++ tailWord_952469).sum := by decide
  have hdescent : baseEnd_952469 < baseStart_952469 := by decide
  rcases family_descends (prefixWord ++ tailWord_952469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952516 : List Nat := [2, 3, 3, 1, 2, 2, 9]
def baseStart_952516 : Nat := 118140960795 + 952516 * 2 ^ 59
def prefixEnd_952516 : Nat := 4983230072969 + 3 ^ 40 * 952516 * 2
def baseEnd_952516 : Nat := 12076507138224703962209

theorem tailTrace_952516 : CollatzResearch.WordTrace tailWord_952516 prefixEnd_952516 12076507138224703962209 := by
  unfold tailWord_952516
  simp only [CollatzResearch.WordTrace]
  refine ⟨17370556308602341813274701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23160741744803122417699601 17370556308602341813274701)
  ·
    refine ⟨6513958615725878179978013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17370556308602341813274701 6513958615725878179978013)
    ·
      refine ⟨2442734480897204317491755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6513958615725878179978013 2442734480897204317491755)
      ·
        refine ⟨3664101721345806476237633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2442734480897204317491755 3664101721345806476237633)
        ·
          refine ⟨2748076291009354857178225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3664101721345806476237633 2748076291009354857178225)
          ·
            refine ⟨2061057218257016142883669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2748076291009354857178225 2061057218257016142883669)
            ·
              refine ⟨12076507138224703962209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2061057218257016142883669 12076507138224703962209)
              ·
                rfl

theorem cell22_952516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 9].length) (baseStart_952516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_952516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_952516 prefixEnd_952516 := by exact prefixLift 952516
  have htrace : WordTrace (prefixWord ++ tailWord_952516) baseStart_952516 baseEnd_952516 := by
    simpa [prefixWord, tailWord_952516, baseEnd_952516] using wordTrace_append hprefix tailTrace_952516
  have hstable : (prefixWord ++ tailWord_952516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952516).length < 2 ^ (prefixWord ++ tailWord_952516).sum := by decide
  have hdescent : baseEnd_952516 < baseStart_952516 := by decide
  rcases family_descends (prefixWord ++ tailWord_952516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952529 : List Nat := [1, 2, 2, 1, 2, 2, 2, 1, 1, 8]
def baseStart_952529 : Nat := 118140960795 + 952529 * 2 ^ 59
def prefixEnd_952529 : Nat := 4983230072969 + 3 ^ 40 * 952529 * 2
def baseEnd_952529 : Nat := 326070142897739306404603

theorem tailTrace_952529 : CollatzResearch.WordTrace tailWord_952529 prefixEnd_952529 326070142897739306404603 := by
  unfold tailWord_952529
  simp only [CollatzResearch.WordTrace]
  refine ⟨34741586766157586846772641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23161057844105057897848427 34741586766157586846772641)
  ·
    refine ⟨26056190074618190135079481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34741586766157586846772641 26056190074618190135079481)
    ·
      refine ⟨19542142555963642601309611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26056190074618190135079481 19542142555963642601309611)
      ·
        refine ⟨29313213833945463901964417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19542142555963642601309611 29313213833945463901964417)
        ·
          refine ⟨21984910375459097926473313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29313213833945463901964417 21984910375459097926473313)
          ·
            refine ⟨16488682781594323444854985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21984910375459097926473313 16488682781594323444854985)
            ·
              refine ⟨12366512086195742583641239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16488682781594323444854985 12366512086195742583641239)
              ·
                refine ⟨18549768129293613875461859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12366512086195742583641239 18549768129293613875461859)
                ·
                  refine ⟨27824652193940420813192789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18549768129293613875461859 27824652193940420813192789)
                  ·
                    refine ⟨326070142897739306404603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 27824652193940420813192789 326070142897739306404603)
                    ·
                      rfl

theorem cell22_952529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 8].length) (baseStart_952529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_952529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_952529 prefixEnd_952529 := by exact prefixLift 952529
  have htrace : WordTrace (prefixWord ++ tailWord_952529) baseStart_952529 baseEnd_952529 := by
    simpa [prefixWord, tailWord_952529, baseEnd_952529] using wordTrace_append hprefix tailTrace_952529
  have hstable : (prefixWord ++ tailWord_952529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952529).length < 2 ^ (prefixWord ++ tailWord_952529).sum := by decide
  have hdescent : baseEnd_952529 < baseStart_952529 := by decide
  rcases family_descends (prefixWord ++ tailWord_952529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952578 : List Nat := [3, 4, 1, 1, 2, 1, 2, 1, 7]
def baseStart_952578 : Nat := 118140960795 + 952578 * 2 ^ 59
def prefixEnd_952578 : Nat := 4983230072969 + 3 ^ 40 * 952578 * 2
def baseEnd_952578 : Nat := 108695638866373170643151

theorem tailTrace_952578 : CollatzResearch.WordTrace tailWord_952578 prefixEnd_952578 108695638866373170643151 := by
  unfold tailWord_952578
  simp only [CollatzResearch.WordTrace]
  refine ⟨8685843485745017053826597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23162249295320045476870925 8685843485745017053826597)
  ·
    refine ⟨1628595653577190697592487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8685843485745017053826597 1628595653577190697592487)
    ·
      refine ⟨2442893480365786046388731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1628595653577190697592487 2442893480365786046388731)
      ·
        refine ⟨3664340220548679069583097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2442893480365786046388731 3664340220548679069583097)
        ·
          refine ⟨2748255165411509302187323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3664340220548679069583097 2748255165411509302187323)
          ·
            refine ⟨4122382748117263953280985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2748255165411509302187323 4122382748117263953280985)
            ·
              refine ⟨3091787061087947964960739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4122382748117263953280985 3091787061087947964960739)
              ·
                refine ⟨4637680591631921947441109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3091787061087947964960739 4637680591631921947441109)
                ·
                  refine ⟨108695638866373170643151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4637680591631921947441109 108695638866373170643151)
                  ·
                    rfl

theorem cell22_952578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_952578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_952578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_952578 prefixEnd_952578 := by exact prefixLift 952578
  have htrace : WordTrace (prefixWord ++ tailWord_952578) baseStart_952578 baseEnd_952578 := by
    simpa [prefixWord, tailWord_952578, baseEnd_952578] using wordTrace_append hprefix tailTrace_952578
  have hstable : (prefixWord ++ tailWord_952578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952578).length < 2 ^ (prefixWord ++ tailWord_952578).sum := by decide
  have hdescent : baseEnd_952578 < baseStart_952578 := by decide
  rcases family_descends (prefixWord ++ tailWord_952578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952608 : List Nat := [2, 1, 1, 5, 2, 2, 1, 1, 3, 4]
def baseStart_952608 : Nat := 118140960795 + 952608 * 2 ^ 59
def prefixEnd_952608 : Nat := 4983230072969 + 3 ^ 40 * 952608 * 2
def baseEnd_952608 : Nat := 326097186212209433679361

theorem tailTrace_952608 : CollatzResearch.WordTrace tailWord_952608 prefixEnd_952608 326097186212209433679361 := by
  unfold tailWord_952608
  simp only [CollatzResearch.WordTrace]
  refine ⟨17372234066435691669449239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23162978755247588892598985 17372234066435691669449239)
  ·
    refine ⟨26058351099653537504173859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17372234066435691669449239 26058351099653537504173859)
    ·
      refine ⟨39087526649480306256260789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26058351099653537504173859 39087526649480306256260789)
      ·
        refine ⟨3664455623388778711524449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39087526649480306256260789 3664455623388778711524449)
        ·
          refine ⟨2748341717541584033643337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3664455623388778711524449 2748341717541584033643337)
          ·
            refine ⟨2061256288156188025232503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2748341717541584033643337 2061256288156188025232503)
            ·
              refine ⟨3091884432234282037848755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2061256288156188025232503 3091884432234282037848755)
              ·
                refine ⟨4637826648351423056773133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3091884432234282037848755 4637826648351423056773133)
                ·
                  refine ⟨1739184993131783646289925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4637826648351423056773133 1739184993131783646289925)
                  ·
                    refine ⟨326097186212209433679361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1739184993131783646289925 326097186212209433679361)
                    ·
                      rfl

theorem cell22_952608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 3, 4].length) (baseStart_952608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_952608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_952608 prefixEnd_952608 := by exact prefixLift 952608
  have htrace : WordTrace (prefixWord ++ tailWord_952608) baseStart_952608 baseEnd_952608 := by
    simpa [prefixWord, tailWord_952608, baseEnd_952608] using wordTrace_append hprefix tailTrace_952608
  have hstable : (prefixWord ++ tailWord_952608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952608).length < 2 ^ (prefixWord ++ tailWord_952608).sum := by decide
  have hdescent : baseEnd_952608 < baseStart_952608 := by decide
  rcases family_descends (prefixWord ++ tailWord_952608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952706 : List Nat := [3, 4, 2, 1, 2, 1, 3, 1, 2, 3]
def baseStart_952706 : Nat := 118140960795 + 952706 * 2 ^ 59
def prefixEnd_952706 : Nat := 4983230072969 + 3 ^ 40 * 952706 * 2
def baseEnd_952706 : Nat := 326130733614969844729061

theorem tailTrace_952706 : CollatzResearch.WordTrace tailWord_952706 prefixEnd_952706 326130733614969844729061 := by
  unfold tailWord_952706
  simp only [CollatzResearch.WordTrace]
  refine ⟨8687010621629086518991493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23165361657677564050643981 8687010621629086518991493)
  ·
    refine ⟨1628814491555453722310905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8687010621629086518991493 1628814491555453722310905)
    ·
      refine ⟨1221610868666590291733179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1628814491555453722310905 1221610868666590291733179)
      ·
        refine ⟨1832416302999885437599769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1221610868666590291733179 1832416302999885437599769)
        ·
          refine ⟨1374312227249914078199827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1832416302999885437599769 1374312227249914078199827)
          ·
            refine ⟨2061468340874871117299741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1374312227249914078199827 2061468340874871117299741)
            ·
              refine ⟨773050627828076668987403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2061468340874871117299741 773050627828076668987403)
              ·
                refine ⟨1159575941742115003481105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 773050627828076668987403 1159575941742115003481105)
                ·
                  refine ⟨869681956306586252610829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1159575941742115003481105 869681956306586252610829)
                  ·
                    refine ⟨326130733614969844729061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 869681956306586252610829 326130733614969844729061)
                    ·
                      rfl

theorem cell22_952706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_952706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_952706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_952706 prefixEnd_952706 := by exact prefixLift 952706
  have htrace : WordTrace (prefixWord ++ tailWord_952706) baseStart_952706 baseEnd_952706 := by
    simpa [prefixWord, tailWord_952706, baseEnd_952706] using wordTrace_append hprefix tailTrace_952706
  have hstable : (prefixWord ++ tailWord_952706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952706).length < 2 ^ (prefixWord ++ tailWord_952706).sum := by decide
  have hdescent : baseEnd_952706 < baseStart_952706 := by decide
  rcases family_descends (prefixWord ++ tailWord_952706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952803 : List Nat := [1, 1, 1, 6, 3, 10]
def baseStart_952803 : Nat := 118140960795 + 952803 * 2 ^ 59
def prefixEnd_952803 : Nat := 4983230072969 + 3 ^ 40 * 952803 * 2
def baseEnd_952803 : Nat := 4026715292559184259923

theorem tailTrace_952803 : CollatzResearch.WordTrace tailWord_952803 prefixEnd_952803 4026715292559184259923 := by
  unfold tailWord_952803
  simp only [CollatzResearch.WordTrace]
  refine ⟨34751580367164931642247063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23167720244776621094831375 34751580367164931642247063)
  ·
    refine ⟨52127370550747397463370595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34751580367164931642247063 52127370550747397463370595)
    ·
      refine ⟨78191055826121096195055893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52127370550747397463370595 78191055826121096195055893)
      ·
        refine ⟨3665205741849426384143245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 78191055826121096195055893 3665205741849426384143245)
        ·
          refine ⟨1374452153193534894053717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3665205741849426384143245 1374452153193534894053717)
          ·
            refine ⟨4026715292559184259923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1374452153193534894053717 4026715292559184259923)
            ·
              rfl

theorem cell22_952803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 10].length) (baseStart_952803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_952803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_952803 prefixEnd_952803 := by exact prefixLift 952803
  have htrace : WordTrace (prefixWord ++ tailWord_952803) baseStart_952803 baseEnd_952803 := by
    simpa [prefixWord, tailWord_952803, baseEnd_952803] using wordTrace_append hprefix tailTrace_952803
  have hstable : (prefixWord ++ tailWord_952803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952803).length < 2 ^ (prefixWord ++ tailWord_952803).sum := by decide
  have hdescent : baseEnd_952803 < baseStart_952803 := by decide
  rcases family_descends (prefixWord ++ tailWord_952803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952807 : List Nat := [1, 1, 5, 2, 1, 1, 4, 2, 2, 3]
def baseStart_952807 : Nat := 118140960795 + 952807 * 2 ^ 59
def prefixEnd_952807 : Nat := 4983230072969 + 3 ^ 40 * 952807 * 2
def baseEnd_952807 : Nat := 326165307979039247953751

theorem tailTrace_952807 : CollatzResearch.WordTrace tailWord_952807 prefixEnd_952807 326165307979039247953751 := by
  unfold tailWord_952807
  simp only [CollatzResearch.WordTrace]
  refine ⟨34751726259150440325392675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23167817506100293550261783 34751726259150440325392675)
  ·
    refine ⟨52127589388725660488089013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34751726259150440325392675 52127589388725660488089013)
    ·
      refine ⟨4886961505193030670758345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52127589388725660488089013 4886961505193030670758345)
      ·
        refine ⟨3665221128894773003068759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4886961505193030670758345 3665221128894773003068759)
        ·
          refine ⟨5497831693342159504603139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3665221128894773003068759 5497831693342159504603139)
          ·
            refine ⟨8246747540013239256904709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5497831693342159504603139 8246747540013239256904709)
            ·
              refine ⟨1546265163752482360669633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8246747540013239256904709 1546265163752482360669633)
              ·
                refine ⟨1159698872814361770502225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1546265163752482360669633 1159698872814361770502225)
                ·
                  refine ⟨869774154610771327876669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1159698872814361770502225 869774154610771327876669)
                  ·
                    refine ⟨326165307979039247953751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 869774154610771327876669 326165307979039247953751)
                    ·
                      rfl

theorem cell22_952807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_952807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_952807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_952807 prefixEnd_952807 := by exact prefixLift 952807
  have htrace : WordTrace (prefixWord ++ tailWord_952807) baseStart_952807 baseEnd_952807 := by
    simpa [prefixWord, tailWord_952807, baseEnd_952807] using wordTrace_append hprefix tailTrace_952807
  have hstable : (prefixWord ++ tailWord_952807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952807).length < 2 ^ (prefixWord ++ tailWord_952807).sum := by decide
  have hdescent : baseEnd_952807 < baseStart_952807 := by decide
  rcases family_descends (prefixWord ++ tailWord_952807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952835 : List Nat := [1, 1, 1, 3, 2, 1, 5, 2, 3, 3]
def baseStart_952835 : Nat := 118140960795 + 952835 * 2 ^ 59
def prefixEnd_952835 : Nat := 4983230072969 + 3 ^ 40 * 952835 * 2
def baseEnd_952835 : Nat := 326174892951256508253665

theorem tailTrace_952835 : CollatzResearch.WordTrace tailWord_952835 prefixEnd_952835 326174892951256508253665 := by
  unfold tailWord_952835
  simp only [CollatzResearch.WordTrace]
  refine ⟨34752747503049001107411959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23168498335366000738274639 34752747503049001107411959)
  ·
    refine ⟨52129121254573501661117939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34752747503049001107411959 52129121254573501661117939)
    ·
      refine ⟨78193681881860252491676909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52129121254573501661117939 78193681881860252491676909)
      ·
        refine ⟨29322630705697594684378841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78193681881860252491676909 29322630705697594684378841)
        ·
          refine ⟨21991973029273196013284131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29322630705697594684378841 21991973029273196013284131)
          ·
            refine ⟨32987959543909794019926197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21991973029273196013284131 32987959543909794019926197)
            ·
              refine ⟨3092621207241543189368081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32987959543909794019926197 3092621207241543189368081)
              ·
                refine ⟨2319465905431157392026061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3092621207241543189368081 2319465905431157392026061)
                ·
                  refine ⟨869799714536684022009773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2319465905431157392026061 869799714536684022009773)
                  ·
                    refine ⟨326174892951256508253665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 869799714536684022009773 326174892951256508253665)
                    ·
                      rfl

theorem cell22_952835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 3, 3].length) (baseStart_952835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_952835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_952835 prefixEnd_952835 := by exact prefixLift 952835
  have htrace : WordTrace (prefixWord ++ tailWord_952835) baseStart_952835 baseEnd_952835 := by
    simpa [prefixWord, tailWord_952835, baseEnd_952835] using wordTrace_append hprefix tailTrace_952835
  have hstable : (prefixWord ++ tailWord_952835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952835).length < 2 ^ (prefixWord ++ tailWord_952835).sum := by decide
  have hdescent : baseEnd_952835 < baseStart_952835 := by decide
  rcases family_descends (prefixWord ++ tailWord_952835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952839 : List Nat := [1, 1, 4, 3, 4, 1, 1, 1, 2, 4]
def baseStart_952839 : Nat := 118140960795 + 952839 * 2 ^ 59
def prefixEnd_952839 : Nat := 4983230072969 + 3 ^ 40 * 952839 * 2
def baseEnd_952839 : Nat := 326176262233001831153653

theorem tailTrace_952839 : CollatzResearch.WordTrace tailWord_952839 prefixEnd_952839 326176262233001831153653 := by
  unfold tailWord_952839
  simp only [CollatzResearch.WordTrace]
  refine ⟨34752893395034509790557571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23168595596689673193705047 34752893395034509790557571)
  ·
    refine ⟨52129340092551764685836357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34752893395034509790557571 52129340092551764685836357)
    ·
      refine ⟨9774251267353455878594317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52129340092551764685836357 9774251267353455878594317)
      ·
        refine ⟨3665344225257545954472869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9774251267353455878594317 3665344225257545954472869)
        ·
          refine ⟨687252042235789866463663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3665344225257545954472869 687252042235789866463663)
          ·
            refine ⟨1030878063353684799695495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 687252042235789866463663 1030878063353684799695495)
            ·
              refine ⟨1546317095030527199543243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1030878063353684799695495 1546317095030527199543243)
              ·
                refine ⟨2319475642545790799314865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1546317095030527199543243 2319475642545790799314865)
                ·
                  refine ⟨1739606731909343099486149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2319475642545790799314865 1739606731909343099486149)
                  ·
                    refine ⟨326176262233001831153653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1739606731909343099486149 326176262233001831153653)
                    ·
                      rfl

theorem cell22_952839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 2, 4].length) (baseStart_952839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_952839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_952839 prefixEnd_952839 := by exact prefixLift 952839
  have htrace : WordTrace (prefixWord ++ tailWord_952839) baseStart_952839 baseEnd_952839 := by
    simpa [prefixWord, tailWord_952839, baseEnd_952839] using wordTrace_append hprefix tailTrace_952839
  have hstable : (prefixWord ++ tailWord_952839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952839).length < 2 ^ (prefixWord ++ tailWord_952839).sum := by decide
  have hdescent : baseEnd_952839 < baseStart_952839 := by decide
  rcases family_descends (prefixWord ++ tailWord_952839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952946 : List Nat := [3, 2, 1, 2, 5, 1, 1, 2, 1, 4]
def baseStart_952946 : Nat := 118140960795 + 952946 * 2 ^ 59
def prefixEnd_952946 : Nat := 4983230072969 + 3 ^ 40 * 952946 * 2
def baseEnd_952946 : Nat := 326212890519689218728325

theorem tailTrace_952946 : CollatzResearch.WordTrace tailWord_952946 prefixEnd_952946 326212890519689218728325 := by
  unfold tailWord_952946
  simp only [CollatzResearch.WordTrace]
  refine ⟨8689199001411716766175673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23171197337097911376468461 8689199001411716766175673)
  ·
    refine ⟨6516899251058787574631755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8689199001411716766175673 6516899251058787574631755)
    ·
      refine ⟨9775348876588181361947633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6516899251058787574631755 9775348876588181361947633)
      ·
        refine ⟨7331511657441136021460725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9775348876588181361947633 7331511657441136021460725)
        ·
          refine ⟨687329217885106502011943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7331511657441136021460725 687329217885106502011943)
          ·
            refine ⟨1030993826827659753017915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 687329217885106502011943 1030993826827659753017915)
            ·
              refine ⟨1546490740241489629526873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1030993826827659753017915 1546490740241489629526873)
              ·
                refine ⟨1159868055181117222145155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1546490740241489629526873 1159868055181117222145155)
                ·
                  refine ⟨1739802082771675833217733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1159868055181117222145155 1739802082771675833217733)
                  ·
                    refine ⟨326212890519689218728325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1739802082771675833217733 326212890519689218728325)
                    ·
                      rfl

theorem cell22_952946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 2, 1, 4].length) (baseStart_952946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_952946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_952946 prefixEnd_952946 := by exact prefixLift 952946
  have htrace : WordTrace (prefixWord ++ tailWord_952946) baseStart_952946 baseEnd_952946 := by
    simpa [prefixWord, tailWord_952946, baseEnd_952946] using wordTrace_append hprefix tailTrace_952946
  have hstable : (prefixWord ++ tailWord_952946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952946).length < 2 ^ (prefixWord ++ tailWord_952946).sum := by decide
  have hdescent : baseEnd_952946 < baseStart_952946 := by decide
  rcases family_descends (prefixWord ++ tailWord_952946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953021 : List Nat := [1, 4, 1, 2, 1, 4, 2, 3, 1, 3]
def baseStart_953021 : Nat := 118140960795 + 953021 * 2 ^ 59
def prefixEnd_953021 : Nat := 4983230072969 + 3 ^ 40 * 953021 * 2
def baseEnd_953021 : Nat := 326238564552414023103095

theorem tailTrace_953021 : CollatzResearch.WordTrace tailWord_953021 prefixEnd_953021 326238564552414023103095 := by
  unfold tailWord_953021
  simp only [CollatzResearch.WordTrace]
  refine ⟨34759531480375154873682917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23173020986916769915788611 34759531480375154873682917)
  ·
    refine ⟨6517412152570341538815547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34759531480375154873682917 6517412152570341538815547)
    ·
      refine ⟨9776118228855512308223321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6517412152570341538815547 9776118228855512308223321)
      ·
        refine ⟨7332088671641634231167491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9776118228855512308223321 7332088671641634231167491)
        ·
          refine ⟨10998133007462451346751237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7332088671641634231167491 10998133007462451346751237)
          ·
            refine ⟨2062149938899209627515857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10998133007462451346751237 2062149938899209627515857)
            ·
              refine ⟨1546612454174407220636893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2062149938899209627515857 1546612454174407220636893)
              ·
                refine ⟨579979670315402707738835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1546612454174407220636893 579979670315402707738835)
                ·
                  refine ⟨869969505473104061608253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 579979670315402707738835 869969505473104061608253)
                  ·
                    refine ⟨326238564552414023103095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 869969505473104061608253 326238564552414023103095)
                    ·
                      rfl

theorem cell22_953021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 3, 1, 3].length) (baseStart_953021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_953021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_953021 prefixEnd_953021 := by exact prefixLift 953021
  have htrace : WordTrace (prefixWord ++ tailWord_953021) baseStart_953021 baseEnd_953021 := by
    simpa [prefixWord, tailWord_953021, baseEnd_953021] using wordTrace_append hprefix tailTrace_953021
  have hstable : (prefixWord ++ tailWord_953021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953021).length < 2 ^ (prefixWord ++ tailWord_953021).sum := by decide
  have hdescent : baseEnd_953021 < baseStart_953021 := by decide
  rcases family_descends (prefixWord ++ tailWord_953021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953034 : List Nat := [3, 1, 2, 1, 4, 3, 1, 2, 5]
def baseStart_953034 : Nat := 118140960795 + 953034 * 2 ^ 59
def prefixEnd_953034 : Nat := 4983230072969 + 3 ^ 40 * 953034 * 2
def baseEnd_953034 : Nat := 108747671572695440842685

theorem tailTrace_953034 : CollatzResearch.WordTrace tailWord_953034 prefixEnd_953034 108747671572695440842685 := by
  unfold tailWord_953034
  simp only [CollatzResearch.WordTrace]
  refine ⟨8690001407332014523476539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23173337086218705395937437 8690001407332014523476539)
  ·
    refine ⟨13035002110998021785214809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8690001407332014523476539 13035002110998021785214809)
    ·
      refine ⟨9776251583248516338911107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13035002110998021785214809 9776251583248516338911107)
      ·
        refine ⟨14664377374872774508366661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9776251583248516338911107 14664377374872774508366661)
        ·
          refine ⟨2749570757788645220318749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14664377374872774508366661 2749570757788645220318749)
          ·
            refine ⟨1031089034170741957619531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2749570757788645220318749 1031089034170741957619531)
            ·
              refine ⟨1546633551256112936429297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1031089034170741957619531 1546633551256112936429297)
              ·
                refine ⟨1159975163442084702321973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1546633551256112936429297 1159975163442084702321973)
                ·
                  refine ⟨108747671572695440842685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1159975163442084702321973 108747671572695440842685)
                  ·
                    rfl

theorem cell22_953034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 2, 5].length) (baseStart_953034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_953034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_953034 prefixEnd_953034 := by exact prefixLift 953034
  have htrace : WordTrace (prefixWord ++ tailWord_953034) baseStart_953034 baseEnd_953034 := by
    simpa [prefixWord, tailWord_953034, baseEnd_953034] using wordTrace_append hprefix tailTrace_953034
  have hstable : (prefixWord ++ tailWord_953034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953034).length < 2 ^ (prefixWord ++ tailWord_953034).sum := by decide
  have hdescent : baseEnd_953034 < baseStart_953034 := by decide
  rcases family_descends (prefixWord ++ tailWord_953034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953096 : List Nat := [2, 1, 3, 2, 2, 3, 3, 2, 4]
def baseStart_953096 : Nat := 118140960795 + 953096 * 2 ^ 59
def prefixEnd_953096 : Nat := 4983230072969 + 3 ^ 40 * 953096 * 2
def baseEnd_953096 : Nat := 108754746195046275825955

theorem tailTrace_953096 : CollatzResearch.WordTrace tailWord_953096 prefixEnd_953096 108754746195046275825955 := by
  unfold tailWord_953096
  simp only [CollatzResearch.WordTrace]
  refine ⟨17381133477551721341331571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23174844636735628455108761 17381133477551721341331571)
  ·
    refine ⟨26071700216327582011997357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17381133477551721341331571 26071700216327582011997357)
    ·
      refine ⟨9776887581122843254499009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26071700216327582011997357 9776887581122843254499009)
      ·
        refine ⟨7332665685842132440874257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9776887581122843254499009 7332665685842132440874257)
        ·
          refine ⟨5499499264381599330655693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7332665685842132440874257 5499499264381599330655693)
          ·
            refine ⟨2062312224143099748995885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5499499264381599330655693 2062312224143099748995885)
            ·
              refine ⟨773367084053662405873457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2062312224143099748995885 773367084053662405873457)
              ·
                refine ⟨580025313040246804405093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 773367084053662405873457 580025313040246804405093)
                ·
                  refine ⟨108754746195046275825955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 580025313040246804405093 108754746195046275825955)
                  ·
                    rfl

theorem cell22_953096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 2, 4].length) (baseStart_953096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_953096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_953096 prefixEnd_953096 := by exact prefixLift 953096
  have htrace : WordTrace (prefixWord ++ tailWord_953096) baseStart_953096 baseEnd_953096 := by
    simpa [prefixWord, tailWord_953096, baseEnd_953096] using wordTrace_append hprefix tailTrace_953096
  have hstable : (prefixWord ++ tailWord_953096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953096).length < 2 ^ (prefixWord ++ tailWord_953096).sum := by decide
  have hdescent : baseEnd_953096 < baseStart_953096 := by decide
  rcases family_descends (prefixWord ++ tailWord_953096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953111 : List Nat := [1, 1, 3, 4, 3, 1, 1, 3, 2, 3]
def baseStart_953111 : Nat := 118140960795 + 953111 * 2 ^ 59
def prefixEnd_953111 : Nat := 4983230072969 + 3 ^ 40 * 953111 * 2
def baseEnd_953111 : Nat := 326269373391683788352819

theorem tailTrace_953111 : CollatzResearch.WordTrace tailWord_953111 prefixEnd_953111 326269373391683788352819 := by
  unfold tailWord_953111
  simp only [CollatzResearch.WordTrace]
  refine ⟨34762814050049100244459187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23175209366699400162972791 34762814050049100244459187)
  ·
    refine ⟨52144221075073650366688781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34762814050049100244459187 52144221075073650366688781)
    ·
      refine ⟨19554082903152618887508293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52144221075073650366688781 19554082903152618887508293)
      ·
        refine ⟨3666390544341116041407805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19554082903152618887508293 3666390544341116041407805)
        ·
          refine ⟨1374896454127918515527927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3666390544341116041407805 1374896454127918515527927)
          ·
            refine ⟨2062344681191877773291891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1374896454127918515527927 2062344681191877773291891)
            ·
              refine ⟨3093517021787816659937837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2062344681191877773291891 3093517021787816659937837)
              ·
                refine ⟨1160068883170431247476689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3093517021787816659937837 1160068883170431247476689)
                ·
                  refine ⟨870051662377823435607517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1160068883170431247476689 870051662377823435607517)
                  ·
                    refine ⟨326269373391683788352819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 870051662377823435607517 326269373391683788352819)
                    ·
                      rfl

theorem cell22_953111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 3, 2, 3].length) (baseStart_953111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_953111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_953111 prefixEnd_953111 := by exact prefixLift 953111
  have htrace : WordTrace (prefixWord ++ tailWord_953111) baseStart_953111 baseEnd_953111 := by
    simpa [prefixWord, tailWord_953111, baseEnd_953111] using wordTrace_append hprefix tailTrace_953111
  have hstable : (prefixWord ++ tailWord_953111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953111).length < 2 ^ (prefixWord ++ tailWord_953111).sum := by decide
  have hdescent : baseEnd_953111 < baseStart_953111 := by decide
  rcases family_descends (prefixWord ++ tailWord_953111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953158 : List Nat := [6, 1, 1, 2, 2, 2, 1, 7]
def baseStart_953158 : Nat := 118140960795 + 953158 * 2 ^ 59
def prefixEnd_953158 : Nat := 4983230072969 + 3 ^ 40 * 953158 * 2
def baseEnd_953158 : Nat := 36253940272465703603075

theorem tailTrace_953158 : CollatzResearch.WordTrace tailWord_953158 prefixEnd_953158 36253940272465703603075 := by
  unfold tailWord_953158
  simp only [CollatzResearch.WordTrace]
  refine ⟨1086391508777463352231879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23176352187252551514280085 1086391508777463352231879)
  ·
    refine ⟨1629587263166195028347819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1086391508777463352231879 1629587263166195028347819)
    ·
      refine ⟨2444380894749292542521729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1629587263166195028347819 2444380894749292542521729)
      ·
        refine ⟨1833285671061969406891297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2444380894749292542521729 1833285671061969406891297)
        ·
          refine ⟨1374964253296477055168473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1833285671061969406891297 1374964253296477055168473)
          ·
            refine ⟨1031223189972357791376355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1374964253296477055168473 1031223189972357791376355)
            ·
              refine ⟨1546834784958536687064533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1031223189972357791376355 1546834784958536687064533)
              ·
                refine ⟨36253940272465703603075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1546834784958536687064533 36253940272465703603075)
                ·
                  rfl

theorem cell22_953158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_953158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_953158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_953158 prefixEnd_953158 := by exact prefixLift 953158
  have htrace : WordTrace (prefixWord ++ tailWord_953158) baseStart_953158 baseEnd_953158 := by
    simpa [prefixWord, tailWord_953158, baseEnd_953158] using wordTrace_append hprefix tailTrace_953158
  have hstable : (prefixWord ++ tailWord_953158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953158).length < 2 ^ (prefixWord ++ tailWord_953158).sum := by decide
  have hdescent : baseEnd_953158 < baseStart_953158 := by decide
  rcases family_descends (prefixWord ++ tailWord_953158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953197 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 10]
def baseStart_953197 : Nat := 118140960795 + 953197 * 2 ^ 59
def prefixEnd_953197 : Nat := 4983230072969 + 3 ^ 40 * 953197 * 2
def baseEnd_953197 : Nat := 108766270983069410234185

theorem tailTrace_953197 : CollatzResearch.WordTrace tailWord_953197 prefixEnd_953197 108766270983069410234185 := by
  unfold tailWord_953197
  simp only [CollatzResearch.WordTrace]
  refine ⟨34765950727737536932089845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23177300485158357954726563 34765950727737536932089845)
  ·
    refine ⟨3259307880725394087383423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34765950727737536932089845 3259307880725394087383423)
    ·
      refine ⟨4888961821088091131075135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3259307880725394087383423 4888961821088091131075135)
      ·
        refine ⟨7333442731632136696612703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4888961821088091131075135 7333442731632136696612703)
        ·
          refine ⟨11000164097448205044919055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7333442731632136696612703 11000164097448205044919055)
          ·
            refine ⟨16500246146172307567378583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11000164097448205044919055 16500246146172307567378583)
            ·
              refine ⟨24750369219258461351067875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16500246146172307567378583 24750369219258461351067875)
              ·
                refine ⟨37125553828887692026601813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24750369219258461351067875 37125553828887692026601813)
                ·
                  refine ⟨108766270983069410234185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 37125553828887692026601813 108766270983069410234185)
                  ·
                    rfl

theorem cell22_953197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_953197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_953197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_953197 prefixEnd_953197 := by exact prefixLift 953197
  have htrace : WordTrace (prefixWord ++ tailWord_953197) baseStart_953197 baseEnd_953197 := by
    simpa [prefixWord, tailWord_953197, baseEnd_953197] using wordTrace_append hprefix tailTrace_953197
  have hstable : (prefixWord ++ tailWord_953197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953197).length < 2 ^ (prefixWord ++ tailWord_953197).sum := by decide
  have hdescent : baseEnd_953197 < baseStart_953197 := by decide
  rcases family_descends (prefixWord ++ tailWord_953197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953212 : List Nat := [2, 2, 2, 1, 1, 1, 1, 4, 3, 5]
def baseStart_953212 : Nat := 118140960795 + 953212 * 2 ^ 59
def prefixEnd_953212 : Nat := 4983230072969 + 3 ^ 40 * 953212 * 2
def baseEnd_953212 : Nat := 326303947755753191577509

theorem tailTrace_953212 : CollatzResearch.WordTrace tailWord_953212 prefixEnd_953212 326303947755753191577509 := by
  unfold tailWord_953212
  simp only [CollatzResearch.WordTrace]
  refine ⟨17383248911341597246942945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23177665215122129662590593 17383248911341597246942945)
  ·
    refine ⟨13037436683506197935207209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17383248911341597246942945 13037436683506197935207209)
    ·
      refine ⟨9778077512629648451405407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13037436683506197935207209 9778077512629648451405407)
      ·
        refine ⟨14667116268944472677108111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9778077512629648451405407 14667116268944472677108111)
        ·
          refine ⟨22000674403416709015662167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14667116268944472677108111 22000674403416709015662167)
          ·
            refine ⟨33001011605125063523493251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22000674403416709015662167 33001011605125063523493251)
            ·
              refine ⟨49501517407687595285239877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33001011605125063523493251 49501517407687595285239877)
              ·
                refine ⟨9281534513941424115982477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49501517407687595285239877 9281534513941424115982477)
                ·
                  refine ⟨3480575442728034043493429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9281534513941424115982477 3480575442728034043493429)
                  ·
                    refine ⟨326303947755753191577509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3480575442728034043493429 326303947755753191577509)
                    ·
                      rfl

theorem cell22_953212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_953212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_953212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_953212 prefixEnd_953212 := by exact prefixLift 953212
  have htrace : WordTrace (prefixWord ++ tailWord_953212) baseStart_953212 baseEnd_953212 := by
    simpa [prefixWord, tailWord_953212, baseEnd_953212] using wordTrace_append hprefix tailTrace_953212
  have hstable : (prefixWord ++ tailWord_953212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953212).length < 2 ^ (prefixWord ++ tailWord_953212).sum := by decide
  have hdescent : baseEnd_953212 < baseStart_953212 := by decide
  rcases family_descends (prefixWord ++ tailWord_953212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953227 : List Nat := [1, 1, 1, 1, 4, 2, 3, 2, 1, 6]
def baseStart_953227 : Nat := 118140960795 + 953227 * 2 ^ 59
def prefixEnd_953227 : Nat := 4983230072969 + 3 ^ 40 * 953227 * 2
def baseEnd_953227 : Nat := 326309082562298152452463

theorem tailTrace_953227 : CollatzResearch.WordTrace tailWord_953227 prefixEnd_953227 326309082562298152452463 := by
  unfold tailWord_953227
  simp only [CollatzResearch.WordTrace]
  refine ⟨34767044917628852055681935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23178029945085901370454623 34767044917628852055681935)
  ·
    refine ⟨52150567376443278083522903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34767044917628852055681935 52150567376443278083522903)
    ·
      refine ⟨78225851064664917125284355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52150567376443278083522903 78225851064664917125284355)
      ·
        refine ⟨117338776596997375687926533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78225851064664917125284355 117338776596997375687926533)
        ·
          refine ⟨22001020611937007941486225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117338776596997375687926533 22001020611937007941486225)
          ·
            refine ⟨16500765458952755956114669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22001020611937007941486225 16500765458952755956114669)
            ·
              refine ⟨6187787047107283483543001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16500765458952755956114669 6187787047107283483543001)
              ·
                refine ⟨4640840285330462612657251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6187787047107283483543001 4640840285330462612657251)
                ·
                  refine ⟨6961260427995693918985877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4640840285330462612657251 6961260427995693918985877)
                  ·
                    refine ⟨326309082562298152452463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6961260427995693918985877 326309082562298152452463)
                    ·
                      rfl

theorem cell22_953227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 6].length) (baseStart_953227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_953227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_953227 prefixEnd_953227 := by exact prefixLift 953227
  have htrace : WordTrace (prefixWord ++ tailWord_953227) baseStart_953227 baseEnd_953227 := by
    simpa [prefixWord, tailWord_953227, baseEnd_953227] using wordTrace_append hprefix tailTrace_953227
  have hstable : (prefixWord ++ tailWord_953227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953227).length < 2 ^ (prefixWord ++ tailWord_953227).sum := by decide
  have hdescent : baseEnd_953227 < baseStart_953227 := by decide
  rcases family_descends (prefixWord ++ tailWord_953227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953349 : List Nat := [1, 3, 1, 1, 2, 3, 3, 2, 6]
def baseStart_953349 : Nat := 118140960795 + 953349 * 2 ^ 59
def prefixEnd_953349 : Nat := 4983230072969 + 3 ^ 40 * 953349 * 2
def baseEnd_953349 : Nat := 108783615218510166967363

theorem tailTrace_953349 : CollatzResearch.WordTrace tailWord_953349 prefixEnd_953349 108783615218510166967363 := by
  unfold tailWord_953349
  simp only [CollatzResearch.WordTrace]
  refine ⟨34771494623186866891623101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23180996415457911261082067 34771494623186866891623101)
  ·
    refine ⟨13039310483695075084358663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34771494623186866891623101 13039310483695075084358663)
    ·
      refine ⟨19558965725542612626537995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13039310483695075084358663 19558965725542612626537995)
      ·
        refine ⟨29338448588313918939806993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19558965725542612626537995 29338448588313918939806993)
        ·
          refine ⟨22003836441235439204855245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29338448588313918939806993 22003836441235439204855245)
          ·
            refine ⟨8251438665463289701820717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22003836441235439204855245 8251438665463289701820717)
            ·
              refine ⟨3094289499548733638182769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8251438665463289701820717 3094289499548733638182769)
              ·
                refine ⟨2320717124661550228637077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3094289499548733638182769 2320717124661550228637077)
                ·
                  refine ⟨108783615218510166967363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2320717124661550228637077 108783615218510166967363)
                  ·
                    rfl

theorem cell22_953349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 6].length) (baseStart_953349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_953349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_953349 prefixEnd_953349 := by exact prefixLift 953349
  have htrace : WordTrace (prefixWord ++ tailWord_953349) baseStart_953349 baseEnd_953349 := by
    simpa [prefixWord, tailWord_953349, baseEnd_953349] using wordTrace_append hprefix tailTrace_953349
  have hstable : (prefixWord ++ tailWord_953349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953349).length < 2 ^ (prefixWord ++ tailWord_953349).sum := by decide
  have hdescent : baseEnd_953349 < baseStart_953349 := by decide
  rcases family_descends (prefixWord ++ tailWord_953349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953351 : List Nat := [1, 1, 4, 3, 1, 1, 2, 4, 1, 4]
def baseStart_953351 : Nat := 118140960795 + 953351 * 2 ^ 59
def prefixEnd_953351 : Nat := 4983230072969 + 3 ^ 40 * 953351 * 2
def baseEnd_953351 : Nat := 326351530296403162352083

theorem tailTrace_953351 : CollatzResearch.WordTrace tailWord_953351 prefixEnd_953351 326351530296403162352083 := by
  unfold tailWord_953351
  simp only [CollatzResearch.WordTrace]
  refine ⟨34771567569179621233195907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23181045046119747488797271 34771567569179621233195907)
  ·
    refine ⟨52157351353769431849793861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34771567569179621233195907 52157351353769431849793861)
    ·
      refine ⟨9779503378831768471836349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52157351353769431849793861 9779503378831768471836349)
      ·
        refine ⟨3667313767061913176938631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9779503378831768471836349 3667313767061913176938631)
        ·
          refine ⟨5500970650592869765407947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3667313767061913176938631 5500970650592869765407947)
          ·
            refine ⟨8251455975889304648111921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5500970650592869765407947 8251455975889304648111921)
            ·
              refine ⟨6188591981916978486083941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8251455975889304648111921 6188591981916978486083941)
              ·
                refine ⟨1160360996609433466140739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6188591981916978486083941 1160360996609433466140739)
                ·
                  refine ⟨1740541494914150199211109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1160360996609433466140739 1740541494914150199211109)
                  ·
                    refine ⟨326351530296403162352083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1740541494914150199211109 326351530296403162352083)
                    ·
                      rfl

theorem cell22_953351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_953351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_953351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_953351 prefixEnd_953351 := by exact prefixLift 953351
  have htrace : WordTrace (prefixWord ++ tailWord_953351) baseStart_953351 baseEnd_953351 := by
    simpa [prefixWord, tailWord_953351, baseEnd_953351] using wordTrace_append hprefix tailTrace_953351
  have hstable : (prefixWord ++ tailWord_953351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953351).length < 2 ^ (prefixWord ++ tailWord_953351).sum := by decide
  have hdescent : baseEnd_953351 < baseStart_953351 := by decide
  rcases family_descends (prefixWord ++ tailWord_953351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953368 : List Nat := [2, 1, 2, 3, 2, 2, 4, 1, 1, 4]
def baseStart_953368 : Nat := 118140960795 + 953368 * 2 ^ 59
def prefixEnd_953368 : Nat := 4983230072969 + 3 ^ 40 * 953368 * 2
def baseEnd_953368 : Nat := 326357349743820784677031

theorem tailTrace_953368 : CollatzResearch.WordTrace tailWord_953368 prefixEnd_953368 326357349743820784677031 := by
  unfold tailWord_953368
  simp only [CollatzResearch.WordTrace]
  refine ⟨17386093805059016568282379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23181458406745355424376505 17386093805059016568282379)
  ·
    refine ⟨26079140707588524852423569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17386093805059016568282379 26079140707588524852423569)
    ·
      refine ⟨19559355530691393639317677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26079140707588524852423569 19559355530691393639317677)
      ·
        refine ⟨7334758324009272614744129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19559355530691393639317677 7334758324009272614744129)
        ·
          refine ⟨5501068743006954461058097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7334758324009272614744129 5501068743006954461058097)
          ·
            refine ⟨4125801557255215845793573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5501068743006954461058097 4125801557255215845793573)
            ·
              refine ⟨773587791985352971086295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4125801557255215845793573 773587791985352971086295)
              ·
                refine ⟨1160381687978029456629443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 773587791985352971086295 1160381687978029456629443)
                ·
                  refine ⟨1740572531967044184944165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1160381687978029456629443 1740572531967044184944165)
                  ·
                    refine ⟨326357349743820784677031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1740572531967044184944165 326357349743820784677031)
                    ·
                      rfl

theorem cell22_953368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 1, 1, 4].length) (baseStart_953368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_953368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_953368 prefixEnd_953368 := by exact prefixLift 953368
  have htrace : WordTrace (prefixWord ++ tailWord_953368) baseStart_953368 baseEnd_953368 := by
    simpa [prefixWord, tailWord_953368, baseEnd_953368] using wordTrace_append hprefix tailTrace_953368
  have hstable : (prefixWord ++ tailWord_953368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953368).length < 2 ^ (prefixWord ++ tailWord_953368).sum := by decide
  have hdescent : baseEnd_953368 < baseStart_953368 := by decide
  rcases family_descends (prefixWord ++ tailWord_953368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953381 : List Nat := [1, 3, 1, 2, 2, 2, 3, 1, 4, 3]
def baseStart_953381 : Nat := 118140960795 + 953381 * 2 ^ 59
def prefixEnd_953381 : Nat := 4983230072969 + 3 ^ 40 * 953381 * 2
def baseEnd_953381 : Nat := 326361799909493084101991

theorem tailTrace_953381 : CollatzResearch.WordTrace tailWord_953381 prefixEnd_953381 326361799909493084101991 := by
  unfold tailWord_953381
  simp only [CollatzResearch.WordTrace]
  refine ⟨34772661759070936356787997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23181774506047290904525331 34772661759070936356787997)
  ·
    refine ⟨13039748159651601133795499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34772661759070936356787997 13039748159651601133795499)
    ·
      refine ⟨19559622239477401700693249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13039748159651601133795499 19559622239477401700693249)
      ·
        refine ⟨14669716679608051275519937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19559622239477401700693249 14669716679608051275519937)
        ·
          refine ⟨11002287509706038456639953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14669716679608051275519937 11002287509706038456639953)
          ·
            refine ⟨8251715632279528842479965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11002287509706038456639953 8251715632279528842479965)
            ·
              refine ⟨3094393362104823315929987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8251715632279528842479965 3094393362104823315929987)
              ·
                refine ⟨4641590043157234973894981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3094393362104823315929987 4641590043157234973894981)
                ·
                  refine ⟨870298133091981557605309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4641590043157234973894981 870298133091981557605309)
                  ·
                    refine ⟨326361799909493084101991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 870298133091981557605309 326361799909493084101991)
                    ·
                      rfl

theorem cell22_953381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 4, 3].length) (baseStart_953381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_953381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_953381 prefixEnd_953381 := by exact prefixLift 953381
  have htrace : WordTrace (prefixWord ++ tailWord_953381) baseStart_953381 baseEnd_953381 := by
    simpa [prefixWord, tailWord_953381, baseEnd_953381] using wordTrace_append hprefix tailTrace_953381
  have hstable : (prefixWord ++ tailWord_953381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953381).length < 2 ^ (prefixWord ++ tailWord_953381).sum := by decide
  have hdescent : baseEnd_953381 < baseStart_953381 := by decide
  rcases family_descends (prefixWord ++ tailWord_953381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953383 : List Nat := [1, 1, 7, 1, 1, 2, 2, 1, 6]
def baseStart_953383 : Nat := 118140960795 + 953383 * 2 ^ 59
def prefixEnd_953383 : Nat := 4983230072969 + 3 ^ 40 * 953383 * 2
def baseEnd_953383 : Nat := 108787494850121915183995

theorem tailTrace_953383 : CollatzResearch.WordTrace tailWord_953383 prefixEnd_953383 108787494850121915183995 := by
  unfold tailWord_953383
  simp only [CollatzResearch.WordTrace]
  refine ⟨34772734705063690698360803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23181823136709127132240535 34772734705063690698360803)
  ·
    refine ⟨52159102057595536047541205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34772734705063690698360803 52159102057595536047541205)
    ·
      refine ⟨1222478954474895376114247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 52159102057595536047541205 1222478954474895376114247)
      ·
        refine ⟨1833718431712343064171371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1222478954474895376114247 1833718431712343064171371)
        ·
          refine ⟨2750577647568514596257057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1833718431712343064171371 2750577647568514596257057)
          ·
            refine ⟨2062933235676385947192793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2750577647568514596257057 2062933235676385947192793)
            ·
              refine ⟨1547199926757289460394595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2062933235676385947192793 1547199926757289460394595)
              ·
                refine ⟨2320799890135934190591893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1547199926757289460394595 2320799890135934190591893)
                ·
                  refine ⟨108787494850121915183995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2320799890135934190591893 108787494850121915183995)
                  ·
                    rfl

theorem cell22_953383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 6].length) (baseStart_953383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_953383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_953383 prefixEnd_953383 := by exact prefixLift 953383
  have htrace : WordTrace (prefixWord ++ tailWord_953383) baseStart_953383 baseEnd_953383 := by
    simpa [prefixWord, tailWord_953383, baseEnd_953383] using wordTrace_append hprefix tailTrace_953383
  have hstable : (prefixWord ++ tailWord_953383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953383).length < 2 ^ (prefixWord ++ tailWord_953383).sum := by decide
  have hdescent : baseEnd_953383 < baseStart_953383 := by decide
  rcases family_descends (prefixWord ++ tailWord_953383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953394 : List Nat := [3, 2, 1, 1, 2, 2, 2, 9]
def baseStart_953394 : Nat := 118140960795 + 953394 * 2 ^ 59
def prefixEnd_953394 : Nat := 4983230072969 + 3 ^ 40 * 953394 * 2
def baseEnd_953394 : Nat := 36262916675018375947439

theorem tailTrace_953394 : CollatzResearch.WordTrace tailWord_953394 prefixEnd_953394 36262916675018375947439 := by
  unfold tailWord_953394
  simp only [CollatzResearch.WordTrace]
  refine ⟨8693283977005959894252809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23182090605349226384674157 8693283977005959894252809)
  ·
    refine ⟨6519962982754469920689607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8693283977005959894252809 6519962982754469920689607)
    ·
      refine ⟨9779944474131704881034411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6519962982754469920689607 9779944474131704881034411)
      ·
        refine ⟨14669916711197557321551617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9779944474131704881034411 14669916711197557321551617)
        ·
          refine ⟨11002437533398167991163713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14669916711197557321551617 11002437533398167991163713)
          ·
            refine ⟨8251828150048625993372785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11002437533398167991163713 8251828150048625993372785)
            ·
              refine ⟨6188871112536469495029589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8251828150048625993372785 6188871112536469495029589)
              ·
                refine ⟨36262916675018375947439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6188871112536469495029589 36262916675018375947439)
                ·
                  rfl

theorem cell22_953394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 9].length) (baseStart_953394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_953394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_953394 prefixEnd_953394 := by exact prefixLift 953394
  have htrace : WordTrace (prefixWord ++ tailWord_953394) baseStart_953394 baseEnd_953394 := by
    simpa [prefixWord, tailWord_953394, baseEnd_953394] using wordTrace_append hprefix tailTrace_953394
  have hstable : (prefixWord ++ tailWord_953394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953394).length < 2 ^ (prefixWord ++ tailWord_953394).sum := by decide
  have hdescent : baseEnd_953394 < baseStart_953394 := by decide
  rcases family_descends (prefixWord ++ tailWord_953394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953398 : List Nat := [5, 1, 2, 1, 1, 2, 3, 1, 1, 5]
def baseStart_953398 : Nat := 118140960795 + 953398 * 2 ^ 59
def prefixEnd_953398 : Nat := 4983230072969 + 3 ^ 40 * 953398 * 2
def baseEnd_953398 : Nat := 326367619356910706426939

theorem tailTrace_953398 : CollatzResearch.WordTrace tailWord_953398 prefixEnd_953398 326367619356910706426939 := by
  unfold tailWord_953398
  simp only [CollatzResearch.WordTrace]
  refine ⟨2173330112500584266259803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23182187866672898840104565 2173330112500584266259803)
  ·
    refine ⟨3259995168750876399389705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2173330112500584266259803 3259995168750876399389705)
    ·
      refine ⟨2444996376563157299542279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3259995168750876399389705 2444996376563157299542279)
      ·
        refine ⟨3667494564844735949313419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2444996376563157299542279 3667494564844735949313419)
        ·
          refine ⟨5501241847267103923970129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3667494564844735949313419 5501241847267103923970129)
          ·
            refine ⟨4125931385450327942977597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5501241847267103923970129 4125931385450327942977597)
            ·
              refine ⟨1547224269543872978616599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4125931385450327942977597 1547224269543872978616599)
              ·
                refine ⟨2320836404315809467924899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1547224269543872978616599 2320836404315809467924899)
                ·
                  refine ⟨3481254606473714201887349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2320836404315809467924899 3481254606473714201887349)
                  ·
                    refine ⟨326367619356910706426939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3481254606473714201887349 326367619356910706426939)
                    ·
                      rfl

theorem cell22_953398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_953398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_953398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_953398 prefixEnd_953398 := by exact prefixLift 953398
  have htrace : WordTrace (prefixWord ++ tailWord_953398) baseStart_953398 baseEnd_953398 := by
    simpa [prefixWord, tailWord_953398, baseEnd_953398] using wordTrace_append hprefix tailTrace_953398
  have hstable : (prefixWord ++ tailWord_953398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953398).length < 2 ^ (prefixWord ++ tailWord_953398).sum := by decide
  have hdescent : baseEnd_953398 < baseStart_953398 := by decide
  rcases family_descends (prefixWord ++ tailWord_953398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953439 : List Nat := [1, 1, 2, 3, 1, 1, 3, 3, 7]
def baseStart_953439 : Nat := 118140960795 + 953439 * 2 ^ 59
def prefixEnd_953439 : Nat := 4983230072969 + 3 ^ 40 * 953439 * 2
def baseEnd_953439 : Nat := 108793884831600088717271

theorem tailTrace_953439 : CollatzResearch.WordTrace tailWord_953439 prefixEnd_953439 108793884831600088717271 := by
  unfold tailWord_953439
  simp only [CollatzResearch.WordTrace]
  refine ⟨34774777192860812262399371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23183184795240541508266247 34774777192860812262399371)
  ·
    refine ⟨52162165789291218393599057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34774777192860812262399371 52162165789291218393599057)
    ·
      refine ⟨39121624341968413795199293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52162165789291218393599057 39121624341968413795199293)
      ·
        refine ⟨14670609128238155173199735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39121624341968413795199293 14670609128238155173199735)
        ·
          refine ⟨22005913692357232759799603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14670609128238155173199735 22005913692357232759799603)
          ·
            refine ⟨33008870538535849139699405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22005913692357232759799603 33008870538535849139699405)
            ·
              refine ⟨12378326451950943427387277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33008870538535849139699405 12378326451950943427387277)
              ·
                refine ⟨4641872419481603785270229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12378326451950943427387277 4641872419481603785270229)
                ·
                  refine ⟨108793884831600088717271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4641872419481603785270229 108793884831600088717271)
                  ·
                    rfl

theorem cell22_953439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 7].length) (baseStart_953439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_953439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_953439 prefixEnd_953439 := by exact prefixLift 953439
  have htrace : WordTrace (prefixWord ++ tailWord_953439) baseStart_953439 baseEnd_953439 := by
    simpa [prefixWord, tailWord_953439, baseEnd_953439] using wordTrace_append hprefix tailTrace_953439
  have hstable : (prefixWord ++ tailWord_953439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953439).length < 2 ^ (prefixWord ++ tailWord_953439).sum := by decide
  have hdescent : baseEnd_953439 < baseStart_953439 := by decide
  rcases family_descends (prefixWord ++ tailWord_953439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953456 : List Nat := [2, 1, 1, 1, 5, 1, 3, 3, 5]
def baseStart_953456 : Nat := 118140960795 + 953456 * 2 ^ 59
def prefixEnd_953456 : Nat := 4983230072969 + 3 ^ 40 * 953456 * 2
def baseEnd_953456 : Nat := 108795824647405962825587

theorem tailTrace_953456 : CollatzResearch.WordTrace tailWord_953456 prefixEnd_953456 108795824647405962825587 := by
  unfold tailWord_953456
  simp only [CollatzResearch.WordTrace]
  refine ⟨17387698616899612082884111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23183598155866149443845481 17387698616899612082884111)
  ·
    refine ⟨26081547925349418124326167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17387698616899612082884111 26081547925349418124326167)
    ·
      refine ⟨39122321888024127186489251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26081547925349418124326167 39122321888024127186489251)
      ·
        refine ⟨58683482832036190779733877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39122321888024127186489251 58683482832036190779733877)
        ·
          refine ⟨5501576515503392885600051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58683482832036190779733877 5501576515503392885600051)
          ·
            refine ⟨8252364773255089328400077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5501576515503392885600051 8252364773255089328400077)
            ·
              refine ⟨3094636789970658498150029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8252364773255089328400077 3094636789970658498150029)
              ·
                refine ⟨1160488796238996936806261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3094636789970658498150029 1160488796238996936806261)
                ·
                  refine ⟨108795824647405962825587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1160488796238996936806261 108795824647405962825587)
                  ·
                    rfl

theorem cell22_953456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 3, 5].length) (baseStart_953456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_953456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_953456 prefixEnd_953456 := by exact prefixLift 953456
  have htrace : WordTrace (prefixWord ++ tailWord_953456) baseStart_953456 baseEnd_953456 := by
    simpa [prefixWord, tailWord_953456, baseEnd_953456] using wordTrace_append hprefix tailTrace_953456
  have hstable : (prefixWord ++ tailWord_953456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953456).length < 2 ^ (prefixWord ++ tailWord_953456).sum := by decide
  have hdescent : baseEnd_953456 < baseStart_953456 := by decide
  rcases family_descends (prefixWord ++ tailWord_953456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953499 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 2, 9]
def baseStart_953499 : Nat := 118140960795 + 953499 * 2 ^ 59
def prefixEnd_953499 : Nat := 4983230072969 + 3 ^ 40 * 953499 * 2
def baseEnd_953499 : Nat := 326402193720980109651629

theorem tailTrace_953499 : CollatzResearch.WordTrace tailWord_953499 prefixEnd_953499 326402193720980109651629 := by
  unfold tailWord_953499
  simp only [CollatzResearch.WordTrace]
  refine ⟨34776965572643442509583551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23184643715095628339722367 34776965572643442509583551)
  ·
    refine ⟨52165448358965163764375327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34776965572643442509583551 52165448358965163764375327)
    ·
      refine ⟨78248172538447745646562991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52165448358965163764375327 78248172538447745646562991)
      ·
        refine ⟨117372258807671618469844487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78248172538447745646562991 117372258807671618469844487)
        ·
          refine ⟨176058388211507427704766731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117372258807671618469844487 176058388211507427704766731)
          ·
            refine ⟨264087582317261141557150097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176058388211507427704766731 264087582317261141557150097)
            ·
              refine ⟨198065686737945856167862573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264087582317261141557150097 198065686737945856167862573)
              ·
                refine ⟨74274632526729696062948465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198065686737945856167862573 74274632526729696062948465)
                ·
                  refine ⟨55705974395047272047211349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74274632526729696062948465 55705974395047272047211349)
                  ·
                    refine ⟨326402193720980109651629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 55705974395047272047211349 326402193720980109651629)
                    ·
                      rfl

theorem cell22_953499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 9].length) (baseStart_953499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_953499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_953499 prefixEnd_953499 := by exact prefixLift 953499
  have htrace : WordTrace (prefixWord ++ tailWord_953499) baseStart_953499 baseEnd_953499 := by
    simpa [prefixWord, tailWord_953499, baseEnd_953499] using wordTrace_append hprefix tailTrace_953499
  have hstable : (prefixWord ++ tailWord_953499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953499).length < 2 ^ (prefixWord ++ tailWord_953499).sum := by decide
  have hdescent : baseEnd_953499 < baseStart_953499 := by decide
  rcases family_descends (prefixWord ++ tailWord_953499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953501 : List Nat := [1, 4, 2, 1, 1, 2, 2, 3, 6]
def baseStart_953501 : Nat := 118140960795 + 953501 * 2 ^ 59
def prefixEnd_953501 : Nat := 4983230072969 + 3 ^ 40 * 953501 * 2
def baseEnd_953501 : Nat := 108800959453950923700541

theorem tailTrace_953501 : CollatzResearch.WordTrace tailWord_953501 prefixEnd_953501 108800959453950923700541 := by
  unfold tailWord_953501
  simp only [CollatzResearch.WordTrace]
  refine ⟨34777038518636196851156357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23184692345757464567437571 34777038518636196851156357)
  ·
    refine ⟨6520694722244286909591817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34777038518636196851156357 6520694722244286909591817)
    ·
      refine ⟨4890521041683215182193863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6520694722244286909591817 4890521041683215182193863)
      ·
        refine ⟨7335781562524822773290795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4890521041683215182193863 7335781562524822773290795)
        ·
          refine ⟨11003672343787234159936193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7335781562524822773290795 11003672343787234159936193)
          ·
            refine ⟨8252754257840425619952145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11003672343787234159936193 8252754257840425619952145)
            ·
              refine ⟨6189565693380319214964109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8252754257840425619952145 6189565693380319214964109)
              ·
                refine ⟨2321087135017619705611541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6189565693380319214964109 2321087135017619705611541)
                ·
                  refine ⟨108800959453950923700541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2321087135017619705611541 108800959453950923700541)
                  ·
                    rfl

theorem cell22_953501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 6].length) (baseStart_953501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_953501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_953501 prefixEnd_953501 := by exact prefixLift 953501
  have htrace : WordTrace (prefixWord ++ tailWord_953501) baseStart_953501 baseEnd_953501 := by
    simpa [prefixWord, tailWord_953501, baseEnd_953501] using wordTrace_append hprefix tailTrace_953501
  have hstable : (prefixWord ++ tailWord_953501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953501).length < 2 ^ (prefixWord ++ tailWord_953501).sum := by decide
  have hdescent : baseEnd_953501 < baseStart_953501 := by decide
  rcases family_descends (prefixWord ++ tailWord_953501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953531 : List Nat := [1, 1, 1, 1, 1, 2, 4, 5, 2, 4]
def baseStart_953531 : Nat := 118140960795 + 953531 * 2 ^ 59
def prefixEnd_953531 : Nat := 4983230072969 + 3 ^ 40 * 953531 * 2
def baseEnd_953531 : Nat := 326413147974942692851531

theorem tailTrace_953531 : CollatzResearch.WordTrace tailWord_953531 prefixEnd_953531 326413147974942692851531 := by
  unfold tailWord_953531
  simp only [CollatzResearch.WordTrace]
  refine ⟨34778132708527511974748447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23185421805685007983165631 34778132708527511974748447)
  ·
    refine ⟨52167199062791267962122671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34778132708527511974748447 52167199062791267962122671)
    ·
      refine ⟨78250798594186901943184007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52167199062791267962122671 78250798594186901943184007)
      ·
        refine ⟨117376197891280352914776011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78250798594186901943184007 117376197891280352914776011)
        ·
          refine ⟨176064296836920529372164017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117376197891280352914776011 176064296836920529372164017)
          ·
            refine ⟨132048222627690397029123013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176064296836920529372164017 132048222627690397029123013)
            ·
              refine ⟨24759041742691949442960565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132048222627690397029123013 24759041742691949442960565)
              ·
                refine ⟨2321160163377370260277553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24759041742691949442960565 2321160163377370260277553)
                ·
                  refine ⟨1740870122533027695208165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2321160163377370260277553 1740870122533027695208165)
                  ·
                    refine ⟨326413147974942692851531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1740870122533027695208165 326413147974942692851531)
                    ·
                      rfl

theorem cell22_953531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 2, 4].length) (baseStart_953531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_953531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_953531 prefixEnd_953531 := by exact prefixLift 953531
  have htrace : WordTrace (prefixWord ++ tailWord_953531) baseStart_953531 baseEnd_953531 := by
    simpa [prefixWord, tailWord_953531, baseEnd_953531] using wordTrace_append hprefix tailTrace_953531
  have hstable : (prefixWord ++ tailWord_953531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953531).length < 2 ^ (prefixWord ++ tailWord_953531).sum := by decide
  have hdescent : baseEnd_953531 < baseStart_953531 := by decide
  rcases family_descends (prefixWord ++ tailWord_953531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953537 : List Nat := [1, 2, 6, 1, 1, 1, 4, 1, 1, 4]
def baseStart_953537 : Nat := 118140960795 + 953537 * 2 ^ 59
def prefixEnd_953537 : Nat := 4983230072969 + 3 ^ 40 * 953537 * 2
def baseEnd_953537 : Nat := 326415201897560677201513

theorem tailTrace_953537 : CollatzResearch.WordTrace tailWord_953537 prefixEnd_953537 326415201897560677201513 := by
  unfold tailWord_953537
  simp only [CollatzResearch.WordTrace]
  refine ⟨34778351546505774999466865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23185567697670516666311243 34778351546505774999466865)
  ·
    refine ⟨26083763659879331249600149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34778351546505774999466865 26083763659879331249600149)
    ·
      refine ⟨1222676421556843652325007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 26083763659879331249600149 1222676421556843652325007)
      ·
        refine ⟨1834014632335265478487511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1222676421556843652325007 1834014632335265478487511)
        ·
          refine ⟨2751021948502898217731267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1834014632335265478487511 2751021948502898217731267)
          ·
            refine ⟨4126532922754347326596901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2751021948502898217731267 4126532922754347326596901)
            ·
              refine ⟨773724923016440123736919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4126532922754347326596901 773724923016440123736919)
              ·
                refine ⟨1160587384524660185605379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 773724923016440123736919 1160587384524660185605379)
                ·
                  refine ⟨1740881076786990278408069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1160587384524660185605379 1740881076786990278408069)
                  ·
                    refine ⟨326415201897560677201513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1740881076786990278408069 326415201897560677201513)
                    ·
                      rfl

theorem cell22_953537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_953537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_953537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_953537 prefixEnd_953537 := by exact prefixLift 953537
  have htrace : WordTrace (prefixWord ++ tailWord_953537) baseStart_953537 baseEnd_953537 := by
    simpa [prefixWord, tailWord_953537, baseEnd_953537] using wordTrace_append hprefix tailTrace_953537
  have hstable : (prefixWord ++ tailWord_953537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953537).length < 2 ^ (prefixWord ++ tailWord_953537).sum := by decide
  have hdescent : baseEnd_953537 < baseStart_953537 := by decide
  rcases family_descends (prefixWord ++ tailWord_953537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953546 : List Nat := [3, 1, 2, 1, 3, 3, 9]
def baseStart_953546 : Nat := 118140960795 + 953546 * 2 ^ 59
def prefixEnd_953546 : Nat := 4983230072969 + 3 ^ 40 * 953546 * 2
def baseEnd_953546 : Nat := 12089566028943987175055

theorem tailTrace_953546 : CollatzResearch.WordTrace tailWord_953546 prefixEnd_953546 12089566028943987175055 := by
  unfold tailWord_953546
  simp only [CollatzResearch.WordTrace]
  refine ⟨8694669950868292384136123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23185786535648779691029661 8694669950868292384136123)
  ·
    refine ⟨13042004926302438576204185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8694669950868292384136123 13042004926302438576204185)
    ·
      refine ⟨9781503694726828932153139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13042004926302438576204185 9781503694726828932153139)
      ·
        refine ⟨14672255542090243398229709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9781503694726828932153139 14672255542090243398229709)
        ·
          refine ⟨5502095828283841274336141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14672255542090243398229709 5502095828283841274336141)
          ·
            refine ⟨2063285935606440477876053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5502095828283841274336141 2063285935606440477876053)
            ·
              refine ⟨12089566028943987175055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2063285935606440477876053 12089566028943987175055)
              ·
                rfl

theorem cell22_953546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 9].length) (baseStart_953546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_953546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_953546 prefixEnd_953546 := by exact prefixLift 953546
  have htrace : WordTrace (prefixWord ++ tailWord_953546) baseStart_953546 baseEnd_953546 := by
    simpa [prefixWord, tailWord_953546, baseEnd_953546] using wordTrace_append hprefix tailTrace_953546
  have hstable : (prefixWord ++ tailWord_953546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953546).length < 2 ^ (prefixWord ++ tailWord_953546).sum := by decide
  have hdescent : baseEnd_953546 < baseStart_953546 := by decide
  rcases family_descends (prefixWord ++ tailWord_953546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953550 : List Nat := [4, 1, 1, 1, 5, 1, 1, 1, 4, 3]
def baseStart_953550 : Nat := 118140960795 + 953550 * 2 ^ 59
def prefixEnd_953550 : Nat := 4983230072969 + 3 ^ 40 * 953550 * 2
def baseEnd_953550 : Nat := 326419652063232976626473

theorem tailTrace_953550 : CollatzResearch.WordTrace tailWord_953550 prefixEnd_953550 326419652063232976626473 := by
  unfold tailWord_953550
  simp only [CollatzResearch.WordTrace]
  refine ⟨4347353211932334777461263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23185883796972452146460069 4347353211932334777461263)
  ·
    refine ⟨6521029817898502166191895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4347353211932334777461263 6521029817898502166191895)
    ·
      refine ⟨9781544726847753249287843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6521029817898502166191895 9781544726847753249287843)
      ·
        refine ⟨14672317090271629873931765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9781544726847753249287843 14672317090271629873931765)
        ·
          refine ⟨1375529727212965300681103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14672317090271629873931765 1375529727212965300681103)
          ·
            refine ⟨2063294590819447951021655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1375529727212965300681103 2063294590819447951021655)
            ·
              refine ⟨3094941886229171926532483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2063294590819447951021655 3094941886229171926532483)
              ·
                refine ⟨4642412829343757889798725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3094941886229171926532483 4642412829343757889798725)
                ·
                  refine ⟨870452405501954604337261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4642412829343757889798725 870452405501954604337261)
                  ·
                    refine ⟨326419652063232976626473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 870452405501954604337261 326419652063232976626473)
                    ·
                      rfl

theorem cell22_953550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 4, 3].length) (baseStart_953550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_953550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_953550 prefixEnd_953550 := by exact prefixLift 953550
  have htrace : WordTrace (prefixWord ++ tailWord_953550) baseStart_953550 baseEnd_953550 := by
    simpa [prefixWord, tailWord_953550, baseEnd_953550] using wordTrace_append hprefix tailTrace_953550
  have hstable : (prefixWord ++ tailWord_953550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953550).length < 2 ^ (prefixWord ++ tailWord_953550).sum := by decide
  have hdescent : baseEnd_953550 < baseStart_953550 := by decide
  rcases family_descends (prefixWord ++ tailWord_953550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953618 : List Nat := [3, 2, 4, 2, 2, 1, 2, 1, 2, 3]
def baseStart_953618 : Nat := 118140960795 + 953618 * 2 ^ 59
def prefixEnd_953618 : Nat := 4983230072969 + 3 ^ 40 * 953618 * 2
def baseEnd_953618 : Nat := 326442929852903465926265

theorem tailTrace_953618 : CollatzResearch.WordTrace tailWord_953618 prefixEnd_953618 326442929852903465926265 := by
  unfold tailWord_953618
  simp only [CollatzResearch.WordTrace]
  refine ⟨8695326464803081458291377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23187537239474883888777005 8695326464803081458291377)
  ·
    refine ⟨6521494848602311093718533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8695326464803081458291377 6521494848602311093718533)
    ·
      refine ⟨1222780284112933330072225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6521494848602311093718533 1222780284112933330072225)
      ·
        refine ⟨917085213084699997554169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1222780284112933330072225 917085213084699997554169)
        ·
          refine ⟨687813909813524998165627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 917085213084699997554169 687813909813524998165627)
          ·
            refine ⟨1031720864720287497248441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 687813909813524998165627 1031720864720287497248441)
            ·
              refine ⟨773790648540215622936331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1031720864720287497248441 773790648540215622936331)
              ·
                refine ⟨1160685972810323434404497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 773790648540215622936331 1160685972810323434404497)
                ·
                  refine ⟨870514479607742575803373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1160685972810323434404497 870514479607742575803373)
                  ·
                    refine ⟨326442929852903465926265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 870514479607742575803373 326442929852903465926265)
                    ·
                      rfl

theorem cell22_953618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_953618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_953618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_953618 prefixEnd_953618 := by exact prefixLift 953618
  have htrace : WordTrace (prefixWord ++ tailWord_953618) baseStart_953618 baseEnd_953618 := by
    simpa [prefixWord, tailWord_953618, baseEnd_953618] using wordTrace_append hprefix tailTrace_953618
  have hstable : (prefixWord ++ tailWord_953618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953618).length < 2 ^ (prefixWord ++ tailWord_953618).sum := by decide
  have hdescent : baseEnd_953618 < baseStart_953618 := by decide
  rcases family_descends (prefixWord ++ tailWord_953618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953621 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 2, 8]
def baseStart_953621 : Nat := 118140960795 + 953621 * 2 ^ 59
def prefixEnd_953621 : Nat := 4983230072969 + 3 ^ 40 * 953621 * 2
def baseEnd_953621 : Nat := 326443956814212458101255

theorem tailTrace_953621 : CollatzResearch.WordTrace tailWord_953621 prefixEnd_953621 326443956814212458101255 := by
  unfold tailWord_953621
  simp only [CollatzResearch.WordTrace]
  refine ⟨34781415278201457345524717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23187610185467638230349811 34781415278201457345524717)
  ·
    refine ⟨13043030729325546504571769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34781415278201457345524717 13043030729325546504571769)
    ·
      refine ⟨9782273046994159878428827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13043030729325546504571769 9782273046994159878428827)
      ·
        refine ⟨14673409570491239817643241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9782273046994159878428827 14673409570491239817643241)
        ·
          refine ⟨11005057177868429863232431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14673409570491239817643241 11005057177868429863232431)
          ·
            refine ⟨16507585766802644794848647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11005057177868429863232431 16507585766802644794848647)
            ·
              refine ⟨24761378650203967192272971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16507585766802644794848647 24761378650203967192272971)
              ·
                refine ⟨37142067975305950788409457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24761378650203967192272971 37142067975305950788409457)
                ·
                  refine ⟨27856550981479463091307093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37142067975305950788409457 27856550981479463091307093)
                  ·
                    refine ⟨326443956814212458101255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 27856550981479463091307093 326443956814212458101255)
                    ·
                      rfl

theorem cell22_953621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_953621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_953621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_953621 prefixEnd_953621 := by exact prefixLift 953621
  have htrace : WordTrace (prefixWord ++ tailWord_953621) baseStart_953621 baseEnd_953621 := by
    simpa [prefixWord, tailWord_953621, baseEnd_953621] using wordTrace_append hprefix tailTrace_953621
  have hstable : (prefixWord ++ tailWord_953621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953621).length < 2 ^ (prefixWord ++ tailWord_953621).sum := by decide
  have hdescent : baseEnd_953621 < baseStart_953621 := by decide
  rcases family_descends (prefixWord ++ tailWord_953621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953685 : List Nat := [1, 3, 2, 2, 3, 2, 2, 1, 1, 5]
def baseStart_953685 : Nat := 118140960795 + 953685 * 2 ^ 59
def prefixEnd_953685 : Nat := 4983230072969 + 3 ^ 40 * 953685 * 2
def baseEnd_953685 : Nat := 326465865322137624501059

theorem tailTrace_953685 : CollatzResearch.WordTrace tailWord_953685 prefixEnd_953685 326465865322137624501059 := by
  unfold tailWord_953685
  simp only [CollatzResearch.WordTrace]
  refine ⟨34783749549969596275854509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23189166366646397517236339 34783749549969596275854509)
  ·
    refine ⟨13043906081238598603445441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34783749549969596275854509 13043906081238598603445441)
    ·
      refine ⟨9782929560928948952584081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13043906081238598603445441 9782929560928948952584081)
      ·
        refine ⟨7337197170696711714438061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9782929560928948952584081 7337197170696711714438061)
        ·
          refine ⟨2751448939011266892914273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7337197170696711714438061 2751448939011266892914273)
          ·
            refine ⟨2063586704258450169685705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2751448939011266892914273 2063586704258450169685705)
            ·
              refine ⟨1547690028193837627264279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2063586704258450169685705 1547690028193837627264279)
              ·
                refine ⟨2321535042290756440896419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1547690028193837627264279 2321535042290756440896419)
                ·
                  refine ⟨3482302563436134661344629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2321535042290756440896419 3482302563436134661344629)
                  ·
                    refine ⟨326465865322137624501059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3482302563436134661344629 326465865322137624501059)
                    ·
                      rfl

theorem cell22_953685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_953685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_953685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_953685 prefixEnd_953685 := by exact prefixLift 953685
  have htrace : WordTrace (prefixWord ++ tailWord_953685) baseStart_953685 baseEnd_953685 := by
    simpa [prefixWord, tailWord_953685, baseEnd_953685] using wordTrace_append hprefix tailTrace_953685
  have hstable : (prefixWord ++ tailWord_953685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953685).length < 2 ^ (prefixWord ++ tailWord_953685).sum := by decide
  have hdescent : baseEnd_953685 < baseStart_953685 := by decide
  rcases family_descends (prefixWord ++ tailWord_953685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953700 : List Nat := [2, 3, 1, 1, 3, 2, 3, 1, 2, 4]
def baseStart_953700 : Nat := 118140960795 + 953700 * 2 ^ 59
def prefixEnd_953700 : Nat := 4983230072969 + 3 ^ 40 * 953700 * 2
def baseEnd_953700 : Nat := 326471000128682585376013

theorem tailTrace_953700 : CollatzResearch.WordTrace tailWord_953700 prefixEnd_953700 326471000128682585376013 := by
  unfold tailWord_953700
  simp only [CollatzResearch.WordTrace]
  refine ⟨17392148322457626918825277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23189531096610169225100369 17392148322457626918825277)
  ·
    refine ⟨6522055620921610094559479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17392148322457626918825277 6522055620921610094559479)
    ·
      refine ⟨9783083431382415141839219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6522055620921610094559479 9783083431382415141839219)
      ·
        refine ⟨14674625147073622712758829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9783083431382415141839219 14674625147073622712758829)
        ·
          refine ⟨5502984430152608517284561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14674625147073622712758829 5502984430152608517284561)
          ·
            refine ⟨4127238322614456387963421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5502984430152608517284561 4127238322614456387963421)
            ·
              refine ⟨1547714370980421145486283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4127238322614456387963421 1547714370980421145486283)
              ·
                refine ⟨2321571556470631718229425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1547714370980421145486283 2321571556470631718229425)
                ·
                  refine ⟨1741178667352973788672069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2321571556470631718229425 1741178667352973788672069)
                  ·
                    refine ⟨326471000128682585376013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1741178667352973788672069 326471000128682585376013)
                    ·
                      rfl

theorem cell22_953700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_953700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_953700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_953700 prefixEnd_953700 := by exact prefixLift 953700
  have htrace : WordTrace (prefixWord ++ tailWord_953700) baseStart_953700 baseEnd_953700 := by
    simpa [prefixWord, tailWord_953700, baseEnd_953700] using wordTrace_append hprefix tailTrace_953700
  have hstable : (prefixWord ++ tailWord_953700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953700).length < 2 ^ (prefixWord ++ tailWord_953700).sum := by decide
  have hdescent : baseEnd_953700 < baseStart_953700 := by decide
  rcases family_descends (prefixWord ++ tailWord_953700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953706 : List Nat := [3, 1, 3, 3, 3, 1, 2, 1, 1, 4]
def baseStart_953706 : Nat := 118140960795 + 953706 * 2 ^ 59
def prefixEnd_953706 : Nat := 4983230072969 + 3 ^ 40 * 953706 * 2
def baseEnd_953706 : Nat := 326473054051300569725995

theorem tailTrace_953706 : CollatzResearch.WordTrace tailWord_953706 prefixEnd_953706 326473054051300569725995 := by
  unfold tailWord_953706
  simp only [CollatzResearch.WordTrace]
  refine ⟨8696128870723379215592243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23189676988595677908245981 8696128870723379215592243)
  ·
    refine ⟨13044193306085068823388365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8696128870723379215592243 13044193306085068823388365)
    ·
      refine ⟨4891572489781900808770637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13044193306085068823388365 4891572489781900808770637)
      ·
        refine ⟨1834339683668212803288989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4891572489781900808770637 1834339683668212803288989)
        ·
          refine ⟨687877381375579801233371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1834339683668212803288989 687877381375579801233371)
          ·
            refine ⟨1031816072063369701850057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 687877381375579801233371 1031816072063369701850057)
            ·
              refine ⟨773862054047527276387543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1031816072063369701850057 773862054047527276387543)
              ·
                refine ⟨1160793081071290914581315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 773862054047527276387543 1160793081071290914581315)
                ·
                  refine ⟨1741189621606936371871973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1160793081071290914581315 1741189621606936371871973)
                  ·
                    refine ⟨326473054051300569725995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1741189621606936371871973 326473054051300569725995)
                    ·
                      rfl

theorem cell22_953706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_953706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_953706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_953706 prefixEnd_953706 := by exact prefixLift 953706
  have htrace : WordTrace (prefixWord ++ tailWord_953706) baseStart_953706 baseEnd_953706 := by
    simpa [prefixWord, tailWord_953706, baseEnd_953706] using wordTrace_append hprefix tailTrace_953706
  have hstable : (prefixWord ++ tailWord_953706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953706).length < 2 ^ (prefixWord ++ tailWord_953706).sum := by decide
  have hdescent : baseEnd_953706 < baseStart_953706 := by decide
  rcases family_descends (prefixWord ++ tailWord_953706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953781 : List Nat := [1, 3, 3, 2, 2, 2, 3, 2, 1, 3]
def baseStart_953781 : Nat := 118140960795 + 953781 * 2 ^ 59
def prefixEnd_953781 : Nat := 4983230072969 + 3 ^ 40 * 953781 * 2
def baseEnd_953781 : Nat := 326498728084025374100765

theorem tailTrace_953781 : CollatzResearch.WordTrace tailWord_953781 prefixEnd_953781 326498728084025374100765 := by
  unfold tailWord_953781
  simp only [CollatzResearch.WordTrace]
  refine ⟨34787250957621804671349197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23191500638414536447566131 34787250957621804671349197)
  ·
    refine ⟨13045219109108176751755949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34787250957621804671349197 13045219109108176751755949)
    ·
      refine ⟨4891957165915566281908481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13045219109108176751755949 4891957165915566281908481)
      ·
        refine ⟨3668967874436674711431361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4891957165915566281908481 3668967874436674711431361)
        ·
          refine ⟨2751725905827506033573521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3668967874436674711431361 2751725905827506033573521)
          ·
            refine ⟨2063794429370629525180141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2751725905827506033573521 2063794429370629525180141)
            ·
              refine ⟨773922911013986071942553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2063794429370629525180141 773922911013986071942553)
              ·
                refine ⟨580442183260489553956915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 773922911013986071942553 580442183260489553956915)
                ·
                  refine ⟨870663274890734330935373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 580442183260489553956915 870663274890734330935373)
                  ·
                    refine ⟨326498728084025374100765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 870663274890734330935373 326498728084025374100765)
                    ·
                      rfl

theorem cell22_953781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_953781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_953781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_953781 prefixEnd_953781 := by exact prefixLift 953781
  have htrace : WordTrace (prefixWord ++ tailWord_953781) baseStart_953781 baseEnd_953781 := by
    simpa [prefixWord, tailWord_953781, baseEnd_953781] using wordTrace_append hprefix tailTrace_953781
  have hstable : (prefixWord ++ tailWord_953781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953781).length < 2 ^ (prefixWord ++ tailWord_953781).sum := by decide
  have hdescent : baseEnd_953781 < baseStart_953781 := by decide
  rcases family_descends (prefixWord ++ tailWord_953781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953790 : List Nat := [4, 2, 1, 1, 1, 1, 1, 4, 3, 4]
def baseStart_953790 : Nat := 118140960795 + 953790 * 2 ^ 59
def prefixEnd_953790 : Nat := 4983230072969 + 3 ^ 40 * 953790 * 2
def baseEnd_953790 : Nat := 326501808967952350625737

theorem tailTrace_953790 : CollatzResearch.WordTrace tailWord_953790 prefixEnd_953790 326501808967952350625737 := by
  unfold tailWord_953790
  simp only [CollatzResearch.WordTrace]
  refine ⟨4348447401823649901053353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23191719476392799472284549 4348447401823649901053353)
  ·
    refine ⟨3261335551367737425790015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4348447401823649901053353 3261335551367737425790015)
    ·
      refine ⟨4892003327051606138685023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3261335551367737425790015 4892003327051606138685023)
      ·
        refine ⟨7338004990577409208027535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4892003327051606138685023 7338004990577409208027535)
        ·
          refine ⟨11007007485866113812041303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7338004990577409208027535 11007007485866113812041303)
          ·
            refine ⟨16510511228799170718061955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11007007485866113812041303 16510511228799170718061955)
            ·
              refine ⟨24765766843198756077092933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16510511228799170718061955 24765766843198756077092933)
              ·
                refine ⟨4643581283099766764454925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24765766843198756077092933 4643581283099766764454925)
                ·
                  refine ⟨1741342981162412536670597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4643581283099766764454925 1741342981162412536670597)
                  ·
                    refine ⟨326501808967952350625737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1741342981162412536670597 326501808967952350625737)
                    ·
                      rfl

theorem cell22_953790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_953790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_953790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_953790 prefixEnd_953790 := by exact prefixLift 953790
  have htrace : WordTrace (prefixWord ++ tailWord_953790) baseStart_953790 baseEnd_953790 := by
    simpa [prefixWord, tailWord_953790, baseEnd_953790] using wordTrace_append hprefix tailTrace_953790
  have hstable : (prefixWord ++ tailWord_953790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953790).length < 2 ^ (prefixWord ++ tailWord_953790).sum := by decide
  have hdescent : baseEnd_953790 < baseStart_953790 := by decide
  rcases family_descends (prefixWord ++ tailWord_953790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953867 : List Nat := [1, 1, 1, 1, 8, 1, 3, 6]
def baseStart_953867 : Nat := 118140960795 + 953867 * 2 ^ 59
def prefixEnd_953867 : Nat := 4983230072969 + 3 ^ 40 * 953867 * 2
def baseEnd_953867 : Nat := 36280907515727757383389

theorem tailTrace_953867 : CollatzResearch.WordTrace tailWord_953867 prefixEnd_953867 36280907515727757383389 := by
  unfold tailWord_953867
  simp only [CollatzResearch.WordTrace]
  refine ⟨34790387635310241358979855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23193591756873494239319903 34790387635310241358979855)
  ·
    refine ⟨52185581452965362038469783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34790387635310241358979855 52185581452965362038469783)
    ·
      refine ⟨78278372179448043057704675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52185581452965362038469783 78278372179448043057704675)
      ·
        refine ⟨117417558269172064586557013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78278372179448043057704675 117417558269172064586557013)
        ·
          refine ⟨1375987010966860131873715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 117417558269172064586557013 1375987010966860131873715)
          ·
            refine ⟨2063980516450290197810573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1375987010966860131873715 2063980516450290197810573)
            ·
              refine ⟨773992693668858824178965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2063980516450290197810573 773992693668858824178965)
              ·
                refine ⟨36280907515727757383389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 773992693668858824178965 36280907515727757383389)
                ·
                  rfl

theorem cell22_953867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 6].length) (baseStart_953867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_953867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_953867 prefixEnd_953867 := by exact prefixLift 953867
  have htrace : WordTrace (prefixWord ++ tailWord_953867) baseStart_953867 baseEnd_953867 := by
    simpa [prefixWord, tailWord_953867, baseEnd_953867] using wordTrace_append hprefix tailTrace_953867
  have hstable : (prefixWord ++ tailWord_953867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953867).length < 2 ^ (prefixWord ++ tailWord_953867).sum := by decide
  have hdescent : baseEnd_953867 < baseStart_953867 := by decide
  rcases family_descends (prefixWord ++ tailWord_953867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953957 : List Nat := [1, 3, 1, 3, 3, 1, 3, 1, 6]
def baseStart_953957 : Nat := 118140960795 + 953957 * 2 ^ 59
def prefixEnd_953957 : Nat := 4983230072969 + 3 ^ 40 * 953957 * 2
def baseEnd_953957 : Nat := 108852992160273193900075

theorem tailTrace_953957 : CollatzResearch.WordTrace tailWord_953957 prefixEnd_953957 108852992160273193900075 := by
  unfold tailWord_953957
  simp only [CollatzResearch.WordTrace]
  refine ⟨34793670204984186729756125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23195780136656124486504083 34793670204984186729756125)
  ·
    refine ⟨13047626326869070023658547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34793670204984186729756125 13047626326869070023658547)
    ·
      refine ⟨19571439490303605035487821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13047626326869070023658547 19571439490303605035487821)
      ·
        refine ⟨7339289808863851888307933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19571439490303605035487821 7339289808863851888307933)
        ·
          refine ⟨2752233678323944458115475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7339289808863851888307933 2752233678323944458115475)
          ·
            refine ⟨4128350517485916687173213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2752233678323944458115475 4128350517485916687173213)
            ·
              refine ⟨1548131444057218757689955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4128350517485916687173213 1548131444057218757689955)
              ·
                refine ⟨2322197166085828136534933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1548131444057218757689955 2322197166085828136534933)
                ·
                  refine ⟨108852992160273193900075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2322197166085828136534933 108852992160273193900075)
                  ·
                    rfl

theorem cell22_953957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 6].length) (baseStart_953957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_953957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_953957 prefixEnd_953957 := by exact prefixLift 953957
  have htrace : WordTrace (prefixWord ++ tailWord_953957) baseStart_953957 baseEnd_953957 := by
    simpa [prefixWord, tailWord_953957, baseEnd_953957] using wordTrace_append hprefix tailTrace_953957
  have hstable : (prefixWord ++ tailWord_953957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953957).length < 2 ^ (prefixWord ++ tailWord_953957).sum := by decide
  have hdescent : baseEnd_953957 < baseStart_953957 := by decide
  rcases family_descends (prefixWord ++ tailWord_953957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954002 : List Nat := [3, 2, 3, 1, 3, 10]
def baseStart_954002 : Nat := 118140960795 + 954002 * 2 ^ 59
def prefixEnd_954002 : Nat := 4983230072969 + 3 ^ 40 * 954002 * 2
def baseEnd_954002 : Nat := 4031782480252524250927

theorem tailTrace_954002 : CollatzResearch.WordTrace tailWord_954002 prefixEnd_954002 4031782480252524250927 := by
  unfold tailWord_954002
  simp only [CollatzResearch.WordTrace]
  refine ⟨8698827872455289853786065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23196874326547439610096173 8698827872455289853786065)
  ·
    refine ⟨6524120904341467390339549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8698827872455289853786065 6524120904341467390339549)
    ·
      refine ⟨2446545339128050271377331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6524120904341467390339549 2446545339128050271377331)
      ·
        refine ⟨3669818008692075407065997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2446545339128050271377331 3669818008692075407065997)
        ·
          refine ⟨1376181753259528277649749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3669818008692075407065997 1376181753259528277649749)
          ·
            refine ⟨4031782480252524250927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1376181753259528277649749 4031782480252524250927)
            ·
              rfl

theorem cell22_954002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 10].length) (baseStart_954002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_954002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_954002 prefixEnd_954002 := by exact prefixLift 954002
  have htrace : WordTrace (prefixWord ++ tailWord_954002) baseStart_954002 baseEnd_954002 := by
    simpa [prefixWord, tailWord_954002, baseEnd_954002] using wordTrace_append hprefix tailTrace_954002
  have hstable : (prefixWord ++ tailWord_954002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954002).length < 2 ^ (prefixWord ++ tailWord_954002).sum := by decide
  have hdescent : baseEnd_954002 < baseStart_954002 := by decide
  rcases family_descends (prefixWord ++ tailWord_954002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954038 : List Nat := [5, 1, 3, 1, 1, 3, 1, 1, 2, 4]
def baseStart_954038 : Nat := 118140960795 + 954038 * 2 ^ 59
def prefixEnd_954038 : Nat := 4983230072969 + 3 ^ 40 * 954038 * 2
def baseEnd_954038 : Nat := 326586704436162370424977

theorem tailTrace_954038 : CollatzResearch.WordTrace tailWord_954038 prefixEnd_954038 326586704436162370424977 := by
  unfold tailWord_954038
  simp only [CollatzResearch.WordTrace]
  refine ⟨2174789032355671097715923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23197749678460491708969845 2174789032355671097715923)
  ·
    refine ⟨3262183548533506646573885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2174789032355671097715923 3262183548533506646573885)
    ·
      refine ⟨1223318830700064992465207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3262183548533506646573885 1223318830700064992465207)
      ·
        refine ⟨1834978246050097488697811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1223318830700064992465207 1834978246050097488697811)
        ·
          refine ⟨2752467369075146233046717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1834978246050097488697811 2752467369075146233046717)
          ·
            refine ⟨1032175263403179837392519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2752467369075146233046717 1032175263403179837392519)
            ·
              refine ⟨1548262895104769756088779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1032175263403179837392519 1548262895104769756088779)
              ·
                refine ⟨2322394342657154634133169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1548262895104769756088779 2322394342657154634133169)
                ·
                  refine ⟨1741795756992865975599877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2322394342657154634133169 1741795756992865975599877)
                  ·
                    refine ⟨326586704436162370424977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1741795756992865975599877 326586704436162370424977)
                    ·
                      rfl

theorem cell22_954038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_954038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_954038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_954038 prefixEnd_954038 := by exact prefixLift 954038
  have htrace : WordTrace (prefixWord ++ tailWord_954038) baseStart_954038 baseEnd_954038 := by
    simpa [prefixWord, tailWord_954038, baseEnd_954038] using wordTrace_append hprefix tailTrace_954038
  have hstable : (prefixWord ++ tailWord_954038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954038).length < 2 ^ (prefixWord ++ tailWord_954038).sum := by decide
  have hdescent : baseEnd_954038 < baseStart_954038 := by decide
  rcases family_descends (prefixWord ++ tailWord_954038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954062 : List Nat := [4, 1, 1, 1, 3, 1, 1, 1, 4, 5]
def baseStart_954062 : Nat := 118140960795 + 954062 * 2 ^ 59
def prefixEnd_954062 : Nat := 4983230072969 + 3 ^ 40 * 954062 * 2
def baseEnd_954062 : Nat := 326594920126634307824903

theorem tailTrace_954062 : CollatzResearch.WordTrace tailWord_954062 prefixEnd_954062 326594920126634307824903 := by
  unfold tailWord_954062
  simp only [CollatzResearch.WordTrace]
  refine ⟨4349687483700473707791055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23198333246402526441552293 4349687483700473707791055)
  ·
    refine ⟨6524531225550710561686583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4349687483700473707791055 6524531225550710561686583)
    ·
      refine ⟨9786796838326065842529875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6524531225550710561686583 9786796838326065842529875)
      ·
        refine ⟨14680195257489098763794813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9786796838326065842529875 14680195257489098763794813)
        ·
          refine ⟨5505073221558412036423055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14680195257489098763794813 5505073221558412036423055)
          ·
            refine ⟨8257609832337618054634583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5505073221558412036423055 8257609832337618054634583)
            ·
              refine ⟨12386414748506427081951875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8257609832337618054634583 12386414748506427081951875)
              ·
                refine ⟨18579622122759640622927813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12386414748506427081951875 18579622122759640622927813)
                ·
                  refine ⟨3483679148017432616798965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18579622122759640622927813 3483679148017432616798965)
                  ·
                    refine ⟨326594920126634307824903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3483679148017432616798965 326594920126634307824903)
                    ·
                      rfl

theorem cell22_954062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_954062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_954062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_954062 prefixEnd_954062 := by exact prefixLift 954062
  have htrace : WordTrace (prefixWord ++ tailWord_954062) baseStart_954062 baseEnd_954062 := by
    simpa [prefixWord, tailWord_954062, baseEnd_954062] using wordTrace_append hprefix tailTrace_954062
  have hstable : (prefixWord ++ tailWord_954062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954062).length < 2 ^ (prefixWord ++ tailWord_954062).sum := by decide
  have hdescent : baseEnd_954062 < baseStart_954062 := by decide
  rcases family_descends (prefixWord ++ tailWord_954062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954068 : List Nat := [2, 4, 1, 3, 1, 1, 2, 4, 1, 3]
def baseStart_954068 : Nat := 118140960795 + 954068 * 2 ^ 59
def prefixEnd_954068 : Nat := 4983230072969 + 3 ^ 40 * 954068 * 2
def baseEnd_954068 : Nat := 326596974049252292174885

theorem tailTrace_954068 : CollatzResearch.WordTrace tailWord_954068 prefixEnd_954068 326596974049252292174885 := by
  unfold tailWord_954068
  simp only [CollatzResearch.WordTrace]
  refine ⟨17398859353791026343523429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23198479138388035124697905 17398859353791026343523429)
  ·
    refine ⟨3262286128835817439410643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17398859353791026343523429 3262286128835817439410643)
    ·
      refine ⟨4893429193253726159115965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3262286128835817439410643 4893429193253726159115965)
      ·
        refine ⟨1835035947470147309668487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4893429193253726159115965 1835035947470147309668487)
        ·
          refine ⟨2752553921205220964502731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1835035947470147309668487 2752553921205220964502731)
          ·
            refine ⟨4128830881807831446754097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2752553921205220964502731 4128830881807831446754097)
            ·
              refine ⟨3096623161355873585065573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4128830881807831446754097 3096623161355873585065573)
              ·
                refine ⟨580616842754226297199795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3096623161355873585065573 580616842754226297199795)
                ·
                  refine ⟨870925264131339445799693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 580616842754226297199795 870925264131339445799693)
                  ·
                    refine ⟨326596974049252292174885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 870925264131339445799693 326596974049252292174885)
                    ·
                      rfl

theorem cell22_954068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_954068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_954068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_954068 prefixEnd_954068 := by exact prefixLift 954068
  have htrace : WordTrace (prefixWord ++ tailWord_954068) baseStart_954068 baseEnd_954068 := by
    simpa [prefixWord, tailWord_954068, baseEnd_954068] using wordTrace_append hprefix tailTrace_954068
  have hstable : (prefixWord ++ tailWord_954068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954068).length < 2 ^ (prefixWord ++ tailWord_954068).sum := by decide
  have hdescent : baseEnd_954068 < baseStart_954068 := by decide
  rcases family_descends (prefixWord ++ tailWord_954068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954081 : List Nat := [1, 2, 3, 1, 5, 1, 3, 1, 5]
def baseStart_954081 : Nat := 118140960795 + 954081 * 2 ^ 59
def prefixEnd_954081 : Nat := 4983230072969 + 3 ^ 40 * 954081 * 2
def baseEnd_954081 : Nat := 108867141404974863866615

theorem tailTrace_954081 : CollatzResearch.WordTrace tailWord_954081 prefixEnd_954081 108867141404974863866615 := by
  unfold tailWord_954081
  simp only [CollatzResearch.WordTrace]
  refine ⟨34798192856534955907270097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23198795237689970604846731 34798192856534955907270097)
  ·
    refine ⟨26098644642401216930452573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34798192856534955907270097 26098644642401216930452573)
    ·
      refine ⟨9786991740900456348919715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26098644642401216930452573 9786991740900456348919715)
      ·
        refine ⟨14680487611350684523379573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9786991740900456348919715 14680487611350684523379573)
        ·
          refine ⟨1376295713564126674066835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14680487611350684523379573 1376295713564126674066835)
          ·
            refine ⟨2064443570346190011100253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1376295713564126674066835 2064443570346190011100253)
            ·
              refine ⟨774166338879821254162595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2064443570346190011100253 774166338879821254162595)
              ·
                refine ⟨1161249508319731881243893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 774166338879821254162595 1161249508319731881243893)
                ·
                  refine ⟨108867141404974863866615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1161249508319731881243893 108867141404974863866615)
                  ·
                    rfl

theorem cell22_954081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 3, 1, 5].length) (baseStart_954081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_954081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_954081 prefixEnd_954081 := by exact prefixLift 954081
  have htrace : WordTrace (prefixWord ++ tailWord_954081) baseStart_954081 baseEnd_954081 := by
    simpa [prefixWord, tailWord_954081, baseEnd_954081] using wordTrace_append hprefix tailTrace_954081
  have hstable : (prefixWord ++ tailWord_954081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954081).length < 2 ^ (prefixWord ++ tailWord_954081).sum := by decide
  have hdescent : baseEnd_954081 < baseStart_954081 := by decide
  rcases family_descends (prefixWord ++ tailWord_954081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954092 : List Nat := [2, 2, 1, 1, 2, 2, 4, 2, 6]
def baseStart_954092 : Nat := 118140960795 + 954092 * 2 ^ 59
def prefixEnd_954092 : Nat := 4983230072969 + 3 ^ 40 * 954092 * 2
def baseEnd_954092 : Nat := 108868396579908076524937

theorem tailTrace_954092 : CollatzResearch.WordTrace tailWord_954092 prefixEnd_954092 108868396579908076524937 := by
  unfold tailWord_954092
  simp only [CollatzResearch.WordTrace]
  refine ⟨17399297029747552392960265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23199062706330069857280353 17399297029747552392960265)
  ·
    refine ⟨13049472772310664294720199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17399297029747552392960265 13049472772310664294720199)
    ·
      refine ⟨19574209158465996442080299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13049472772310664294720199 19574209158465996442080299)
      ·
        refine ⟨29361313737698994663120449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19574209158465996442080299 29361313737698994663120449)
        ·
          refine ⟨22020985303274245997340337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29361313737698994663120449 22020985303274245997340337)
          ·
            refine ⟨16515738977455684498005253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22020985303274245997340337 16515738977455684498005253)
            ·
              refine ⟨3096701058272940843375985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16515738977455684498005253 3096701058272940843375985)
              ·
                refine ⟨2322525793704705632531989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3096701058272940843375985 2322525793704705632531989)
                ·
                  refine ⟨108868396579908076524937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2322525793704705632531989 108868396579908076524937)
                  ·
                    rfl

theorem cell22_954092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 6].length) (baseStart_954092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_954092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_954092 prefixEnd_954092 := by exact prefixLift 954092
  have htrace : WordTrace (prefixWord ++ tailWord_954092) baseStart_954092 baseEnd_954092 := by
    simpa [prefixWord, tailWord_954092, baseEnd_954092] using wordTrace_append hprefix tailTrace_954092
  have hstable : (prefixWord ++ tailWord_954092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954092).length < 2 ^ (prefixWord ++ tailWord_954092).sum := by decide
  have hdescent : baseEnd_954092 < baseStart_954092 := by decide
  rcases family_descends (prefixWord ++ tailWord_954092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954109 : List Nat := [1, 4, 1, 1, 1, 1, 2, 7, 4]
def baseStart_954109 : Nat := 118140960795 + 954109 * 2 ^ 59
def prefixEnd_954109 : Nat := 4983230072969 + 3 ^ 40 * 954109 * 2
def baseEnd_954109 : Nat := 108870336395713950633253

theorem tailTrace_954109 : CollatzResearch.WordTrace tailWord_954109 prefixEnd_954109 108870336395713950633253 := by
  unfold tailWord_954109
  simp only [CollatzResearch.WordTrace]
  refine ⟨34799214100433516689289381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23199476066955677792859587 34799214100433516689289381)
  ·
    refine ⟨6524852643831284379241759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34799214100433516689289381 6524852643831284379241759)
    ·
      refine ⟨9787278965746926568862639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6524852643831284379241759 9787278965746926568862639)
      ·
        refine ⟨14680918448620389853293959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9787278965746926568862639 14680918448620389853293959)
        ·
          refine ⟨22021377672930584779940939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14680918448620389853293959 22021377672930584779940939)
          ·
            refine ⟨33032066509395877169911409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22021377672930584779940939 33032066509395877169911409)
            ·
              refine ⟨24774049882046907877433557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33032066509395877169911409 24774049882046907877433557)
              ·
                refine ⟨580641794110474403377349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 24774049882046907877433557 580641794110474403377349)
                ·
                  refine ⟨108870336395713950633253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 580641794110474403377349 108870336395713950633253)
                  ·
                    rfl

theorem cell22_954109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 7, 4].length) (baseStart_954109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_954109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_954109 prefixEnd_954109 := by exact prefixLift 954109
  have htrace : WordTrace (prefixWord ++ tailWord_954109) baseStart_954109 baseEnd_954109 := by
    simpa [prefixWord, tailWord_954109, baseEnd_954109] using wordTrace_append hprefix tailTrace_954109
  have hstable : (prefixWord ++ tailWord_954109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954109).length < 2 ^ (prefixWord ++ tailWord_954109).sum := by decide
  have hdescent : baseEnd_954109 < baseStart_954109 := by decide
  rcases family_descends (prefixWord ++ tailWord_954109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954124 : List Nat := [2, 2, 1, 2, 2, 1, 4, 1, 4, 3]
def baseStart_954124 : Nat := 118140960795 + 954124 * 2 ^ 59
def prefixEnd_954124 : Nat := 4983230072969 + 3 ^ 40 * 954124 * 2
def baseEnd_954124 : Nat := 326616143993686812774713

theorem tailTrace_954124 : CollatzResearch.WordTrace tailWord_954124 prefixEnd_954124 326616143993686812774713 := by
  unfold tailWord_954124
  simp only [CollatzResearch.WordTrace]
  refine ⟨17399880597689587125542713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23199840796919449500723617 17399880597689587125542713)
  ·
    refine ⟨13049910448267190344157035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17399880597689587125542713 13049910448267190344157035)
    ·
      refine ⟨19574865672400785516235553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13049910448267190344157035 19574865672400785516235553)
      ·
        refine ⟨14681149254300589137176665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19574865672400785516235553 14681149254300589137176665)
        ·
          refine ⟨11010861940725441852882499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14681149254300589137176665 11010861940725441852882499)
          ·
            refine ⟨16516292911088162779323749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11010861940725441852882499 16516292911088162779323749)
            ·
              refine ⟨3096804920829030521123203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16516292911088162779323749 3096804920829030521123203)
              ·
                refine ⟨4645207381243545781684805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3096804920829030521123203 4645207381243545781684805)
                ·
                  refine ⟨870976383983164834065901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4645207381243545781684805 870976383983164834065901)
                  ·
                    refine ⟨326616143993686812774713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 870976383983164834065901 326616143993686812774713)
                    ·
                      rfl

theorem cell22_954124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 4, 3].length) (baseStart_954124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_954124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_954124 prefixEnd_954124 := by exact prefixLift 954124
  have htrace : WordTrace (prefixWord ++ tailWord_954124) baseStart_954124 baseEnd_954124 := by
    simpa [prefixWord, tailWord_954124, baseEnd_954124] using wordTrace_append hprefix tailTrace_954124
  have hstable : (prefixWord ++ tailWord_954124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954124).length < 2 ^ (prefixWord ++ tailWord_954124).sum := by decide
  have hdescent : baseEnd_954124 < baseStart_954124 := by decide
  rcases family_descends (prefixWord ++ tailWord_954124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954132 : List Nat := [2, 4, 4, 1, 1, 2, 2, 1, 5]
def baseStart_954132 : Nat := 118140960795 + 954132 * 2 ^ 59
def prefixEnd_954132 : Nat := 4983230072969 + 3 ^ 40 * 954132 * 2
def baseEnd_954132 : Nat := 108872960852392486191563

theorem tailTrace_954132 : CollatzResearch.WordTrace tailWord_954132 prefixEnd_954132 108872960852392486191563 := by
  unfold tailWord_954132
  simp only [CollatzResearch.WordTrace]
  refine ⟨17400026489675095808688325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23200035319566794411584433 17400026489675095808688325)
  ·
    refine ⟨3262504966814080464129061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17400026489675095808688325 3262504966814080464129061)
    ·
      refine ⟨611719681277640087024199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3262504966814080464129061 611719681277640087024199)
      ·
        refine ⟨917579521916460130536299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 611719681277640087024199 917579521916460130536299)
        ·
          refine ⟨1376369282874690195804449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 917579521916460130536299 1376369282874690195804449)
          ·
            refine ⟨1032276962156017646853337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1376369282874690195804449 1032276962156017646853337)
            ·
              refine ⟨774207721617013235140003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1032276962156017646853337 774207721617013235140003)
              ·
                refine ⟨1161311582425519852710005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 774207721617013235140003 1161311582425519852710005)
                ·
                  refine ⟨108872960852392486191563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1161311582425519852710005 108872960852392486191563)
                  ·
                    rfl

theorem cell22_954132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_954132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_954132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_954132 prefixEnd_954132 := by exact prefixLift 954132
  have htrace : WordTrace (prefixWord ++ tailWord_954132) baseStart_954132 baseEnd_954132 := by
    simpa [prefixWord, tailWord_954132, baseEnd_954132] using wordTrace_append hprefix tailTrace_954132
  have hstable : (prefixWord ++ tailWord_954132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954132).length < 2 ^ (prefixWord ++ tailWord_954132).sum := by decide
  have hdescent : baseEnd_954132 < baseStart_954132 := by decide
  rcases family_descends (prefixWord ++ tailWord_954132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954227 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 10]
def baseStart_954227 : Nat := 118140960795 + 954227 * 2 ^ 59
def prefixEnd_954227 : Nat := 4983230072969 + 3 ^ 40 * 954227 * 2
def baseEnd_954227 : Nat := 108883800999542959149799

theorem tailTrace_954227 : CollatzResearch.WordTrace tailWord_954227 prefixEnd_954227 108883800999542959149799 := by
  unfold tailWord_954227
  simp only [CollatzResearch.WordTrace]
  refine ⟨34803517914006022842084935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23202345276004015228056623 34803517914006022842084935)
  ·
    refine ⟨52205276871009034263127403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34803517914006022842084935 52205276871009034263127403)
    ·
      refine ⟨78307915306513551394691105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52205276871009034263127403 78307915306513551394691105)
      ·
        refine ⟨58730936479885163546018329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78307915306513551394691105 58730936479885163546018329)
        ·
          refine ⟨44048202359913872659513747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58730936479885163546018329 44048202359913872659513747)
          ·
            refine ⟨66072303539870808989270621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44048202359913872659513747 66072303539870808989270621)
            ·
              refine ⟨24777113827451553370976483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66072303539870808989270621 24777113827451553370976483)
              ·
                refine ⟨37165670741177330056464725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24777113827451553370976483 37165670741177330056464725)
                ·
                  refine ⟨108883800999542959149799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 37165670741177330056464725 108883800999542959149799)
                  ·
                    rfl

theorem cell22_954227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 10].length) (baseStart_954227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_954227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_954227 prefixEnd_954227 := by exact prefixLift 954227
  have htrace : WordTrace (prefixWord ++ tailWord_954227) baseStart_954227 baseEnd_954227 := by
    simpa [prefixWord, tailWord_954227, baseEnd_954227] using wordTrace_append hprefix tailTrace_954227
  have hstable : (prefixWord ++ tailWord_954227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954227).length < 2 ^ (prefixWord ++ tailWord_954227).sum := by decide
  have hdescent : baseEnd_954227 < baseStart_954227 := by decide
  rcases family_descends (prefixWord ++ tailWord_954227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954244 : List Nat := [2, 3, 2, 1, 1, 1, 3, 3, 6]
def baseStart_954244 : Nat := 118140960795 + 954244 * 2 ^ 59
def prefixEnd_954244 : Nat := 4983230072969 + 3 ^ 40 * 954244 * 2
def baseEnd_954244 : Nat := 108885740815348833258115

theorem tailTrace_954244 : CollatzResearch.WordTrace tailWord_954244 prefixEnd_954244 108885740815348833258115 := by
  unfold tailWord_954244
  simp only [CollatzResearch.WordTrace]
  refine ⟨17402068977472217372726893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23202758636629623163635857 17402068977472217372726893)
  ·
    refine ⟨6525775866552081514772585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17402068977472217372726893 6525775866552081514772585)
    ·
      refine ⟨4894331899914061136079439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6525775866552081514772585 4894331899914061136079439)
      ·
        refine ⟨7341497849871091704119159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4894331899914061136079439 7341497849871091704119159)
        ·
          refine ⟨11012246774806637556178739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7341497849871091704119159 11012246774806637556178739)
          ·
            refine ⟨16518370162209956334268109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11012246774806637556178739 16518370162209956334268109)
            ·
              refine ⟨6194388810828733625350541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16518370162209956334268109 6194388810828733625350541)
              ·
                refine ⟨2322895804060775109506453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6194388810828733625350541 2322895804060775109506453)
                ·
                  refine ⟨108885740815348833258115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2322895804060775109506453 108885740815348833258115)
                  ·
                    rfl

theorem cell22_954244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 6].length) (baseStart_954244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_954244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_954244 prefixEnd_954244 := by exact prefixLift 954244
  have htrace : WordTrace (prefixWord ++ tailWord_954244) baseStart_954244 baseEnd_954244 := by
    simpa [prefixWord, tailWord_954244, baseEnd_954244] using wordTrace_append hprefix tailTrace_954244
  have hstable : (prefixWord ++ tailWord_954244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954244).length < 2 ^ (prefixWord ++ tailWord_954244).sum := by decide
  have hdescent : baseEnd_954244 < baseStart_954244 := by decide
  rcases family_descends (prefixWord ++ tailWord_954244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954276 : List Nat := [2, 3, 1, 2, 1, 3, 1, 2, 4, 3]
def baseStart_954276 : Nat := 118140960795 + 954276 * 2 ^ 59
def prefixEnd_954276 : Nat := 4983230072969 + 3 ^ 40 * 954276 * 2
def baseEnd_954276 : Nat := 326668176700009082974247

theorem tailTrace_954276 : CollatzResearch.WordTrace tailWord_954276 prefixEnd_954276 326668176700009082974247 := by
  unfold tailWord_954276
  simp only [CollatzResearch.WordTrace]
  refine ⟨17402652545414252105309341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23203536727219002807079121 17402652545414252105309341)
  ·
    refine ⟨6525994704530344539491003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17402652545414252105309341 6525994704530344539491003)
    ·
      refine ⟨9788992056795516809236505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6525994704530344539491003 9788992056795516809236505)
      ·
        refine ⟨7341744042596637606927379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9788992056795516809236505 7341744042596637606927379)
        ·
          refine ⟨11012616063894956410391069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7341744042596637606927379 11012616063894956410391069)
          ·
            refine ⟨4129731023960608653896651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11012616063894956410391069 4129731023960608653896651)
            ·
              refine ⟨6194596535940912980844977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4129731023960608653896651 6194596535940912980844977)
              ·
                refine ⟨4645947401955684735633733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6194596535940912980844977 4645947401955684735633733)
                ·
                  refine ⟨871115137866690887931325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4645947401955684735633733 871115137866690887931325)
                  ·
                    refine ⟨326668176700009082974247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 871115137866690887931325 326668176700009082974247)
                    ·
                      rfl

theorem cell22_954276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 4, 3].length) (baseStart_954276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_954276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_954276 prefixEnd_954276 := by exact prefixLift 954276
  have htrace : WordTrace (prefixWord ++ tailWord_954276) baseStart_954276 baseEnd_954276 := by
    simpa [prefixWord, tailWord_954276, baseEnd_954276] using wordTrace_append hprefix tailTrace_954276
  have hstable : (prefixWord ++ tailWord_954276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954276).length < 2 ^ (prefixWord ++ tailWord_954276).sum := by decide
  have hdescent : baseEnd_954276 < baseStart_954276 := by decide
  rcases family_descends (prefixWord ++ tailWord_954276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954289 : List Nat := [1, 2, 2, 4, 2, 1, 10]
def baseStart_954289 : Nat := 118140960795 + 954289 * 2 ^ 59
def prefixEnd_954289 : Nat := 4983230072969 + 3 ^ 40 * 954289 * 2
def baseEnd_954289 : Nat := 12098986180210421570341

theorem tailTrace_954289 : CollatzResearch.WordTrace tailWord_954289 prefixEnd_954289 12098986180210421570341 := by
  unfold tailWord_954289
  simp only [CollatzResearch.WordTrace]
  refine ⟨34805779239781407430841921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23203852826520938287227947 34805779239781407430841921)
  ·
    refine ⟨26104334429836055573131441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34805779239781407430841921 26104334429836055573131441)
    ·
      refine ⟨19578250822377041679848581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26104334429836055573131441 19578250822377041679848581)
      ·
        refine ⟨3670922029195695314971609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19578250822377041679848581 3670922029195695314971609)
        ·
          refine ⟨2753191521896771486228707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3670922029195695314971609 2753191521896771486228707)
          ·
            refine ⟨4129787282845157229343061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2753191521896771486228707 4129787282845157229343061)
            ·
              refine ⟨12098986180210421570341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4129787282845157229343061 12098986180210421570341)
              ·
                rfl

theorem cell22_954289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 10].length) (baseStart_954289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_954289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_954289 prefixEnd_954289 := by exact prefixLift 954289
  have htrace : WordTrace (prefixWord ++ tailWord_954289) baseStart_954289 baseEnd_954289 := by
    simpa [prefixWord, tailWord_954289, baseEnd_954289] using wordTrace_append hprefix tailTrace_954289
  have hstable : (prefixWord ++ tailWord_954289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954289).length < 2 ^ (prefixWord ++ tailWord_954289).sum := by decide
  have hdescent : baseEnd_954289 < baseStart_954289 := by decide
  rcases family_descends (prefixWord ++ tailWord_954289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954351 : List Nat := [1, 1, 2, 1, 4, 2, 4, 2, 5]
def baseStart_954351 : Nat := 118140960795 + 954351 * 2 ^ 59
def prefixEnd_954351 : Nat := 4983230072969 + 3 ^ 40 * 954351 * 2
def baseEnd_954351 : Nat := 108897950244244629116339

theorem tailTrace_954351 : CollatzResearch.WordTrace tailWord_954351 prefixEnd_954351 108897950244244629116339 := by
  unfold tailWord_954351
  simp only [CollatzResearch.WordTrace]
  refine ⟨34808040565556792019598907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23205360377037861346399271 34808040565556792019598907)
  ·
    refine ⟨52212060848335188029398361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34808040565556792019598907 52212060848335188029398361)
    ·
      refine ⟨39159045636251391022048771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52212060848335188029398361 39159045636251391022048771)
      ·
        refine ⟨58738568454377086533073157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39159045636251391022048771 58738568454377086533073157)
        ·
          refine ⟨11013481585195703724951217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58738568454377086533073157 11013481585195703724951217)
          ·
            refine ⟨8260111188896777793713413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11013481585195703724951217 8260111188896777793713413)
            ·
              refine ⟨1548770847918145836321265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8260111188896777793713413 1548770847918145836321265)
              ·
                refine ⟨1161578135938609377240949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1548770847918145836321265 1161578135938609377240949)
                ·
                  refine ⟨108897950244244629116339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1161578135938609377240949 108897950244244629116339)
                  ·
                    rfl

theorem cell22_954351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 2, 5].length) (baseStart_954351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_954351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_954351 prefixEnd_954351 := by exact prefixLift 954351
  have htrace : WordTrace (prefixWord ++ tailWord_954351) baseStart_954351 baseEnd_954351 := by
    simpa [prefixWord, tailWord_954351, baseEnd_954351] using wordTrace_append hprefix tailTrace_954351
  have hstable : (prefixWord ++ tailWord_954351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954351).length < 2 ^ (prefixWord ++ tailWord_954351).sum := by decide
  have hdescent : baseEnd_954351 < baseStart_954351 := by decide
  rcases family_descends (prefixWord ++ tailWord_954351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954374 : List Nat := [6, 2, 1, 2, 1, 1, 3, 6]
def baseStart_954374 : Nat := 118140960795 + 954374 * 2 ^ 59
def prefixEnd_954374 : Nat := 4983230072969 + 3 ^ 40 * 954374 * 2
def baseEnd_954374 : Nat := 36300191566974388224883

theorem tailTrace_954374 : CollatzResearch.WordTrace tailWord_954374 prefixEnd_954374 36300191566974388224883 := by
  unfold tailWord_954374
  simp only [CollatzResearch.WordTrace]
  refine ⟨1087777482639795842115193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23205919629648977965124117 1087777482639795842115193)
  ·
    refine ⟨815833111979846881586395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1087777482639795842115193 815833111979846881586395)
    ·
      refine ⟨1223749667969770322379593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 815833111979846881586395 1223749667969770322379593)
      ·
        refine ⟨917812250977327741784695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1223749667969770322379593 917812250977327741784695)
        ·
          refine ⟨1376718376465991612677043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 917812250977327741784695 1376718376465991612677043)
          ·
            refine ⟨2065077564698987419015565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1376718376465991612677043 2065077564698987419015565)
            ·
              refine ⟨774404086762120282130837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2065077564698987419015565 774404086762120282130837)
              ·
                refine ⟨36300191566974388224883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 774404086762120282130837 36300191566974388224883)
                ·
                  rfl

theorem cell22_954374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_954374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_954374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_954374 prefixEnd_954374 := by exact prefixLift 954374
  have htrace : WordTrace (prefixWord ++ tailWord_954374) baseStart_954374 baseEnd_954374 := by
    simpa [prefixWord, tailWord_954374, baseEnd_954374] using wordTrace_append hprefix tailTrace_954374
  have hstable : (prefixWord ++ tailWord_954374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954374).length < 2 ^ (prefixWord ++ tailWord_954374).sum := by decide
  have hdescent : baseEnd_954374 < baseStart_954374 := by decide
  rcases family_descends (prefixWord ++ tailWord_954374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954471 : List Nat := [1, 1, 5, 1, 1, 2, 2, 1, 2, 6]
def baseStart_954471 : Nat := 118140960795 + 954471 * 2 ^ 59
def prefixEnd_954471 : Nat := 4983230072969 + 3 ^ 40 * 954471 * 2
def baseEnd_954471 : Nat := 326734929185093574348649

theorem tailTrace_954471 : CollatzResearch.WordTrace tailWord_954471 prefixEnd_954471 326734929185093574348649 := by
  unfold tailWord_954471
  simp only [CollatzResearch.WordTrace]
  refine ⟨34812417325122052513967267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23208278216748035009311511 34812417325122052513967267)
  ·
    refine ⟨52218625987683078770950901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34812417325122052513967267 52218625987683078770950901)
    ·
      refine ⟨4895496186345288634776647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52218625987683078770950901 4895496186345288634776647)
      ·
        refine ⟨7343244279517932952164971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4895496186345288634776647 7343244279517932952164971)
        ·
          refine ⟨11014866419276899428247457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7343244279517932952164971 11014866419276899428247457)
          ·
            refine ⟨8261149814457674571185593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11014866419276899428247457 8261149814457674571185593)
            ·
              refine ⟨6195862360843255928389195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8261149814457674571185593 6195862360843255928389195)
              ·
                refine ⟨9293793541264883892583793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6195862360843255928389195 9293793541264883892583793)
                ·
                  refine ⟨6970345155948662919437845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9293793541264883892583793 6970345155948662919437845)
                  ·
                    refine ⟨326734929185093574348649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6970345155948662919437845 326734929185093574348649)
                    ·
                      rfl

theorem cell22_954471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_954471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_954471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_954471 prefixEnd_954471 := by exact prefixLift 954471
  have htrace : WordTrace (prefixWord ++ tailWord_954471) baseStart_954471 baseEnd_954471 := by
    simpa [prefixWord, tailWord_954471, baseEnd_954471] using wordTrace_append hprefix tailTrace_954471
  have hstable : (prefixWord ++ tailWord_954471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954471).length < 2 ^ (prefixWord ++ tailWord_954471).sum := by decide
  have hdescent : baseEnd_954471 < baseStart_954471 := by decide
  rcases family_descends (prefixWord ++ tailWord_954471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954520 : List Nat := [2, 1, 2, 4, 3, 1, 2, 2, 5]
def baseStart_954520 : Nat := 118140960795 + 954520 * 2 ^ 59
def prefixEnd_954520 : Nat := 4983230072969 + 3 ^ 40 * 954520 * 2
def baseEnd_954520 : Nat := 108917234295491259957833

theorem tailTrace_954520 : CollatzResearch.WordTrace tailWord_954520 prefixEnd_954520 108917234295491259957833 := by
  unfold tailWord_954520
  simp only [CollatzResearch.WordTrace]
  refine ⟨17407102250972266941250507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23209469667963022588334009 17407102250972266941250507)
  ·
    refine ⟨26110653376458400411875761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17407102250972266941250507 26110653376458400411875761)
    ·
      refine ⟨19582990032343800308906821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26110653376458400411875761 19582990032343800308906821)
      ·
        refine ⟨3671810631064462557920029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19582990032343800308906821 3671810631064462557920029)
        ·
          refine ⟨1376928986649173459220011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3671810631064462557920029 1376928986649173459220011)
          ·
            refine ⟨2065393479973760188830017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1376928986649173459220011 2065393479973760188830017)
            ·
              refine ⟨1549045109980320141622513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2065393479973760188830017 1549045109980320141622513)
              ·
                refine ⟨1161783832485240106216885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1549045109980320141622513 1161783832485240106216885)
                ·
                  refine ⟨108917234295491259957833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1161783832485240106216885 108917234295491259957833)
                  ·
                    rfl

theorem cell22_954520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 2, 5].length) (baseStart_954520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_954520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_954520 prefixEnd_954520 := by exact prefixLift 954520
  have htrace : WordTrace (prefixWord ++ tailWord_954520) baseStart_954520 baseEnd_954520 := by
    simpa [prefixWord, tailWord_954520, baseEnd_954520] using wordTrace_append hprefix tailTrace_954520
  have hstable : (prefixWord ++ tailWord_954520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954520).length < 2 ^ (prefixWord ++ tailWord_954520).sum := by decide
  have hdescent : baseEnd_954520 < baseStart_954520 := by decide
  rcases family_descends (prefixWord ++ tailWord_954520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954535 : List Nat := [1, 1, 6, 2, 2, 1, 1, 1, 2, 5]
def baseStart_954535 : Nat := 118140960795 + 954535 * 2 ^ 59
def prefixEnd_954535 : Nat := 4983230072969 + 3 ^ 40 * 954535 * 2
def baseEnd_954535 : Nat := 326756837693018740748453

theorem tailTrace_954535 : CollatzResearch.WordTrace tailWord_954535 prefixEnd_954535 326756837693018740748453 := by
  unfold tailWord_954535
  simp only [CollatzResearch.WordTrace]
  refine ⟨34814751596890191444297059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23209834397926794296198039 34814751596890191444297059)
  ·
    refine ⟨52222127395335287166445589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34814751596890191444297059 52222127395335287166445589)
    ·
      refine ⟨2447912221656341585927137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 52222127395335287166445589 2447912221656341585927137)
      ·
        refine ⟨1835934166242256189445353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2447912221656341585927137 1835934166242256189445353)
        ·
          refine ⟨1376950624681692142084015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1835934166242256189445353 1376950624681692142084015)
          ·
            refine ⟨2065425937022538213126023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1376950624681692142084015 2065425937022538213126023)
            ·
              refine ⟨3098138905533807319689035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2065425937022538213126023 3098138905533807319689035)
              ·
                refine ⟨4647208358300710979533553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3098138905533807319689035 4647208358300710979533553)
                ·
                  refine ⟨3485406268725533234650165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4647208358300710979533553 3485406268725533234650165)
                  ·
                    refine ⟨326756837693018740748453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3485406268725533234650165 326756837693018740748453)
                    ·
                      rfl

theorem cell22_954535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_954535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_954535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_954535 prefixEnd_954535 := by exact prefixLift 954535
  have htrace : WordTrace (prefixWord ++ tailWord_954535) baseStart_954535 baseEnd_954535 := by
    simpa [prefixWord, tailWord_954535, baseEnd_954535] using wordTrace_append hprefix tailTrace_954535
  have hstable : (prefixWord ++ tailWord_954535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954535).length < 2 ^ (prefixWord ++ tailWord_954535).sum := by decide
  have hdescent : baseEnd_954535 < baseStart_954535 := by decide
  rcases family_descends (prefixWord ++ tailWord_954535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954582 : List Nat := [5, 2, 1, 2, 1, 2, 2, 1, 6]
def baseStart_954582 : Nat := 118140960795 + 954582 * 2 ^ 59
def prefixEnd_954582 : Nat := 4983230072969 + 3 ^ 40 * 954582 * 2
def baseEnd_954582 : Nat := 108924308917842094941103

theorem tailTrace_954582 : CollatzResearch.WordTrace tailWord_954582 prefixEnd_954582 108924308917842094941103 := by
  unfold tailWord_954582
  simp only [CollatzResearch.WordTrace]
  refine ⟨2176029114232494904453625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23210977218479945647505333 2176029114232494904453625)
  ·
    refine ⟨1632021835674371178340219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2176029114232494904453625 1632021835674371178340219)
    ·
      refine ⟨2448032753511556767510329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1632021835674371178340219 2448032753511556767510329)
      ·
        refine ⟨1836024565133667575632747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2448032753511556767510329 1836024565133667575632747)
        ·
          refine ⟨2754036847700501363449121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1836024565133667575632747 2754036847700501363449121)
          ·
            refine ⟨2065527635775376022586841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2754036847700501363449121 2065527635775376022586841)
            ·
              refine ⟨1549145726831532016940131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2065527635775376022586841 1549145726831532016940131)
              ·
                refine ⟨2323718590247298025410197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1549145726831532016940131 2323718590247298025410197)
                ·
                  refine ⟨108924308917842094941103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2323718590247298025410197 108924308917842094941103)
                  ·
                    rfl

theorem cell22_954582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_954582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_954582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_954582 prefixEnd_954582 := by exact prefixLift 954582
  have htrace : WordTrace (prefixWord ++ tailWord_954582) baseStart_954582 baseEnd_954582 := by
    simpa [prefixWord, tailWord_954582, baseEnd_954582] using wordTrace_append hprefix tailTrace_954582
  have hstable : (prefixWord ++ tailWord_954582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954582).length < 2 ^ (prefixWord ++ tailWord_954582).sum := by decide
  have hdescent : baseEnd_954582 < baseStart_954582 := by decide
  rcases family_descends (prefixWord ++ tailWord_954582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954610 : List Nat := [3, 2, 1, 3, 2, 1, 4, 6]
def baseStart_954610 : Nat := 118140960795 + 954610 * 2 ^ 59
def prefixEnd_954610 : Nat := 4983230072969 + 3 ^ 40 * 954610 * 2
def baseEnd_954610 : Nat := 36309167969527060569247

theorem tailTrace_954610 : CollatzResearch.WordTrace tailWord_954610 prefixEnd_954610 36309167969527060569247 := by
  unfold tailWord_954610
  simp only [CollatzResearch.WordTrace]
  refine ⟨8704371767904619813319321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23211658047745652835518189 8704371767904619813319321)
  ·
    refine ⟨6528278825928464859989491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8704371767904619813319321 6528278825928464859989491)
    ·
      refine ⟨9792418238892697289984237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6528278825928464859989491 9792418238892697289984237)
      ·
        refine ⟨3672156839584761483744089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9792418238892697289984237 3672156839584761483744089)
        ·
          refine ⟨2754117629688571112808067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3672156839584761483744089 2754117629688571112808067)
          ·
            refine ⟨4131176444532856669212101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2754117629688571112808067 4131176444532856669212101)
            ·
              refine ⟨774595583349910625477269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4131176444532856669212101 774595583349910625477269)
              ·
                refine ⟨36309167969527060569247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 774595583349910625477269 36309167969527060569247)
                ·
                  rfl

theorem cell22_954610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 6].length) (baseStart_954610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_954610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_954610 prefixEnd_954610 := by exact prefixLift 954610
  have htrace : WordTrace (prefixWord ++ tailWord_954610) baseStart_954610 baseEnd_954610 := by
    simpa [prefixWord, tailWord_954610, baseEnd_954610] using wordTrace_append hprefix tailTrace_954610
  have hstable : (prefixWord ++ tailWord_954610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954610).length < 2 ^ (prefixWord ++ tailWord_954610).sum := by decide
  have hdescent : baseEnd_954610 < baseStart_954610 := by decide
  rcases family_descends (prefixWord ++ tailWord_954610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954638 : List Nat := [4, 1, 1, 2, 1, 2, 1, 3, 7]
def baseStart_954638 : Nat := 118140960795 + 954638 * 2 ^ 59
def prefixEnd_954638 : Nat := 4983230072969 + 3 ^ 40 * 954638 * 2
def baseEnd_954638 : Nat := 108930698899320268474379

theorem tailTrace_954638 : CollatzResearch.WordTrace tailWord_954638 prefixEnd_954638 108930698899320268474379 := by
  unfold tailWord_954638
  simp only [CollatzResearch.WordTrace]
  refine ⟨4352313539439630004412071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23212338877011360023531045 4352313539439630004412071)
  ·
    refine ⟨6528470309159445006618107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4352313539439630004412071 6528470309159445006618107)
    ·
      refine ⟨9792705463739167509927161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6528470309159445006618107 9792705463739167509927161)
      ·
        refine ⟨7344529097804375632445371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9792705463739167509927161 7344529097804375632445371)
        ·
          refine ⟨11016793646706563448668057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7344529097804375632445371 11016793646706563448668057)
          ·
            refine ⟨8262595235029922586501043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11016793646706563448668057 8262595235029922586501043)
            ·
              refine ⟨12393892852544883879751565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8262595235029922586501043 12393892852544883879751565)
              ·
                refine ⟨4647709819704331454906837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12393892852544883879751565 4647709819704331454906837)
                ·
                  refine ⟨108930698899320268474379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4647709819704331454906837 108930698899320268474379)
                  ·
                    rfl

theorem cell22_954638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 7].length) (baseStart_954638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_954638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_954638 prefixEnd_954638 := by exact prefixLift 954638
  have htrace : WordTrace (prefixWord ++ tailWord_954638) baseStart_954638 baseEnd_954638 := by
    simpa [prefixWord, tailWord_954638, baseEnd_954638] using wordTrace_append hprefix tailTrace_954638
  have hstable : (prefixWord ++ tailWord_954638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954638).length < 2 ^ (prefixWord ++ tailWord_954638).sum := by decide
  have hdescent : baseEnd_954638 < baseStart_954638 := by decide
  rcases family_descends (prefixWord ++ tailWord_954638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954655 : List Nat := [1, 1, 2, 4, 3, 2, 1, 3, 5]
def baseStart_954655 : Nat := 118140960795 + 954655 * 2 ^ 59
def prefixEnd_954655 : Nat := 4983230072969 + 3 ^ 40 * 954655 * 2
def baseEnd_954655 : Nat := 108932638715126142582695

theorem tailTrace_954655 : CollatzResearch.WordTrace tailWord_954655 prefixEnd_954655 108932638715126142582695 := by
  unfold tailWord_954655
  simp only [CollatzResearch.WordTrace]
  refine ⟨34819128356455451938665419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23212752237636967959110279 34819128356455451938665419)
  ·
    refine ⟨52228692534683177907998129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34819128356455451938665419 52228692534683177907998129)
    ·
      refine ⟨39171519401012383430998597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52228692534683177907998129 39171519401012383430998597)
      ·
        refine ⟨7344659887689821893312237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39171519401012383430998597 7344659887689821893312237)
        ·
          refine ⟨2754247457883683209992089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7344659887689821893312237 2754247457883683209992089)
          ·
            refine ⟨2065685593412762407494067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2754247457883683209992089 2065685593412762407494067)
            ·
              refine ⟨3098528390119143611241101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2065685593412762407494067 3098528390119143611241101)
              ·
                refine ⟨1161948146294678854215413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3098528390119143611241101 1161948146294678854215413)
                ·
                  refine ⟨108932638715126142582695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1161948146294678854215413 108932638715126142582695)
                  ·
                    rfl

theorem cell22_954655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 3, 5].length) (baseStart_954655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_954655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_954655 prefixEnd_954655 := by exact prefixLift 954655
  have htrace : WordTrace (prefixWord ++ tailWord_954655) baseStart_954655 baseEnd_954655 := by
    simpa [prefixWord, tailWord_954655, baseEnd_954655] using wordTrace_append hprefix tailTrace_954655
  have hstable : (prefixWord ++ tailWord_954655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954655).length < 2 ^ (prefixWord ++ tailWord_954655).sum := by decide
  have hdescent : baseEnd_954655 < baseStart_954655 := by decide
  rcases family_descends (prefixWord ++ tailWord_954655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954713 : List Nat := [1, 2, 1, 2, 2, 2, 1, 4, 1, 6]
def baseStart_954713 : Nat := 118140960795 + 954713 * 2 ^ 59
def prefixEnd_954713 : Nat := 4983230072969 + 3 ^ 40 * 954713 * 2
def baseEnd_954713 : Nat := 326817770730685609797907

theorem tailTrace_954713 : CollatzResearch.WordTrace tailWord_954713 prefixEnd_954713 326817770730685609797907 := by
  unfold tailWord_954713
  simp only [CollatzResearch.WordTrace]
  refine ⟨34821243790245327844276793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23214162526830218562851195 34821243790245327844276793)
  ·
    refine ⟨26115932842683995883207595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34821243790245327844276793 26115932842683995883207595)
    ·
      refine ⟨39173899264025993824811393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26115932842683995883207595 39173899264025993824811393)
      ·
        refine ⟨29380424448019495368608545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39173899264025993824811393 29380424448019495368608545)
        ·
          refine ⟨22035318336014621526456409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29380424448019495368608545 22035318336014621526456409)
          ·
            refine ⟨16526488752010966144842307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22035318336014621526456409 16526488752010966144842307)
            ·
              refine ⟨24789733128016449217263461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16526488752010966144842307 24789733128016449217263461)
              ·
                refine ⟨4648074961503084228236899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24789733128016449217263461 4648074961503084228236899)
                ·
                  refine ⟨6972112442254626342355349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4648074961503084228236899 6972112442254626342355349)
                  ·
                    refine ⟨326817770730685609797907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6972112442254626342355349 326817770730685609797907)
                    ·
                      rfl

theorem cell22_954713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 6].length) (baseStart_954713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_954713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_954713 prefixEnd_954713 := by exact prefixLift 954713
  have htrace : WordTrace (prefixWord ++ tailWord_954713) baseStart_954713 baseEnd_954713 := by
    simpa [prefixWord, tailWord_954713, baseEnd_954713] using wordTrace_append hprefix tailTrace_954713
  have hstable : (prefixWord ++ tailWord_954713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954713).length < 2 ^ (prefixWord ++ tailWord_954713).sum := by decide
  have hdescent : baseEnd_954713 < baseStart_954713 := by decide
  rcases family_descends (prefixWord ++ tailWord_954713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954749 : List Nat := [1, 4, 1, 1, 2, 5, 1, 2, 2, 3]
def baseStart_954749 : Nat := 118140960795 + 954749 * 2 ^ 59
def prefixEnd_954749 : Nat := 4983230072969 + 3 ^ 40 * 954749 * 2
def baseEnd_954749 : Nat := 326830094266393515897797

theorem tailTrace_954749 : CollatzResearch.WordTrace tailWord_954749 prefixEnd_954749 326830094266393515897797 := by
  unfold tailWord_954749
  simp only [CollatzResearch.WordTrace]
  refine ⟨34822556818114905992587301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23215037878743270661724867 34822556818114905992587301)
  ·
    refine ⟨6529229403396544873610119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34822556818114905992587301 6529229403396544873610119)
    ·
      refine ⟨9793844105094817310415179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6529229403396544873610119 9793844105094817310415179)
      ·
        refine ⟨14690766157642225965622769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9793844105094817310415179 14690766157642225965622769)
        ·
          refine ⟨11018074618231669474217077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14690766157642225965622769 11018074618231669474217077)
          ·
            refine ⟨1032944495459219013207851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11018074618231669474217077 1032944495459219013207851)
            ·
              refine ⟨1549416743188828519811777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1032944495459219013207851 1549416743188828519811777)
              ·
                refine ⟨1162062557391621389858833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1549416743188828519811777 1162062557391621389858833)
                ·
                  refine ⟨871546918043716042394125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1162062557391621389858833 871546918043716042394125)
                  ·
                    refine ⟨326830094266393515897797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 871546918043716042394125 326830094266393515897797)
                    ·
                      rfl

theorem cell22_954749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 2, 2, 3].length) (baseStart_954749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_954749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_954749 prefixEnd_954749 := by exact prefixLift 954749
  have htrace : WordTrace (prefixWord ++ tailWord_954749) baseStart_954749 baseEnd_954749 := by
    simpa [prefixWord, tailWord_954749, baseEnd_954749] using wordTrace_append hprefix tailTrace_954749
  have hstable : (prefixWord ++ tailWord_954749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954749).length < 2 ^ (prefixWord ++ tailWord_954749).sum := by decide
  have hdescent : baseEnd_954749 < baseStart_954749 := by decide
  rcases family_descends (prefixWord ++ tailWord_954749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954766 : List Nat := [4, 1, 1, 4, 1, 2, 3, 1, 2, 3]
def baseStart_954766 : Nat := 118140960795 + 954766 * 2 ^ 59
def prefixEnd_954766 : Nat := 4983230072969 + 3 ^ 40 * 954766 * 2
def baseEnd_954766 : Nat := 326835913713811138222745

theorem tailTrace_954766 : CollatzResearch.WordTrace tailWord_954766 prefixEnd_954766 326835913713811138222745 := by
  unfold tailWord_954766
  simp only [CollatzResearch.WordTrace]
  refine ⟨4352897107381664736994519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23215451239368878597304101 4352897107381664736994519)
  ·
    refine ⟨6529345661072497105491779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4352897107381664736994519 6529345661072497105491779)
    ·
      refine ⟨9794018491608745658237669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6529345661072497105491779 9794018491608745658237669)
      ·
        refine ⟨1836378467176639810919563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9794018491608745658237669 1836378467176639810919563)
        ·
          refine ⟨2754567700764959716379345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1836378467176639810919563 2754567700764959716379345)
          ·
            refine ⟨2065925775573719787284509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2754567700764959716379345 2065925775573719787284509)
            ·
              refine ⟨774722165840144920231691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2065925775573719787284509 774722165840144920231691)
              ·
                refine ⟨1162083248760217380347537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 774722165840144920231691 1162083248760217380347537)
                ·
                  refine ⟨871562436570163035260653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1162083248760217380347537 871562436570163035260653)
                  ·
                    refine ⟨326835913713811138222745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 871562436570163035260653 326835913713811138222745)
                    ·
                      rfl

theorem cell22_954766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 1, 2, 3].length) (baseStart_954766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_954766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_954766 prefixEnd_954766 := by exact prefixLift 954766
  have htrace : WordTrace (prefixWord ++ tailWord_954766) baseStart_954766 baseEnd_954766 := by
    simpa [prefixWord, tailWord_954766, baseEnd_954766] using wordTrace_append hprefix tailTrace_954766
  have hstable : (prefixWord ++ tailWord_954766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954766).length < 2 ^ (prefixWord ++ tailWord_954766).sum := by decide
  have hdescent : baseEnd_954766 < baseStart_954766 := by decide
  rcases family_descends (prefixWord ++ tailWord_954766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954817 : List Nat := [1, 2, 7, 1, 2, 1, 2, 1, 2, 3]
def baseStart_954817 : Nat := 118140960795 + 954817 * 2 ^ 59
def prefixEnd_954817 : Nat := 4983230072969 + 3 ^ 40 * 954817 * 2
def baseEnd_954817 : Nat := 326853372056064005197589

theorem tailTrace_954817 : CollatzResearch.WordTrace tailWord_954817 prefixEnd_954817 326853372056064005197589 := by
  unfold tailWord_954817
  simp only [CollatzResearch.WordTrace]
  refine ⟨34825036981868553606062705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23216691321245702404041803 34825036981868553606062705)
  ·
    refine ⟨26118777736401415204547029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34825036981868553606062705 26118777736401415204547029)
    ·
      refine ⟨612158853196908168856571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 26118777736401415204547029 612158853196908168856571)
      ·
        refine ⟨918238279795362253284857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 612158853196908168856571 918238279795362253284857)
        ·
          refine ⟨688678709846521689963643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 918238279795362253284857 688678709846521689963643)
          ·
            refine ⟨1033018064769782534945465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 688678709846521689963643 1033018064769782534945465)
            ·
              refine ⟨774763548577336901209099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1033018064769782534945465 774763548577336901209099)
              ·
                refine ⟨1162145322866005351813649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 774763548577336901209099 1162145322866005351813649)
                ·
                  refine ⟨871608992149504013860237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1162145322866005351813649 871608992149504013860237)
                  ·
                    refine ⟨326853372056064005197589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 871608992149504013860237 326853372056064005197589)
                    ·
                      rfl

theorem cell22_954817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_954817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_954817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_954817 prefixEnd_954817 := by exact prefixLift 954817
  have htrace : WordTrace (prefixWord ++ tailWord_954817) baseStart_954817 baseEnd_954817 := by
    simpa [prefixWord, tailWord_954817, baseEnd_954817] using wordTrace_append hprefix tailTrace_954817
  have hstable : (prefixWord ++ tailWord_954817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954817).length < 2 ^ (prefixWord ++ tailWord_954817).sum := by decide
  have hdescent : baseEnd_954817 < baseStart_954817 := by decide
  rcases family_descends (prefixWord ++ tailWord_954817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954824 : List Nat := [2, 1, 3, 1, 3, 4, 2, 1, 5]
def baseStart_954824 : Nat := 118140960795 + 954824 * 2 ^ 59
def prefixEnd_954824 : Nat := 4983230072969 + 3 ^ 40 * 954824 * 2
def baseEnd_954824 : Nat := 108951922766372773424189

theorem tailTrace_954824 : CollatzResearch.WordTrace tailWord_954824 prefixEnd_954824 108951922766372773424189 := by
  unfold tailWord_954824
  simp only [CollatzResearch.WordTrace]
  refine ⟨17412646146421596900783763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23216861528562129201045017 17412646146421596900783763)
  ·
    refine ⟨26118969219632395351175645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17412646146421596900783763 26118969219632395351175645)
    ·
      refine ⟨9794613457362148256690867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26118969219632395351175645 9794613457362148256690867)
      ·
        refine ⟨14691920186043222385036301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9794613457362148256690867 14691920186043222385036301)
        ·
          refine ⟨5509470069766208394388613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14691920186043222385036301 5509470069766208394388613)
          ·
            refine ⟨1033025638081164073947865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5509470069766208394388613 1033025638081164073947865)
            ·
              refine ⟨774769228560873055460899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1033025638081164073947865 774769228560873055460899)
              ·
                refine ⟨1162153842841309583191349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 774769228560873055460899 1162153842841309583191349)
                ·
                  refine ⟨108951922766372773424189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1162153842841309583191349 108951922766372773424189)
                  ·
                    rfl

theorem cell22_954824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 1, 5].length) (baseStart_954824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_954824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_954824 prefixEnd_954824 := by exact prefixLift 954824
  have htrace : WordTrace (prefixWord ++ tailWord_954824) baseStart_954824 baseEnd_954824 := by
    simpa [prefixWord, tailWord_954824, baseEnd_954824] using wordTrace_append hprefix tailTrace_954824
  have hstable : (prefixWord ++ tailWord_954824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954824).length < 2 ^ (prefixWord ++ tailWord_954824).sum := by decide
  have hdescent : baseEnd_954824 < baseStart_954824 := by decide
  rcases family_descends (prefixWord ++ tailWord_954824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954837 : List Nat := [1, 3, 2, 3, 1, 3, 1, 1, 3, 4]
def baseStart_954837 : Nat := 118140960795 + 954837 * 2 ^ 59
def prefixEnd_954837 : Nat := 4983230072969 + 3 ^ 40 * 954837 * 2
def baseEnd_954837 : Nat := 326860218464790619697527

theorem tailTrace_954837 : CollatzResearch.WordTrace tailWord_954837 prefixEnd_954837 326860218464790619697527 := by
  unfold tailWord_954837
  simp only [CollatzResearch.WordTrace]
  refine ⟨34825766441796097021790765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23217177627864064681193843 34825766441796097021790765)
  ·
    refine ⟨13059662415673536383171537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34825766441796097021790765 13059662415673536383171537)
    ·
      refine ⟨9794746811755152287378653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13059662415673536383171537 9794746811755152287378653)
      ·
        refine ⟨3673030054408182107766995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9794746811755152287378653 3673030054408182107766995)
        ·
          refine ⟨5509545081612273161650493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3673030054408182107766995 5509545081612273161650493)
          ·
            refine ⟨2066079405604602435618935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5509545081612273161650493 2066079405604602435618935)
            ·
              refine ⟨3099119108406903653428403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2066079405604602435618935 3099119108406903653428403)
              ·
                refine ⟨4648678662610355480142605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3099119108406903653428403 4648678662610355480142605)
                ·
                  refine ⟨1743254498478883305053477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4648678662610355480142605 1743254498478883305053477)
                  ·
                    refine ⟨326860218464790619697527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1743254498478883305053477 326860218464790619697527)
                    ·
                      rfl

theorem cell22_954837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_954837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_954837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_954837 prefixEnd_954837 := by exact prefixLift 954837
  have htrace : WordTrace (prefixWord ++ tailWord_954837) baseStart_954837 baseEnd_954837 := by
    simpa [prefixWord, tailWord_954837, baseEnd_954837] using wordTrace_append hprefix tailTrace_954837
  have hstable : (prefixWord ++ tailWord_954837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954837).length < 2 ^ (prefixWord ++ tailWord_954837).sum := by decide
  have hdescent : baseEnd_954837 < baseStart_954837 := by decide
  rcases family_descends (prefixWord ++ tailWord_954837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954884 : List Nat := [2, 3, 2, 3, 1, 2, 2, 1, 1, 5]
def baseStart_954884 : Nat := 118140960795 + 954884 * 2 ^ 59
def prefixEnd_954884 : Nat := 4983230072969 + 3 ^ 40 * 954884 * 2
def baseEnd_954884 : Nat := 326876307525298163772383

theorem tailTrace_954884 : CollatzResearch.WordTrace tailWord_954884 prefixEnd_954884 326876307525298163772383 := by
  unfold tailWord_954884
  simp only [CollatzResearch.WordTrace]
  refine ⟨17413740336312912024375853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23218320448417216032501137 17413740336312912024375853)
  ·
    refine ⟨6530152626117342009140945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17413740336312912024375853 6530152626117342009140945)
    ·
      refine ⟨4897614469588006506855709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6530152626117342009140945 4897614469588006506855709)
      ·
        refine ⟨1836605426095502440070891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4897614469588006506855709 1836605426095502440070891)
        ·
          refine ⟨2754908139143253660106337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1836605426095502440070891 2754908139143253660106337)
          ·
            refine ⟨2066181104357440245079753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2754908139143253660106337 2066181104357440245079753)
            ·
              refine ⟨1549635828268080183809815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2066181104357440245079753 1549635828268080183809815)
              ·
                refine ⟨2324453742402120275714723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1549635828268080183809815 2324453742402120275714723)
                ·
                  refine ⟨3486680613603180413572085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2324453742402120275714723 3486680613603180413572085)
                  ·
                    refine ⟨326876307525298163772383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3486680613603180413572085 326876307525298163772383)
                    ·
                      rfl

theorem cell22_954884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_954884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_954884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_954884 prefixEnd_954884 := by exact prefixLift 954884
  have htrace : WordTrace (prefixWord ++ tailWord_954884) baseStart_954884 baseEnd_954884 := by
    simpa [prefixWord, tailWord_954884, baseEnd_954884] using wordTrace_append hprefix tailTrace_954884
  have hstable : (prefixWord ++ tailWord_954884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954884).length < 2 ^ (prefixWord ++ tailWord_954884).sum := by decide
  have hdescent : baseEnd_954884 < baseStart_954884 := by decide
  rcases family_descends (prefixWord ++ tailWord_954884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954886 : List Nat := [6, 2, 1, 1, 1, 1, 1, 1, 8]
def baseStart_954886 : Nat := 118140960795 + 954886 * 2 ^ 59
def prefixEnd_954886 : Nat := 4983230072969 + 3 ^ 40 * 954886 * 2
def baseEnd_954886 : Nat := 108958997388723608407459

theorem tailTrace_954886 : CollatzResearch.WordTrace tailWord_954886 prefixEnd_954886 108958997388723608407459 := by
  unfold tailWord_954886
  simp only [CollatzResearch.WordTrace]
  refine ⟨1088361050581830574697641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23218369079079052260216341 1088361050581830574697641)
  ·
    refine ⟨816270787936372931023231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1088361050581830574697641 816270787936372931023231)
    ·
      refine ⟨1224406181904559396534847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 816270787936372931023231 1224406181904559396534847)
      ·
        refine ⟨1836609272856839094802271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1224406181904559396534847 1836609272856839094802271)
        ·
          refine ⟨2754913909285258642203407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1836609272856839094802271 2754913909285258642203407)
          ·
            refine ⟨4132370863927887963305111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2754913909285258642203407 4132370863927887963305111)
            ·
              refine ⟨6198556295891831944957667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4132370863927887963305111 6198556295891831944957667)
              ·
                refine ⟨9297834443837747917436501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6198556295891831944957667 9297834443837747917436501)
                ·
                  refine ⟨108958997388723608407459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9297834443837747917436501 108958997388723608407459)
                  ·
                    rfl

theorem cell22_954886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_954886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_954886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_954886 prefixEnd_954886 := by exact prefixLift 954886
  have htrace : WordTrace (prefixWord ++ tailWord_954886) baseStart_954886 baseEnd_954886 := by
    simpa [prefixWord, tailWord_954886, baseEnd_954886] using wordTrace_append hprefix tailTrace_954886
  have hstable : (prefixWord ++ tailWord_954886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954886).length < 2 ^ (prefixWord ++ tailWord_954886).sum := by decide
  have hdescent : baseEnd_954886 < baseStart_954886 := by decide
  rcases family_descends (prefixWord ++ tailWord_954886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955036 : List Nat := [2, 2, 3, 2, 2, 1, 1, 4, 2, 3]
def baseStart_955036 : Nat := 118140960795 + 955036 * 2 ^ 59
def prefixEnd_955036 : Nat := 4983230072969 + 3 ^ 40 * 955036 * 2
def baseEnd_955036 : Nat := 326928340231620433971917

theorem tailTrace_955036 : CollatzResearch.WordTrace tailWord_955036 prefixEnd_955036 326928340231620433971917 := by
  unfold tailWord_955036
  simp only [CollatzResearch.WordTrace]
  refine ⟨17416512284037577004142481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23222016378716769338856641 17416512284037577004142481)
  ·
    refine ⟨13062384213028182753106861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17416512284037577004142481 13062384213028182753106861)
    ·
      refine ⟨4898394079885568532415073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13062384213028182753106861 4898394079885568532415073)
      ·
        refine ⟨3673795559914176399311305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4898394079885568532415073 3673795559914176399311305)
        ·
          refine ⟨2755346669935632299483479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3673795559914176399311305 2755346669935632299483479)
          ·
            refine ⟨4133020004903448449225219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2755346669935632299483479 4133020004903448449225219)
            ·
              refine ⟨6199530007355172673837829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4133020004903448449225219 6199530007355172673837829)
              ·
                refine ⟨1162411876379094876344593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6199530007355172673837829 1162411876379094876344593)
                ·
                  refine ⟨871808907284321157258445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1162411876379094876344593 871808907284321157258445)
                  ·
                    refine ⟨326928340231620433971917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 871808907284321157258445 326928340231620433971917)
                    ·
                      rfl

theorem cell22_955036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_955036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_955036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_955036 prefixEnd_955036 := by exact prefixLift 955036
  have htrace : WordTrace (prefixWord ++ tailWord_955036) baseStart_955036 baseEnd_955036 := by
    simpa [prefixWord, tailWord_955036, baseEnd_955036] using wordTrace_append hprefix tailTrace_955036
  have hstable : (prefixWord ++ tailWord_955036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955036).length < 2 ^ (prefixWord ++ tailWord_955036).sum := by decide
  have hdescent : baseEnd_955036 < baseStart_955036 := by decide
  rcases family_descends (prefixWord ++ tailWord_955036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955109 : List Nat := [1, 3, 1, 4, 1, 2, 2, 1, 2, 5]
def baseStart_955109 : Nat := 118140960795 + 955109 * 2 ^ 59
def prefixEnd_955109 : Nat := 4983230072969 + 3 ^ 40 * 955109 * 2
def baseEnd_955109 : Nat := 326953329623472576896693

theorem tailTrace_955109 : CollatzResearch.WordTrace tailWord_955109 prefixEnd_955109 326953329623472576896693 := by
  unfold tailWord_955109
  simp only [CollatzResearch.WordTrace]
  refine ⟨34835687096810687475692381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23223791397873791650461587 34835687096810687475692381)
  ·
    refine ⟨13063382661304007803384643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34835687096810687475692381 13063382661304007803384643)
    ·
      refine ⟨19595073991956011705076965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13063382661304007803384643 19595073991956011705076965)
      ·
        refine ⟨3674076373491752194701931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19595073991956011705076965 3674076373491752194701931)
        ·
          refine ⟨5511114560237628292052897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3674076373491752194701931 5511114560237628292052897)
          ·
            refine ⟨4133335920178221219039673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5511114560237628292052897 4133335920178221219039673)
            ·
              refine ⟨3100001940133665914279755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4133335920178221219039673 3100001940133665914279755)
              ·
                refine ⟨4650002910200498871419633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3100001940133665914279755 4650002910200498871419633)
                ·
                  refine ⟨3487502182650374153564725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4650002910200498871419633 3487502182650374153564725)
                  ·
                    refine ⟨326953329623472576896693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3487502182650374153564725 326953329623472576896693)
                    ·
                      rfl

theorem cell22_955109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 5].length) (baseStart_955109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_955109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_955109 prefixEnd_955109 := by exact prefixLift 955109
  have htrace : WordTrace (prefixWord ++ tailWord_955109) baseStart_955109 baseEnd_955109 := by
    simpa [prefixWord, tailWord_955109, baseEnd_955109] using wordTrace_append hprefix tailTrace_955109
  have hstable : (prefixWord ++ tailWord_955109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955109).length < 2 ^ (prefixWord ++ tailWord_955109).sum := by decide
  have hdescent : baseEnd_955109 < baseStart_955109 := by decide
  rcases family_descends (prefixWord ++ tailWord_955109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955152 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 1, 12]
def baseStart_955152 : Nat := 118140960795 + 955152 * 2 ^ 59
def prefixEnd_955152 : Nat := 4983230072969 + 3 ^ 40 * 955152 * 2
def baseEnd_955152 : Nat := 326968049402234798071561

theorem tailTrace_955152 : CollatzResearch.WordTrace tailWord_955152 prefixEnd_955152 326968049402234798071561 := by
  unfold tailWord_955152
  simp only [CollatzResearch.WordTrace]
  refine ⟨17418627717827452909753855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23224836957103270546338473 17418627717827452909753855)
  ·
    refine ⟨26127941576741179364630783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17418627717827452909753855 26127941576741179364630783)
    ·
      refine ⟨39191912365111769046946175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26127941576741179364630783 39191912365111769046946175)
      ·
        refine ⟨58787868547667653570419263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39191912365111769046946175 58787868547667653570419263)
        ·
          refine ⟨88181802821501480355628895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58787868547667653570419263 88181802821501480355628895)
          ·
            refine ⟨132272704232252220533443343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88181802821501480355628895 132272704232252220533443343)
            ·
              refine ⟨198409056348378330800165015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132272704232252220533443343 198409056348378330800165015)
              ·
                refine ⟨297613584522567496200247523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198409056348378330800165015 297613584522567496200247523)
                ·
                  refine ⟨446420376783851244300371285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 297613584522567496200247523 446420376783851244300371285)
                  ·
                    refine ⟨326968049402234798071561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 446420376783851244300371285 326968049402234798071561)
                    ·
                      rfl

theorem cell22_955152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 12].length) (baseStart_955152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_955152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_955152 prefixEnd_955152 := by exact prefixLift 955152
  have htrace : WordTrace (prefixWord ++ tailWord_955152) baseStart_955152 baseEnd_955152 := by
    simpa [prefixWord, tailWord_955152, baseEnd_955152] using wordTrace_append hprefix tailTrace_955152
  have hstable : (prefixWord ++ tailWord_955152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955152).length < 2 ^ (prefixWord ++ tailWord_955152).sum := by decide
  have hdescent : baseEnd_955152 < baseStart_955152 := by decide
  rcases family_descends (prefixWord ++ tailWord_955152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955169 : List Nat := [1, 2, 3, 2, 1, 2, 1, 2, 4, 4]
def baseStart_955169 : Nat := 118140960795 + 955169 * 2 ^ 59
def prefixEnd_955169 : Nat := 4983230072969 + 3 ^ 40 * 955169 * 2
def baseEnd_955169 : Nat := 326973868849652420396509

theorem tailTrace_955169 : CollatzResearch.WordTrace tailWord_955169 prefixEnd_955169 326973868849652420396509 := by
  unfold tailWord_955169
  simp only [CollatzResearch.WordTrace]
  refine ⟨34837875476593317722876561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23225250317728878481917707 34837875476593317722876561)
  ·
    refine ⟨26128406607444988292157421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34837875476593317722876561 26128406607444988292157421)
    ·
      refine ⟨9798152477791870609559033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26128406607444988292157421 9798152477791870609559033)
      ·
        refine ⟨7348614358343902957169275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9798152477791870609559033 7348614358343902957169275)
        ·
          refine ⟨11022921537515854435753913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7348614358343902957169275 11022921537515854435753913)
          ·
            refine ⟨8267191153136890826815435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11022921537515854435753913 8267191153136890826815435)
            ·
              refine ⟨12400786729705336240223153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8267191153136890826815435 12400786729705336240223153)
              ·
                refine ⟨9300590047279002180167365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12400786729705336240223153 9300590047279002180167365)
                ·
                  refine ⟨1743860633864812908781381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9300590047279002180167365 1743860633864812908781381)
                  ·
                    refine ⟨326973868849652420396509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1743860633864812908781381 326973868849652420396509)
                    ·
                      rfl

theorem cell22_955169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_955169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_955169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_955169 prefixEnd_955169 := by exact prefixLift 955169
  have htrace : WordTrace (prefixWord ++ tailWord_955169) baseStart_955169 baseEnd_955169 := by
    simpa [prefixWord, tailWord_955169, baseEnd_955169] using wordTrace_append hprefix tailTrace_955169
  have hstable : (prefixWord ++ tailWord_955169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955169).length < 2 ^ (prefixWord ++ tailWord_955169).sum := by decide
  have hdescent : baseEnd_955169 < baseStart_955169 := by decide
  rcases family_descends (prefixWord ++ tailWord_955169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955186 : List Nat := [3, 2, 1, 1, 3, 1, 4, 1, 2, 4]
def baseStart_955186 : Nat := 118140960795 + 955186 * 2 ^ 59
def prefixEnd_955186 : Nat := 4983230072969 + 3 ^ 40 * 955186 * 2
def baseEnd_955186 : Nat := 326979688297070042721457

theorem tailTrace_955186 : CollatzResearch.WordTrace tailWord_955186 prefixEnd_955186 326979688297070042721457 := by
  unfold tailWord_955186
  simp only [CollatzResearch.WordTrace]
  refine ⟨8709623879382932406561353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23225663678354486417496941 8709623879382932406561353)
  ·
    refine ⟨6532217909537199304921015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8709623879382932406561353 6532217909537199304921015)
    ·
      refine ⟨9798326864305798957381523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6532217909537199304921015 9798326864305798957381523)
      ·
        refine ⟨14697490296458698436072285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9798326864305798957381523 14697490296458698436072285)
        ·
          refine ⟨5511558861172011913527107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14697490296458698436072285 5511558861172011913527107)
          ·
            refine ⟨8267338291758017870290661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5511558861172011913527107 8267338291758017870290661)
            ·
              refine ⟨1550125929704628350679499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8267338291758017870290661 1550125929704628350679499)
              ·
                refine ⟨2325188894556942526019249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1550125929704628350679499 2325188894556942526019249)
                ·
                  refine ⟨1743891670917706894514437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2325188894556942526019249 1743891670917706894514437)
                  ·
                    refine ⟨326979688297070042721457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1743891670917706894514437 326979688297070042721457)
                    ·
                      rfl

theorem cell22_955186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_955186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_955186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_955186 prefixEnd_955186 := by exact prefixLift 955186
  have htrace : WordTrace (prefixWord ++ tailWord_955186) baseStart_955186 baseEnd_955186 := by
    simpa [prefixWord, tailWord_955186, baseEnd_955186] using wordTrace_append hprefix tailTrace_955186
  have hstable : (prefixWord ++ tailWord_955186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955186).length < 2 ^ (prefixWord ++ tailWord_955186).sum := by decide
  have hdescent : baseEnd_955186 < baseStart_955186 := by decide
  rcases family_descends (prefixWord ++ tailWord_955186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955188 : List Nat := [2, 5, 1, 1, 3, 1, 1, 2, 1, 5]
def baseStart_955188 : Nat := 118140960795 + 955188 * 2 ^ 59
def prefixEnd_955188 : Nat := 4983230072969 + 3 ^ 40 * 955188 * 2
def baseEnd_955188 : Nat := 326980372937942704171451

theorem tailTrace_955188 : CollatzResearch.WordTrace tailWord_955188 prefixEnd_955188 326980372937942704171451 := by
  unfold tailWord_955188
  simp only [CollatzResearch.WordTrace]
  refine ⟨17419284231762241983909109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23225712309016322645212145 17419284231762241983909109)
  ·
    refine ⟨1633057896727710185991479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17419284231762241983909109 1633057896727710185991479)
    ·
      refine ⟨2449586845091565278987219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1633057896727710185991479 2449586845091565278987219)
      ·
        refine ⟨3674380267637347918480829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2449586845091565278987219 3674380267637347918480829)
        ·
          refine ⟨1377892600364005469430311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3674380267637347918480829 1377892600364005469430311)
          ·
            refine ⟨2066838900546008204145467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1377892600364005469430311 2066838900546008204145467)
            ·
              refine ⟨3100258350819012306218201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2066838900546008204145467 3100258350819012306218201)
              ·
                refine ⟨2325193763114259229663651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3100258350819012306218201 2325193763114259229663651)
                ·
                  refine ⟨3487790644671388844495477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2325193763114259229663651 3487790644671388844495477)
                  ·
                    refine ⟨326980372937942704171451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3487790644671388844495477 326980372937942704171451)
                    ·
                      rfl

theorem cell22_955188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_955188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_955188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_955188 prefixEnd_955188 := by exact prefixLift 955188
  have htrace : WordTrace (prefixWord ++ tailWord_955188) baseStart_955188 baseEnd_955188 := by
    simpa [prefixWord, tailWord_955188, baseEnd_955188] using wordTrace_append hprefix tailTrace_955188
  have hstable : (prefixWord ++ tailWord_955188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955188).length < 2 ^ (prefixWord ++ tailWord_955188).sum := by decide
  have hdescent : baseEnd_955188 < baseStart_955188 := by decide
  rcases family_descends (prefixWord ++ tailWord_955188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955201 : List Nat := [1, 2, 5, 3, 1, 10]
def baseStart_955201 : Nat := 118140960795 + 955201 * 2 ^ 59
def prefixEnd_955201 : Nat := 4983230072969 + 3 ^ 40 * 955201 * 2
def baseEnd_955201 : Nat := 4036849667945864241931

theorem tailTrace_955201 : CollatzResearch.WordTrace tailWord_955201 prefixEnd_955201 4036849667945864241931 := by
  unfold tailWord_955201
  simp only [CollatzResearch.WordTrace]
  refine ⟨34839042612477387188041457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23226028408318258125360971 34839042612477387188041457)
  ·
    refine ⟨26129281959358040391031093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34839042612477387188041457 26129281959358040391031093)
    ·
      refine ⟨2449620183689816286659165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26129281959358040391031093 2449620183689816286659165)
      ·
        refine ⟨918607568883681107497187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2449620183689816286659165 918607568883681107497187)
        ·
          refine ⟨1377911353325521661245781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 918607568883681107497187 1377911353325521661245781)
          ·
            refine ⟨4036849667945864241931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1377911353325521661245781 4036849667945864241931)
            ·
              rfl

theorem cell22_955201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 10].length) (baseStart_955201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_955201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_955201 prefixEnd_955201 := by exact prefixLift 955201
  have htrace : WordTrace (prefixWord ++ tailWord_955201) baseStart_955201 baseEnd_955201 := by
    simpa [prefixWord, tailWord_955201, baseEnd_955201] using wordTrace_append hprefix tailTrace_955201
  have hstable : (prefixWord ++ tailWord_955201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955201).length < 2 ^ (prefixWord ++ tailWord_955201).sum := by decide
  have hdescent : baseEnd_955201 < baseStart_955201 := by decide
  rcases family_descends (prefixWord ++ tailWord_955201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955244 : List Nat := [2, 2, 1, 1, 4, 1, 1, 2, 1, 7]
def baseStart_955244 : Nat := 118140960795 + 955244 * 2 ^ 59
def prefixEnd_955244 : Nat := 4983230072969 + 3 ^ 40 * 955244 * 2
def baseEnd_955244 : Nat := 326999542882377224771279

theorem tailTrace_955244 : CollatzResearch.WordTrace tailWord_955244 prefixEnd_955244 326999542882377224771279 := by
  unfold tailWord_955244
  simp only [CollatzResearch.WordTrace]
  refine ⟨17420305475660802765928393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23227073967547737021237857 17420305475660802765928393)
  ·
    refine ⟨13065229106745602074446295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17420305475660802765928393 13065229106745602074446295)
    ·
      refine ⟨19597843660118403111669443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13065229106745602074446295 19597843660118403111669443)
      ·
        refine ⟨29396765490177604667504165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19597843660118403111669443 29396765490177604667504165)
        ·
          refine ⟨5511893529408300875157031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29396765490177604667504165 5511893529408300875157031)
          ·
            refine ⟨8267840294112451312735547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5511893529408300875157031 8267840294112451312735547)
            ·
              refine ⟨12401760441168676969103321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8267840294112451312735547 12401760441168676969103321)
              ·
                refine ⟨9301320330876507726827491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12401760441168676969103321 9301320330876507726827491)
                ·
                  refine ⟨13951980496314761590241237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9301320330876507726827491 13951980496314761590241237)
                  ·
                    refine ⟨326999542882377224771279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13951980496314761590241237 326999542882377224771279)
                    ·
                      rfl

theorem cell22_955244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 7].length) (baseStart_955244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_955244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_955244 prefixEnd_955244 := by exact prefixLift 955244
  have htrace : WordTrace (prefixWord ++ tailWord_955244) baseStart_955244 baseEnd_955244 := by
    simpa [prefixWord, tailWord_955244, baseEnd_955244] using wordTrace_append hprefix tailTrace_955244
  have hstable : (prefixWord ++ tailWord_955244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955244).length < 2 ^ (prefixWord ++ tailWord_955244).sum := by decide
  have hdescent : baseEnd_955244 < baseStart_955244 := by decide
  rcases family_descends (prefixWord ++ tailWord_955244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955293 : List Nat := [1, 4, 2, 1, 2, 1, 4, 2, 1, 4]
def baseStart_955293 : Nat := 118140960795 + 955293 * 2 ^ 59
def prefixEnd_955293 : Nat := 4983230072969 + 3 ^ 40 * 955293 * 2
def baseEnd_955293 : Nat := 327016316583757430296129

theorem tailTrace_955293 : CollatzResearch.WordTrace tailWord_955293 prefixEnd_955293 327016316583757430296129 := by
  unfold tailWord_955293
  simp only [CollatzResearch.WordTrace]
  refine ⟨34842398128144086900390533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23228265418762724600260355 34842398128144086900390533)
  ·
    refine ⟨6532949649027016293823225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34842398128144086900390533 6532949649027016293823225)
    ·
      refine ⟨4899712236770262220367419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6532949649027016293823225 4899712236770262220367419)
      ·
        refine ⟨7349568355155393330551129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4899712236770262220367419 7349568355155393330551129)
        ·
          refine ⟨5512176266366544997913347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7349568355155393330551129 5512176266366544997913347)
          ·
            refine ⟨8268264399549817496870021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5512176266366544997913347 8268264399549817496870021)
            ·
              refine ⟨1550299574915590780663129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8268264399549817496870021 1550299574915590780663129)
              ·
                refine ⟨1162724681186693085497347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1550299574915590780663129 1162724681186693085497347)
                ·
                  refine ⟨1744087021780039628246021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1162724681186693085497347 1744087021780039628246021)
                  ·
                    refine ⟨327016316583757430296129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1744087021780039628246021 327016316583757430296129)
                    ·
                      rfl

theorem cell22_955293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_955293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_955293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_955293 prefixEnd_955293 := by exact prefixLift 955293
  have htrace : WordTrace (prefixWord ++ tailWord_955293) baseStart_955293 baseEnd_955293 := by
    simpa [prefixWord, tailWord_955293, baseEnd_955293] using wordTrace_append hprefix tailTrace_955293
  have hstable : (prefixWord ++ tailWord_955293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955293).length < 2 ^ (prefixWord ++ tailWord_955293).sum := by decide
  have hdescent : baseEnd_955293 < baseStart_955293 := by decide
  rcases family_descends (prefixWord ++ tailWord_955293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955318 : List Nat := [5, 1, 4, 1, 1, 1, 3, 2, 1, 3]
def baseStart_955318 : Nat := 118140960795 + 955318 * 2 ^ 59
def prefixEnd_955318 : Nat := 4983230072969 + 3 ^ 40 * 955318 * 2
def baseEnd_955318 : Nat := 327024874594665698421053

theorem tailTrace_955318 : CollatzResearch.WordTrace tailWord_955318 prefixEnd_955318 327024874594665698421053 := by
  unfold tailWord_955318
  simp only [CollatzResearch.WordTrace]
  refine ⟨2177706872065844760628163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23228873302035677446700405 2177706872065844760628163)
  ·
    refine ⟨3266560308098767140942245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2177706872065844760628163 3266560308098767140942245)
    ·
      refine ⟨612480057768518838926671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3266560308098767140942245 612480057768518838926671)
      ·
        refine ⟨918720086652778258390007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 612480057768518838926671 918720086652778258390007)
        ·
          refine ⟨1378080129979167387585011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 918720086652778258390007 1378080129979167387585011)
          ·
            refine ⟨2067120194968751081377517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1378080129979167387585011 2067120194968751081377517)
            ·
              refine ⟨775170073113281655516569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2067120194968751081377517 775170073113281655516569)
              ·
                refine ⟨581377554834961241637427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 775170073113281655516569 581377554834961241637427)
                ·
                  refine ⟨872066332252441862456141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 581377554834961241637427 872066332252441862456141)
                  ·
                    refine ⟨327024874594665698421053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 872066332252441862456141 327024874594665698421053)
                    ·
                      rfl

theorem cell22_955318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_955318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_955318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_955318 prefixEnd_955318 := by exact prefixLift 955318
  have htrace : WordTrace (prefixWord ++ tailWord_955318) baseStart_955318 baseEnd_955318 := by
    simpa [prefixWord, tailWord_955318, baseEnd_955318] using wordTrace_append hprefix tailTrace_955318
  have hstable : (prefixWord ++ tailWord_955318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955318).length < 2 ^ (prefixWord ++ tailWord_955318).sum := by decide
  have hdescent : baseEnd_955318 < baseStart_955318 := by decide
  rcases family_descends (prefixWord ++ tailWord_955318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955319 : List Nat := [1, 1, 3, 1, 3, 1, 12]
def baseStart_955319 : Nat := 118140960795 + 955319 * 2 ^ 59
def prefixEnd_955319 : Nat := 4983230072969 + 3 ^ 40 * 955319 * 2
def baseEnd_955319 : Nat := 12112045070929704783187

theorem tailTrace_955319 : CollatzResearch.WordTrace tailWord_955319 prefixEnd_955319 12112045070929704783187 := by
  unfold tailWord_955319
  simp only [CollatzResearch.WordTrace]
  refine ⟨34843346426049893340837011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23228897617366595560558007 34843346426049893340837011)
  ·
    refine ⟨52265019639074840011255517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34843346426049893340837011 52265019639074840011255517)
    ·
      refine ⟨19599382364653065004220819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52265019639074840011255517 19599382364653065004220819)
      ·
        refine ⟨29399073546979597506331229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19599382364653065004220819 29399073546979597506331229)
        ·
          refine ⟨11024652580117349064874211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29399073546979597506331229 11024652580117349064874211)
          ·
            refine ⟨16536978870176023597311317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11024652580117349064874211 16536978870176023597311317)
            ·
              refine ⟨12112045070929704783187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 16536978870176023597311317 12112045070929704783187)
              ·
                rfl

theorem cell22_955319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 12].length) (baseStart_955319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_955319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_955319 prefixEnd_955319 := by exact prefixLift 955319
  have htrace : WordTrace (prefixWord ++ tailWord_955319) baseStart_955319 baseEnd_955319 := by
    simpa [prefixWord, tailWord_955319, baseEnd_955319] using wordTrace_append hprefix tailTrace_955319
  have hstable : (prefixWord ++ tailWord_955319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955319).length < 2 ^ (prefixWord ++ tailWord_955319).sum := by decide
  have hdescent : baseEnd_955319 < baseStart_955319 := by decide
  rcases family_descends (prefixWord ++ tailWord_955319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955321 : List Nat := [1, 2, 1, 4, 2, 2, 1, 1, 4, 4]
def baseStart_955321 : Nat := 118140960795 + 955321 * 2 ^ 59
def prefixEnd_955321 : Nat := 4983230072969 + 3 ^ 40 * 955321 * 2
def baseEnd_955321 : Nat := 327025901555974690596043

theorem tailTrace_955321 : CollatzResearch.WordTrace tailWord_955321 prefixEnd_955321 327025901555974690596043 := by
  unfold tailWord_955321
  simp only [CollatzResearch.WordTrace]
  refine ⟨34843419372042647682409817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23228946248028431788273211 34843419372042647682409817)
  ·
    refine ⟨26132564529031985761807363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34843419372042647682409817 26132564529031985761807363)
    ·
      refine ⟨39198846793547978642711045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26132564529031985761807363 39198846793547978642711045)
      ·
        refine ⟨7349783773790245995508321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39198846793547978642711045 7349783773790245995508321)
        ·
          refine ⟨5512337830342684496631241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7349783773790245995508321 5512337830342684496631241)
          ·
            refine ⟨4134253372757013372473431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5512337830342684496631241 4134253372757013372473431)
            ·
              refine ⟨6201380059135520058710147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4134253372757013372473431 6201380059135520058710147)
              ·
                refine ⟨9302070088703280088065221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6201380059135520058710147 9302070088703280088065221)
                ·
                  refine ⟨1744138141631865016512229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9302070088703280088065221 1744138141631865016512229)
                  ·
                    refine ⟨327025901555974690596043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1744138141631865016512229 327025901555974690596043)
                    ·
                      rfl

theorem cell22_955321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 4, 4].length) (baseStart_955321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_955321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_955321 prefixEnd_955321 := by exact prefixLift 955321
  have htrace : WordTrace (prefixWord ++ tailWord_955321) baseStart_955321 baseEnd_955321 := by
    simpa [prefixWord, tailWord_955321, baseEnd_955321] using wordTrace_append hprefix tailTrace_955321
  have hstable : (prefixWord ++ tailWord_955321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955321).length < 2 ^ (prefixWord ++ tailWord_955321).sum := by decide
  have hdescent : baseEnd_955321 < baseStart_955321 := by decide
  rcases family_descends (prefixWord ++ tailWord_955321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955325 : List Nat := [1, 4, 1, 2, 5, 1, 1, 1, 6]
def baseStart_955325 : Nat := 118140960795 + 955325 * 2 ^ 59
def prefixEnd_955325 : Nat := 4983230072969 + 3 ^ 40 * 955325 * 2
def baseEnd_955325 : Nat := 109009090279240004498677

theorem tailTrace_955325 : CollatzResearch.WordTrace tailWord_955325 prefixEnd_955325 109009090279240004498677 := by
  unfold tailWord_955325
  simp only [CollatzResearch.WordTrace]
  refine ⟨34843565264028156365555429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23229043509352104243703619 34843565264028156365555429)
  ·
    refine ⟨6533168487005279318541643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34843565264028156365555429 6533168487005279318541643)
    ·
      refine ⟨9799752730507918977812465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6533168487005279318541643 9799752730507918977812465)
      ·
        refine ⟨7349814547880939233359349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9799752730507918977812465 7349814547880939233359349)
        ·
          refine ⟨689045113863838053127439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7349814547880939233359349 689045113863838053127439)
          ·
            refine ⟨1033567670795757079691159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 689045113863838053127439 1033567670795757079691159)
            ·
              refine ⟨1550351506193635619536739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1033567670795757079691159 1550351506193635619536739)
              ·
                refine ⟨2325527259290453429305109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1550351506193635619536739 2325527259290453429305109)
                ·
                  refine ⟨109009090279240004498677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2325527259290453429305109 109009090279240004498677)
                  ·
                    rfl

theorem cell22_955325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 6].length) (baseStart_955325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_955325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_955325 prefixEnd_955325 := by exact prefixLift 955325
  have htrace : WordTrace (prefixWord ++ tailWord_955325) baseStart_955325 baseEnd_955325 := by
    simpa [prefixWord, tailWord_955325, baseEnd_955325] using wordTrace_append hprefix tailTrace_955325
  have hstable : (prefixWord ++ tailWord_955325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955325).length < 2 ^ (prefixWord ++ tailWord_955325).sum := by decide
  have hdescent : baseEnd_955325 < baseStart_955325 := by decide
  rcases family_descends (prefixWord ++ tailWord_955325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955385 : List Nat := [1, 2, 1, 3, 1, 3, 3, 4, 1, 3]
def baseStart_955385 : Nat := 118140960795 + 955385 * 2 ^ 59
def prefixEnd_955385 : Nat := 4983230072969 + 3 ^ 40 * 955385 * 2
def baseEnd_955385 : Nat := 327047810063899856995847

theorem tailTrace_955385 : CollatzResearch.WordTrace tailWord_955385 prefixEnd_955385 327047810063899856995847 := by
  unfold tailWord_955385
  simp only [CollatzResearch.WordTrace]
  refine ⟨34845753643810786612739609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23230502429207191075159739 34845753643810786612739609)
  ·
    refine ⟨26134315232858089959554707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34845753643810786612739609 26134315232858089959554707)
    ·
      refine ⟨39201472849287134939332061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26134315232858089959554707 39201472849287134939332061)
      ·
        refine ⟨14700552318482675602249523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39201472849287134939332061 14700552318482675602249523)
        ·
          refine ⟨22050828477724013403374285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14700552318482675602249523 22050828477724013403374285)
          ·
            refine ⟨8269060679146505026265357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22050828477724013403374285 8269060679146505026265357)
            ·
              refine ⟨3100897754679939384849509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8269060679146505026265357 3100897754679939384849509)
              ·
                refine ⟨581418329002488634659283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3100897754679939384849509 581418329002488634659283)
                ·
                  refine ⟨872127493503732951988925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 581418329002488634659283 872127493503732951988925)
                  ·
                    refine ⟨327047810063899856995847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 872127493503732951988925 327047810063899856995847)
                    ·
                      rfl

theorem cell22_955385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 4, 1, 3].length) (baseStart_955385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_955385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_955385 prefixEnd_955385 := by exact prefixLift 955385
  have htrace : WordTrace (prefixWord ++ tailWord_955385) baseStart_955385 baseEnd_955385 := by
    simpa [prefixWord, tailWord_955385, baseEnd_955385] using wordTrace_append hprefix tailTrace_955385
  have hstable : (prefixWord ++ tailWord_955385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955385).length < 2 ^ (prefixWord ++ tailWord_955385).sum := by decide
  have hdescent : baseEnd_955385 < baseStart_955385 := by decide
  rcases family_descends (prefixWord ++ tailWord_955385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955456 : List Nat := [2, 1, 1, 2, 2, 3, 1, 1, 3, 6]
def baseStart_955456 : Nat := 118140960795 + 955456 * 2 ^ 59
def prefixEnd_955456 : Nat := 4983230072969 + 3 ^ 40 * 955456 * 2
def baseEnd_955456 : Nat := 327072114814879338470629

theorem tailTrace_955456 : CollatzResearch.WordTrace tailWord_955456 prefixEnd_955456 327072114814879338470629 := by
  unfold tailWord_955456
  simp only [CollatzResearch.WordTrace]
  refine ⟨17424171613276782869287111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23232228817702377159049481 17424171613276782869287111)
  ·
    refine ⟨26136257419915174303930667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17424171613276782869287111 26136257419915174303930667)
    ·
      refine ⟨39204386129872761455896001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26136257419915174303930667 39204386129872761455896001)
      ·
        refine ⟨29403289597404571091922001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39204386129872761455896001 29403289597404571091922001)
        ·
          refine ⟨22052467198053428318941501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29403289597404571091922001 22052467198053428318941501)
          ·
            refine ⟨8269675199270035619603063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22052467198053428318941501 8269675199270035619603063)
            ·
              refine ⟨12404512798905053429404595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8269675199270035619603063 12404512798905053429404595)
              ·
                refine ⟨18606769198357580144106893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12404512798905053429404595 18606769198357580144106893)
                ·
                  refine ⟨6977538449384092554040085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18606769198357580144106893 6977538449384092554040085)
                  ·
                    refine ⟨327072114814879338470629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6977538449384092554040085 327072114814879338470629)
                    ·
                      rfl

theorem cell22_955456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 3, 6].length) (baseStart_955456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_955456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_955456 prefixEnd_955456 := by exact prefixLift 955456
  have htrace : WordTrace (prefixWord ++ tailWord_955456) baseStart_955456 baseEnd_955456 := by
    simpa [prefixWord, tailWord_955456, baseEnd_955456] using wordTrace_append hprefix tailTrace_955456
  have hstable : (prefixWord ++ tailWord_955456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955456).length < 2 ^ (prefixWord ++ tailWord_955456).sum := by decide
  have hdescent : baseEnd_955456 < baseStart_955456 := by decide
  rcases family_descends (prefixWord ++ tailWord_955456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955462 : List Nat := [6, 1, 1, 1, 1, 2, 1, 4, 1, 4]
def baseStart_955462 : Nat := 118140960795 + 955462 * 2 ^ 59
def prefixEnd_955462 : Nat := 4983230072969 + 3 ^ 40 * 955462 * 2
def baseEnd_955462 : Nat := 327074168737497322820611

theorem tailTrace_955462 : CollatzResearch.WordTrace tailWord_955462 prefixEnd_955462 327074168737497322820611 := by
  unfold tailWord_955462
  simp only [CollatzResearch.WordTrace]
  refine ⟨1089017564516619648852895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23232374709687885842195093 1089017564516619648852895)
  ·
    refine ⟨1633526346774929473279343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1089017564516619648852895 1633526346774929473279343)
    ·
      refine ⟨2450289520162394209919015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1633526346774929473279343 2450289520162394209919015)
      ·
        refine ⟨3675434280243591314878523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2450289520162394209919015 3675434280243591314878523)
        ·
          refine ⟨5513151420365386972317785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3675434280243591314878523 5513151420365386972317785)
          ·
            refine ⟨4134863565274040229238339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5513151420365386972317785 4134863565274040229238339)
            ·
              refine ⟨6202295347911060343857509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4134863565274040229238339 6202295347911060343857509)
              ·
                refine ⟨1162930377733323814473283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6202295347911060343857509 1162930377733323814473283)
                ·
                  refine ⟨1744395566599985721709925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1162930377733323814473283 1744395566599985721709925)
                  ·
                    refine ⟨327074168737497322820611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1744395566599985721709925 327074168737497322820611)
                    ·
                      rfl

theorem cell22_955462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_955462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_955462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_955462 prefixEnd_955462 := by exact prefixLift 955462
  have htrace : WordTrace (prefixWord ++ tailWord_955462) baseStart_955462 baseEnd_955462 := by
    simpa [prefixWord, tailWord_955462, baseEnd_955462] using wordTrace_append hprefix tailTrace_955462
  have hstable : (prefixWord ++ tailWord_955462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955462).length < 2 ^ (prefixWord ++ tailWord_955462).sum := by decide
  have hdescent : baseEnd_955462 < baseStart_955462 := by decide
  rcases family_descends (prefixWord ++ tailWord_955462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955490 : List Nat := [3, 3, 2, 2, 1, 1, 1, 1, 4, 4]
def baseStart_955490 : Nat := 118140960795 + 955490 * 2 ^ 59
def prefixEnd_955490 : Nat := 4983230072969 + 3 ^ 40 * 955490 * 2
def baseEnd_955490 : Nat := 327083753709714583120525

theorem tailTrace_955490 : CollatzResearch.WordTrace tailWord_955490 prefixEnd_955490 327083753709714583120525 := by
  unfold tailWord_955490
  simp only [CollatzResearch.WordTrace]
  refine ⟨8712395827107597386327981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23233055538953593030207949 8712395827107597386327981)
  ·
    refine ⟨3267148435165349019872993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8712395827107597386327981 3267148435165349019872993)
    ·
      refine ⟨2450361326374011764904745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3267148435165349019872993 2450361326374011764904745)
      ·
        refine ⟨1837770994780508823678559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2450361326374011764904745 1837770994780508823678559)
        ·
          refine ⟨2756656492170763235517839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1837770994780508823678559 2756656492170763235517839)
          ·
            refine ⟨4134984738256144853276759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2756656492170763235517839 4134984738256144853276759)
            ·
              refine ⟨6202477107384217279915139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4134984738256144853276759 6202477107384217279915139)
              ·
                refine ⟨9303715661076325919872709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6202477107384217279915139 9303715661076325919872709)
                ·
                  refine ⟨1744446686451811109976133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9303715661076325919872709 1744446686451811109976133)
                  ·
                    refine ⟨327083753709714583120525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1744446686451811109976133 327083753709714583120525)
                    ·
                      rfl

theorem cell22_955490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_955490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_955490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_955490 prefixEnd_955490 := by exact prefixLift 955490
  have htrace : WordTrace (prefixWord ++ tailWord_955490) baseStart_955490 baseEnd_955490 := by
    simpa [prefixWord, tailWord_955490, baseEnd_955490] using wordTrace_append hprefix tailTrace_955490
  have hstable : (prefixWord ++ tailWord_955490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955490).length < 2 ^ (prefixWord ++ tailWord_955490).sum := by decide
  have hdescent : baseEnd_955490 < baseStart_955490 := by decide
  rcases family_descends (prefixWord ++ tailWord_955490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955509 : List Nat := [1, 3, 4, 3, 1, 1, 1, 3, 2, 3]
def baseStart_955509 : Nat := 118140960795 + 955509 * 2 ^ 59
def prefixEnd_955509 : Nat := 4983230072969 + 3 ^ 40 * 955509 * 2
def baseEnd_955509 : Nat := 327090257798004866895467

theorem tailTrace_955509 : CollatzResearch.WordTrace tailWord_955509 prefixEnd_955509 327090257798004866895467 := by
  unfold tailWord_955509
  simp only [CollatzResearch.WordTrace]
  refine ⟨34850276295361555790253581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23233517530241037193502387 34850276295361555790253581)
  ·
    refine ⟨13068853610760583421345093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34850276295361555790253581 13068853610760583421345093)
    ·
      refine ⟨2450410052017609391502205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13068853610760583421345093 2450410052017609391502205)
      ·
        refine ⟨918903769506603521813327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2450410052017609391502205 918903769506603521813327)
        ·
          refine ⟨1378355654259905282719991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 918903769506603521813327 1378355654259905282719991)
          ·
            refine ⟨2067533481389857924079987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1378355654259905282719991 2067533481389857924079987)
            ·
              refine ⟨3101300222084786886119981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2067533481389857924079987 3101300222084786886119981)
              ·
                refine ⟨1162987583281795082294993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3101300222084786886119981 1162987583281795082294993)
                ·
                  refine ⟨872240687461346311721245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1162987583281795082294993 872240687461346311721245)
                  ·
                    refine ⟨327090257798004866895467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 872240687461346311721245 327090257798004866895467)
                    ·
                      rfl

theorem cell22_955509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_955509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_955509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_955509 prefixEnd_955509 := by exact prefixLift 955509
  have htrace : WordTrace (prefixWord ++ tailWord_955509) baseStart_955509 baseEnd_955509 := by
    simpa [prefixWord, tailWord_955509, baseEnd_955509] using wordTrace_append hprefix tailTrace_955509
  have hstable : (prefixWord ++ tailWord_955509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955509).length < 2 ^ (prefixWord ++ tailWord_955509).sum := by decide
  have hdescent : baseEnd_955509 < baseStart_955509 := by decide
  rcases family_descends (prefixWord ++ tailWord_955509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955580 : List Nat := [2, 2, 2, 3, 2, 1, 2, 1, 3, 4]
def baseStart_955580 : Nat := 118140960795 + 955580 * 2 ^ 59
def prefixEnd_955580 : Nat := 4983230072969 + 3 ^ 40 * 955580 * 2
def baseEnd_955580 : Nat := 327114562548984348370249

theorem tailTrace_955580 : CollatzResearch.WordTrace tailWord_955580 prefixEnd_955580 327114562548984348370249 := by
  unfold tailWord_955580
  simp only [CollatzResearch.WordTrace]
  refine ⟨17426432939052167458044097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23235243918736223277392129 17426432939052167458044097)
  ·
    refine ⟨13069824704289125593533073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17426432939052167458044097 13069824704289125593533073)
    ·
      refine ⟨9802368528216844195149805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13069824704289125593533073 9802368528216844195149805)
      ·
        refine ⟨3675888198081316573181177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9802368528216844195149805 3675888198081316573181177)
        ·
          refine ⟨2756916148560987429885883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3675888198081316573181177 2756916148560987429885883)
          ·
            refine ⟨4135374222841481144828825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2756916148560987429885883 4135374222841481144828825)
            ·
              refine ⟨3101530667131110858621619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4135374222841481144828825 3101530667131110858621619)
              ·
                refine ⟨4652296000696666287932429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3101530667131110858621619 4652296000696666287932429)
                ·
                  refine ⟨1744611000261249857974661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4652296000696666287932429 1744611000261249857974661)
                  ·
                    refine ⟨327114562548984348370249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1744611000261249857974661 327114562548984348370249)
                    ·
                      rfl

theorem cell22_955580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_955580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_955580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_955580 prefixEnd_955580 := by exact prefixLift 955580
  have htrace : WordTrace (prefixWord ++ tailWord_955580) baseStart_955580 baseEnd_955580 := by
    simpa [prefixWord, tailWord_955580, baseEnd_955580] using wordTrace_append hprefix tailTrace_955580
  have hstable : (prefixWord ++ tailWord_955580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955580).length < 2 ^ (prefixWord ++ tailWord_955580).sum := by decide
  have hdescent : baseEnd_955580 < baseStart_955580 := by decide
  rcases family_descends (prefixWord ++ tailWord_955580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955672 : List Nat := [2, 1, 2, 3, 1, 3, 3, 1, 3, 3]
def baseStart_955672 : Nat := 118140960795 + 955672 * 2 ^ 59
def prefixEnd_955672 : Nat := 4983230072969 + 3 ^ 40 * 955672 * 2
def baseEnd_955672 : Nat := 327146056029126775069967

theorem tailTrace_955672 : CollatzResearch.WordTrace tailWord_955672 prefixEnd_955672 327146056029126775069967 := by
  unfold tailWord_955672
  simp only [CollatzResearch.WordTrace]
  refine ⟨17428110696885517314218635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23237480929180689752291513 17428110696885517314218635)
  ·
    refine ⟨26142166045328275971327953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17428110696885517314218635 26142166045328275971327953)
    ·
      refine ⟨19606624533996206978495965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26142166045328275971327953 19606624533996206978495965)
      ·
        refine ⟨7352484200248577616935987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19606624533996206978495965 7352484200248577616935987)
        ·
          refine ⟨11028726300372866425403981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7352484200248577616935987 11028726300372866425403981)
          ·
            refine ⟨4135772362639824909526493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11028726300372866425403981 4135772362639824909526493)
            ·
              refine ⟨1550914635989934341072435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4135772362639824909526493 1550914635989934341072435)
              ·
                refine ⟨2326371953984901511608653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1550914635989934341072435 2326371953984901511608653)
                ·
                  refine ⟨872389482744338066853245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2326371953984901511608653 872389482744338066853245)
                  ·
                    refine ⟨327146056029126775069967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 872389482744338066853245 327146056029126775069967)
                    ·
                      rfl

theorem cell22_955672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 3, 3].length) (baseStart_955672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_955672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_955672 prefixEnd_955672 := by exact prefixLift 955672
  have htrace : WordTrace (prefixWord ++ tailWord_955672) baseStart_955672 baseEnd_955672 := by
    simpa [prefixWord, tailWord_955672, baseEnd_955672] using wordTrace_append hprefix tailTrace_955672
  have hstable : (prefixWord ++ tailWord_955672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955672).length < 2 ^ (prefixWord ++ tailWord_955672).sum := by decide
  have hdescent : baseEnd_955672 < baseStart_955672 := by decide
  rcases family_descends (prefixWord ++ tailWord_955672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955730 : List Nat := [3, 2, 2, 1, 1, 1, 1, 5, 6]
def baseStart_955730 : Nat := 118140960795 + 955730 * 2 ^ 59
def prefixEnd_955730 : Nat := 4983230072969 + 3 ^ 40 * 955730 * 2
def baseEnd_955730 : Nat := 109055303538144652373263

theorem tailTrace_955730 : CollatzResearch.WordTrace tailWord_955730 prefixEnd_955730 109055303538144652373263 := by
  unfold tailWord_955730
  simp only [CollatzResearch.WordTrace]
  refine ⟨8714584206890227633512161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23238891218373940356032429 8714584206890227633512161)
  ·
    refine ⟨6535938155167670725134121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8714584206890227633512161 6535938155167670725134121)
    ·
      refine ⟨4901953616375753043850591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6535938155167670725134121 4901953616375753043850591)
      ·
        refine ⟨7352930424563629565775887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4901953616375753043850591 7352930424563629565775887)
        ·
          refine ⟨11029395636845444348663831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7352930424563629565775887 11029395636845444348663831)
          ·
            refine ⟨16544093455268166522995747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11029395636845444348663831 16544093455268166522995747)
            ·
              refine ⟨24816140182902249784493621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16544093455268166522995747 24816140182902249784493621)
              ·
                refine ⟨2326513142147085917296277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24816140182902249784493621 2326513142147085917296277)
                ·
                  refine ⟨109055303538144652373263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2326513142147085917296277 109055303538144652373263)
                  ·
                    rfl

theorem cell22_955730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 6].length) (baseStart_955730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_955730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_955730 prefixEnd_955730 := by exact prefixLift 955730
  have htrace : WordTrace (prefixWord ++ tailWord_955730) baseStart_955730 baseEnd_955730 := by
    simpa [prefixWord, tailWord_955730, baseEnd_955730] using wordTrace_append hprefix tailTrace_955730
  have hstable : (prefixWord ++ tailWord_955730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955730).length < 2 ^ (prefixWord ++ tailWord_955730).sum := by decide
  have hdescent : baseEnd_955730 < baseStart_955730 := by decide
  rcases family_descends (prefixWord ++ tailWord_955730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955760 : List Nat := [2, 1, 1, 1, 4, 2, 3, 1, 1, 6]
def baseStart_955760 : Nat := 118140960795 + 955760 * 2 ^ 59
def prefixEnd_955760 : Nat := 4983230072969 + 3 ^ 40 * 955760 * 2
def baseEnd_955760 : Nat := 327176180227523878869697

theorem tailTrace_955760 : CollatzResearch.WordTrace tailWord_955760 prefixEnd_955760 327176180227523878869697 := by
  unfold tailWord_955760
  simp only [CollatzResearch.WordTrace]
  refine ⟨17429715508726112828820367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23239620678301483771760489 17429715508726112828820367)
  ·
    refine ⟨26144573263089169243230551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17429715508726112828820367 26144573263089169243230551)
    ·
      refine ⟨39216859894633753864845827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26144573263089169243230551 39216859894633753864845827)
      ·
        refine ⟨58825289841950630797268741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39216859894633753864845827 58825289841950630797268741)
        ·
          refine ⟨11029741845365743274487889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58825289841950630797268741 11029741845365743274487889)
          ·
            refine ⟨8272306384024307455865917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11029741845365743274487889 8272306384024307455865917)
            ·
              refine ⟨3102114894009115295949719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8272306384024307455865917 3102114894009115295949719)
              ·
                refine ⟨4653172341013672943924579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3102114894009115295949719 4653172341013672943924579)
                ·
                  refine ⟨6979758511520509415886869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4653172341013672943924579 6979758511520509415886869)
                  ·
                    refine ⟨327176180227523878869697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6979758511520509415886869 327176180227523878869697)
                    ·
                      rfl

theorem cell22_955760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 1, 6].length) (baseStart_955760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_955760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_955760 prefixEnd_955760 := by exact prefixLift 955760
  have htrace : WordTrace (prefixWord ++ tailWord_955760) baseStart_955760 baseEnd_955760 := by
    simpa [prefixWord, tailWord_955760, baseEnd_955760] using wordTrace_append hprefix tailTrace_955760
  have hstable : (prefixWord ++ tailWord_955760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955760).length < 2 ^ (prefixWord ++ tailWord_955760).sum := by decide
  have hdescent : baseEnd_955760 < baseStart_955760 := by decide
  rcases family_descends (prefixWord ++ tailWord_955760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955762 : List Nat := [3, 2, 1, 2, 1, 2, 2, 2, 4, 3]
def baseStart_955762 : Nat := 118140960795 + 955762 * 2 ^ 59
def prefixEnd_955762 : Nat := 4983230072969 + 3 ^ 40 * 955762 * 2
def baseEnd_955762 : Nat := 327176864868396540319691

theorem tailTrace_955762 : CollatzResearch.WordTrace tailWord_955762 prefixEnd_955762 327176864868396540319691 := by
  unfold tailWord_955762
  simp only [CollatzResearch.WordTrace]
  refine ⟨8714875990861244999803385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23239669308963319999475693 8714875990861244999803385)
  ·
    refine ⟨6536156993145933749852539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8714875990861244999803385 6536156993145933749852539)
    ·
      refine ⟨9804235489718900624778809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6536156993145933749852539 9804235489718900624778809)
      ·
        refine ⟨7353176617289175468584107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9804235489718900624778809 7353176617289175468584107)
        ·
          refine ⟨11029764925933763202876161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7353176617289175468584107 11029764925933763202876161)
          ·
            refine ⟨8272323694450322402157121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11029764925933763202876161 8272323694450322402157121)
            ·
              refine ⟨6204242770837741801617841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8272323694450322402157121 6204242770837741801617841)
              ·
                refine ⟨4653182078128306351213381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6204242770837741801617841 4653182078128306351213381)
                ·
                  refine ⟨872471639649057440852509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4653182078128306351213381 872471639649057440852509)
                  ·
                    refine ⟨327176864868396540319691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 872471639649057440852509 327176864868396540319691)
                    ·
                      rfl

theorem cell22_955762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 4, 3].length) (baseStart_955762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_955762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_955762 prefixEnd_955762 := by exact prefixLift 955762
  have htrace : WordTrace (prefixWord ++ tailWord_955762) baseStart_955762 baseEnd_955762 := by
    simpa [prefixWord, tailWord_955762, baseEnd_955762] using wordTrace_append hprefix tailTrace_955762
  have hstable : (prefixWord ++ tailWord_955762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955762).length < 2 ^ (prefixWord ++ tailWord_955762).sum := by decide
  have hdescent : baseEnd_955762 < baseStart_955762 := by decide
  rcases family_descends (prefixWord ++ tailWord_955762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955779 : List Nat := [1, 1, 1, 3, 5, 1, 3, 2, 2, 3]
def baseStart_955779 : Nat := 118140960795 + 955779 * 2 ^ 59
def prefixEnd_955779 : Nat := 4983230072969 + 3 ^ 40 * 955779 * 2
def baseEnd_955779 : Nat := 327182684315814162644639

theorem tailTrace_955779 : CollatzResearch.WordTrace tailWord_955779 prefixEnd_955779 327182684315814162644639 := by
  unfold tailWord_955779
  simp only [CollatzResearch.WordTrace]
  refine ⟨34860124004383391902582391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23240082669588927935054927 34860124004383391902582391)
  ·
    refine ⟨52290186006575087853873587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34860124004383391902582391 52290186006575087853873587)
    ·
      refine ⟨78435279009862631780810381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52290186006575087853873587 78435279009862631780810381)
      ·
        refine ⟨29413229628698486917803893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78435279009862631780810381 29413229628698486917803893)
        ·
          refine ⟨2757490277690483148544115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29413229628698486917803893 2757490277690483148544115)
          ·
            refine ⟨4136235416535724722816173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2757490277690483148544115 4136235416535724722816173)
            ·
              refine ⟨1551088281200896771056065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4136235416535724722816173 1551088281200896771056065)
              ·
                refine ⟨1163316210900672578292049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1551088281200896771056065 1163316210900672578292049)
                ·
                  refine ⟨872487158175504433719037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1163316210900672578292049 872487158175504433719037)
                  ·
                    refine ⟨327182684315814162644639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 872487158175504433719037 327182684315814162644639)
                    ·
                      rfl

theorem cell22_955779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 2, 2, 3].length) (baseStart_955779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_955779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_955779 prefixEnd_955779 := by exact prefixLift 955779
  have htrace : WordTrace (prefixWord ++ tailWord_955779) baseStart_955779 baseEnd_955779 := by
    simpa [prefixWord, tailWord_955779, baseEnd_955779] using wordTrace_append hprefix tailTrace_955779
  have hstable : (prefixWord ++ tailWord_955779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955779).length < 2 ^ (prefixWord ++ tailWord_955779).sum := by decide
  have hdescent : baseEnd_955779 < baseStart_955779 := by decide
  rcases family_descends (prefixWord ++ tailWord_955779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955820 : List Nat := [2, 2, 1, 1, 1, 1, 5, 2, 7]
def baseStart_955820 : Nat := 118140960795 + 955820 * 2 ^ 59
def prefixEnd_955820 : Nat := 4983230072969 + 3 ^ 40 * 955820 * 2
def baseEnd_955820 : Nat := 109065573151234574123171

theorem tailTrace_955820 : CollatzResearch.WordTrace tailWord_955820 prefixEnd_955820 109065573151234574123171 := by
  unfold tailWord_955820
  simp only [CollatzResearch.WordTrace]
  refine ⟨17430809698617427952412457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23241079598156570603216609 17430809698617427952412457)
  ·
    refine ⟨13073107273963070964309343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17430809698617427952412457 13073107273963070964309343)
    ·
      refine ⟨19609660910944606446464015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13073107273963070964309343 19609660910944606446464015)
      ·
        refine ⟨29414491366416909669696023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19609660910944606446464015 29414491366416909669696023)
        ·
          refine ⟨44121737049625364504544035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29414491366416909669696023 44121737049625364504544035)
          ·
            refine ⟨66182605574438046756816053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44121737049625364504544035 66182605574438046756816053)
            ·
              refine ⟨6204619272603566883451505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66182605574438046756816053 6204619272603566883451505)
              ·
                refine ⟨4653464454452675162588629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6204619272603566883451505 4653464454452675162588629)
                ·
                  refine ⟨109065573151234574123171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4653464454452675162588629 109065573151234574123171)
                  ·
                    rfl

theorem cell22_955820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 7].length) (baseStart_955820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_955820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_955820 prefixEnd_955820 := by exact prefixLift 955820
  have htrace : WordTrace (prefixWord ++ tailWord_955820) baseStart_955820 baseEnd_955820 := by
    simpa [prefixWord, tailWord_955820, baseEnd_955820] using wordTrace_append hprefix tailTrace_955820
  have hstable : (prefixWord ++ tailWord_955820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955820).length < 2 ^ (prefixWord ++ tailWord_955820).sum := by decide
  have hdescent : baseEnd_955820 < baseStart_955820 := by decide
  rcases family_descends (prefixWord ++ tailWord_955820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955824 : List Nat := [2, 1, 1, 1, 2, 1, 1, 9, 1, 3]
def baseStart_955824 : Nat := 118140960795 + 955824 * 2 ^ 59
def prefixEnd_955824 : Nat := 4983230072969 + 3 ^ 40 * 955824 * 2
def baseEnd_955824 : Nat := 327198088735449045269501

theorem tailTrace_955824 : CollatzResearch.WordTrace tailWord_955824 prefixEnd_955824 327198088735449045269501 := by
  unfold tailWord_955824
  simp only [CollatzResearch.WordTrace]
  refine ⟨17430882644610182293985263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23241176859480243058647017 17430882644610182293985263)
  ·
    refine ⟨26146323966915273440977895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17430882644610182293985263 26146323966915273440977895)
    ·
      refine ⟨39219485950372910161466843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26146323966915273440977895 39219485950372910161466843)
      ·
        refine ⟨58829228925559365242200265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39219485950372910161466843 58829228925559365242200265)
        ·
          refine ⟨44121921694169523931650199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58829228925559365242200265 44121921694169523931650199)
          ·
            refine ⟨66182882541254285897475299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44121921694169523931650199 66182882541254285897475299)
            ·
              refine ⟨99274323811881428846212949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66182882541254285897475299 99274323811881428846212949)
              ·
                refine ⟨581685491085242747145779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 99274323811881428846212949 581685491085242747145779)
                ·
                  refine ⟨872528236627864120718669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 581685491085242747145779 872528236627864120718669)
                  ·
                    refine ⟨327198088735449045269501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 872528236627864120718669 327198088735449045269501)
                    ·
                      rfl

theorem cell22_955824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 9, 1, 3].length) (baseStart_955824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_955824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_955824 prefixEnd_955824 := by exact prefixLift 955824
  have htrace : WordTrace (prefixWord ++ tailWord_955824) baseStart_955824 baseEnd_955824 := by
    simpa [prefixWord, tailWord_955824, baseEnd_955824] using wordTrace_append hprefix tailTrace_955824
  have hstable : (prefixWord ++ tailWord_955824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955824).length < 2 ^ (prefixWord ++ tailWord_955824).sum := by decide
  have hdescent : baseEnd_955824 < baseStart_955824 := by decide
  rcases family_descends (prefixWord ++ tailWord_955824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955837 : List Nat := [1, 4, 1, 2, 2, 1, 2, 4, 5]
def baseStart_955837 : Nat := 118140960795 + 955837 * 2 ^ 59
def prefixEnd_955837 : Nat := 4983230072969 + 3 ^ 40 * 955837 * 2
def baseEnd_955837 : Nat := 109067512967040448231487

theorem tailTrace_955837 : CollatzResearch.WordTrace tailWord_955837 prefixEnd_955837 109067512967040448231487 := by
  unfold tailWord_955837
  simp only [CollatzResearch.WordTrace]
  refine ⟨34862239438173267808193765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23241492958782178538795843 34862239438173267808193765)
  ·
    refine ⟨6536669894657487714036331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34862239438173267808193765 6536669894657487714036331)
    ·
      refine ⟨9805004841986231571054497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6536669894657487714036331 9805004841986231571054497)
      ·
        refine ⟨7353753631489673678290873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9805004841986231571054497 7353753631489673678290873)
        ·
          refine ⟨5515315223617255258718155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7353753631489673678290873 5515315223617255258718155)
          ·
            refine ⟨8272972835425882888077233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5515315223617255258718155 8272972835425882888077233)
            ·
              refine ⟨6204729626569412166057925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8272972835425882888077233 6204729626569412166057925)
              ·
                refine ⟨1163386804981764781135861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6204729626569412166057925 1163386804981764781135861)
                ·
                  refine ⟨109067512967040448231487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1163386804981764781135861 109067512967040448231487)
                  ·
                    rfl

theorem cell22_955837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 4, 5].length) (baseStart_955837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_955837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_955837 prefixEnd_955837 := by exact prefixLift 955837
  have htrace : WordTrace (prefixWord ++ tailWord_955837) baseStart_955837 baseEnd_955837 := by
    simpa [prefixWord, tailWord_955837, baseEnd_955837] using wordTrace_append hprefix tailTrace_955837
  have hstable : (prefixWord ++ tailWord_955837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955837).length < 2 ^ (prefixWord ++ tailWord_955837).sum := by decide
  have hdescent : baseEnd_955837 < baseStart_955837 := by decide
  rcases family_descends (prefixWord ++ tailWord_955837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955854 : List Nat := [4, 1, 1, 1, 2, 1, 6, 1, 5]
def baseStart_955854 : Nat := 118140960795 + 955854 * 2 ^ 59
def prefixEnd_955854 : Nat := 4983230072969 + 3 ^ 40 * 955854 * 2
def baseEnd_955854 : Nat := 109069452782846322339803

theorem tailTrace_955854 : CollatzResearch.WordTrace tailWord_955854 prefixEnd_955854 109069452782846322339803 := by
  unfold tailWord_955854
  simp only [CollatzResearch.WordTrace]
  refine ⟨4357857434888959963945327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23241906319407786474375077 4357857434888959963945327)
  ·
    refine ⟨6536786152333439945917991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4357857434888959963945327 6536786152333439945917991)
    ·
      refine ⟨9805179228500159918876987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6536786152333439945917991 9805179228500159918876987)
      ·
        refine ⟨14707768842750239878315481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9805179228500159918876987 14707768842750239878315481)
        ·
          refine ⟨11030826632062679908736611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14707768842750239878315481 11030826632062679908736611)
          ·
            refine ⟨16546239948094019863104917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11030826632062679908736611 16546239948094019863104917)
            ·
              refine ⟨775604997566907181083043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16546239948094019863104917 775604997566907181083043)
              ·
                refine ⟨1163407496350360771624565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 775604997566907181083043 1163407496350360771624565)
                ·
                  refine ⟨109069452782846322339803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1163407496350360771624565 109069452782846322339803)
                  ·
                    rfl

theorem cell22_955854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 1, 5].length) (baseStart_955854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_955854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_955854 prefixEnd_955854 := by exact prefixLift 955854
  have htrace : WordTrace (prefixWord ++ tailWord_955854) baseStart_955854 baseEnd_955854 := by
    simpa [prefixWord, tailWord_955854, baseEnd_955854] using wordTrace_append hprefix tailTrace_955854
  have hstable : (prefixWord ++ tailWord_955854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955854).length < 2 ^ (prefixWord ++ tailWord_955854).sum := by decide
  have hdescent : baseEnd_955854 < baseStart_955854 := by decide
  rcases family_descends (prefixWord ++ tailWord_955854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955912 : List Nat := [2, 1, 3, 2, 1, 1, 2, 2, 4, 4]
def baseStart_955912 : Nat := 118140960795 + 955912 * 2 ^ 59
def prefixEnd_955912 : Nat := 4983230072969 + 3 ^ 40 * 955912 * 2
def baseEnd_955912 : Nat := 327228212933846149069231

theorem tailTrace_955912 : CollatzResearch.WordTrace tailWord_955912 prefixEnd_955912 327228212933846149069231 := by
  unfold tailWord_955912
  simp only [CollatzResearch.WordTrace]
  refine ⟨17432487456450777808586995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23243316608601037078115993 17432487456450777808586995)
  ·
    refine ⟨26148731184676166712880493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17432487456450777808586995 26148731184676166712880493)
    ·
      refine ⟨9805774194253562517330185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26148731184676166712880493 9805774194253562517330185)
      ·
        refine ⟨7354330645690171887997639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9805774194253562517330185 7354330645690171887997639)
        ·
          refine ⟨11031495968535257831996459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7354330645690171887997639 11031495968535257831996459)
          ·
            refine ⟨16547243952802886747994689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11031495968535257831996459 16547243952802886747994689)
            ·
              refine ⟨12410432964602165060996017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16547243952802886747994689 12410432964602165060996017)
              ·
                refine ⟨9307824723451623795747013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12410432964602165060996017 9307824723451623795747013)
                ·
                  refine ⟨1745217135647179461702565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9307824723451623795747013 1745217135647179461702565)
                  ·
                    refine ⟨327228212933846149069231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1745217135647179461702565 327228212933846149069231)
                    ·
                      rfl

theorem cell22_955912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_955912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_955912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_955912 prefixEnd_955912 := by exact prefixLift 955912
  have htrace : WordTrace (prefixWord ++ tailWord_955912) baseStart_955912 baseEnd_955912 := by
    simpa [prefixWord, tailWord_955912, baseEnd_955912] using wordTrace_append hprefix tailTrace_955912
  have hstable : (prefixWord ++ tailWord_955912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955912).length < 2 ^ (prefixWord ++ tailWord_955912).sum := by decide
  have hdescent : baseEnd_955912 < baseStart_955912 := by decide
  rcases family_descends (prefixWord ++ tailWord_955912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955914 : List Nat := [3, 1, 2, 2, 2, 3, 2, 1, 1, 5]
def baseStart_955914 : Nat := 118140960795 + 955914 * 2 ^ 59
def prefixEnd_955914 : Nat := 4983230072969 + 3 ^ 40 * 955914 * 2
def baseEnd_955914 : Nat := 327228897574718810519225

theorem tailTrace_955914 : CollatzResearch.WordTrace tailWord_955914 prefixEnd_955914 327228897574718810519225 := by
  unfold tailWord_955914
  simp only [CollatzResearch.WordTrace]
  refine ⟨8716261964723577489686699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23243365239262873305831197 8716261964723577489686699)
  ·
    refine ⟨13074392947085366234530049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8716261964723577489686699 13074392947085366234530049)
    ·
      refine ⟨9805794710314024675897537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13074392947085366234530049 9805794710314024675897537)
      ·
        refine ⟨7354346032735518506923153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9805794710314024675897537 7354346032735518506923153)
        ·
          refine ⟨5515759524551638880192365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7354346032735518506923153 5515759524551638880192365)
          ·
            refine ⟨2068409821706864580072137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5515759524551638880192365 2068409821706864580072137)
            ·
              refine ⟨1551307366280148435054103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2068409821706864580072137 1551307366280148435054103)
              ·
                refine ⟨2326961049420222652581155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1551307366280148435054103 2326961049420222652581155)
                ·
                  refine ⟨3490441574130333978871733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2326961049420222652581155 3490441574130333978871733)
                  ·
                    refine ⟨327228897574718810519225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3490441574130333978871733 327228897574718810519225)
                    ·
                      rfl

theorem cell22_955914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_955914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_955914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_955914 prefixEnd_955914 := by exact prefixLift 955914
  have htrace : WordTrace (prefixWord ++ tailWord_955914) baseStart_955914 baseEnd_955914 := by
    simpa [prefixWord, tailWord_955914, baseEnd_955914] using wordTrace_append hprefix tailTrace_955914
  have hstable : (prefixWord ++ tailWord_955914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955914).length < 2 ^ (prefixWord ++ tailWord_955914).sum := by decide
  have hdescent : baseEnd_955914 < baseStart_955914 := by decide
  rcases family_descends (prefixWord ++ tailWord_955914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955944 : List Nat := [2, 1, 5, 2, 2, 1, 9]
def baseStart_955944 : Nat := 118140960795 + 955944 * 2 ^ 59
def prefixEnd_955944 : Nat := 4983230072969 + 3 ^ 40 * 955944 * 2
def baseEnd_955944 : Nat := 12119969155104027121079

theorem tailTrace_955944 : CollatzResearch.WordTrace tailWord_955944 prefixEnd_955944 12119969155104027121079 := by
  unfold tailWord_955944
  simp only [CollatzResearch.WordTrace]
  refine ⟨17433071024392812541169443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23244094699190416721559257 17433071024392812541169443)
  ·
    refine ⟨26149606536589218811754165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17433071024392812541169443 26149606536589218811754165)
    ·
      refine ⟨2451525612805239263601953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26149606536589218811754165 2451525612805239263601953)
      ·
        refine ⟨1838644209603929447701465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2451525612805239263601953 1838644209603929447701465)
        ·
          refine ⟨1378983157202947085776099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1838644209603929447701465 1378983157202947085776099)
          ·
            refine ⟨2068474735804420628664149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1378983157202947085776099 2068474735804420628664149)
            ·
              refine ⟨12119969155104027121079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2068474735804420628664149 12119969155104027121079)
              ·
                rfl

theorem cell22_955944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 9].length) (baseStart_955944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_955944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_955944 prefixEnd_955944 := by exact prefixLift 955944
  have htrace : WordTrace (prefixWord ++ tailWord_955944) baseStart_955944 baseEnd_955944 := by
    simpa [prefixWord, tailWord_955944, baseEnd_955944] using wordTrace_append hprefix tailTrace_955944
  have hstable : (prefixWord ++ tailWord_955944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955944).length < 2 ^ (prefixWord ++ tailWord_955944).sum := by decide
  have hdescent : baseEnd_955944 < baseStart_955944 := by decide
  rcases family_descends (prefixWord ++ tailWord_955944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955959 : List Nat := [1, 1, 3, 1, 2, 4, 1, 3, 3, 3]
def baseStart_955959 : Nat := 118140960795 + 955959 * 2 ^ 59
def prefixEnd_955959 : Nat := 4983230072969 + 3 ^ 40 * 955959 * 2
def baseEnd_955959 : Nat := 327244301994353693144087

theorem tailTrace_955959 : CollatzResearch.WordTrace tailWord_955959 prefixEnd_955959 327244301994353693144087 := by
  unfold tailWord_955959
  simp only [CollatzResearch.WordTrace]
  refine ⟨34866689143731282644134931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23244459429154188429423287 34866689143731282644134931)
  ·
    refine ⟨52300033715596923966202397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34866689143731282644134931 52300033715596923966202397)
    ·
      refine ⟨19612512643348846487325899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52300033715596923966202397 19612512643348846487325899)
      ·
        refine ⟨29418768965023269730988849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19612512643348846487325899 29418768965023269730988849)
        ·
          refine ⟨22064076723767452298241637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29418768965023269730988849 22064076723767452298241637)
          ·
            refine ⟨4137014385706397305920307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22064076723767452298241637 4137014385706397305920307)
            ·
              refine ⟨6205521578559595958880461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4137014385706397305920307 6205521578559595958880461)
              ·
                refine ⟨2327070591959848484580173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6205521578559595958880461 2327070591959848484580173)
                ·
                  refine ⟨872651471984943181717565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2327070591959848484580173 872651471984943181717565)
                  ·
                    refine ⟨327244301994353693144087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 872651471984943181717565 327244301994353693144087)
                    ·
                      rfl

theorem cell22_955959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 3, 3].length) (baseStart_955959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_955959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_955959 prefixEnd_955959 := by exact prefixLift 955959
  have htrace : WordTrace (prefixWord ++ tailWord_955959) baseStart_955959 baseEnd_955959 := by
    simpa [prefixWord, tailWord_955959, baseEnd_955959] using wordTrace_append hprefix tailTrace_955959
  have hstable : (prefixWord ++ tailWord_955959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955959).length < 2 ^ (prefixWord ++ tailWord_955959).sum := by decide
  have hdescent : baseEnd_955959 < baseStart_955959 := by decide
  rcases family_descends (prefixWord ++ tailWord_955959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956010 : List Nat := [3, 1, 3, 2, 1, 3, 3, 2, 1, 3]
def baseStart_956010 : Nat := 118140960795 + 956010 * 2 ^ 59
def prefixEnd_956010 : Nat := 4983230072969 + 3 ^ 40 * 956010 * 2
def baseEnd_956010 : Nat := 327261760336606560118931

theorem tailTrace_956010 : CollatzResearch.WordTrace tailWord_956010 prefixEnd_956010 327261760336606560118931 := by
  unfold tailWord_956010
  simp only [CollatzResearch.WordTrace]
  refine ⟨8717137316636629588560371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23245699511031012236160989 8717137316636629588560371)
  ·
    refine ⟨13075705974954944382840557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8717137316636629588560371 13075705974954944382840557)
    ·
      refine ⟨4903389740608104143565209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13075705974954944382840557 4903389740608104143565209)
      ·
        refine ⟨3677542305456078107673907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4903389740608104143565209 3677542305456078107673907)
        ·
          refine ⟨5516313458184117161510861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3677542305456078107673907 5516313458184117161510861)
          ·
            refine ⟨2068617546819043935566573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5516313458184117161510861 2068617546819043935566573)
            ·
              refine ⟨775731580057141475837465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2068617546819043935566573 775731580057141475837465)
              ·
                refine ⟨581798685042856106878099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 775731580057141475837465 581798685042856106878099)
                ·
                  refine ⟨872698027564284160317149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 581798685042856106878099 872698027564284160317149)
                  ·
                    refine ⟨327261760336606560118931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 872698027564284160317149 327261760336606560118931)
                    ·
                      rfl

theorem cell22_956010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_956010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_956010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_956010 prefixEnd_956010 := by exact prefixLift 956010
  have htrace : WordTrace (prefixWord ++ tailWord_956010) baseStart_956010 baseEnd_956010 := by
    simpa [prefixWord, tailWord_956010, baseEnd_956010] using wordTrace_append hprefix tailTrace_956010
  have hstable : (prefixWord ++ tailWord_956010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956010).length < 2 ^ (prefixWord ++ tailWord_956010).sum := by decide
  have hdescent : baseEnd_956010 < baseStart_956010 := by decide
  rcases family_descends (prefixWord ++ tailWord_956010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956036 : List Nat := [2, 3, 2, 1, 4, 1, 1, 1, 3, 4]
def baseStart_956036 : Nat := 118140960795 + 956036 * 2 ^ 59
def prefixEnd_956036 : Nat := 4983230072969 + 3 ^ 40 * 956036 * 2
def baseEnd_956036 : Nat := 327270660667951158968851

theorem tailTrace_956036 : CollatzResearch.WordTrace tailWord_956036 prefixEnd_956036 327270660667951158968851 := by
  unfold tailWord_956036
  simp only [CollatzResearch.WordTrace]
  refine ⟨17434748782226162397343981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23246331709634883196458641 17434748782226162397343981)
  ·
    refine ⟨6538030793334810899003993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17434748782226162397343981 6538030793334810899003993)
    ·
      refine ⟨4903523095001108174252995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6538030793334810899003993 4903523095001108174252995)
      ·
        refine ⟨7355284642501662261379493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4903523095001108174252995 7355284642501662261379493)
        ·
          refine ⟨1379115870469061674008655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7355284642501662261379493 1379115870469061674008655)
          ·
            refine ⟨2068673805703592511012983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1379115870469061674008655 2068673805703592511012983)
            ·
              refine ⟨3103010708555388766519475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2068673805703592511012983 3103010708555388766519475)
              ·
                refine ⟨4654516062833083149779213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3103010708555388766519475 4654516062833083149779213)
                ·
                  refine ⟨1745443523562406181167205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4654516062833083149779213 1745443523562406181167205)
                  ·
                    refine ⟨327270660667951158968851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1745443523562406181167205 327270660667951158968851)
                    ·
                      rfl

theorem cell22_956036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_956036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_956036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_956036 prefixEnd_956036 := by exact prefixLift 956036
  have htrace : WordTrace (prefixWord ++ tailWord_956036) baseStart_956036 baseEnd_956036 := by
    simpa [prefixWord, tailWord_956036, baseEnd_956036] using wordTrace_append hprefix tailTrace_956036
  have hstable : (prefixWord ++ tailWord_956036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956036).length < 2 ^ (prefixWord ++ tailWord_956036).sum := by decide
  have hdescent : baseEnd_956036 < baseStart_956036 := by decide
  rcases family_descends (prefixWord ++ tailWord_956036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956049 : List Nat := [1, 2, 2, 1, 1, 1, 1, 6, 4, 3]
def baseStart_956049 : Nat := 118140960795 + 956049 * 2 ^ 59
def prefixEnd_956049 : Nat := 4983230072969 + 3 ^ 40 * 956049 * 2
def baseEnd_956049 : Nat := 327275110833623458393811

theorem tailTrace_956049 : CollatzResearch.WordTrace tailWord_956049 prefixEnd_956049 327275110833623458393811 := by
  unfold tailWord_956049
  simp only [CollatzResearch.WordTrace]
  refine ⟨34869971713405228014911201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23246647808936818676607467 34869971713405228014911201)
  ·
    refine ⟨26152478785053921011183401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34869971713405228014911201 26152478785053921011183401)
    ·
      refine ⟨19614359088790440758387551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26152478785053921011183401 19614359088790440758387551)
      ·
        refine ⟨29421538633185661137581327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19614359088790440758387551 29421538633185661137581327)
        ·
          refine ⟨44132307949778491706371991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29421538633185661137581327 44132307949778491706371991)
          ·
            refine ⟨66198461924667737559557987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44132307949778491706371991 66198461924667737559557987)
            ·
              refine ⟨99297692887001606339336981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66198461924667737559557987 99297692887001606339336981)
              ·
                refine ⟨4654579354078200297156421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99297692887001606339336981 4654579354078200297156421)
                ·
                  refine ⟨872733628889662555716829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4654579354078200297156421 872733628889662555716829)
                  ·
                    refine ⟨327275110833623458393811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 872733628889662555716829 327275110833623458393811)
                    ·
                      rfl

theorem cell22_956049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 4, 3].length) (baseStart_956049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_956049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_956049 prefixEnd_956049 := by exact prefixLift 956049
  have htrace : WordTrace (prefixWord ++ tailWord_956049) baseStart_956049 baseEnd_956049 := by
    simpa [prefixWord, tailWord_956049, baseEnd_956049] using wordTrace_append hprefix tailTrace_956049
  have hstable : (prefixWord ++ tailWord_956049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956049).length < 2 ^ (prefixWord ++ tailWord_956049).sum := by decide
  have hdescent : baseEnd_956049 < baseStart_956049 := by decide
  rcases family_descends (prefixWord ++ tailWord_956049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956068 : List Nat := [2, 3, 1, 2, 2, 2, 4, 2, 4]
def baseStart_956068 : Nat := 118140960795 + 956068 * 2 ^ 59
def prefixEnd_956068 : Nat := 4983230072969 + 3 ^ 40 * 956068 * 2
def baseEnd_956068 : Nat := 109093871640637914056251

theorem tailTrace_956068 : CollatzResearch.WordTrace tailWord_956068 prefixEnd_956068 109093871640637914056251 := by
  unfold tailWord_956068
  simp only [CollatzResearch.WordTrace]
  refine ⟨17435332350168197129926429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23247109800224262839901905 17435332350168197129926429)
  ·
    refine ⟨6538249631313073923722411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17435332350168197129926429 6538249631313073923722411)
    ·
      refine ⟨9807374446969610885583617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6538249631313073923722411 9807374446969610885583617)
      ·
        refine ⟨7355530835227208164187713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9807374446969610885583617 7355530835227208164187713)
        ·
          refine ⟨5516648126420406123140785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7355530835227208164187713 5516648126420406123140785)
          ·
            refine ⟨4137486094815304592355589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5516648126420406123140785 4137486094815304592355589)
            ·
              refine ⟨775778642777869611066673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4137486094815304592355589 775778642777869611066673)
              ·
                refine ⟨581833982083402208300005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 775778642777869611066673 581833982083402208300005)
                ·
                  refine ⟨109093871640637914056251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 581833982083402208300005 109093871640637914056251)
                  ·
                    rfl

theorem cell22_956068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 2, 4].length) (baseStart_956068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_956068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_956068 prefixEnd_956068 := by exact prefixLift 956068
  have htrace : WordTrace (prefixWord ++ tailWord_956068) baseStart_956068 baseEnd_956068 := by
    simpa [prefixWord, tailWord_956068, baseEnd_956068] using wordTrace_append hprefix tailTrace_956068
  have hstable : (prefixWord ++ tailWord_956068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956068).length < 2 ^ (prefixWord ++ tailWord_956068).sum := by decide
  have hdescent : baseEnd_956068 < baseStart_956068 := by decide
  rcases family_descends (prefixWord ++ tailWord_956068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956102 : List Nat := [6, 1, 2, 1, 1, 2, 2, 3, 4]
def baseStart_956102 : Nat := 118140960795 + 956102 * 2 ^ 59
def prefixEnd_956102 : Nat := 4983230072969 + 3 ^ 40 * 956102 * 2
def baseEnd_956102 : Nat := 109097751272249662272883

theorem tailTrace_956102 : CollatzResearch.WordTrace tailWord_956102 prefixEnd_956102 109097751272249662272883 := by
  unfold tailWord_956102
  simp only [CollatzResearch.WordTrace]
  refine ⟨1089747024444163064580955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23247936521475478711060373 1089747024444163064580955)
  ·
    refine ⟨1634620536666244596871433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1089747024444163064580955 1634620536666244596871433)
    ·
      refine ⟨1225965402499683447653575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1634620536666244596871433 1225965402499683447653575)
      ·
        refine ⟨1838948103749525171480363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1225965402499683447653575 1838948103749525171480363)
        ·
          refine ⟨2758422155624287757220545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1838948103749525171480363 2758422155624287757220545)
          ·
            refine ⟨2068816616718215817915409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2758422155624287757220545 2068816616718215817915409)
            ·
              refine ⟨1551612462538661863436557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2068816616718215817915409 1551612462538661863436557)
              ·
                refine ⟨581854673451998198788709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1551612462538661863436557 581854673451998198788709)
                ·
                  refine ⟨109097751272249662272883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 581854673451998198788709 109097751272249662272883)
                  ·
                    rfl

theorem cell22_956102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_956102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_956102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_956102 prefixEnd_956102 := by exact prefixLift 956102
  have htrace : WordTrace (prefixWord ++ tailWord_956102) baseStart_956102 baseEnd_956102 := by
    simpa [prefixWord, tailWord_956102, baseEnd_956102] using wordTrace_append hprefix tailTrace_956102
  have hstable : (prefixWord ++ tailWord_956102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956102).length < 2 ^ (prefixWord ++ tailWord_956102).sum := by decide
  have hdescent : baseEnd_956102 < baseStart_956102 := by decide
  rcases family_descends (prefixWord ++ tailWord_956102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956128 : List Nat := [2, 1, 1, 3, 1, 2, 4, 4, 1, 3]
def baseStart_956128 : Nat := 118140960795 + 956128 * 2 ^ 59
def prefixEnd_956128 : Nat := 4983230072969 + 3 ^ 40 * 956128 * 2
def baseEnd_956128 : Nat := 327302154148093585668569

theorem tailTrace_956128 : CollatzResearch.WordTrace tailWord_956128 prefixEnd_956128 327302154148093585668569 := by
  unfold tailWord_956128
  simp only [CollatzResearch.WordTrace]
  refine ⟨17436426540059512253518519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23248568720079349671358025 17436426540059512253518519)
  ·
    refine ⟨26154639810089268380277779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17436426540059512253518519 26154639810089268380277779)
    ·
      refine ⟨39231959715133902570416669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26154639810089268380277779 39231959715133902570416669)
      ·
        refine ⟨14711984893175213463906251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39231959715133902570416669 14711984893175213463906251)
        ·
          refine ⟨22067977339762820195859377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14711984893175213463906251 22067977339762820195859377)
          ·
            refine ⟨16550983004822115146894533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22067977339762820195859377 16550983004822115146894533)
            ·
              refine ⟨3103309313404146590042725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16550983004822115146894533 3103309313404146590042725)
              ·
                refine ⟨581870496263277485633011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3103309313404146590042725 581870496263277485633011)
                ·
                  refine ⟨872805744394916228449517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 581870496263277485633011 872805744394916228449517)
                  ·
                    refine ⟨327302154148093585668569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 872805744394916228449517 327302154148093585668569)
                    ·
                      rfl

theorem cell22_956128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 4, 1, 3].length) (baseStart_956128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_956128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_956128 prefixEnd_956128 := by exact prefixLift 956128
  have htrace : WordTrace (prefixWord ++ tailWord_956128) baseStart_956128 baseEnd_956128 := by
    simpa [prefixWord, tailWord_956128, baseEnd_956128] using wordTrace_append hprefix tailTrace_956128
  have hstable : (prefixWord ++ tailWord_956128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956128).length < 2 ^ (prefixWord ++ tailWord_956128).sum := by decide
  have hdescent : baseEnd_956128 < baseStart_956128 := by decide
  rcases family_descends (prefixWord ++ tailWord_956128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956139 : List Nat := [1, 1, 1, 1, 2, 4, 4, 1, 2, 5]
def baseStart_956139 : Nat := 118140960795 + 956139 * 2 ^ 59
def prefixEnd_956139 : Nat := 4983230072969 + 3 ^ 40 * 956139 * 2
def baseEnd_956139 : Nat := 327305919672893223643535

theorem tailTrace_956139 : CollatzResearch.WordTrace tailWord_956139 prefixEnd_956139 327305919672893223643535 := by
  unfold tailWord_956139
  simp only [CollatzResearch.WordTrace]
  refine ⟨34873254283079173385687471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23248836188719448923791647 34873254283079173385687471)
  ·
    refine ⟨52309881424618760078531207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34873254283079173385687471 52309881424618760078531207)
    ·
      refine ⟨78464822136928140117796811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52309881424618760078531207 78464822136928140117796811)
      ·
        refine ⟨117697233205392210176695217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78464822136928140117796811 117697233205392210176695217)
        ·
          refine ⟨88272924904044157632521413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117697233205392210176695217 88272924904044157632521413)
          ·
            refine ⟨16551173419508279556097765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88272924904044157632521413 16551173419508279556097765)
            ·
              refine ⟨3103345016157802416768331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16551173419508279556097765 3103345016157802416768331)
              ·
                refine ⟨4655017524236703625152497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3103345016157802416768331 4655017524236703625152497)
                ·
                  refine ⟨3491263143177527718864373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4655017524236703625152497 3491263143177527718864373)
                  ·
                    refine ⟨327305919672893223643535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3491263143177527718864373 327305919672893223643535)
                    ·
                      rfl

theorem cell22_956139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 5].length) (baseStart_956139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_956139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_956139 prefixEnd_956139 := by exact prefixLift 956139
  have htrace : WordTrace (prefixWord ++ tailWord_956139) baseStart_956139 baseEnd_956139 := by
    simpa [prefixWord, tailWord_956139, baseEnd_956139] using wordTrace_append hprefix tailTrace_956139
  have hstable : (prefixWord ++ tailWord_956139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956139).length < 2 ^ (prefixWord ++ tailWord_956139).sum := by decide
  have hdescent : baseEnd_956139 < baseStart_956139 := by decide
  rcases family_descends (prefixWord ++ tailWord_956139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956171 : List Nat := [1, 1, 1, 1, 5, 1, 4, 3, 1, 4]
def baseStart_956171 : Nat := 118140960795 + 956171 * 2 ^ 59
def prefixEnd_956171 : Nat := 4983230072969 + 3 ^ 40 * 956171 * 2
def baseEnd_956171 : Nat := 327316873926855806843437

theorem tailTrace_956171 : CollatzResearch.WordTrace tailWord_956171 prefixEnd_956171 327316873926855806843437 := by
  unfold tailWord_956171
  simp only [CollatzResearch.WordTrace]
  refine ⟨34874421418963242850852367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23249614279308828567234911 34874421418963242850852367)
  ·
    refine ⟨52311632128444864276278551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34874421418963242850852367 52311632128444864276278551)
    ·
      refine ⟨78467448192667296414417827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52311632128444864276278551 78467448192667296414417827)
      ·
        refine ⟨117701172289000944621626741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78467448192667296414417827 117701172289000944621626741)
        ·
          refine ⟨11034484902093838558277507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 117701172289000944621626741 11034484902093838558277507)
          ·
            refine ⟨16551727353140757837416261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11034484902093838558277507 16551727353140757837416261)
            ·
              refine ⟨3103448878713892094515549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16551727353140757837416261 3103448878713892094515549)
              ·
                refine ⟨1163793329517709535443331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3103448878713892094515549 1163793329517709535443331)
                ·
                  refine ⟨1745689994276564303164997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1163793329517709535443331 1745689994276564303164997)
                  ·
                    refine ⟨327316873926855806843437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1745689994276564303164997 327316873926855806843437)
                    ·
                      rfl

theorem cell22_956171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 3, 1, 4].length) (baseStart_956171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_956171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_956171 prefixEnd_956171 := by exact prefixLift 956171
  have htrace : WordTrace (prefixWord ++ tailWord_956171) baseStart_956171 baseEnd_956171 := by
    simpa [prefixWord, tailWord_956171, baseEnd_956171] using wordTrace_append hprefix tailTrace_956171
  have hstable : (prefixWord ++ tailWord_956171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956171).length < 2 ^ (prefixWord ++ tailWord_956171).sum := by decide
  have hdescent : baseEnd_956171 < baseStart_956171 := by decide
  rcases family_descends (prefixWord ++ tailWord_956171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956186 : List Nat := [3, 1, 1, 3, 2, 2, 3, 1, 6]
def baseStart_956186 : Nat := 118140960795 + 956186 * 2 ^ 59
def prefixEnd_956186 : Nat := 4983230072969 + 3 ^ 40 * 956186 * 2
def baseEnd_956186 : Nat := 109107336244466922572797

theorem tailTrace_956186 : CollatzResearch.WordTrace tailWord_956186 prefixEnd_956186 109107336244466922572797 := by
  unfold tailWord_956186
  simp only [CollatzResearch.WordTrace]
  refine ⟨8718742128477225103162103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23249979009272600275098941 8718742128477225103162103)
  ·
    refine ⟨13078113192715837654743155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8718742128477225103162103 13078113192715837654743155)
    ·
      refine ⟨19617169789073756482114733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13078113192715837654743155 19617169789073756482114733)
      ·
        refine ⟨7356438670902658680793025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19617169789073756482114733 7356438670902658680793025)
        ·
          refine ⟨5517329003176994010594769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7356438670902658680793025 5517329003176994010594769)
          ·
            refine ⟨4137996752382745507946077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5517329003176994010594769 4137996752382745507946077)
            ·
              refine ⟨1551748782143529565479779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4137996752382745507946077 1551748782143529565479779)
              ·
                refine ⟨2327623173215294348219669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1551748782143529565479779 2327623173215294348219669)
                ·
                  refine ⟨109107336244466922572797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2327623173215294348219669 109107336244466922572797)
                  ·
                    rfl

theorem cell22_956186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 6].length) (baseStart_956186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_956186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_956186 prefixEnd_956186 := by exact prefixLift 956186
  have htrace : WordTrace (prefixWord ++ tailWord_956186) baseStart_956186 baseEnd_956186 := by
    simpa [prefixWord, tailWord_956186, baseEnd_956186] using wordTrace_append hprefix tailTrace_956186
  have hstable : (prefixWord ++ tailWord_956186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956186).length < 2 ^ (prefixWord ++ tailWord_956186).sum := by decide
  have hdescent : baseEnd_956186 < baseStart_956186 := by decide
  rcases family_descends (prefixWord ++ tailWord_956186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956216 : List Nat := [2, 1, 2, 1, 3, 3, 1, 3, 2, 4]
def baseStart_956216 : Nat := 118140960795 + 956216 * 2 ^ 59
def prefixEnd_956216 : Nat := 4983230072969 + 3 ^ 40 * 956216 * 2
def baseEnd_956216 : Nat := 327332278346490689468299

theorem tailTrace_956216 : CollatzResearch.WordTrace tailWord_956216 prefixEnd_956216 327332278346490689468299 := by
  unfold tailWord_956216
  simp only [CollatzResearch.WordTrace]
  refine ⟨17438031351900107768120251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23250708469200143690827001 17438031351900107768120251)
  ·
    refine ⟨26157047027850161652180377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17438031351900107768120251 26157047027850161652180377)
    ·
      refine ⟨19617785270887621239135283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26157047027850161652180377 19617785270887621239135283)
      ·
        refine ⟨29426677906331431858702925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19617785270887621239135283 29426677906331431858702925)
        ·
          refine ⟨11035004214874286947013597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29426677906331431858702925 11035004214874286947013597)
          ·
            refine ⟨4138126580577857605130099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11035004214874286947013597 4138126580577857605130099)
            ·
              refine ⟨6207189870866786407695149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4138126580577857605130099 6207189870866786407695149)
              ·
                refine ⟨2327696201575044902885681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6207189870866786407695149 2327696201575044902885681)
                ·
                  refine ⟨1745772151181283677164261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2327696201575044902885681 1745772151181283677164261)
                  ·
                    refine ⟨327332278346490689468299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1745772151181283677164261 327332278346490689468299)
                    ·
                      rfl

theorem cell22_956216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 2, 4].length) (baseStart_956216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_956216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_956216 prefixEnd_956216 := by exact prefixLift 956216
  have htrace : WordTrace (prefixWord ++ tailWord_956216) baseStart_956216 baseEnd_956216 := by
    simpa [prefixWord, tailWord_956216, baseEnd_956216] using wordTrace_append hprefix tailTrace_956216
  have hstable : (prefixWord ++ tailWord_956216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956216).length < 2 ^ (prefixWord ++ tailWord_956216).sum := by decide
  have hdescent : baseEnd_956216 < baseStart_956216 := by decide
  rcases family_descends (prefixWord ++ tailWord_956216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956237 : List Nat := [1, 6, 1, 2, 1, 1, 4, 2, 4]
def baseStart_956237 : Nat := 118140960795 + 956237 * 2 ^ 59
def prefixEnd_956237 : Nat := 4983230072969 + 3 ^ 40 * 956237 * 2
def baseEnd_956237 : Nat := 109113155691884544897745

theorem tailTrace_956237 : CollatzResearch.WordTrace tailWord_956237 prefixEnd_956237 109113155691884544897745 := by
  unfold tailWord_956237
  simp only [CollatzResearch.WordTrace]
  refine ⟨34876828636724136122754965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23251219091149424081836643 34876828636724136122754965)
  ·
    refine ⟨1634851342346443880754139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 34876828636724136122754965 1634851342346443880754139)
    ·
      refine ⟨2452277013519665821131209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1634851342346443880754139 2452277013519665821131209)
      ·
        refine ⟨1839207760139749365848407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2452277013519665821131209 1839207760139749365848407)
        ·
          refine ⟨2758811640209624048772611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1839207760139749365848407 2758811640209624048772611)
          ·
            refine ⟨4138217460314436073158917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2758811640209624048772611 4138217460314436073158917)
            ·
              refine ⟨775915773808956763717297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4138217460314436073158917 775915773808956763717297)
              ·
                refine ⟨581936830356717572787973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 775915773808956763717297 581936830356717572787973)
                ·
                  refine ⟨109113155691884544897745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 581936830356717572787973 109113155691884544897745)
                  ·
                    rfl

theorem cell22_956237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_956237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_956237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_956237 prefixEnd_956237 := by exact prefixLift 956237
  have htrace : WordTrace (prefixWord ++ tailWord_956237) baseStart_956237 baseEnd_956237 := by
    simpa [prefixWord, tailWord_956237, baseEnd_956237] using wordTrace_append hprefix tailTrace_956237
  have hstable : (prefixWord ++ tailWord_956237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956237).length < 2 ^ (prefixWord ++ tailWord_956237).sum := by decide
  have hdescent : baseEnd_956237 < baseStart_956237 := by decide
  rcases family_descends (prefixWord ++ tailWord_956237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956263 : List Nat := [1, 1, 5, 1, 2, 1, 3, 2, 3, 3]
def baseStart_956263 : Nat := 118140960795 + 956263 * 2 ^ 59
def prefixEnd_956263 : Nat := 4983230072969 + 3 ^ 40 * 956263 * 2
def baseEnd_956263 : Nat := 327348367406998233543155

theorem tailTrace_956263 : CollatzResearch.WordTrace tailWord_956263 prefixEnd_956263 327348367406998233543155 := by
  unfold tailWord_956263
  simp only [CollatzResearch.WordTrace]
  refine ⟨34877776934629942563201443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23251851289753295042134295 34877776934629942563201443)
  ·
    refine ⟨52316665401944913844802165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34877776934629942563201443 52316665401944913844802165)
    ·
      refine ⟨4904687381432335672950203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52316665401944913844802165 4904687381432335672950203)
      ·
        refine ⟨7357031072148503509425305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4904687381432335672950203 7357031072148503509425305)
        ·
          refine ⟨5517773304111377632068979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7357031072148503509425305 5517773304111377632068979)
          ·
            refine ⟨8276659956167066448103469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5517773304111377632068979 8276659956167066448103469)
            ·
              refine ⟨3103747483562649918038801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8276659956167066448103469 3103747483562649918038801)
              ·
                refine ⟨2327810612671987438529101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3103747483562649918038801 2327810612671987438529101)
                ·
                  refine ⟨872928979751995289448413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2327810612671987438529101 872928979751995289448413)
                  ·
                    refine ⟨327348367406998233543155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 872928979751995289448413 327348367406998233543155)
                    ·
                      rfl

theorem cell22_956263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_956263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_956263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_956263 prefixEnd_956263 := by exact prefixLift 956263
  have htrace : WordTrace (prefixWord ++ tailWord_956263) baseStart_956263 baseEnd_956263 := by
    simpa [prefixWord, tailWord_956263, baseEnd_956263] using wordTrace_append hprefix tailTrace_956263
  have hstable : (prefixWord ++ tailWord_956263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956263).length < 2 ^ (prefixWord ++ tailWord_956263).sum := by decide
  have hdescent : baseEnd_956263 < baseStart_956263 := by decide
  rcases family_descends (prefixWord ++ tailWord_956263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956291 : List Nat := [1, 1, 1, 3, 4, 2, 1, 2, 2, 5]
def baseStart_956291 : Nat := 118140960795 + 956291 * 2 ^ 59
def prefixEnd_956291 : Nat := 4983230072969 + 3 ^ 40 * 956291 * 2
def baseEnd_956291 : Nat := 327357952379215493843069

theorem tailTrace_956291 : CollatzResearch.WordTrace tailWord_956291 prefixEnd_956291 327357952379215493843069 := by
  unfold tailWord_956291
  simp only [CollatzResearch.WordTrace]
  refine ⟨34878798178528503345220727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23252532119019002230147151 34878798178528503345220727)
  ·
    refine ⟨52318197267792755017831091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34878798178528503345220727 52318197267792755017831091)
    ·
      refine ⟨78477295901689132526746637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52318197267792755017831091 78477295901689132526746637)
      ·
        refine ⟨29428985963133424697529989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78477295901689132526746637 29428985963133424697529989)
        ·
          refine ⟨5517934868087517130786873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29428985963133424697529989 5517934868087517130786873)
          ·
            refine ⟨4138451151065637848090155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5517934868087517130786873 4138451151065637848090155)
            ·
              refine ⟨6207676726598456772135233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4138451151065637848090155 6207676726598456772135233)
              ·
                refine ⟨4655757544948842579101425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6207676726598456772135233 4655757544948842579101425)
                ·
                  refine ⟨3491818158711631934326069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4655757544948842579101425 3491818158711631934326069)
                  ·
                    refine ⟨327357952379215493843069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3491818158711631934326069 327357952379215493843069)
                    ·
                      rfl

theorem cell22_956291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 5].length) (baseStart_956291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_956291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_956291 prefixEnd_956291 := by exact prefixLift 956291
  have htrace : WordTrace (prefixWord ++ tailWord_956291) baseStart_956291 baseEnd_956291 := by
    simpa [prefixWord, tailWord_956291, baseEnd_956291] using wordTrace_append hprefix tailTrace_956291
  have hstable : (prefixWord ++ tailWord_956291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956291).length < 2 ^ (prefixWord ++ tailWord_956291).sum := by decide
  have hdescent : baseEnd_956291 < baseStart_956291 := by decide
  rcases family_descends (prefixWord ++ tailWord_956291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956308 : List Nat := [2, 4, 2, 1, 1, 2, 2, 1, 2, 5]
def baseStart_956308 : Nat := 118140960795 + 956308 * 2 ^ 59
def prefixEnd_956308 : Nat := 4983230072969 + 3 ^ 40 * 956308 * 2
def baseEnd_956308 : Nat := 327363771826633116168017

theorem tailTrace_956308 : CollatzResearch.WordTrace tailWord_956308 prefixEnd_956308 327363771826633116168017 := by
  unfold tailWord_956308
  simp only [CollatzResearch.WordTrace]
  refine ⟨17439709109733457624294789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23252945479644610165726385 17439709109733457624294789)
  ·
    refine ⟨3269945458075023304555273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17439709109733457624294789 3269945458075023304555273)
    ·
      refine ⟨2452459093556267478416455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3269945458075023304555273 2452459093556267478416455)
      ·
        refine ⟨3678688640334401217624683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2452459093556267478416455 3678688640334401217624683)
        ·
          refine ⟨5518032960501601826437025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3678688640334401217624683 5518032960501601826437025)
          ·
            refine ⟨4138524720376201369827769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5518032960501601826437025 4138524720376201369827769)
            ·
              refine ⟨3103893540282151027370827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4138524720376201369827769 3103893540282151027370827)
              ·
                refine ⟨4655840310423226541056241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3103893540282151027370827 4655840310423226541056241)
                ·
                  refine ⟨3491880232817419905792181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4655840310423226541056241 3491880232817419905792181)
                  ·
                    refine ⟨327363771826633116168017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3491880232817419905792181 327363771826633116168017)
                    ·
                      rfl

theorem cell22_956308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_956308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_956308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_956308 prefixEnd_956308 := by exact prefixLift 956308
  have htrace : WordTrace (prefixWord ++ tailWord_956308) baseStart_956308 baseEnd_956308 := by
    simpa [prefixWord, tailWord_956308, baseEnd_956308] using wordTrace_append hprefix tailTrace_956308
  have hstable : (prefixWord ++ tailWord_956308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956308).length < 2 ^ (prefixWord ++ tailWord_956308).sum := by decide
  have hdescent : baseEnd_956308 < baseStart_956308 := by decide
  rcases family_descends (prefixWord ++ tailWord_956308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956374 : List Nat := [5, 2, 1, 1, 3, 2, 1, 2, 1, 4]
def baseStart_956374 : Nat := 118140960795 + 956374 * 2 ^ 59
def prefixEnd_956374 : Nat := 4983230072969 + 3 ^ 40 * 956374 * 2
def baseEnd_956374 : Nat := 327386364975430944017815

theorem tailTrace_956374 : CollatzResearch.WordTrace tailWord_956374 prefixEnd_956374 327386364975430944017815 := by
  unfold tailWord_956374
  simp only [CollatzResearch.WordTrace]
  refine ⟨2180114089826738032530761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23254550291485205680328117 2180114089826738032530761)
  ·
    refine ⟨1635085567370053524398071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2180114089826738032530761 1635085567370053524398071)
    ·
      refine ⟨2452628351055080286597107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1635085567370053524398071 2452628351055080286597107)
      ·
        refine ⟨3678942526582620429895661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2452628351055080286597107 3678942526582620429895661)
        ·
          refine ⟨1379603447468482661210873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3678942526582620429895661 1379603447468482661210873)
          ·
            refine ⟨1034702585601361995908155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1379603447468482661210873 1034702585601361995908155)
            ·
              refine ⟨1552053878402042993862233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1034702585601361995908155 1552053878402042993862233)
              ·
                refine ⟨1164040408801532245396675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1552053878402042993862233 1164040408801532245396675)
                ·
                  refine ⟨1746060613202298368095013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1164040408801532245396675 1746060613202298368095013)
                  ·
                    refine ⟨327386364975430944017815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1746060613202298368095013 327386364975430944017815)
                    ·
                      rfl

theorem cell22_956374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_956374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_956374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_956374 prefixEnd_956374 := by exact prefixLift 956374
  have htrace : WordTrace (prefixWord ++ tailWord_956374) baseStart_956374 baseEnd_956374 := by
    simpa [prefixWord, tailWord_956374, baseEnd_956374] using wordTrace_append hprefix tailTrace_956374
  have hstable : (prefixWord ++ tailWord_956374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956374).length < 2 ^ (prefixWord ++ tailWord_956374).sum := by decide
  have hdescent : baseEnd_956374 < baseStart_956374 := by decide
  rcases family_descends (prefixWord ++ tailWord_956374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956396 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 4, 6]
def baseStart_956396 : Nat := 118140960795 + 956396 * 2 ^ 59
def prefixEnd_956396 : Nat := 4983230072969 + 3 ^ 40 * 956396 * 2
def baseEnd_956396 : Nat := 327393896025030219967747

theorem tailTrace_956396 : CollatzResearch.WordTrace tailWord_956396 prefixEnd_956396 327393896025030219967747 := by
  unfold tailWord_956396
  simp only [CollatzResearch.WordTrace]
  refine ⟨17441313921574053138896521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23255085228765404185195361 17441313921574053138896521)
  ·
    refine ⟨13080985441180539854172391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17441313921574053138896521 13080985441180539854172391)
    ·
      refine ⟨19621478161770809781258587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13080985441180539854172391 19621478161770809781258587)
      ·
        refine ⟨29432217242656214671887881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19621478161770809781258587 29432217242656214671887881)
        ·
          refine ⟨22074162931992161003915911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29432217242656214671887881 22074162931992161003915911)
          ·
            refine ⟨33111244397988241505873867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22074162931992161003915911 33111244397988241505873867)
            ·
              refine ⟨49666866596982362258810801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33111244397988241505873867 49666866596982362258810801)
              ·
                refine ⟨37250149947736771694108101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49666866596982362258810801 37250149947736771694108101)
                ·
                  refine ⟨6984403115200644692645269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37250149947736771694108101 6984403115200644692645269)
                  ·
                    refine ⟨327393896025030219967747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6984403115200644692645269 327393896025030219967747)
                    ·
                      rfl

theorem cell22_956396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 6].length) (baseStart_956396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_956396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_956396 prefixEnd_956396 := by exact prefixLift 956396
  have htrace : WordTrace (prefixWord ++ tailWord_956396) baseStart_956396 baseEnd_956396 := by
    simpa [prefixWord, tailWord_956396, baseEnd_956396] using wordTrace_append hprefix tailTrace_956396
  have hstable : (prefixWord ++ tailWord_956396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956396).length < 2 ^ (prefixWord ++ tailWord_956396).sum := by decide
  have hdescent : baseEnd_956396 < baseStart_956396 := by decide
  rcases family_descends (prefixWord ++ tailWord_956396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956406 : List Nat := [5, 1, 1, 1, 5, 1, 2, 2, 4]
def baseStart_956406 : Nat := 118140960795 + 956406 * 2 ^ 59
def prefixEnd_956406 : Nat := 4983230072969 + 3 ^ 40 * 956406 * 2
def baseEnd_956406 : Nat := 109132439743131175739239

theorem tailTrace_956406 : CollatzResearch.WordTrace tailWord_956406 prefixEnd_956406 109132439743131175739239 := by
  unfold tailWord_956406
  simp only [CollatzResearch.WordTrace]
  refine ⟨2180187035819492374103567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23255328382074585323771381 2180187035819492374103567)
  ·
    refine ⟨3270280553729238561155351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2180187035819492374103567 3270280553729238561155351)
    ·
      refine ⟨4905420830593857841733027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3270280553729238561155351 4905420830593857841733027)
      ·
        refine ⟨7358131245890786762599541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4905420830593857841733027 7358131245890786762599541)
        ·
          refine ⟨689824804302261258993707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7358131245890786762599541 689824804302261258993707)
          ·
            refine ⟨1034737206453391888490561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 689824804302261258993707 1034737206453391888490561)
            ·
              refine ⟨776052904840043916367921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1034737206453391888490561 776052904840043916367921)
              ·
                refine ⟨582039678630032937275941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 776052904840043916367921 582039678630032937275941)
                ·
                  refine ⟨109132439743131175739239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 582039678630032937275941 109132439743131175739239)
                  ·
                    rfl

theorem cell22_956406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_956406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_956406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_956406 prefixEnd_956406 := by exact prefixLift 956406
  have htrace : WordTrace (prefixWord ++ tailWord_956406) baseStart_956406 baseEnd_956406 := by
    simpa [prefixWord, tailWord_956406, baseEnd_956406] using wordTrace_append hprefix tailTrace_956406
  have hstable : (prefixWord ++ tailWord_956406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956406).length < 2 ^ (prefixWord ++ tailWord_956406).sum := by decide
  have hdescent : baseEnd_956406 < baseStart_956406 := by decide
  rcases family_descends (prefixWord ++ tailWord_956406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956411 : List Nat := [1, 1, 1, 1, 1, 3, 4, 3, 7]
def baseStart_956411 : Nat := 118140960795 + 956411 * 2 ^ 59
def prefixEnd_956411 : Nat := 4983230072969 + 3 ^ 40 * 956411 * 2
def baseEnd_956411 : Nat := 109133010277191726947567

theorem tailTrace_956411 : CollatzResearch.WordTrace tailWord_956411 prefixEnd_956411 109133010277191726947567 := by
  unfold tailWord_956411
  simp only [CollatzResearch.WordTrace]
  refine ⟨34883174938093763839589087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23255449958729175893059391 34883174938093763839589087)
  ·
    refine ⟨52324762407140645759383631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34883174938093763839589087 52324762407140645759383631)
    ·
      refine ⟨78487143610710968639075447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52324762407140645759383631 78487143610710968639075447)
      ·
        refine ⟨117730715416066452958613171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78487143610710968639075447 117730715416066452958613171)
        ·
          refine ⟨176596073124099679437919757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117730715416066452958613171 176596073124099679437919757)
          ·
            refine ⟨66223527421537379789219909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176596073124099679437919757 66223527421537379789219909)
            ·
              refine ⟨12416911391538258710478733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66223527421537379789219909 12416911391538258710478733)
              ·
                refine ⟨4656341771826847016429525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12416911391538258710478733 4656341771826847016429525)
                ·
                  refine ⟨109133010277191726947567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4656341771826847016429525 109133010277191726947567)
                  ·
                    rfl

theorem cell22_956411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 7].length) (baseStart_956411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_956411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_956411 prefixEnd_956411 := by exact prefixLift 956411
  have htrace : WordTrace (prefixWord ++ tailWord_956411) baseStart_956411 baseEnd_956411 := by
    simpa [prefixWord, tailWord_956411, baseEnd_956411] using wordTrace_append hprefix tailTrace_956411
  have hstable : (prefixWord ++ tailWord_956411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956411).length < 2 ^ (prefixWord ++ tailWord_956411).sum := by decide
  have hdescent : baseEnd_956411 < baseStart_956411 := by decide
  rcases family_descends (prefixWord ++ tailWord_956411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956428 : List Nat := [2, 2, 1, 2, 3, 1, 1, 5, 5]
def baseStart_956428 : Nat := 118140960795 + 956428 * 2 ^ 59
def prefixEnd_956428 : Nat := 4983230072969 + 3 ^ 40 * 956428 * 2
def baseEnd_956428 : Nat := 109134950092997601055883

theorem tailTrace_956428 : CollatzResearch.WordTrace tailWord_956428 prefixEnd_956428 109134950092997601055883 := by
  unfold tailWord_956428
  simp only [CollatzResearch.WordTrace]
  refine ⟨17441897489516087871478969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23255863319354783828638625 17441897489516087871478969)
  ·
    refine ⟨13081423117137065903609227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17441897489516087871478969 13081423117137065903609227)
    ·
      refine ⟨19622134675705598855413841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13081423117137065903609227 19622134675705598855413841)
      ·
        refine ⟨14716601006779199141560381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19622134675705598855413841 14716601006779199141560381)
        ·
          refine ⟨5518725377542199678085143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14716601006779199141560381 5518725377542199678085143)
          ·
            refine ⟨8278088066313299517127715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5518725377542199678085143 8278088066313299517127715)
            ·
              refine ⟨12417132099469949275691573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8278088066313299517127715 12417132099469949275691573)
              ·
                refine ⟨1164106134325307744596085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12417132099469949275691573 1164106134325307744596085)
                ·
                  refine ⟨109134950092997601055883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1164106134325307744596085 109134950092997601055883)
                  ·
                    rfl

theorem cell22_956428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 5, 5].length) (baseStart_956428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_956428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_956428 prefixEnd_956428 := by exact prefixLift 956428
  have htrace : WordTrace (prefixWord ++ tailWord_956428) baseStart_956428 baseEnd_956428 := by
    simpa [prefixWord, tailWord_956428, baseEnd_956428] using wordTrace_append hprefix tailTrace_956428
  have hstable : (prefixWord ++ tailWord_956428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956428).length < 2 ^ (prefixWord ++ tailWord_956428).sum := by decide
  have hdescent : baseEnd_956428 < baseStart_956428 := by decide
  rcases family_descends (prefixWord ++ tailWord_956428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956436 : List Nat := [2, 4, 3, 2, 2, 1, 1, 1, 2, 4]
def baseStart_956436 : Nat := 118140960795 + 956436 * 2 ^ 59
def prefixEnd_956436 : Nat := 4983230072969 + 3 ^ 40 * 956436 * 2
def baseEnd_956436 : Nat := 327407588842483448967625

theorem tailTrace_956436 : CollatzResearch.WordTrace tailWord_956436 prefixEnd_956436 327407588842483448967625 := by
  unfold tailWord_956436
  simp only [CollatzResearch.WordTrace]
  refine ⟨17442043381501596554624581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23256057842002128739499441 17442043381501596554624581)
  ·
    refine ⟨3270383134031549353992109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17442043381501596554624581 3270383134031549353992109)
    ·
      refine ⟨1226393675261831007747041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3270383134031549353992109 1226393675261831007747041)
      ·
        refine ⟨919795256446373255810281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1226393675261831007747041 919795256446373255810281)
        ·
          refine ⟨689846442334779941857711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 919795256446373255810281 689846442334779941857711)
          ·
            refine ⟨1034769663502169912786567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 689846442334779941857711 1034769663502169912786567)
            ·
              refine ⟨1552154495253254869179851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1034769663502169912786567 1552154495253254869179851)
              ·
                refine ⟨2328231742879882303769777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1552154495253254869179851 2328231742879882303769777)
                ·
                  refine ⟨1746173807159911727827333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2328231742879882303769777 1746173807159911727827333)
                  ·
                    refine ⟨327407588842483448967625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1746173807159911727827333 327407588842483448967625)
                    ·
                      rfl

theorem cell22_956436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_956436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_956436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_956436 prefixEnd_956436 := by exact prefixLift 956436
  have htrace : WordTrace (prefixWord ++ tailWord_956436) baseStart_956436 baseEnd_956436 := by
    simpa [prefixWord, tailWord_956436, baseEnd_956436] using wordTrace_append hprefix tailTrace_956436
  have hstable : (prefixWord ++ tailWord_956436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956436).length < 2 ^ (prefixWord ++ tailWord_956436).sum := by decide
  have hdescent : baseEnd_956436 < baseStart_956436 := by decide
  rcases family_descends (prefixWord ++ tailWord_956436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956449 : List Nat := [1, 2, 3, 2, 4, 1, 2, 3, 1, 3]
def baseStart_956449 : Nat := 118140960795 + 956449 * 2 ^ 59
def prefixEnd_956449 : Nat := 4983230072969 + 3 ^ 40 * 956449 * 2
def baseEnd_956449 : Nat := 327412039008155748392585

theorem tailTrace_956449 : CollatzResearch.WordTrace tailWord_956449 prefixEnd_956449 327412039008155748392585 := by
  unfold tailWord_956449
  simp only [CollatzResearch.WordTrace]
  refine ⟨34884560911956096329472401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23256373941304064219648267 34884560911956096329472401)
  ·
    refine ⟨26163420683967072247104301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34884560911956096329472401 26163420683967072247104301)
    ·
      refine ⟨9811282756487652092664113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26163420683967072247104301 9811282756487652092664113)
      ·
        refine ⟨7358462067365739069498085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9811282756487652092664113 7358462067365739069498085)
        ·
          refine ⟨1379711637631076075530891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7358462067365739069498085 1379711637631076075530891)
          ·
            refine ⟨2069567456446614113296337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1379711637631076075530891 2069567456446614113296337)
            ·
              refine ⟨1552175592334960584972253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2069567456446614113296337 1552175592334960584972253)
              ·
                refine ⟨582065847125610219364595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1552175592334960584972253 582065847125610219364595)
                ·
                  refine ⟨873098770688415329046893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 582065847125610219364595 873098770688415329046893)
                  ·
                    refine ⟨327412039008155748392585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 873098770688415329046893 327412039008155748392585)
                    ·
                      rfl

theorem cell22_956449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 3, 1, 3].length) (baseStart_956449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_956449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_956449 prefixEnd_956449 := by exact prefixLift 956449
  have htrace : WordTrace (prefixWord ++ tailWord_956449) baseStart_956449 baseEnd_956449 := by
    simpa [prefixWord, tailWord_956449, baseEnd_956449] using wordTrace_append hprefix tailTrace_956449
  have hstable : (prefixWord ++ tailWord_956449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956449).length < 2 ^ (prefixWord ++ tailWord_956449).sum := by decide
  have hdescent : baseEnd_956449 < baseStart_956449 := by decide
  rcases family_descends (prefixWord ++ tailWord_956449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956462 : List Nat := [4, 1, 3, 1, 1, 4, 1, 2, 5]
def baseStart_956462 : Nat := 118140960795 + 956462 * 2 ^ 59
def prefixEnd_956462 : Nat := 4983230072969 + 3 ^ 40 * 956462 * 2
def baseEnd_956462 : Nat := 109138829724609349272515

theorem tailTrace_956462 : CollatzResearch.WordTrace tailWord_956462 prefixEnd_956462 109138829724609349272515 := by
  unfold tailWord_956462
  simp only [CollatzResearch.WordTrace]
  refine ⟨4360629382613624943711955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23256690040605999699797093 4360629382613624943711955)
  ·
    refine ⟨6540944073920437415567933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4360629382613624943711955 6540944073920437415567933)
    ·
      refine ⟨2452854027720164030837975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6540944073920437415567933 2452854027720164030837975)
      ·
        refine ⟨3679281041580246046256963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2452854027720164030837975 3679281041580246046256963)
        ·
          refine ⟨5518921562370369069385445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3679281041580246046256963 5518921562370369069385445)
          ·
            refine ⟨1034797792944444200509771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5518921562370369069385445 1034797792944444200509771)
            ·
              refine ⟨1552196689416666300764657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1034797792944444200509771 1552196689416666300764657)
              ·
                refine ⟨1164147517062499725573493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1552196689416666300764657 1164147517062499725573493)
                ·
                  refine ⟨109138829724609349272515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1164147517062499725573493 109138829724609349272515)
                  ·
                    rfl

theorem cell22_956462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 2, 5].length) (baseStart_956462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_956462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_956462 prefixEnd_956462 := by exact prefixLift 956462
  have htrace : WordTrace (prefixWord ++ tailWord_956462) baseStart_956462 baseEnd_956462 := by
    simpa [prefixWord, tailWord_956462, baseEnd_956462] using wordTrace_append hprefix tailTrace_956462
  have hstable : (prefixWord ++ tailWord_956462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956462).length < 2 ^ (prefixWord ++ tailWord_956462).sum := by decide
  have hdescent : baseEnd_956462 < baseStart_956462 := by decide
  rcases family_descends (prefixWord ++ tailWord_956462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956488 : List Nat := [2, 1, 3, 1, 1, 1, 2, 5, 1, 5]
def baseStart_956488 : Nat := 118140960795 + 956488 * 2 ^ 59
def prefixEnd_956488 : Nat := 4983230072969 + 3 ^ 40 * 956488 * 2
def baseEnd_956488 : Nat := 327425389505172646667465

theorem tailTrace_956488 : CollatzResearch.WordTrace tailWord_956488 prefixEnd_956488 327425389505172646667465 := by
  unfold tailWord_956488
  simp only [CollatzResearch.WordTrace]
  refine ⟨17442991679407402995071059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23257322239209870660094745 17442991679407402995071059)
  ·
    refine ⟨26164487519111104492606589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17442991679407402995071059 26164487519111104492606589)
    ·
      refine ⟨9811682819666664184727471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26164487519111104492606589 9811682819666664184727471)
      ·
        refine ⟨14717524229499996277091207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9811682819666664184727471 14717524229499996277091207)
        ·
          refine ⟨22076286344249994415636811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14717524229499996277091207 22076286344249994415636811)
          ·
            refine ⟨33114429516374991623455217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22076286344249994415636811 33114429516374991623455217)
            ·
              refine ⟨24835822137281243717591413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33114429516374991623455217 24835822137281243717591413)
              ·
                refine ⟨2328358325370116598524195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24835822137281243717591413 2328358325370116598524195)
                ·
                  refine ⟨3492537488055174897786293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2328358325370116598524195 3492537488055174897786293)
                  ·
                    refine ⟨327425389505172646667465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3492537488055174897786293 327425389505172646667465)
                    ·
                      rfl

theorem cell22_956488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_956488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_956488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_956488 prefixEnd_956488 := by exact prefixLift 956488
  have htrace : WordTrace (prefixWord ++ tailWord_956488) baseStart_956488 baseEnd_956488 := by
    simpa [prefixWord, tailWord_956488, baseEnd_956488] using wordTrace_append hprefix tailTrace_956488
  have hstable : (prefixWord ++ tailWord_956488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956488).length < 2 ^ (prefixWord ++ tailWord_956488).sum := by decide
  have hdescent : baseEnd_956488 < baseStart_956488 := by decide
  rcases family_descends (prefixWord ++ tailWord_956488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956503 : List Nat := [1, 1, 3, 2, 2, 1, 4, 1, 1, 6]
def baseStart_956503 : Nat := 118140960795 + 956503 * 2 ^ 59
def prefixEnd_956503 : Nat := 4983230072969 + 3 ^ 40 * 956503 * 2
def baseEnd_956503 : Nat := 327430524311717607542419

theorem tailTrace_956503 : CollatzResearch.WordTrace tailWord_956503 prefixEnd_956503 327430524311717607542419 := by
  unfold tailWord_956503
  simp only [CollatzResearch.WordTrace]
  refine ⟨34886530453760463551938163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23257686969173642367958775 34886530453760463551938163)
  ·
    refine ⟨52329795680640695327907245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34886530453760463551938163 52329795680640695327907245)
    ·
      refine ⟨19623673380240260747965217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52329795680640695327907245 19623673380240260747965217)
      ·
        refine ⟨14717755035180195560973913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19623673380240260747965217 14717755035180195560973913)
        ·
          refine ⟨11038316276385146670730435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14717755035180195560973913 11038316276385146670730435)
          ·
            refine ⟨16557474414577720006095653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11038316276385146670730435 16557474414577720006095653)
            ·
              refine ⟨3104526452733322501142935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16557474414577720006095653 3104526452733322501142935)
              ·
                refine ⟨4656789679099983751714403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3104526452733322501142935 4656789679099983751714403)
                ·
                  refine ⟨6985184518649975627571605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4656789679099983751714403 6985184518649975627571605)
                  ·
                    refine ⟨327430524311717607542419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6985184518649975627571605 327430524311717607542419)
                    ·
                      rfl

theorem cell22_956503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 6].length) (baseStart_956503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_956503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_956503 prefixEnd_956503 := by exact prefixLift 956503
  have htrace : WordTrace (prefixWord ++ tailWord_956503) baseStart_956503 baseEnd_956503 := by
    simpa [prefixWord, tailWord_956503, baseEnd_956503] using wordTrace_append hprefix tailTrace_956503
  have hstable : (prefixWord ++ tailWord_956503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956503).length < 2 ^ (prefixWord ++ tailWord_956503).sum := by decide
  have hdescent : baseEnd_956503 < baseStart_956503 := by decide
  rcases family_descends (prefixWord ++ tailWord_956503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956655 : List Nat := [1, 1, 2, 1, 6, 1, 1, 2, 1, 6]
def baseStart_956655 : Nat := 118140960795 + 956655 * 2 ^ 59
def prefixEnd_956655 : Nat := 4983230072969 + 3 ^ 40 * 956655 * 2
def baseEnd_956655 : Nat := 327482557018039877741953

theorem tailTrace_956655 : CollatzResearch.WordTrace tailWord_956655 prefixEnd_956655 327482557018039877741953 := by
  unfold tailWord_956655
  simp only [CollatzResearch.WordTrace]
  refine ⟨34892074349209793511471419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23261382899473195674314279 34892074349209793511471419)
  ·
    refine ⟨52338111523814690267207129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34892074349209793511471419 52338111523814690267207129)
    ·
      refine ⟨39253583642861017700405347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52338111523814690267207129 39253583642861017700405347)
      ·
        refine ⟨58880375464291526550608021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39253583642861017700405347 58880375464291526550608021)
        ·
          refine ⟨2760017599888665307059751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 58880375464291526550608021 2760017599888665307059751)
          ·
            refine ⟨4140026399832997960589627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2760017599888665307059751 4140026399832997960589627)
            ·
              refine ⟨6210039599749496940884441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4140026399832997960589627 6210039599749496940884441)
              ·
                refine ⟨4657529699812122705663331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6210039599749496940884441 4657529699812122705663331)
                ·
                  refine ⟨6986294549718184058494997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4657529699812122705663331 6986294549718184058494997)
                  ·
                    refine ⟨327482557018039877741953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6986294549718184058494997 327482557018039877741953)
                    ·
                      rfl

theorem cell22_956655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 6].length) (baseStart_956655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_956655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_956655 prefixEnd_956655 := by exact prefixLift 956655
  have htrace : WordTrace (prefixWord ++ tailWord_956655) baseStart_956655 baseEnd_956655 := by
    simpa [prefixWord, tailWord_956655, baseEnd_956655] using wordTrace_append hprefix tailTrace_956655
  have hstable : (prefixWord ++ tailWord_956655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956655).length < 2 ^ (prefixWord ++ tailWord_956655).sum := by decide
  have hdescent : baseEnd_956655 < baseStart_956655 := by decide
  rcases family_descends (prefixWord ++ tailWord_956655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956657 : List Nat := [1, 2, 2, 2, 2, 1, 2, 5, 2, 3]
def baseStart_956657 : Nat := 118140960795 + 956657 * 2 ^ 59
def prefixEnd_956657 : Nat := 4983230072969 + 3 ^ 40 * 956657 * 2
def baseEnd_956657 : Nat := 327483241658912539191947

theorem tailTrace_956657 : CollatzResearch.WordTrace tailWord_956657 prefixEnd_956657 327483241658912539191947 := by
  unfold tailWord_956657
  simp only [CollatzResearch.WordTrace]
  refine ⟨34892147295202547853044225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23261431530135031902029483 34892147295202547853044225)
  ·
    refine ⟨26169110471401910889783169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34892147295202547853044225 26169110471401910889783169)
    ·
      refine ⟨19626832853551433167337377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26169110471401910889783169 19626832853551433167337377)
      ·
        refine ⟨14720124640163574875503033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19626832853551433167337377 14720124640163574875503033)
        ·
          refine ⟨11040093480122681156627275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14720124640163574875503033 11040093480122681156627275)
          ·
            refine ⟨16560140220184021734940913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11040093480122681156627275 16560140220184021734940913)
            ·
              refine ⟨12420105165138016301205685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16560140220184021734940913 12420105165138016301205685)
              ·
                refine ⟨1164384859231689028238033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12420105165138016301205685 1164384859231689028238033)
                ·
                  refine ⟨873288644423766771178525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1164384859231689028238033 873288644423766771178525)
                  ·
                    refine ⟨327483241658912539191947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 873288644423766771178525 327483241658912539191947)
                    ·
                      rfl

theorem cell22_956657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 5, 2, 3].length) (baseStart_956657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_956657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_956657 prefixEnd_956657 := by exact prefixLift 956657
  have htrace : WordTrace (prefixWord ++ tailWord_956657) baseStart_956657 baseEnd_956657 := by
    simpa [prefixWord, tailWord_956657, baseEnd_956657] using wordTrace_append hprefix tailTrace_956657
  have hstable : (prefixWord ++ tailWord_956657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956657).length < 2 ^ (prefixWord ++ tailWord_956657).sum := by decide
  have hdescent : baseEnd_956657 < baseStart_956657 := by decide
  rcases family_descends (prefixWord ++ tailWord_956657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956674 : List Nat := [3, 4, 1, 1, 2, 1, 1, 2, 4, 3]
def baseStart_956674 : Nat := 118140960795 + 956674 * 2 ^ 59
def prefixEnd_956674 : Nat := 4983230072969 + 3 ^ 40 * 956674 * 2
def baseEnd_956674 : Nat := 327489061106330161516895

theorem tailTrace_956674 : CollatzResearch.WordTrace tailWord_956674 prefixEnd_956674 327489061106330161516895 := by
  unfold tailWord_956674
  simp only [CollatzResearch.WordTrace]
  refine ⟨8723191834035239939103269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23261844890760639837608717 8723191834035239939103269)
  ·
    refine ⟨1635598468881607488581863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8723191834035239939103269 1635598468881607488581863)
    ·
      refine ⟨2453397703322411232872795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1635598468881607488581863 2453397703322411232872795)
      ·
        refine ⟨3680096554983616849309193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2453397703322411232872795 3680096554983616849309193)
        ·
          refine ⟨2760072416237712636981895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3680096554983616849309193 2760072416237712636981895)
          ·
            refine ⟨4140108624356568955472843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2760072416237712636981895 4140108624356568955472843)
            ·
              refine ⟨6210162936534853433209265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4140108624356568955472843 6210162936534853433209265)
              ·
                refine ⟨4657622202401140074906949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6210162936534853433209265 4657622202401140074906949)
                ·
                  refine ⟨873304162950213764045053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4657622202401140074906949 873304162950213764045053)
                  ·
                    refine ⟨327489061106330161516895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 873304162950213764045053 327489061106330161516895)
                    ·
                      rfl

theorem cell22_956674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_956674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_956674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_956674 prefixEnd_956674 := by exact prefixLift 956674
  have htrace : WordTrace (prefixWord ++ tailWord_956674) baseStart_956674 baseEnd_956674 := by
    simpa [prefixWord, tailWord_956674, baseEnd_956674] using wordTrace_append hprefix tailTrace_956674
  have hstable : (prefixWord ++ tailWord_956674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956674).length < 2 ^ (prefixWord ++ tailWord_956674).sum := by decide
  have hdescent : baseEnd_956674 < baseStart_956674 := by decide
  rcases family_descends (prefixWord ++ tailWord_956674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956676 : List Nat := [2, 3, 2, 2, 3, 2, 1, 3, 4]
def baseStart_956676 : Nat := 118140960795 + 956676 * 2 ^ 59
def prefixEnd_956676 : Nat := 4983230072969 + 3 ^ 40 * 956676 * 2
def baseEnd_956676 : Nat := 109163248582400940988963

theorem tailTrace_956676 : CollatzResearch.WordTrace tailWord_956676 prefixEnd_956676 109163248582400940988963 := by
  unfold tailWord_956676
  simp only [CollatzResearch.WordTrace]
  refine ⟨17446420141066857048992941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23261893521422476065323921 17446420141066857048992941)
  ·
    refine ⟨6542407552900071393372353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17446420141066857048992941 6542407552900071393372353)
    ·
      refine ⟨4906805664675053545029265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6542407552900071393372353 4906805664675053545029265)
      ·
        refine ⟨3680104248506290158771949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4906805664675053545029265 3680104248506290158771949)
        ·
          refine ⟨1380039093189858809539481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3680104248506290158771949 1380039093189858809539481)
          ·
            refine ⟨1035029319892394107154611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1380039093189858809539481 1035029319892394107154611)
            ·
              refine ⟨1552543979838591160731917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1035029319892394107154611 1552543979838591160731917)
              ·
                refine ⟨582203992439471685274469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1552543979838591160731917 582203992439471685274469)
                ·
                  refine ⟨109163248582400940988963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 582203992439471685274469 109163248582400940988963)
                  ·
                    rfl

theorem cell22_956676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 3, 4].length) (baseStart_956676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_956676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_956676 prefixEnd_956676 := by exact prefixLift 956676
  have htrace : WordTrace (prefixWord ++ tailWord_956676) baseStart_956676 baseEnd_956676 := by
    simpa [prefixWord, tailWord_956676, baseEnd_956676] using wordTrace_append hprefix tailTrace_956676
  have hstable : (prefixWord ++ tailWord_956676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956676).length < 2 ^ (prefixWord ++ tailWord_956676).sum := by decide
  have hdescent : baseEnd_956676 < baseStart_956676 := by decide
  rcases family_descends (prefixWord ++ tailWord_956676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956700 : List Nat := [2, 2, 3, 1, 1, 1, 1, 3, 2, 6]
def baseStart_956700 : Nat := 118140960795 + 956700 * 2 ^ 59
def prefixEnd_956700 : Nat := 4983230072969 + 3 ^ 40 * 956700 * 2
def baseEnd_956700 : Nat := 327497961437674760366815

theorem tailTrace_956700 : CollatzResearch.WordTrace tailWord_956700 prefixEnd_956700 327497961437674760366815 := by
  unfold tailWord_956700
  simp only [CollatzResearch.WordTrace]
  refine ⟨17446857817023383098429777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23262477089364510797906369 17446857817023383098429777)
  ·
    refine ⟨13085143362767537323822333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17446857817023383098429777 13085143362767537323822333)
    ·
      refine ⟨4906928761037826496433375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13085143362767537323822333 4906928761037826496433375)
      ·
        refine ⟨7360393141556739744650063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4906928761037826496433375 7360393141556739744650063)
        ·
          refine ⟨11040589712335109616975095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7360393141556739744650063 11040589712335109616975095)
          ·
            refine ⟨16560884568502664425462643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11040589712335109616975095 16560884568502664425462643)
            ·
              refine ⟨24841326852753996638193965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16560884568502664425462643 24841326852753996638193965)
              ·
                refine ⟨9315497569782748739322737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24841326852753996638193965 9315497569782748739322737)
                ·
                  refine ⟨6986623177337061554492053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9315497569782748739322737 6986623177337061554492053)
                  ·
                    refine ⟨327497961437674760366815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6986623177337061554492053 327497961437674760366815)
                    ·
                      rfl

theorem cell22_956700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_956700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_956700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_956700 prefixEnd_956700 := by exact prefixLift 956700
  have htrace : WordTrace (prefixWord ++ tailWord_956700) baseStart_956700 baseEnd_956700 := by
    simpa [prefixWord, tailWord_956700, baseEnd_956700] using wordTrace_append hprefix tailTrace_956700
  have hstable : (prefixWord ++ tailWord_956700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956700).length < 2 ^ (prefixWord ++ tailWord_956700).sum := by decide
  have hdescent : baseEnd_956700 < baseStart_956700 := by decide
  rcases family_descends (prefixWord ++ tailWord_956700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956753 : List Nat := [1, 2, 2, 1, 4, 4, 2, 2, 1, 3]
def baseStart_956753 : Nat := 118140960795 + 956753 * 2 ^ 59
def prefixEnd_956753 : Nat := 4983230072969 + 3 ^ 40 * 956753 * 2
def baseEnd_956753 : Nat := 327516104420800288791653

theorem tailTrace_956753 : CollatzResearch.WordTrace tailWord_956753 prefixEnd_956753 327516104420800288791653 := by
  unfold tailWord_956753
  simp only [CollatzResearch.WordTrace]
  refine ⟨34895648702854756248538913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23263765801903170832359275 34895648702854756248538913)
  ·
    refine ⟨26171736527141067186404185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34895648702854756248538913 26171736527141067186404185)
    ·
      refine ⟨19628802395355800389803139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26171736527141067186404185 19628802395355800389803139)
      ·
        refine ⟨29443203593033700584704709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19628802395355800389803139 29443203593033700584704709)
        ·
          refine ⟨5520600673693818859632133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29443203593033700584704709 5520600673693818859632133)
          ·
            refine ⟨1035112626317591036181025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5520600673693818859632133 1035112626317591036181025)
            ·
              refine ⟨776334469738193277135769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1035112626317591036181025 776334469738193277135769)
              ·
                refine ⟨582250852303644957851827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 776334469738193277135769 582250852303644957851827)
                ·
                  refine ⟨873376278455467436777741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 582250852303644957851827 873376278455467436777741)
                  ·
                    refine ⟨327516104420800288791653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 873376278455467436777741 327516104420800288791653)
                    ·
                      rfl

theorem cell22_956753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 2, 1, 3].length) (baseStart_956753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_956753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_956753 prefixEnd_956753 := by exact prefixLift 956753
  have htrace : WordTrace (prefixWord ++ tailWord_956753) baseStart_956753 baseEnd_956753 := by
    simpa [prefixWord, tailWord_956753, baseEnd_956753] using wordTrace_append hprefix tailTrace_956753
  have hstable : (prefixWord ++ tailWord_956753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956753).length < 2 ^ (prefixWord ++ tailWord_956753).sum := by decide
  have hdescent : baseEnd_956753 < baseStart_956753 := by decide
  rcases family_descends (prefixWord ++ tailWord_956753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956807 : List Nat := [1, 1, 4, 2, 2, 1, 2, 1, 4, 4]
def baseStart_956807 : Nat := 118140960795 + 956807 * 2 ^ 59
def prefixEnd_956807 : Nat := 4983230072969 + 3 ^ 40 * 956807 * 2
def baseEnd_956807 : Nat := 327534589724362147941487

theorem tailTrace_956807 : CollatzResearch.WordTrace tailWord_956807 prefixEnd_956807 327534589724362147941487 := by
  unfold tailWord_956807
  simp only [CollatzResearch.WordTrace]
  refine ⟨34897618244659123471004675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23265078829772748980669783 34897618244659123471004675)
  ·
    refine ⟨52346427366988685206507013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34897618244659123471004675 52346427366988685206507013)
    ·
      refine ⟨9814955131310378476220065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52346427366988685206507013 9814955131310378476220065)
      ·
        refine ⟨7361216348482783857165049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9814955131310378476220065 7361216348482783857165049)
        ·
          refine ⟨5520912261362087892873787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7361216348482783857165049 5520912261362087892873787)
          ·
            refine ⟨8281368392043131839310681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5520912261362087892873787 8281368392043131839310681)
            ·
              refine ⟨6211026294032348879483011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8281368392043131839310681 6211026294032348879483011)
              ·
                refine ⟨9316539441048523319224517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6211026294032348879483011 9316539441048523319224517)
                ·
                  refine ⟨1746851145196598122354597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9316539441048523319224517 1746851145196598122354597)
                  ·
                    refine ⟨327534589724362147941487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1746851145196598122354597 327534589724362147941487)
                    ·
                      rfl

theorem cell22_956807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_956807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_956807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_956807 prefixEnd_956807 := by exact prefixLift 956807
  have htrace : WordTrace (prefixWord ++ tailWord_956807) baseStart_956807 baseEnd_956807 := by
    simpa [prefixWord, tailWord_956807, baseEnd_956807] using wordTrace_append hprefix tailTrace_956807
  have hstable : (prefixWord ++ tailWord_956807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956807).length < 2 ^ (prefixWord ++ tailWord_956807).sum := by decide
  have hdescent : baseEnd_956807 < baseStart_956807 := by decide
  rcases family_descends (prefixWord ++ tailWord_956807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956809 : List Nat := [1, 2, 1, 1, 6, 2, 1, 1, 4, 3]
def baseStart_956809 : Nat := 118140960795 + 956809 * 2 ^ 59
def prefixEnd_956809 : Nat := 4983230072969 + 3 ^ 40 * 956809 * 2
def baseEnd_956809 : Nat := 327535274365234809391481

theorem tailTrace_956809 : CollatzResearch.WordTrace tailWord_956809 prefixEnd_956809 327535274365234809391481 := by
  unfold tailWord_956809
  simp only [CollatzResearch.WordTrace]
  refine ⟨34897691190651877812577481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23265127460434585208384987 34897691190651877812577481)
  ·
    refine ⟨26173268392988908359433111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34897691190651877812577481 26173268392988908359433111)
    ·
      refine ⟨39259902589483362539149667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26173268392988908359433111 39259902589483362539149667)
      ·
        refine ⟨58889853884225043808724501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39259902589483362539149667 58889853884225043808724501)
        ·
          refine ⟨2760461900823048928533961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 58889853884225043808724501 2760461900823048928533961)
          ·
            refine ⟨2070346425617286696400471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2760461900823048928533961 2070346425617286696400471)
            ·
              refine ⟨3105519638425930044600707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2070346425617286696400471 3105519638425930044600707)
              ·
                refine ⟨4658279457638895066901061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3105519638425930044600707 4658279457638895066901061)
                ·
                  refine ⟨873427398307292825043949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4658279457638895066901061 873427398307292825043949)
                  ·
                    refine ⟨327535274365234809391481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 873427398307292825043949 327535274365234809391481)
                    ·
                      rfl

theorem cell22_956809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 4, 3].length) (baseStart_956809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_956809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_956809 prefixEnd_956809 := by exact prefixLift 956809
  have htrace : WordTrace (prefixWord ++ tailWord_956809) baseStart_956809 baseEnd_956809 := by
    simpa [prefixWord, tailWord_956809, baseEnd_956809] using wordTrace_append hprefix tailTrace_956809
  have hstable : (prefixWord ++ tailWord_956809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956809).length < 2 ^ (prefixWord ++ tailWord_956809).sum := by decide
  have hdescent : baseEnd_956809 < baseStart_956809 := by decide
  rcases family_descends (prefixWord ++ tailWord_956809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956839 : List Nat := [1, 1, 6, 1, 1, 2, 4, 6]
def baseStart_956839 : Nat := 118140960795 + 956839 * 2 ^ 59
def prefixEnd_956839 : Nat := 4983230072969 + 3 ^ 40 * 956839 * 2
def baseEnd_956839 : Nat := 36393949330924970126821

theorem tailTrace_956839 : CollatzResearch.WordTrace tailWord_956839 prefixEnd_956839 36393949330924970126821 := by
  unfold tailWord_956839
  simp only [CollatzResearch.WordTrace]
  refine ⟨34898785380543192936169571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23265856920362128624113047 34898785380543192936169571)
  ·
    refine ⟨52348178070814789404254357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34898785380543192936169571 52348178070814789404254357)
    ·
      refine ⟨2453820847069443253324423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 52348178070814789404254357 2453820847069443253324423)
      ·
        refine ⟨3680731270604164879986635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2453820847069443253324423 3680731270604164879986635)
        ·
          refine ⟨5521096905906247319979953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3680731270604164879986635 5521096905906247319979953)
          ·
            refine ⟨4140822679429685489984965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5521096905906247319979953 4140822679429685489984965)
            ·
              refine ⟨776404252393066029372181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4140822679429685489984965 776404252393066029372181)
              ·
                refine ⟨36393949330924970126821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 776404252393066029372181 36393949330924970126821)
                ·
                  rfl

theorem cell22_956839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 6].length) (baseStart_956839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_956839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_956839 prefixEnd_956839 := by exact prefixLift 956839
  have htrace : WordTrace (prefixWord ++ tailWord_956839) baseStart_956839 baseEnd_956839 := by
    simpa [prefixWord, tailWord_956839, baseEnd_956839] using wordTrace_append hprefix tailTrace_956839
  have hstable : (prefixWord ++ tailWord_956839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956839).length < 2 ^ (prefixWord ++ tailWord_956839).sum := by decide
  have hdescent : baseEnd_956839 < baseStart_956839 := by decide
  rcases family_descends (prefixWord ++ tailWord_956839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956845 : List Nat := [1, 5, 2, 2, 3, 1, 1, 3, 4]
def baseStart_956845 : Nat := 118140960795 + 956845 * 2 ^ 59
def prefixEnd_956845 : Nat := 4983230072969 + 3 ^ 40 * 956845 * 2
def baseEnd_956845 : Nat := 109182532633647571830457

theorem tailTrace_956845 : CollatzResearch.WordTrace tailWord_956845 prefixEnd_956845 109182532633647571830457 := by
  unfold tailWord_956845
  simp only [CollatzResearch.WordTrace]
  refine ⟨34899004218521455960887989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23266002812347637307258659 34899004218521455960887989)
  ·
    refine ⟨3271781645486386496333249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34899004218521455960887989 3271781645486386496333249)
    ·
      refine ⟨2453836234114789872249937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3271781645486386496333249 2453836234114789872249937)
      ·
        refine ⟨1840377175586092404187453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2453836234114789872249937 1840377175586092404187453)
        ·
          refine ⟨690141440844784651570295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1840377175586092404187453 690141440844784651570295)
          ·
            refine ⟨1035212161267176977355443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 690141440844784651570295 1035212161267176977355443)
            ·
              refine ⟨1552818241900765466033165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1035212161267176977355443 1552818241900765466033165)
              ·
                refine ⟨582306840712787049762437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1552818241900765466033165 582306840712787049762437)
                ·
                  refine ⟨109182532633647571830457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 582306840712787049762437 109182532633647571830457)
                  ·
                    rfl

theorem cell22_956845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_956845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_956845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_956845 prefixEnd_956845 := by exact prefixLift 956845
  have htrace : WordTrace (prefixWord ++ tailWord_956845) baseStart_956845 baseEnd_956845 := by
    simpa [prefixWord, tailWord_956845, baseEnd_956845] using wordTrace_append hprefix tailTrace_956845
  have hstable : (prefixWord ++ tailWord_956845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956845).length < 2 ^ (prefixWord ++ tailWord_956845).sum := by decide
  have hdescent : baseEnd_956845 < baseStart_956845 := by decide
  rcases family_descends (prefixWord ++ tailWord_956845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956867 : List Nat := [1, 1, 1, 3, 1, 1, 3, 6, 5]
def baseStart_956867 : Nat := 118140960795 + 956867 * 2 ^ 59
def prefixEnd_956867 : Nat := 4983230072969 + 3 ^ 40 * 956867 * 2
def baseEnd_956867 : Nat := 109185042983513997147101

theorem tailTrace_956867 : CollatzResearch.WordTrace tailWord_956867 prefixEnd_956867 109185042983513997147101 := by
  unfold tailWord_956867
  simp only [CollatzResearch.WordTrace]
  refine ⟨34899806624441753718188855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23266537749627835812125903 34899806624441753718188855)
  ·
    refine ⟨52349709936662630577283283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34899806624441753718188855 52349709936662630577283283)
    ·
      refine ⟨78524564904993945865924925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52349709936662630577283283 78524564904993945865924925)
      ·
        refine ⟨29446711839372729699721847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78524564904993945865924925 29446711839372729699721847)
        ·
          refine ⟨44170067759059094549582771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29446711839372729699721847 44170067759059094549582771)
          ·
            refine ⟨66255101638588641824374157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44170067759059094549582771 66255101638588641824374157)
            ·
              refine ⟨24845663114470740684140309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66255101638588641824374157 24845663114470740684140309)
              ·
                refine ⟨1164640458490815969569077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24845663114470740684140309 1164640458490815969569077)
                ·
                  refine ⟨109185042983513997147101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1164640458490815969569077 109185042983513997147101)
                  ·
                    rfl

theorem cell22_956867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 6, 5].length) (baseStart_956867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_956867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_956867 prefixEnd_956867 := by exact prefixLift 956867
  have htrace : WordTrace (prefixWord ++ tailWord_956867) baseStart_956867 baseEnd_956867 := by
    simpa [prefixWord, tailWord_956867, baseEnd_956867] using wordTrace_append hprefix tailTrace_956867
  have hstable : (prefixWord ++ tailWord_956867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956867).length < 2 ^ (prefixWord ++ tailWord_956867).sum := by decide
  have hdescent : baseEnd_956867 < baseStart_956867 := by decide
  rcases family_descends (prefixWord ++ tailWord_956867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956871 : List Nat := [1, 1, 4, 1, 1, 6, 1, 1, 3, 3]
def baseStart_956871 : Nat := 118140960795 + 956871 * 2 ^ 59
def prefixEnd_956871 : Nat := 4983230072969 + 3 ^ 40 * 956871 * 2
def baseEnd_956871 : Nat := 327556498232287314341291

theorem tailTrace_956871 : CollatzResearch.WordTrace tailWord_956871 prefixEnd_956871 327556498232287314341291 := by
  unfold tailWord_956871
  simp only [CollatzResearch.WordTrace]
  refine ⟨34899952516427262401334467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23266635010951508267556311 34899952516427262401334467)
  ·
    refine ⟨52349928774640893602001701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34899952516427262401334467 52349928774640893602001701)
    ·
      refine ⟨9815611645245167550375319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52349928774640893602001701 9815611645245167550375319)
      ·
        refine ⟨14723417467867751325562979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9815611645245167550375319 14723417467867751325562979)
        ·
          refine ⟨22085126201801626988344469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14723417467867751325562979 22085126201801626988344469)
          ·
            refine ⟨1035240290709451265078647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22085126201801626988344469 1035240290709451265078647)
            ·
              refine ⟨1552860436064176897617971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1035240290709451265078647 1552860436064176897617971)
              ·
                refine ⟨2329290654096265346426957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1552860436064176897617971 2329290654096265346426957)
                ·
                  refine ⟨873483995286099504910109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2329290654096265346426957 873483995286099504910109)
                  ·
                    refine ⟨327556498232287314341291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 873483995286099504910109 327556498232287314341291)
                    ·
                      rfl

theorem cell22_956871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 3, 3].length) (baseStart_956871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_956871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_956871 prefixEnd_956871 := by exact prefixLift 956871
  have htrace : WordTrace (prefixWord ++ tailWord_956871) baseStart_956871 baseEnd_956871 := by
    simpa [prefixWord, tailWord_956871, baseEnd_956871] using wordTrace_append hprefix tailTrace_956871
  have hstable : (prefixWord ++ tailWord_956871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956871).length < 2 ^ (prefixWord ++ tailWord_956871).sum := by decide
  have hdescent : baseEnd_956871 < baseStart_956871 := by decide
  rcases family_descends (prefixWord ++ tailWord_956871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956927 : List Nat := [1, 1, 2, 2, 1, 2, 3, 2, 3, 5]
def baseStart_956927 : Nat := 118140960795 + 956927 * 2 ^ 59
def prefixEnd_956927 : Nat := 4983230072969 + 3 ^ 40 * 956927 * 2
def baseEnd_956927 : Nat := 327575668176721834941119

theorem tailTrace_956927 : CollatzResearch.WordTrace tailWord_956927 prefixEnd_956927 327575668176721834941119 := by
  unfold tailWord_956927
  simp only [CollatzResearch.WordTrace]
  refine ⟨34901995004224383965373035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23267996669482922643582023 34901995004224383965373035)
  ·
    refine ⟨52352992506336575948059553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34901995004224383965373035 52352992506336575948059553)
    ·
      refine ⟨39264744379752431961044665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52352992506336575948059553 39264744379752431961044665)
      ·
        refine ⟨29448558284814323970783499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39264744379752431961044665 29448558284814323970783499)
        ·
          refine ⟨44172837427221485956175249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29448558284814323970783499 44172837427221485956175249)
          ·
            refine ⟨33129628070416114467131437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44172837427221485956175249 33129628070416114467131437)
            ·
              refine ⟨12423610526406042925174289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33129628070416114467131437 12423610526406042925174289)
              ·
                refine ⟨9317707894804532193880717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12423610526406042925174289 9317707894804532193880717)
                ·
                  refine ⟨3494140460551699572705269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9317707894804532193880717 3494140460551699572705269)
                  ·
                    refine ⟨327575668176721834941119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3494140460551699572705269 327575668176721834941119)
                    ·
                      rfl

theorem cell22_956927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 5].length) (baseStart_956927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_956927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_956927 prefixEnd_956927 := by exact prefixLift 956927
  have htrace : WordTrace (prefixWord ++ tailWord_956927) baseStart_956927 baseEnd_956927 := by
    simpa [prefixWord, tailWord_956927, baseEnd_956927] using wordTrace_append hprefix tailTrace_956927
  have hstable : (prefixWord ++ tailWord_956927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956927).length < 2 ^ (prefixWord ++ tailWord_956927).sum := by decide
  have hdescent : baseEnd_956927 < baseStart_956927 := by decide
  rcases family_descends (prefixWord ++ tailWord_956927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956972 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 1, 9]
def baseStart_956972 : Nat := 118140960795 + 956972 * 2 ^ 59
def prefixEnd_956972 : Nat := 4983230072969 + 3 ^ 40 * 956972 * 2
def baseEnd_956972 : Nat := 327591072596356717565981

theorem tailTrace_956972 : CollatzResearch.WordTrace tailWord_956972 prefixEnd_956972 327591072596356717565981 := by
  unfold tailWord_956972
  simp only [CollatzResearch.WordTrace]
  refine ⟨17451818144530678325380585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23269090859374237767174113 17451818144530678325380585)
  ·
    refine ⟨13088863608398008744035439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17451818144530678325380585 13088863608398008744035439)
    ·
      refine ⟨19633295412597013116053159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13088863608398008744035439 19633295412597013116053159)
      ·
        refine ⟨29449943118895519674079739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19633295412597013116053159 29449943118895519674079739)
        ·
          refine ⟨44174914678343279511119609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29449943118895519674079739 44174914678343279511119609)
          ·
            refine ⟨33131186008757459633339707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44174914678343279511119609 33131186008757459633339707)
            ·
              refine ⟨49696779013136189450009561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33131186008757459633339707 49696779013136189450009561)
              ·
                refine ⟨37272584259852142087507171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49696779013136189450009561 37272584259852142087507171)
                ·
                  refine ⟨55908876389778213131260757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37272584259852142087507171 55908876389778213131260757)
                  ·
                    refine ⟨327591072596356717565981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 55908876389778213131260757 327591072596356717565981)
                    ·
                      rfl

theorem cell22_956972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 9].length) (baseStart_956972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_956972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_956972 prefixEnd_956972 := by exact prefixLift 956972
  have htrace : WordTrace (prefixWord ++ tailWord_956972) baseStart_956972 baseEnd_956972 := by
    simpa [prefixWord, tailWord_956972, baseEnd_956972] using wordTrace_append hprefix tailTrace_956972
  have hstable : (prefixWord ++ tailWord_956972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956972).length < 2 ^ (prefixWord ++ tailWord_956972).sum := by decide
  have hdescent : baseEnd_956972 < baseStart_956972 := by decide
  rcases family_descends (prefixWord ++ tailWord_956972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956987 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 6, 6]
def baseStart_956987 : Nat := 118140960795 + 956987 * 2 ^ 59
def prefixEnd_956987 : Nat := 4983230072969 + 3 ^ 40 * 956987 * 2
def baseEnd_956987 : Nat := 327596207402901678440935

theorem tailTrace_956987 : CollatzResearch.WordTrace tailWord_956987 prefixEnd_956987 327596207402901678440935 := by
  unfold tailWord_956987
  simp only [CollatzResearch.WordTrace]
  refine ⟨34904183384007014212557215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23269455589338009475038143 34904183384007014212557215)
  ·
    refine ⟨52356275076010521318835823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34904183384007014212557215 52356275076010521318835823)
    ·
      refine ⟨78534412614015781978253735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52356275076010521318835823 78534412614015781978253735)
      ·
        refine ⟨117801618921023672967380603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78534412614015781978253735 117801618921023672967380603)
        ·
          refine ⟨176702428381535509451070905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117801618921023672967380603 176702428381535509451070905)
          ·
            refine ⟨132526821286151632088303179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176702428381535509451070905 132526821286151632088303179)
            ·
              refine ⟨198790231929227448132454769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132526821286151632088303179 198790231929227448132454769)
              ·
                refine ⟨149092673946920586099341077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198790231929227448132454769 149092673946920586099341077)
                ·
                  refine ⟨6988719091261902473406613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 149092673946920586099341077 6988719091261902473406613)
                  ·
                    refine ⟨327596207402901678440935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6988719091261902473406613 327596207402901678440935)
                    ·
                      rfl

theorem cell22_956987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 6].length) (baseStart_956987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_956987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_956987 prefixEnd_956987 := by exact prefixLift 956987
  have htrace : WordTrace (prefixWord ++ tailWord_956987) baseStart_956987 baseEnd_956987 := by
    simpa [prefixWord, tailWord_956987, baseEnd_956987] using wordTrace_append hprefix tailTrace_956987
  have hstable : (prefixWord ++ tailWord_956987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956987).length < 2 ^ (prefixWord ++ tailWord_956987).sum := by decide
  have hdescent : baseEnd_956987 < baseStart_956987 := by decide
  rcases family_descends (prefixWord ++ tailWord_956987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957006 : List Nat := [4, 1, 1, 1, 1, 2, 4, 2, 3, 3]
def baseStart_957006 : Nat := 118140960795 + 957006 * 2 ^ 59
def prefixEnd_957006 : Nat := 4983230072969 + 3 ^ 40 * 957006 * 2
def baseEnd_957006 : Nat := 327602711491191962215877

theorem tailTrace_957006 : CollatzResearch.WordTrace tailWord_957006 prefixEnd_957006 327602711491191962215877 := by
  unfold tailWord_957006
  simp only [CollatzResearch.WordTrace]
  refine ⟨4363109546367272557187359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23269917580625453638332581 4363109546367272557187359)
  ·
    refine ⟨6544664319550908835781039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4363109546367272557187359 6544664319550908835781039)
    ·
      refine ⟨9816996479326363253671559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6544664319550908835781039 9816996479326363253671559)
      ·
        refine ⟨14725494718989544880507339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9816996479326363253671559 14725494718989544880507339)
        ·
          refine ⟨22088242078484317320761009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14725494718989544880507339 22088242078484317320761009)
          ·
            refine ⟨16566181558863237990570757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22088242078484317320761009 16566181558863237990570757)
            ·
              refine ⟨3106159042286857123232017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16566181558863237990570757 3106159042286857123232017)
              ·
                refine ⟨2329619281715142842424013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3106159042286857123232017 2329619281715142842424013)
                ·
                  refine ⟨873607230643178565909005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2329619281715142842424013 873607230643178565909005)
                  ·
                    refine ⟨327602711491191962215877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 873607230643178565909005 327602711491191962215877)
                    ·
                      rfl

theorem cell22_957006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 3, 3].length) (baseStart_957006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_957006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_957006 prefixEnd_957006 := by exact prefixLift 957006
  have htrace : WordTrace (prefixWord ++ tailWord_957006) baseStart_957006 baseEnd_957006 := by
    simpa [prefixWord, tailWord_957006, baseEnd_957006] using wordTrace_append hprefix tailTrace_957006
  have hstable : (prefixWord ++ tailWord_957006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957006).length < 2 ^ (prefixWord ++ tailWord_957006).sum := by decide
  have hdescent : baseEnd_957006 < baseStart_957006 := by decide
  rcases family_descends (prefixWord ++ tailWord_957006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957040 : List Nat := [2, 1, 1, 1, 8, 1, 1, 1, 3, 3]
def baseStart_957040 : Nat := 118140960795 + 957040 * 2 ^ 59
def prefixEnd_957040 : Nat := 4983230072969 + 3 ^ 40 * 957040 * 2
def baseEnd_957040 : Nat := 327614350386027206865773

theorem tailTrace_957040 : CollatzResearch.WordTrace tailWord_957040 prefixEnd_957040 327614350386027206865773 := by
  unfold tailWord_957040
  simp only [CollatzResearch.WordTrace]
  refine ⟨17453058226407502132118287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23270744301876669509491049 17453058226407502132118287)
  ·
    refine ⟨26179587339611253198177431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17453058226407502132118287 26179587339611253198177431)
    ·
      refine ⟨39269381009416879797266147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26179587339611253198177431 39269381009416879797266147)
      ·
        refine ⟨58904071514125319695899221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39269381009416879797266147 58904071514125319695899221)
        ·
          refine ⟨690282088056156090186319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 58904071514125319695899221 690282088056156090186319)
          ·
            refine ⟨1035423132084234135279479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 690282088056156090186319 1035423132084234135279479)
            ·
              refine ⟨1553134698126351202919219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1035423132084234135279479 1553134698126351202919219)
              ·
                refine ⟨2329702047189526804378829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1553134698126351202919219 2329702047189526804378829)
                ·
                  refine ⟨873638267696072551642061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2329702047189526804378829 873638267696072551642061)
                  ·
                    refine ⟨327614350386027206865773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 873638267696072551642061 327614350386027206865773)
                    ·
                      rfl

theorem cell22_957040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 3, 3].length) (baseStart_957040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_957040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_957040 prefixEnd_957040 := by exact prefixLift 957040
  have htrace : WordTrace (prefixWord ++ tailWord_957040) baseStart_957040 baseEnd_957040 := by
    simpa [prefixWord, tailWord_957040, baseEnd_957040] using wordTrace_append hprefix tailTrace_957040
  have hstable : (prefixWord ++ tailWord_957040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957040).length < 2 ^ (prefixWord ++ tailWord_957040).sum := by decide
  have hdescent : baseEnd_957040 < baseStart_957040 := by decide
  rcases family_descends (prefixWord ++ tailWord_957040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957081 : List Nat := [1, 2, 1, 2, 1, 2, 4, 5, 4]
def baseStart_957081 : Nat := 118140960795 + 957081 * 2 ^ 59
def prefixEnd_957081 : Nat := 4983230072969 + 3 ^ 40 * 957081 * 2
def baseEnd_957081 : Nat := 109209461841305588863549

theorem tailTrace_957081 : CollatzResearch.WordTrace tailWord_957081 prefixEnd_957081 109209461841305588863549 := by
  unfold tailWord_957081
  simp only [CollatzResearch.WordTrace]
  refine ⟨34907611845666468266479097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23271741230444312177652731 34907611845666468266479097)
  ·
    refine ⟨26180708884249851199859323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34907611845666468266479097 26180708884249851199859323)
    ·
      refine ⟨39271063326374776799788985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26180708884249851199859323 39271063326374776799788985)
      ·
        refine ⟨29453297494781082599841739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39271063326374776799788985 29453297494781082599841739)
        ·
          refine ⟨44179946242171623899762609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29453297494781082599841739 44179946242171623899762609)
          ·
            refine ⟨33134959681628717924821957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44179946242171623899762609 33134959681628717924821957)
            ·
              refine ⟨6212804940305384610904117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33134959681628717924821957 6212804940305384610904117)
              ·
                refine ⟨582450463153629807272261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6212804940305384610904117 582450463153629807272261)
                ·
                  refine ⟨109209461841305588863549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 582450463153629807272261 109209461841305588863549)
                  ·
                    rfl

theorem cell22_957081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 5, 4].length) (baseStart_957081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_957081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_957081 prefixEnd_957081 := by exact prefixLift 957081
  have htrace : WordTrace (prefixWord ++ tailWord_957081) baseStart_957081 baseEnd_957081 := by
    simpa [prefixWord, tailWord_957081, baseEnd_957081] using wordTrace_append hprefix tailTrace_957081
  have hstable : (prefixWord ++ tailWord_957081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957081).length < 2 ^ (prefixWord ++ tailWord_957081).sum := by decide
  have hdescent : baseEnd_957081 < baseStart_957081 := by decide
  rcases family_descends (prefixWord ++ tailWord_957081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957128 : List Nat := [2, 1, 3, 1, 2, 5, 1, 1, 2, 4]
def baseStart_957128 : Nat := 118140960795 + 957128 * 2 ^ 59
def prefixEnd_957128 : Nat := 4983230072969 + 3 ^ 40 * 957128 * 2
def baseEnd_957128 : Nat := 327644474584424310665503

theorem tailTrace_957128 : CollatzResearch.WordTrace tailWord_957128 prefixEnd_957128 327644474584424310665503 := by
  unfold tailWord_957128
  simp only [CollatzResearch.WordTrace]
  refine ⟨17454663038248097646720019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23272884050997463528960025 17454663038248097646720019)
  ·
    refine ⟨26181994557372146470080029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17454663038248097646720019 26181994557372146470080029)
    ·
      refine ⟨9818247959014554926280011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26181994557372146470080029 9818247959014554926280011)
      ·
        refine ⟨14727371938521832389420017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9818247959014554926280011 14727371938521832389420017)
        ·
          refine ⟨11045528953891374292065013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14727371938521832389420017 11045528953891374292065013)
          ·
            refine ⟨1035518339427316339881095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11045528953891374292065013 1035518339427316339881095)
            ·
              refine ⟨1553277509140974509821643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1035518339427316339881095 1553277509140974509821643)
              ·
                refine ⟨2329916263711461764732465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1553277509140974509821643 2329916263711461764732465)
                ·
                  refine ⟨1747437197783596323549349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2329916263711461764732465 1747437197783596323549349)
                  ·
                    refine ⟨327644474584424310665503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1747437197783596323549349 327644474584424310665503)
                    ·
                      rfl

theorem cell22_957128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 2, 4].length) (baseStart_957128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_957128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_957128 prefixEnd_957128 := by exact prefixLift 957128
  have htrace : WordTrace (prefixWord ++ tailWord_957128) baseStart_957128 baseEnd_957128 := by
    simpa [prefixWord, tailWord_957128, baseEnd_957128] using wordTrace_append hprefix tailTrace_957128
  have hstable : (prefixWord ++ tailWord_957128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957128).length < 2 ^ (prefixWord ++ tailWord_957128).sum := by decide
  have hdescent : baseEnd_957128 < baseStart_957128 := by decide
  rcases family_descends (prefixWord ++ tailWord_957128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957192 : List Nat := [2, 1, 3, 2, 2, 4, 1, 3, 1, 3]
def baseStart_957192 : Nat := 118140960795 + 957192 * 2 ^ 59
def prefixEnd_957192 : Nat := 4983230072969 + 3 ^ 40 * 957192 * 2
def baseEnd_957192 : Nat := 327666383092349477065307

theorem tailTrace_957192 : CollatzResearch.WordTrace tailWord_957192 prefixEnd_957192 327666383092349477065307 := by
  unfold tailWord_957192
  simp only [CollatzResearch.WordTrace]
  refine ⟨17455830174132167111884915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23274440232176222815846553 17455830174132167111884915)
  ·
    refine ⟨26183745261198250667827373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17455830174132167111884915 26183745261198250667827373)
    ·
      refine ⟨9818904472949344000435265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26183745261198250667827373 9818904472949344000435265)
      ·
        refine ⟨7364178354712008000326449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9818904472949344000435265 7364178354712008000326449)
        ·
          refine ⟨5523133766034006000244837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7364178354712008000326449 5523133766034006000244837)
          ·
            refine ⟨1035587581131376125045907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5523133766034006000244837 1035587581131376125045907)
            ·
              refine ⟨1553381371697064187568861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1035587581131376125045907 1553381371697064187568861)
              ·
                refine ⟨582518014386399070338323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1553381371697064187568861 582518014386399070338323)
                ·
                  refine ⟨873777021579598605507485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 582518014386399070338323 873777021579598605507485)
                  ·
                    refine ⟨327666383092349477065307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 873777021579598605507485 327666383092349477065307)
                    ·
                      rfl

theorem cell22_957192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 3, 1, 3].length) (baseStart_957192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_957192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_957192 prefixEnd_957192 := by exact prefixLift 957192
  have htrace : WordTrace (prefixWord ++ tailWord_957192) baseStart_957192 baseEnd_957192 := by
    simpa [prefixWord, tailWord_957192, baseEnd_957192] using wordTrace_append hprefix tailTrace_957192
  have hstable : (prefixWord ++ tailWord_957192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957192).length < 2 ^ (prefixWord ++ tailWord_957192).sum := by decide
  have hdescent : baseEnd_957192 < baseStart_957192 := by decide
  rcases family_descends (prefixWord ++ tailWord_957192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957235 : List Nat := [1, 1, 1, 2, 6, 3, 1, 2, 1, 4]
def baseStart_957235 : Nat := 118140960795 + 957235 * 2 ^ 59
def prefixEnd_957235 : Nat := 4983230072969 + 3 ^ 40 * 957235 * 2
def baseEnd_957235 : Nat := 327681102871111698240175

theorem tailTrace_957235 : CollatzResearch.WordTrace tailWord_957235 prefixEnd_957235 327681102871111698240175 := by
  unfold tailWord_957235
  simp only [CollatzResearch.WordTrace]
  refine ⟨34913228687108552567585159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23275485791405701711723439 34913228687108552567585159)
  ·
    refine ⟨52369843030662828851377739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34913228687108552567585159 52369843030662828851377739)
    ·
      refine ⟨78554764545994243277066609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52369843030662828851377739 78554764545994243277066609)
      ·
        refine ⟨58916073409495682457799957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78554764545994243277066609 58916073409495682457799957)
        ·
          refine ⟨2761690941070110115209373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 58916073409495682457799957 2761690941070110115209373)
          ·
            refine ⟨1035634102901291293203515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2761690941070110115209373 1035634102901291293203515)
            ·
              refine ⟨1553451154351936939805273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1035634102901291293203515 1553451154351936939805273)
              ·
                refine ⟨1165088365763952704853955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1553451154351936939805273 1165088365763952704853955)
                ·
                  refine ⟨1747632548645929057280933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1165088365763952704853955 1747632548645929057280933)
                  ·
                    refine ⟨327681102871111698240175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1747632548645929057280933 327681102871111698240175)
                    ·
                      rfl

theorem cell22_957235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 2, 1, 4].length) (baseStart_957235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_957235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_957235 prefixEnd_957235 := by exact prefixLift 957235
  have htrace : WordTrace (prefixWord ++ tailWord_957235) baseStart_957235 baseEnd_957235 := by
    simpa [prefixWord, tailWord_957235, baseEnd_957235] using wordTrace_append hprefix tailTrace_957235
  have hstable : (prefixWord ++ tailWord_957235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957235).length < 2 ^ (prefixWord ++ tailWord_957235).sum := by decide
  have hdescent : baseEnd_957235 < baseStart_957235 := by decide
  rcases family_descends (prefixWord ++ tailWord_957235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957306 : List Nat := [3, 1, 1, 1, 1, 1, 3, 4, 7]
def baseStart_957306 : Nat := 118140960795 + 957306 * 2 ^ 59
def prefixEnd_957306 : Nat := 4983230072969 + 3 ^ 40 * 957306 * 2
def baseEnd_957306 : Nat := 109235135874030393238319

theorem tailTrace_957306 : CollatzResearch.WordTrace tailWord_957306 prefixEnd_957306 109235135874030393238319 := by
  unfold tailWord_957306
  simp only [CollatzResearch.WordTrace]
  refine ⟨8728954567462832923354943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23277212179900887795613181 8728954567462832923354943)
  ·
    refine ⟨13093431851194249385032415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8728954567462832923354943 13093431851194249385032415)
    ·
      refine ⟨19640147776791374077548623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13093431851194249385032415 19640147776791374077548623)
      ·
        refine ⟨29460221665187061116322935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19640147776791374077548623 29460221665187061116322935)
        ·
          refine ⟨44190332497780591674484403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29460221665187061116322935 44190332497780591674484403)
          ·
            refine ⟨66285498746670887511726605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44190332497780591674484403 66285498746670887511726605)
            ·
              refine ⟨24857062030001582816897477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66285498746670887511726605 24857062030001582816897477)
              ·
                refine ⟨4660699130625296778168277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24857062030001582816897477 4660699130625296778168277)
                ·
                  refine ⟨109235135874030393238319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4660699130625296778168277 109235135874030393238319)
                  ·
                    rfl

theorem cell22_957306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 7].length) (baseStart_957306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_957306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_957306 prefixEnd_957306 := by exact prefixLift 957306
  have htrace : WordTrace (prefixWord ++ tailWord_957306) baseStart_957306 baseEnd_957306 := by
    simpa [prefixWord, tailWord_957306, baseEnd_957306] using wordTrace_append hprefix tailTrace_957306
  have hstable : (prefixWord ++ tailWord_957306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957306).length < 2 ^ (prefixWord ++ tailWord_957306).sum := by decide
  have hdescent : baseEnd_957306 < baseStart_957306 := by decide
  rcases family_descends (prefixWord ++ tailWord_957306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957323 : List Nat := [1, 1, 1, 1, 4, 2, 5, 2, 5]
def baseStart_957323 : Nat := 118140960795 + 957323 * 2 ^ 59
def prefixEnd_957323 : Nat := 4983230072969 + 3 ^ 40 * 957323 * 2
def baseEnd_957323 : Nat := 109237075689836267346635

theorem tailTrace_957323 : CollatzResearch.WordTrace tailWord_957323 prefixEnd_957323 109237075689836267346635 := by
  unfold tailWord_957323
  simp only [CollatzResearch.WordTrace]
  refine ⟨34916438310789743596788623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23277625540526495731192415 34916438310789743596788623)
  ·
    refine ⟨52374657466184615395182935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34916438310789743596788623 52374657466184615395182935)
    ·
      refine ⟨78561986199276923092774403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52374657466184615395182935 78561986199276923092774403)
      ·
        refine ⟨117842979298915384639161605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78561986199276923092774403 117842979298915384639161605)
        ·
          refine ⟨22095558618546634619842801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117842979298915384639161605 22095558618546634619842801)
          ·
            refine ⟨16571668963909975964882101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22095558618546634619842801 16571668963909975964882101)
            ·
              refine ⟨1553593965366560246707697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16571668963909975964882101 1553593965366560246707697)
              ·
                refine ⟨1165195474024920185030773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1553593965366560246707697 1165195474024920185030773)
                ·
                  refine ⟨109237075689836267346635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1165195474024920185030773 109237075689836267346635)
                  ·
                    rfl

theorem cell22_957323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 2, 5].length) (baseStart_957323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_957323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_957323 prefixEnd_957323 := by exact prefixLift 957323
  have htrace : WordTrace (prefixWord ++ tailWord_957323) baseStart_957323 baseEnd_957323 := by
    simpa [prefixWord, tailWord_957323, baseEnd_957323] using wordTrace_append hprefix tailTrace_957323
  have hstable : (prefixWord ++ tailWord_957323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957323).length < 2 ^ (prefixWord ++ tailWord_957323).sum := by decide
  have hdescent : baseEnd_957323 < baseStart_957323 := by decide
  rcases family_descends (prefixWord ++ tailWord_957323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957361 : List Nat := [1, 2, 2, 4, 4, 1, 1, 3, 1, 3]
def baseStart_957361 : Nat := 118140960795 + 957361 * 2 ^ 59
def prefixEnd_957361 : Nat := 4983230072969 + 3 ^ 40 * 957361 * 2
def baseEnd_957361 : Nat := 327724235246089369589789

theorem tailTrace_957361 : CollatzResearch.WordTrace tailWord_957361 prefixEnd_957361 327724235246089369589789 := by
  unfold tailWord_957361
  simp only [CollatzResearch.WordTrace]
  refine ⟨34917824284652076086671937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23278549523101384057781291 34917824284652076086671937)
  ·
    refine ⟨26188368213489057065003953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34917824284652076086671937 26188368213489057065003953)
    ·
      refine ⟨19641276160116792798752965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26188368213489057065003953 19641276160116792798752965)
      ·
        refine ⟨3682739280021898649766181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19641276160116792798752965 3682739280021898649766181)
        ·
          refine ⟨690513615004105996831159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3682739280021898649766181 690513615004105996831159)
          ·
            refine ⟨1035770422506158995246739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 690513615004105996831159 1035770422506158995246739)
            ·
              refine ⟨1553655633759238492870109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1035770422506158995246739 1553655633759238492870109)
              ·
                refine ⟨582620862659714434826291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1553655633759238492870109 582620862659714434826291)
                ·
                  refine ⟨873931293989571652239437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 582620862659714434826291 873931293989571652239437)
                  ·
                    refine ⟨327724235246089369589789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 873931293989571652239437 327724235246089369589789)
                    ·
                      rfl

theorem cell22_957361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 3, 1, 3].length) (baseStart_957361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_957361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_957361 prefixEnd_957361 := by exact prefixLift 957361
  have htrace : WordTrace (prefixWord ++ tailWord_957361) baseStart_957361 baseEnd_957361 := by
    simpa [prefixWord, tailWord_957361, baseEnd_957361] using wordTrace_append hprefix tailTrace_957361
  have hstable : (prefixWord ++ tailWord_957361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957361).length < 2 ^ (prefixWord ++ tailWord_957361).sum := by decide
  have hdescent : baseEnd_957361 < baseStart_957361 := by decide
  rcases family_descends (prefixWord ++ tailWord_957361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957415 : List Nat := [1, 1, 5, 2, 2, 1, 1, 3, 2, 4]
def baseStart_957415 : Nat := 118140960795 + 957415 * 2 ^ 59
def prefixEnd_957415 : Nat := 4983230072969 + 3 ^ 40 * 957415 * 2
def baseEnd_957415 : Nat := 327742720549651228739623

theorem tailTrace_957415 : CollatzResearch.WordTrace tailWord_957415 prefixEnd_957415 327742720549651228739623 := by
  unfold tailWord_957415
  simp only [CollatzResearch.WordTrace]
  refine ⟨34919793826456443309137699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23279862550970962206091799 34919793826456443309137699)
  ·
    refine ⟨52379690739684664963706549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34919793826456443309137699 52379690739684664963706549)
    ·
      refine ⟨4910596006845437340347489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52379690739684664963706549 4910596006845437340347489)
      ·
        refine ⟨3682947005134078005260617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4910596006845437340347489 3682947005134078005260617)
        ·
          refine ⟨2762210253850558503945463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3682947005134078005260617 2762210253850558503945463)
          ·
            refine ⟨4143315380775837755918195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2762210253850558503945463 4143315380775837755918195)
            ·
              refine ⟨6214973071163756633877293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4143315380775837755918195 6214973071163756633877293)
              ·
                refine ⟨2330614901686408737703985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6214973071163756633877293 2330614901686408737703985)
                ·
                  refine ⟨1747961176264806553277989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2330614901686408737703985 1747961176264806553277989)
                  ·
                    refine ⟨327742720549651228739623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1747961176264806553277989 327742720549651228739623)
                    ·
                      rfl

theorem cell22_957415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_957415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_957415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_957415 prefixEnd_957415 := by exact prefixLift 957415
  have htrace : WordTrace (prefixWord ++ tailWord_957415) baseStart_957415 baseEnd_957415 := by
    simpa [prefixWord, tailWord_957415, baseEnd_957415] using wordTrace_append hprefix tailTrace_957415
  have hstable : (prefixWord ++ tailWord_957415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957415).length < 2 ^ (prefixWord ++ tailWord_957415).sum := by decide
  have hdescent : baseEnd_957415 < baseStart_957415 := by decide
  rcases family_descends (prefixWord ++ tailWord_957415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957445 : List Nat := [1, 3, 1, 1, 2, 3, 2, 3, 3, 3]
def baseStart_957445 : Nat := 118140960795 + 957445 * 2 ^ 59
def prefixEnd_957445 : Nat := 4983230072969 + 3 ^ 40 * 957445 * 2
def baseEnd_957445 : Nat := 327752990162741150489531

theorem tailTrace_957445 : CollatzResearch.WordTrace tailWord_957445 prefixEnd_957445 327752990162741150489531 := by
  unfold tailWord_957445
  simp only [CollatzResearch.WordTrace]
  refine ⟨34920888016347758432729789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23280592010898505621819859 34920888016347758432729789)
  ·
    refine ⟨13095333006130409412273671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34920888016347758432729789 13095333006130409412273671)
    ·
      refine ⟨19642999509195614118410507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13095333006130409412273671 19642999509195614118410507)
      ·
        refine ⟨29464499263793421177615761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19642999509195614118410507 29464499263793421177615761)
        ·
          refine ⟨22098374447845065883211821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29464499263793421177615761 22098374447845065883211821)
          ·
            refine ⟨8286890417941899706204433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22098374447845065883211821 8286890417941899706204433)
            ·
              refine ⟨6215167813456424779653325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8286890417941899706204433 6215167813456424779653325)
              ·
                refine ⟨2330687930046159292369997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6215167813456424779653325 2330687930046159292369997)
                ·
                  refine ⟨874007973767309734638749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2330687930046159292369997 874007973767309734638749)
                  ·
                    refine ⟨327752990162741150489531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 874007973767309734638749 327752990162741150489531)
                    ·
                      rfl

theorem cell22_957445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 3, 3].length) (baseStart_957445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_957445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_957445 prefixEnd_957445 := by exact prefixLift 957445
  have htrace : WordTrace (prefixWord ++ tailWord_957445) baseStart_957445 baseEnd_957445 := by
    simpa [prefixWord, tailWord_957445, baseEnd_957445] using wordTrace_append hprefix tailTrace_957445
  have hstable : (prefixWord ++ tailWord_957445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957445).length < 2 ^ (prefixWord ++ tailWord_957445).sum := by decide
  have hdescent : baseEnd_957445 < baseStart_957445 := by decide
  rcases family_descends (prefixWord ++ tailWord_957445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957492 : List Nat := [2, 5, 1, 2, 1, 2, 1, 1, 7]
def baseStart_957492 : Nat := 118140960795 + 957492 * 2 ^ 59
def prefixEnd_957492 : Nat := 4983230072969 + 3 ^ 40 * 957492 * 2
def baseEnd_957492 : Nat := 109256359741082898188129

theorem tailTrace_957492 : CollatzResearch.WordTrace tailWord_957492 prefixEnd_957492 109256359741082898188129 := by
  unfold tailWord_957492
  simp only [CollatzResearch.WordTrace]
  refine ⟨17461301123588742729845365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23281734831451656973127153 17461301123588742729845365)
  ·
    refine ⟨1636996980336444630923003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17461301123588742729845365 1636996980336444630923003)
    ·
      refine ⟨2455495470504666946384505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1636996980336444630923003 2455495470504666946384505)
      ·
        refine ⟨1841621602878500209788379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2455495470504666946384505 1841621602878500209788379)
        ·
          refine ⟨2762432404317750314682569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1841621602878500209788379 2762432404317750314682569)
          ·
            refine ⟨2071824303238312736011927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2762432404317750314682569 2071824303238312736011927)
            ·
              refine ⟨3107736454857469104017891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2071824303238312736011927 3107736454857469104017891)
              ·
                refine ⟨4661604682286203656026837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3107736454857469104017891 4661604682286203656026837)
                ·
                  refine ⟨109256359741082898188129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4661604682286203656026837 109256359741082898188129)
                  ·
                    rfl

theorem cell22_957492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_957492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_957492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_957492 prefixEnd_957492 := by exact prefixLift 957492
  have htrace : WordTrace (prefixWord ++ tailWord_957492) baseStart_957492 baseEnd_957492 := by
    simpa [prefixWord, tailWord_957492, baseEnd_957492] using wordTrace_append hprefix tailTrace_957492
  have hstable : (prefixWord ++ tailWord_957492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957492).length < 2 ^ (prefixWord ++ tailWord_957492).sum := by decide
  have hdescent : baseEnd_957492 < baseStart_957492 := by decide
  rcases family_descends (prefixWord ++ tailWord_957492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957522 : List Nat := [3, 2, 2, 1, 3, 1, 1, 4, 1, 4]
def baseStart_957522 : Nat := 118140960795 + 957522 * 2 ^ 59
def prefixEnd_957522 : Nat := 4983230072969 + 3 ^ 40 * 957522 * 2
def baseEnd_957522 : Nat := 327779348836338616314295

theorem tailTrace_957522 : CollatzResearch.WordTrace tailWord_957522 prefixEnd_957522 327779348836338616314295 := by
  unfold tailWord_957522
  simp only [CollatzResearch.WordTrace]
  refine ⟨8730924109267200145820705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23282464291379200388855213 8730924109267200145820705)
  ·
    refine ⟨6548193081950400109365529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8730924109267200145820705 6548193081950400109365529)
    ·
      refine ⟨4911144811462800082024147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6548193081950400109365529 4911144811462800082024147)
      ·
        refine ⟨7366717217194200123036221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4911144811462800082024147 7366717217194200123036221)
        ·
          refine ⟨2762518956447825046138583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7366717217194200123036221 2762518956447825046138583)
          ·
            refine ⟨4143778434671737569207875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2762518956447825046138583 4143778434671737569207875)
            ·
              refine ⟨6215667652007606353811813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4143778434671737569207875 6215667652007606353811813)
              ·
                refine ⟨1165437684751426191339715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6215667652007606353811813 1165437684751426191339715)
                ·
                  refine ⟨1748156527127139287009573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1165437684751426191339715 1748156527127139287009573)
                  ·
                    refine ⟨327779348836338616314295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1748156527127139287009573 327779348836338616314295)
                    ·
                      rfl

theorem cell22_957522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_957522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_957522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_957522 prefixEnd_957522 := by exact prefixLift 957522
  have htrace : WordTrace (prefixWord ++ tailWord_957522) baseStart_957522 baseEnd_957522 := by
    simpa [prefixWord, tailWord_957522, baseEnd_957522] using wordTrace_append hprefix tailTrace_957522
  have hstable : (prefixWord ++ tailWord_957522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957522).length < 2 ^ (prefixWord ++ tailWord_957522).sum := by decide
  have hdescent : baseEnd_957522 < baseStart_957522 := by decide
  rcases family_descends (prefixWord ++ tailWord_957522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957535 : List Nat := [1, 1, 2, 3, 1, 1, 3, 1, 6, 3]
def baseStart_957535 : Nat := 118140960795 + 957535 * 2 ^ 59
def prefixEnd_957535 : Nat := 4983230072969 + 3 ^ 40 * 957535 * 2
def baseEnd_957535 : Nat := 327783799002010915739255

theorem tailTrace_957535 : CollatzResearch.WordTrace tailWord_957535 prefixEnd_957535 327783799002010915739255 := by
  unfold tailWord_957535
  simp only [CollatzResearch.WordTrace]
  refine ⟨34924170586021703803506059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23282780390681135869004039 34924170586021703803506059)
  ·
    refine ⟨52386255879032555705259089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34924170586021703803506059 52386255879032555705259089)
    ·
      refine ⟨39289691909274416778944317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52386255879032555705259089 39289691909274416778944317)
      ·
        refine ⟨14733634465977906292104119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39289691909274416778944317 14733634465977906292104119)
        ·
          refine ⟨22100451698966859438156179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14733634465977906292104119 22100451698966859438156179)
          ·
            refine ⟨33150677548450289157234269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22100451698966859438156179 33150677548450289157234269)
            ·
              refine ⟨12431504080668858433962851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33150677548450289157234269 12431504080668858433962851)
              ·
                refine ⟨18647256121003287650944277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12431504080668858433962851 18647256121003287650944277)
                ·
                  refine ⟨874090130672029108638013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 18647256121003287650944277 874090130672029108638013)
                  ·
                    refine ⟨327783799002010915739255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 874090130672029108638013 327783799002010915739255)
                    ·
                      rfl

theorem cell22_957535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 6, 3].length) (baseStart_957535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_957535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_957535 prefixEnd_957535 := by exact prefixLift 957535
  have htrace : WordTrace (prefixWord ++ tailWord_957535) baseStart_957535 baseEnd_957535 := by
    simpa [prefixWord, tailWord_957535, baseEnd_957535] using wordTrace_append hprefix tailTrace_957535
  have hstable : (prefixWord ++ tailWord_957535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957535).length < 2 ^ (prefixWord ++ tailWord_957535).sum := by decide
  have hdescent : baseEnd_957535 < baseStart_957535 := by decide
  rcases family_descends (prefixWord ++ tailWord_957535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957537 : List Nat := [1, 2, 3, 1, 1, 2, 5, 3, 4]
def baseStart_957537 : Nat := 118140960795 + 957537 * 2 ^ 59
def prefixEnd_957537 : Nat := 4983230072969 + 3 ^ 40 * 957537 * 2
def baseEnd_957537 : Nat := 109261494547627859063083

theorem tailTrace_957537 : CollatzResearch.WordTrace tailWord_957537 prefixEnd_957537 109261494547627859063083 := by
  unfold tailWord_957537
  simp only [CollatzResearch.WordTrace]
  refine ⟨34924243532014458145078865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23282829021342972096719243 34924243532014458145078865)
  ·
    refine ⟨26193182649010843608809149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34924243532014458145078865 26193182649010843608809149)
    ·
      refine ⟨9822443493379066353303431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26193182649010843608809149 9822443493379066353303431)
      ·
        refine ⟨14733665240068599529955147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9822443493379066353303431 14733665240068599529955147)
        ·
          refine ⟨22100497860102899294932721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14733665240068599529955147 22100497860102899294932721)
          ·
            refine ⟨16575373395077174471199541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22100497860102899294932721 16575373395077174471199541)
            ·
              refine ⟨1553941255788485106674957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16575373395077174471199541 1553941255788485106674957)
              ·
                refine ⟨582727970920681915003109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1553941255788485106674957 582727970920681915003109)
                ·
                  refine ⟨109261494547627859063083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 582727970920681915003109 109261494547627859063083)
                  ·
                    rfl

theorem cell22_957537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 3, 4].length) (baseStart_957537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_957537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_957537 prefixEnd_957537 := by exact prefixLift 957537
  have htrace : WordTrace (prefixWord ++ tailWord_957537) baseStart_957537 baseEnd_957537 := by
    simpa [prefixWord, tailWord_957537, baseEnd_957537] using wordTrace_append hprefix tailTrace_957537
  have hstable : (prefixWord ++ tailWord_957537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957537).length < 2 ^ (prefixWord ++ tailWord_957537).sum := by decide
  have hdescent : baseEnd_957537 < baseStart_957537 := by decide
  rcases family_descends (prefixWord ++ tailWord_957537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957552 : List Nat := [2, 1, 1, 1, 5, 1, 2, 4, 2, 3]
def baseStart_957552 : Nat := 118140960795 + 957552 * 2 ^ 59
def prefixEnd_957552 : Nat := 4983230072969 + 3 ^ 40 * 957552 * 2
def baseEnd_957552 : Nat := 327789618449428538064203

theorem tailTrace_957552 : CollatzResearch.WordTrace tailWord_957552 prefixEnd_957552 327789618449428538064203 := by
  unfold tailWord_957552
  simp only [CollatzResearch.WordTrace]
  refine ⟨17462395313480057853437455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23283193751306743804583273 17462395313480057853437455)
  ·
    refine ⟨26193592970220086780156183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17462395313480057853437455 26193592970220086780156183)
    ·
      refine ⟨39290389455330130170234275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26193592970220086780156183 39290389455330130170234275)
      ·
        refine ⟨58935584182995195255351413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39290389455330130170234275 58935584182995195255351413)
        ·
          refine ⟨5525211017155799555189195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58935584182995195255351413 5525211017155799555189195)
          ·
            refine ⟨8287816525733699332783793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5525211017155799555189195 8287816525733699332783793)
            ·
              refine ⟨6215862394300274499587845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8287816525733699332783793 6215862394300274499587845)
              ·
                refine ⟨1165474198931301468672721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6215862394300274499587845 1165474198931301468672721)
                ·
                  refine ⟨874105649198476101504541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1165474198931301468672721 874105649198476101504541)
                  ·
                    refine ⟨327789618449428538064203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 874105649198476101504541 327789618449428538064203)
                    ·
                      rfl

theorem cell22_957552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 4, 2, 3].length) (baseStart_957552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_957552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_957552 prefixEnd_957552 := by exact prefixLift 957552
  have htrace : WordTrace (prefixWord ++ tailWord_957552) baseStart_957552 baseEnd_957552 := by
    simpa [prefixWord, tailWord_957552, baseEnd_957552] using wordTrace_append hprefix tailTrace_957552
  have hstable : (prefixWord ++ tailWord_957552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957552).length < 2 ^ (prefixWord ++ tailWord_957552).sum := by decide
  have hdescent : baseEnd_957552 < baseStart_957552 := by decide
  rcases family_descends (prefixWord ++ tailWord_957552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957554 : List Nat := [3, 2, 1, 2, 2, 1, 5, 2, 4]
def baseStart_957554 : Nat := 118140960795 + 957554 * 2 ^ 59
def prefixEnd_957554 : Nat := 4983230072969 + 3 ^ 40 * 957554 * 2
def baseEnd_957554 : Nat := 109263434363433733171399

theorem tailTrace_957554 : CollatzResearch.WordTrace tailWord_957554 prefixEnd_957554 109263434363433733171399 := by
  unfold tailWord_957554
  simp only [CollatzResearch.WordTrace]
  refine ⟨8731215893238217512111929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23283242381968580032298477 8731215893238217512111929)
  ·
    refine ⟨6548411919928663134083947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8731215893238217512111929 6548411919928663134083947)
    ·
      refine ⟨9822617879892994701125921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6548411919928663134083947 9822617879892994701125921)
      ·
        refine ⟨7366963409919746025844441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9822617879892994701125921 7366963409919746025844441)
        ·
          refine ⟨5525222557439809519383331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7366963409919746025844441 5525222557439809519383331)
          ·
            refine ⟨8287833836159714279074997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5525222557439809519383331 8287833836159714279074997)
            ·
              refine ⟨776984422139973213663281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8287833836159714279074997 776984422139973213663281)
              ·
                refine ⟨582738316604979910247461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 776984422139973213663281 582738316604979910247461)
                ·
                  refine ⟨109263434363433733171399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 582738316604979910247461 109263434363433733171399)
                  ·
                    rfl

theorem cell22_957554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 2, 4].length) (baseStart_957554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_957554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_957554 prefixEnd_957554 := by exact prefixLift 957554
  have htrace : WordTrace (prefixWord ++ tailWord_957554) baseStart_957554 baseEnd_957554 := by
    simpa [prefixWord, tailWord_957554, baseEnd_957554] using wordTrace_append hprefix tailTrace_957554
  have hstable : (prefixWord ++ tailWord_957554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957554).length < 2 ^ (prefixWord ++ tailWord_957554).sum := by decide
  have hdescent : baseEnd_957554 < baseStart_957554 := by decide
  rcases family_descends (prefixWord ++ tailWord_957554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957565 : List Nat := [1, 4, 1, 1, 3, 1, 4, 7]
def baseStart_957565 : Nat := 118140960795 + 957565 * 2 ^ 59
def prefixEnd_957565 : Nat := 4983230072969 + 3 ^ 40 * 957565 * 2
def baseEnd_957565 : Nat := 36421563179455648609907

theorem tailTrace_957565 : CollatzResearch.WordTrace tailWord_957565 prefixEnd_957565 36421563179455648609907 := by
  unfold tailWord_957565
  simp only [CollatzResearch.WordTrace]
  refine ⟨34925264775913018927098149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23283509850608679284732099 34925264775913018927098149)
  ·
    refine ⟨6548487145483691048830903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34925264775913018927098149 6548487145483691048830903)
    ·
      refine ⟨9822730718225536573246355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6548487145483691048830903 9822730718225536573246355)
      ·
        refine ⟨14734096077338304859869533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9822730718225536573246355 14734096077338304859869533)
        ·
          refine ⟨5525286029001864322451075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14734096077338304859869533 5525286029001864322451075)
          ·
            refine ⟨8287929043502796483676613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5525286029001864322451075 8287929043502796483676613)
            ·
              refine ⟨1553986695656774340689365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8287929043502796483676613 1553986695656774340689365)
              ·
                refine ⟨36421563179455648609907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1553986695656774340689365 36421563179455648609907)
                ·
                  rfl

theorem cell22_957565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 7].length) (baseStart_957565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_957565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_957565 prefixEnd_957565 := by exact prefixLift 957565
  have htrace : WordTrace (prefixWord ++ tailWord_957565) baseStart_957565 baseEnd_957565 := by
    simpa [prefixWord, tailWord_957565, baseEnd_957565] using wordTrace_append hprefix tailTrace_957565
  have hstable : (prefixWord ++ tailWord_957565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957565).length < 2 ^ (prefixWord ++ tailWord_957565).sum := by decide
  have hdescent : baseEnd_957565 < baseStart_957565 := by decide
  rcases family_descends (prefixWord ++ tailWord_957565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957569 : List Nat := [1, 2, 4, 2, 2, 2, 1, 3, 2, 3]
def baseStart_957569 : Nat := 118140960795 + 957569 * 2 ^ 59
def prefixEnd_957569 : Nat := 4983230072969 + 3 ^ 40 * 957569 * 2
def baseEnd_957569 : Nat := 327795437896846160389151

theorem tailTrace_957569 : CollatzResearch.WordTrace tailWord_957569 prefixEnd_957569 327795437896846160389151 := by
  unfold tailWord_957569
  simp only [CollatzResearch.WordTrace]
  refine ⟨34925410667898527610243761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23283607111932351740162507 34925410667898527610243761)
  ·
    refine ⟨26194058000923895707682821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34925410667898527610243761 26194058000923895707682821)
    ·
      refine ⟨4911385875173230445190529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26194058000923895707682821 4911385875173230445190529)
      ·
        refine ⟨3683539406379922833892897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4911385875173230445190529 3683539406379922833892897)
        ·
          refine ⟨2762654554784942125419673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3683539406379922833892897 2762654554784942125419673)
          ·
            refine ⟨2071990916088706594064755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2762654554784942125419673 2071990916088706594064755)
            ·
              refine ⟨3107986374133059891097133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2071990916088706594064755 3107986374133059891097133)
              ·
                refine ⟨1165494890299897459161425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3107986374133059891097133 1165494890299897459161425)
                ·
                  refine ⟨874121167724923094371069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1165494890299897459161425 874121167724923094371069)
                  ·
                    refine ⟨327795437896846160389151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 874121167724923094371069 327795437896846160389151)
                    ·
                      rfl

theorem cell22_957569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_957569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_957569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_957569 prefixEnd_957569 := by exact prefixLift 957569
  have htrace : WordTrace (prefixWord ++ tailWord_957569) baseStart_957569 baseEnd_957569 := by
    simpa [prefixWord, tailWord_957569, baseEnd_957569] using wordTrace_append hprefix tailTrace_957569
  have hstable : (prefixWord ++ tailWord_957569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957569).length < 2 ^ (prefixWord ++ tailWord_957569).sum := by decide
  have hdescent : baseEnd_957569 < baseStart_957569 := by decide
  rcases family_descends (prefixWord ++ tailWord_957569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957625 : List Nat := [1, 2, 1, 4, 1, 3, 1, 1, 1, 7]
def baseStart_957625 : Nat := 118140960795 + 957625 * 2 ^ 59
def prefixEnd_957625 : Nat := 4983230072969 + 3 ^ 40 * 957625 * 2
def baseEnd_957625 : Nat := 327814607841280680988979

theorem tailTrace_957625 : CollatzResearch.WordTrace tailWord_957625 prefixEnd_957625 327814607841280680988979 := by
  unfold tailWord_957625
  simp only [CollatzResearch.WordTrace]
  refine ⟨34927453155695649174282329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23284968770463766116188219 34927453155695649174282329)
  ·
    refine ⟨26195589866771736880711747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34927453155695649174282329 26195589866771736880711747)
    ·
      refine ⟨39293384800157605321067621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26195589866771736880711747 39293384800157605321067621)
      ·
        refine ⟨7367509650029550997700179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39293384800157605321067621 7367509650029550997700179)
        ·
          refine ⟨11051264475044326496550269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7367509650029550997700179 11051264475044326496550269)
          ·
            refine ⟨4144224178141622436206351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11051264475044326496550269 4144224178141622436206351)
            ·
              refine ⟨6216336267212433654309527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4144224178141622436206351 6216336267212433654309527)
              ·
                refine ⟨9324504400818650481464291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6216336267212433654309527 9324504400818650481464291)
                ·
                  refine ⟨13986756601227975722196437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9324504400818650481464291 13986756601227975722196437)
                  ·
                    refine ⟨327814607841280680988979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13986756601227975722196437 327814607841280680988979)
                    ·
                      rfl

theorem cell22_957625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 7].length) (baseStart_957625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_957625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_957625 prefixEnd_957625 := by exact prefixLift 957625
  have htrace : WordTrace (prefixWord ++ tailWord_957625) baseStart_957625 baseEnd_957625 := by
    simpa [prefixWord, tailWord_957625, baseEnd_957625] using wordTrace_append hprefix tailTrace_957625
  have hstable : (prefixWord ++ tailWord_957625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957625).length < 2 ^ (prefixWord ++ tailWord_957625).sum := by decide
  have hdescent : baseEnd_957625 < baseStart_957625 := by decide
  rcases family_descends (prefixWord ++ tailWord_957625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957661 : List Nat := [1, 4, 3, 2, 2, 2, 1, 2, 5]
def baseStart_957661 : Nat := 118140960795 + 957661 * 2 ^ 59
def prefixEnd_957661 : Nat := 4983230072969 + 3 ^ 40 * 957661 * 2
def baseEnd_957661 : Nat := 109275643792329529029623

theorem tailTrace_957661 : CollatzResearch.WordTrace tailWord_957661 prefixEnd_957661 109275643792329529029623 := by
  unfold tailWord_957661
  simp only [CollatzResearch.WordTrace]
  refine ⟨34928766183565227322592837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23285844122376818215061891 34928766183565227322592837)
  ·
    refine ⟨6549143659418480122986157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34928766183565227322592837 6549143659418480122986157)
    ·
      refine ⟨2455928872281930046119809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6549143659418480122986157 2455928872281930046119809)
      ·
        refine ⟨1841946654211447534589857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2455928872281930046119809 1841946654211447534589857)
        ·
          refine ⟨1381459990658585650942393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1841946654211447534589857 1381459990658585650942393)
          ·
            refine ⟨1036094992993939238206795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1381459990658585650942393 1036094992993939238206795)
            ·
              refine ⟨1554142489490908857310193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1036094992993939238206795 1554142489490908857310193)
              ·
                refine ⟨1165606867118181642982645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1554142489490908857310193 1165606867118181642982645)
                ·
                  refine ⟨109275643792329529029623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1165606867118181642982645 109275643792329529029623)
                  ·
                    rfl

theorem cell22_957661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 2, 5].length) (baseStart_957661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_957661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_957661 prefixEnd_957661 := by exact prefixLift 957661
  have htrace : WordTrace (prefixWord ++ tailWord_957661) baseStart_957661 baseEnd_957661 := by
    simpa [prefixWord, tailWord_957661, baseEnd_957661] using wordTrace_append hprefix tailTrace_957661
  have hstable : (prefixWord ++ tailWord_957661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957661).length < 2 ^ (prefixWord ++ tailWord_957661).sum := by decide
  have hdescent : baseEnd_957661 < baseStart_957661 := by decide
  rcases family_descends (prefixWord ++ tailWord_957661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957672 : List Nat := [2, 1, 4, 1, 2, 1, 4, 1, 6]
def baseStart_957672 : Nat := 118140960795 + 957672 * 2 ^ 59
def prefixEnd_957672 : Nat := 4983230072969 + 3 ^ 40 * 957672 * 2
def baseEnd_957672 : Nat := 109276898967262741687945

theorem tailTrace_957672 : CollatzResearch.WordTrace tailWord_957672 prefixEnd_957672 109276898967262741687945 := by
  unfold tailWord_957672
  simp only [CollatzResearch.WordTrace]
  refine ⟨17464583693262688100621635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23286111591016917467495513 17464583693262688100621635)
  ·
    refine ⟨26196875539894032150932453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17464583693262688100621635 26196875539894032150932453)
    ·
      refine ⟨4911914163730131028299835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26196875539894032150932453 4911914163730131028299835)
      ·
        refine ⟨7367871245595196542449753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4911914163730131028299835 7367871245595196542449753)
        ·
          refine ⟨5525903434196397406837315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7367871245595196542449753 5525903434196397406837315)
          ·
            refine ⟨8288855151294596110255973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5525903434196397406837315 8288855151294596110255973)
            ·
              refine ⟨1554160340867736770672995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8288855151294596110255973 1554160340867736770672995)
              ·
                refine ⟨2331240511301605156009493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1554160340867736770672995 2331240511301605156009493)
                ·
                  refine ⟨109276898967262741687945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2331240511301605156009493 109276898967262741687945)
                  ·
                    rfl

theorem cell22_957672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 6].length) (baseStart_957672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_957672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_957672 prefixEnd_957672 := by exact prefixLift 957672
  have htrace : WordTrace (prefixWord ++ tailWord_957672) baseStart_957672 baseEnd_957672 := by
    simpa [prefixWord, tailWord_957672, baseEnd_957672] using wordTrace_append hprefix tailTrace_957672
  have hstable : (prefixWord ++ tailWord_957672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957672).length < 2 ^ (prefixWord ++ tailWord_957672).sum := by decide
  have hdescent : baseEnd_957672 < baseStart_957672 := by decide
  rcases family_descends (prefixWord ++ tailWord_957672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957738 : List Nat := [3, 1, 4, 2, 1, 1, 4, 1, 2, 3]
def baseStart_957738 : Nat := 118140960795 + 957738 * 2 ^ 59
def prefixEnd_957738 : Nat := 4983230072969 + 3 ^ 40 * 957738 * 2
def baseEnd_957738 : Nat := 327853290050586052913633

theorem tailTrace_957738 : CollatzResearch.WordTrace tailWord_957738 prefixEnd_957738 327853290050586052913633 := by
  unfold tailWord_957738
  simp only [CollatzResearch.WordTrace]
  refine ⟨8732893651071567368286467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23287716402857512982097245 8732893651071567368286467)
  ·
    refine ⟨13099340476607351052429701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8732893651071567368286467 13099340476607351052429701)
    ·
      refine ⟨2456126339363878322330569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13099340476607351052429701 2456126339363878322330569)
      ·
        refine ⟨1842094754522908741747927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2456126339363878322330569 1842094754522908741747927)
        ·
          refine ⟨2763142131784363112621891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1842094754522908741747927 2763142131784363112621891)
          ·
            refine ⟨4144713197676544668932837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2763142131784363112621891 4144713197676544668932837)
            ·
              refine ⟨777133724564352125424907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4144713197676544668932837 777133724564352125424907)
              ·
                refine ⟨1165700586846528188137361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 777133724564352125424907 1165700586846528188137361)
                ·
                  refine ⟨874275440134896141103021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1165700586846528188137361 874275440134896141103021)
                  ·
                    refine ⟨327853290050586052913633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 874275440134896141103021 327853290050586052913633)
                    ·
                      rfl

theorem cell22_957738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_957738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_957738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_957738 prefixEnd_957738 := by exact prefixLift 957738
  have htrace : WordTrace (prefixWord ++ tailWord_957738) baseStart_957738 baseEnd_957738 := by
    simpa [prefixWord, tailWord_957738, baseEnd_957738] using wordTrace_append hprefix tailTrace_957738
  have hstable : (prefixWord ++ tailWord_957738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957738).length < 2 ^ (prefixWord ++ tailWord_957738).sum := by decide
  have hdescent : baseEnd_957738 < baseStart_957738 := by decide
  rcases family_descends (prefixWord ++ tailWord_957738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957777 : List Nat := [1, 2, 2, 1, 4, 1, 2, 2, 2, 5]
def baseStart_957777 : Nat := 118140960795 + 957777 * 2 ^ 59
def prefixEnd_957777 : Nat := 4983230072969 + 3 ^ 40 * 957777 * 2
def baseEnd_957777 : Nat := 327866640547602951188513

theorem tailTrace_957777 : CollatzResearch.WordTrace tailWord_957777 prefixEnd_957777 327866640547602951188513 := by
  unfold tailWord_957777
  simp only [CollatzResearch.WordTrace]
  refine ⟨34932997051144979133815585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23288664700763319422543723 34932997051144979133815585)
  ·
    refine ⟨26199747788358734350361689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34932997051144979133815585 26199747788358734350361689)
    ·
      refine ⟨19649810841269050762771267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26199747788358734350361689 19649810841269050762771267)
      ·
        refine ⟨29474716261903576144156901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19649810841269050762771267 29474716261903576144156901)
        ·
          refine ⟨5526509299106920527029419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29474716261903576144156901 5526509299106920527029419)
          ·
            refine ⟨8289763948660380790544129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5526509299106920527029419 8289763948660380790544129)
            ·
              refine ⟨6217322961495285592908097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8289763948660380790544129 6217322961495285592908097)
              ·
                refine ⟨4662992221121464194681073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6217322961495285592908097 4662992221121464194681073)
                ·
                  refine ⟨3497244165841098146010805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4662992221121464194681073 3497244165841098146010805)
                  ·
                    refine ⟨327866640547602951188513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3497244165841098146010805 327866640547602951188513)
                    ·
                      rfl

theorem cell22_957777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 5].length) (baseStart_957777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_957777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_957777 prefixEnd_957777 := by exact prefixLift 957777
  have htrace : WordTrace (prefixWord ++ tailWord_957777) baseStart_957777 baseEnd_957777 := by
    simpa [prefixWord, tailWord_957777, baseEnd_957777] using wordTrace_append hprefix tailTrace_957777
  have hstable : (prefixWord ++ tailWord_957777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957777).length < 2 ^ (prefixWord ++ tailWord_957777).sum := by decide
  have hdescent : baseEnd_957777 < baseStart_957777 := by decide
  rcases family_descends (prefixWord ++ tailWord_957777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957783 : List Nat := [1, 1, 3, 2, 3, 2, 4, 2, 1, 3]
def baseStart_957783 : Nat := 118140960795 + 957783 * 2 ^ 59
def prefixEnd_957783 : Nat := 4983230072969 + 3 ^ 40 * 957783 * 2
def baseEnd_957783 : Nat := 327868694470220935538495

theorem tailTrace_957783 : CollatzResearch.WordTrace tailWord_957783 prefixEnd_957783 327868694470220935538495 := by
  unfold tailWord_957783
  simp only [CollatzResearch.WordTrace]
  refine ⟨34933215889123242158534003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23288810592748828105689335 34933215889123242158534003)
  ·
    refine ⟨52399823833684863237801005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34933215889123242158534003 52399823833684863237801005)
    ·
      refine ⟨19649933937631823714175377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52399823833684863237801005 19649933937631823714175377)
      ·
        refine ⟨14737450453223867785631533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19649933937631823714175377 14737450453223867785631533)
        ·
          refine ⟨5526543919958950419611825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14737450453223867785631533 5526543919958950419611825)
          ·
            refine ⟨4144907939969212814708869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5526543919958950419611825 4144907939969212814708869)
            ·
              refine ⟨777170238744227402757913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4144907939969212814708869 777170238744227402757913)
              ·
                refine ⟨582877679058170552068435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 777170238744227402757913 582877679058170552068435)
                ·
                  refine ⟨874316518587255828102653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 582877679058170552068435 874316518587255828102653)
                  ·
                    refine ⟨327868694470220935538495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 874316518587255828102653 327868694470220935538495)
                    ·
                      rfl

theorem cell22_957783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 2, 1, 3].length) (baseStart_957783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_957783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_957783 prefixEnd_957783 := by exact prefixLift 957783
  have htrace : WordTrace (prefixWord ++ tailWord_957783) baseStart_957783 baseEnd_957783 := by
    simpa [prefixWord, tailWord_957783, baseEnd_957783] using wordTrace_append hprefix tailTrace_957783
  have hstable : (prefixWord ++ tailWord_957783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957783).length < 2 ^ (prefixWord ++ tailWord_957783).sum := by decide
  have hdescent : baseEnd_957783 < baseStart_957783 := by decide
  rcases family_descends (prefixWord ++ tailWord_957783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957794 : List Nat := [3, 3, 2, 1, 1, 1, 3, 1, 2, 5]
def baseStart_957794 : Nat := 118140960795 + 957794 * 2 ^ 59
def prefixEnd_957794 : Nat := 4983230072969 + 3 ^ 40 * 957794 * 2
def baseEnd_957794 : Nat := 327872459995020573513461

theorem tailTrace_957794 : CollatzResearch.WordTrace tailWord_957794 prefixEnd_957794 327872459995020573513461 := by
  unfold tailWord_957794
  simp only [CollatzResearch.WordTrace]
  refine ⟨8733404273020847759296109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23289078061388927358122957 8733404273020847759296109)
  ·
    refine ⟨3275026602382817909736041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8733404273020847759296109 3275026602382817909736041)
    ·
      refine ⟨2456269951787113432302031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3275026602382817909736041 2456269951787113432302031)
      ·
        refine ⟨3684404927680670148453047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2456269951787113432302031 3684404927680670148453047)
        ·
          refine ⟨5526607391521005222679571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3684404927680670148453047 5526607391521005222679571)
          ·
            refine ⟨8289911087281507834019357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5526607391521005222679571 8289911087281507834019357)
            ·
              refine ⟨3108716657730565437757259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8289911087281507834019357 3108716657730565437757259)
              ·
                refine ⟨4663074986595848156635889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3108716657730565437757259 4663074986595848156635889)
                ·
                  refine ⟨3497306239946886117476917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4663074986595848156635889 3497306239946886117476917)
                  ·
                    refine ⟨327872459995020573513461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3497306239946886117476917 327872459995020573513461)
                    ·
                      rfl

theorem cell22_957794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_957794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_957794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_957794 prefixEnd_957794 := by exact prefixLift 957794
  have htrace : WordTrace (prefixWord ++ tailWord_957794) baseStart_957794 baseEnd_957794 := by
    simpa [prefixWord, tailWord_957794, baseEnd_957794] using wordTrace_append hprefix tailTrace_957794
  have hstable : (prefixWord ++ tailWord_957794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957794).length < 2 ^ (prefixWord ++ tailWord_957794).sum := by decide
  have hdescent : baseEnd_957794 < baseStart_957794 := by decide
  rcases family_descends (prefixWord ++ tailWord_957794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957807 : List Nat := [1, 1, 2, 1, 3, 1, 5, 2, 6]
def baseStart_957807 : Nat := 118140960795 + 957807 * 2 ^ 59
def prefixEnd_957807 : Nat := 4983230072969 + 3 ^ 40 * 957807 * 2
def baseEnd_957807 : Nat := 109292303386897624312807

theorem tailTrace_957807 : CollatzResearch.WordTrace tailWord_957807 prefixEnd_957807 109292303386897624312807 := by
  unfold tailWord_957807
  simp only [CollatzResearch.WordTrace]
  refine ⟨34934091241036294257407675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23289394160690862838271783 34934091241036294257407675)
  ·
    refine ⟨52401136861554441386111513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34934091241036294257407675 52401136861554441386111513)
    ·
      refine ⟨39300852646165831039583635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52401136861554441386111513 39300852646165831039583635)
      ·
        refine ⟨58951278969248746559375453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39300852646165831039583635 58951278969248746559375453)
        ·
          refine ⟨22106729613468279959765795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58951278969248746559375453 22106729613468279959765795)
          ·
            refine ⟨33160094420202419939648693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22106729613468279959765795 33160094420202419939648693)
            ·
              refine ⟨3108758851893976869342065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33160094420202419939648693 3108758851893976869342065)
              ·
                refine ⟨2331569138920482652006549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3108758851893976869342065 2331569138920482652006549)
                ·
                  refine ⟨109292303386897624312807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2331569138920482652006549 109292303386897624312807)
                  ·
                    rfl

theorem cell22_957807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 6].length) (baseStart_957807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_957807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_957807 prefixEnd_957807 := by exact prefixLift 957807
  have htrace : WordTrace (prefixWord ++ tailWord_957807) baseStart_957807 baseEnd_957807 := by
    simpa [prefixWord, tailWord_957807, baseEnd_957807] using wordTrace_append hprefix tailTrace_957807
  have hstable : (prefixWord ++ tailWord_957807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957807).length < 2 ^ (prefixWord ++ tailWord_957807).sum := by decide
  have hdescent : baseEnd_957807 < baseStart_957807 := by decide
  rcases family_descends (prefixWord ++ tailWord_957807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957882 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 3, 8]
def baseStart_957882 : Nat := 118140960795 + 957882 * 2 ^ 59
def prefixEnd_957882 : Nat := 4983230072969 + 3 ^ 40 * 957882 * 2
def baseEnd_957882 : Nat := 327902584193417677313191

theorem tailTrace_957882 : CollatzResearch.WordTrace tailWord_957882 prefixEnd_957882 327902584193417677313191 := by
  unfold tailWord_957882
  simp only [CollatzResearch.WordTrace]
  refine ⟨8734206678941145516596975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23291217810509721377591933 8734206678941145516596975)
  ·
    refine ⟨13101310018411718274895463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8734206678941145516596975 13101310018411718274895463)
    ·
      refine ⟨19651965027617577412343195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13101310018411718274895463 19651965027617577412343195)
      ·
        refine ⟨29477947541426366118514793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19651965027617577412343195 29477947541426366118514793)
        ·
          refine ⟨22108460656069774588886095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29477947541426366118514793 22108460656069774588886095)
          ·
            refine ⟨33162690984104661883329143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22108460656069774588886095 33162690984104661883329143)
            ·
              refine ⟨49744036476156992824993715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33162690984104661883329143 49744036476156992824993715)
              ·
                refine ⟨74616054714235489237490573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49744036476156992824993715 74616054714235489237490573)
                ·
                  refine ⟨27981020517838308464058965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74616054714235489237490573 27981020517838308464058965)
                  ·
                    refine ⟨327902584193417677313191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 27981020517838308464058965 327902584193417677313191)
                    ·
                      rfl

theorem cell22_957882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 3, 8].length) (baseStart_957882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_957882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_957882 prefixEnd_957882 := by exact prefixLift 957882
  have htrace : WordTrace (prefixWord ++ tailWord_957882) baseStart_957882 baseEnd_957882 := by
    simpa [prefixWord, tailWord_957882, baseEnd_957882] using wordTrace_append hprefix tailTrace_957882
  have hstable : (prefixWord ++ tailWord_957882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957882).length < 2 ^ (prefixWord ++ tailWord_957882).sum := by decide
  have hdescent : baseEnd_957882 < baseStart_957882 := by decide
  rcases family_descends (prefixWord ++ tailWord_957882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957976 : List Nat := [2, 1, 2, 3, 4, 1, 1, 2, 6]
def baseStart_957976 : Nat := 118140960795 + 957976 * 2 ^ 59
def prefixEnd_957976 : Nat := 4983230072969 + 3 ^ 40 * 957976 * 2
def baseEnd_957976 : Nat := 109311587438144255154301

theorem tailTrace_957976 : CollatzResearch.WordTrace tailWord_957976 prefixEnd_957976 109311587438144255154301 := by
  unfold tailWord_957976
  simp only [CollatzResearch.WordTrace]
  refine ⟨17470127588712018060154891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23293503451616024080206521 17470127588712018060154891)
  ·
    refine ⟨26205191383068027090232337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17470127588712018060154891 26205191383068027090232337)
    ·
      refine ⟨19653893537301020317674253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26205191383068027090232337 19653893537301020317674253)
      ·
        refine ⟨7370210076487882619127845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19653893537301020317674253 7370210076487882619127845)
        ·
          refine ⟨1381914389341477991086471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7370210076487882619127845 1381914389341477991086471)
          ·
            refine ⟨2072871584012216986629707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1381914389341477991086471 2072871584012216986629707)
            ·
              refine ⟨3109307376018325479944561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2072871584012216986629707 3109307376018325479944561)
              ·
                refine ⟨2331980532013744109958421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3109307376018325479944561 2331980532013744109958421)
                ·
                  refine ⟨109311587438144255154301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2331980532013744109958421 109311587438144255154301)
                  ·
                    rfl

theorem cell22_957976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 6].length) (baseStart_957976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_957976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_957976 prefixEnd_957976 := by exact prefixLift 957976
  have htrace : WordTrace (prefixWord ++ tailWord_957976) baseStart_957976 baseEnd_957976 := by
    simpa [prefixWord, tailWord_957976, baseEnd_957976] using wordTrace_append hprefix tailTrace_957976
  have hstable : (prefixWord ++ tailWord_957976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957976).length < 2 ^ (prefixWord ++ tailWord_957976).sum := by decide
  have hdescent : baseEnd_957976 < baseStart_957976 := by decide
  rcases family_descends (prefixWord ++ tailWord_957976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958008 : List Nat := [2, 1, 2, 1, 4, 2, 3, 2, 2, 3]
def baseStart_958008 : Nat := 118140960795 + 958008 * 2 ^ 59
def prefixEnd_958008 : Nat := 4983230072969 + 3 ^ 40 * 958008 * 2
def baseEnd_958008 : Nat := 327945716568395348662805

theorem tailTrace_958008 : CollatzResearch.WordTrace tailWord_958008 prefixEnd_958008 327945716568395348662805 := by
  unfold tailWord_958008
  simp only [CollatzResearch.WordTrace]
  refine ⟨17470711156654052792737339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23294281542205403723649785 17470711156654052792737339)
  ·
    refine ⟨26206066734981079189106009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17470711156654052792737339 26206066734981079189106009)
    ·
      refine ⟨19654550051235809391829507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26206066734981079189106009 19654550051235809391829507)
      ·
        refine ⟨29481825076853714087744261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19654550051235809391829507 29481825076853714087744261)
        ·
          refine ⟨5527842201910071391452049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29481825076853714087744261 5527842201910071391452049)
          ·
            refine ⟨4145881651432553543589037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5527842201910071391452049 4145881651432553543589037)
            ·
              refine ⟨1554705619287207578845889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4145881651432553543589037 1554705619287207578845889)
              ·
                refine ⟨1166029214465405684134417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1554705619287207578845889 1166029214465405684134417)
                ·
                  refine ⟨874521910849054263100813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1166029214465405684134417 874521910849054263100813)
                  ·
                    refine ⟨327945716568395348662805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 874521910849054263100813 327945716568395348662805)
                    ·
                      rfl

theorem cell22_958008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 2, 2, 3].length) (baseStart_958008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_958008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_958008 prefixEnd_958008 := by exact prefixLift 958008
  have htrace : WordTrace (prefixWord ++ tailWord_958008) baseStart_958008 baseEnd_958008 := by
    simpa [prefixWord, tailWord_958008, baseEnd_958008] using wordTrace_append hprefix tailTrace_958008
  have hstable : (prefixWord ++ tailWord_958008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958008).length < 2 ^ (prefixWord ++ tailWord_958008).sum := by decide
  have hdescent : baseEnd_958008 < baseStart_958008 := by decide
  rcases family_descends (prefixWord ++ tailWord_958008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958049 : List Nat := [1, 2, 3, 1, 1, 3, 1, 1, 9]
def baseStart_958049 : Nat := 118140960795 + 958049 * 2 ^ 59
def prefixEnd_958049 : Nat := 4983230072969 + 3 ^ 40 * 958049 * 2
def baseEnd_958049 : Nat := 109319917235428302795893

theorem tailTrace_958049 : CollatzResearch.WordTrace tailWord_958049 prefixEnd_958049 109319917235428302795893 := by
  unfold tailWord_958049
  simp only [CollatzResearch.WordTrace]
  refine ⟨34942917706159569587717201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23295278470773046391811467 34942917706159569587717201)
  ·
    refine ⟨26207188279619677190787901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34942917706159569587717201 26207188279619677190787901)
    ·
      refine ⟨9827695604857378946545463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26207188279619677190787901 9827695604857378946545463)
      ·
        refine ⟨14741543407286068419818195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9827695604857378946545463 14741543407286068419818195)
        ·
          refine ⟨22112315110929102629727293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14741543407286068419818195 22112315110929102629727293)
          ·
            refine ⟨8292118166598413486147735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22112315110929102629727293 8292118166598413486147735)
            ·
              refine ⟨12438177249897620229221603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8292118166598413486147735 12438177249897620229221603)
              ·
                refine ⟨18657265874846430343832405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12438177249897620229221603 18657265874846430343832405)
                ·
                  refine ⟨109319917235428302795893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 18657265874846430343832405 109319917235428302795893)
                  ·
                    rfl

theorem cell22_958049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 9].length) (baseStart_958049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_958049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_958049 prefixEnd_958049 := by exact prefixLift 958049
  have htrace : WordTrace (prefixWord ++ tailWord_958049) baseStart_958049 baseEnd_958049 := by
    simpa [prefixWord, tailWord_958049, baseEnd_958049] using wordTrace_append hprefix tailTrace_958049
  have hstable : (prefixWord ++ tailWord_958049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958049).length < 2 ^ (prefixWord ++ tailWord_958049).sum := by decide
  have hdescent : baseEnd_958049 < baseStart_958049 := by decide
  rcases family_descends (prefixWord ++ tailWord_958049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958066 : List Nat := [3, 2, 1, 2, 3, 1, 2, 1, 7]
def baseStart_958066 : Nat := 118140960795 + 958066 * 2 ^ 59
def prefixEnd_958066 : Nat := 4983230072969 + 3 ^ 40 * 958066 * 2
def baseEnd_958066 : Nat := 109321857051234176904209

theorem tailTrace_958066 : CollatzResearch.WordTrace tailWord_958066 prefixEnd_958066 109321857051234176904209 := by
  unfold tailWord_958066
  simp only [CollatzResearch.WordTrace]
  refine ⟨8735884436774495372771513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23295691831398654327390701 8735884436774495372771513)
  ·
    refine ⟨6551913327580871529578635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8735884436774495372771513 6551913327580871529578635)
    ·
      refine ⟨9827869991371307294367953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6551913327580871529578635 9827869991371307294367953)
      ·
        refine ⟨7370902493528480470775965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9827869991371307294367953 7370902493528480470775965)
        ·
          refine ⟨2764088435073180176540987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7370902493528480470775965 2764088435073180176540987)
          ·
            refine ⟨4146132652609770264811481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2764088435073180176540987 4146132652609770264811481)
            ·
              refine ⟨3109599489457327698608611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4146132652609770264811481 3109599489457327698608611)
              ·
                refine ⟨4664399234185991547912917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3109599489457327698608611 4664399234185991547912917)
                ·
                  refine ⟨109321857051234176904209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4664399234185991547912917 109321857051234176904209)
                  ·
                    rfl

theorem cell22_958066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 7].length) (baseStart_958066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_958066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_958066 prefixEnd_958066 := by exact prefixLift 958066
  have htrace : WordTrace (prefixWord ++ tailWord_958066) baseStart_958066 baseEnd_958066 := by
    simpa [prefixWord, tailWord_958066, baseEnd_958066] using wordTrace_append hprefix tailTrace_958066
  have hstable : (prefixWord ++ tailWord_958066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958066).length < 2 ^ (prefixWord ++ tailWord_958066).sum := by decide
  have hdescent : baseEnd_958066 < baseStart_958066 := by decide
  rcases family_descends (prefixWord ++ tailWord_958066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958070 : List Nat := [5, 1, 1, 2, 2, 1, 3, 1, 3, 3]
def baseStart_958070 : Nat := 118140960795 + 958070 * 2 ^ 59
def prefixEnd_958070 : Nat := 4983230072969 + 3 ^ 40 * 958070 * 2
def baseEnd_958070 : Nat := 327966940435447853612615

theorem tailTrace_958070 : CollatzResearch.WordTrace tailWord_958070 prefixEnd_958070 327966940435447853612615 := by
  unfold tailWord_958070
  simp only [CollatzResearch.WordTrace]
  refine ⟨2183980227442718135889479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23295789092722326782821109 2183980227442718135889479)
  ·
    refine ⟨3275970341164077203834219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2183980227442718135889479 3275970341164077203834219)
    ·
      refine ⟨4913955511746115805751329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3275970341164077203834219 4913955511746115805751329)
      ·
        refine ⟨3685466633809586854313497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4913955511746115805751329 3685466633809586854313497)
        ·
          refine ⟨2764099975357190140735123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3685466633809586854313497 2764099975357190140735123)
          ·
            refine ⟨4146149963035785211102685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2764099975357190140735123 4146149963035785211102685)
            ·
              refine ⟨1554806236138419454163507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4146149963035785211102685 1554806236138419454163507)
              ·
                refine ⟨2332209354207629181245261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1554806236138419454163507 2332209354207629181245261)
                ·
                  refine ⟨874578507827860942966973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2332209354207629181245261 874578507827860942966973)
                  ·
                    refine ⟨327966940435447853612615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 874578507827860942966973 327966940435447853612615)
                    ·
                      rfl

theorem cell22_958070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_958070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_958070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_958070 prefixEnd_958070 := by exact prefixLift 958070
  have htrace : WordTrace (prefixWord ++ tailWord_958070) baseStart_958070 baseEnd_958070 := by
    simpa [prefixWord, tailWord_958070, baseEnd_958070] using wordTrace_append hprefix tailTrace_958070
  have hstable : (prefixWord ++ tailWord_958070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958070).length < 2 ^ (prefixWord ++ tailWord_958070).sum := by decide
  have hdescent : baseEnd_958070 < baseStart_958070 := by decide
  rcases family_descends (prefixWord ++ tailWord_958070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958141 : List Nat := [1, 4, 1, 2, 1, 2, 2, 2, 1, 6]
def baseStart_958141 : Nat := 118140960795 + 958141 * 2 ^ 59
def prefixEnd_958141 : Nat := 4983230072969 + 3 ^ 40 * 958141 * 2
def baseEnd_958141 : Nat := 327991245186427335087397

theorem tailTrace_958141 : CollatzResearch.WordTrace tailWord_958141 prefixEnd_958141 327991245186427335087397 := by
  unfold tailWord_958141
  simp only [CollatzResearch.WordTrace]
  refine ⟨34946273221826269300066277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23297515481217512866710851 34946273221826269300066277)
  ·
    refine ⟨6552426229092425493762427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34946273221826269300066277 6552426229092425493762427)
    ·
      refine ⟨9828639343638638240643641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6552426229092425493762427 9828639343638638240643641)
      ·
        refine ⟨7371479507728978680482731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9828639343638638240643641 7371479507728978680482731)
        ·
          refine ⟨11057219261593468020724097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7371479507728978680482731 11057219261593468020724097)
          ·
            refine ⟨8292914446195101015543073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11057219261593468020724097 8292914446195101015543073)
            ·
              refine ⟨6219685834646325761657305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8292914446195101015543073 6219685834646325761657305)
              ·
                refine ⟨4664764375984744321242979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6219685834646325761657305 4664764375984744321242979)
                ·
                  refine ⟨6997146563977116481864469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4664764375984744321242979 6997146563977116481864469)
                  ·
                    refine ⟨327991245186427335087397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6997146563977116481864469 327991245186427335087397)
                    ·
                      rfl

theorem cell22_958141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_958141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_958141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_958141 prefixEnd_958141 := by exact prefixLift 958141
  have htrace : WordTrace (prefixWord ++ tailWord_958141) baseStart_958141 baseEnd_958141 := by
    simpa [prefixWord, tailWord_958141, baseEnd_958141] using wordTrace_append hprefix tailTrace_958141
  have hstable : (prefixWord ++ tailWord_958141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958141).length < 2 ^ (prefixWord ++ tailWord_958141).sum := by decide
  have hdescent : baseEnd_958141 < baseStart_958141 := by decide
  rcases family_descends (prefixWord ++ tailWord_958141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958143 : List Nat := [1, 1, 2, 2, 2, 3, 1, 5, 2, 3]
def baseStart_958143 : Nat := 118140960795 + 958143 * 2 ^ 59
def prefixEnd_958143 : Nat := 4983230072969 + 3 ^ 40 * 958143 * 2
def baseEnd_958143 : Nat := 327991929827299996537391

theorem tailTrace_958143 : CollatzResearch.WordTrace tailWord_958143 prefixEnd_958143 327991929827299996537391 := by
  unfold tailWord_958143
  simp only [CollatzResearch.WordTrace]
  refine ⟨34946346167819023641639083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23297564111879349094426055 34946346167819023641639083)
  ·
    refine ⟨52419519251728535462458625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34946346167819023641639083 52419519251728535462458625)
    ·
      refine ⟨39314639438796401596843969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52419519251728535462458625 39314639438796401596843969)
      ·
        refine ⟨29485979579097301197632977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39314639438796401596843969 29485979579097301197632977)
        ·
          refine ⟨22114484684322975898224733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29485979579097301197632977 22114484684322975898224733)
          ·
            refine ⟨8292931756621115961834275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22114484684322975898224733 8292931756621115961834275)
            ·
              refine ⟨12439397634931673942751413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8292931756621115961834275 12439397634931673942751413)
              ·
                refine ⟨1166193528274844432132945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12439397634931673942751413 1166193528274844432132945)
                ·
                  refine ⟨874645146206133324099709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1166193528274844432132945 874645146206133324099709)
                  ·
                    refine ⟨327991929827299996537391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 874645146206133324099709 327991929827299996537391)
                    ·
                      rfl

theorem cell22_958143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 5, 2, 3].length) (baseStart_958143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_958143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_958143 prefixEnd_958143 := by exact prefixLift 958143
  have htrace : WordTrace (prefixWord ++ tailWord_958143) baseStart_958143 baseEnd_958143 := by
    simpa [prefixWord, tailWord_958143, baseEnd_958143] using wordTrace_append hprefix tailTrace_958143
  have hstable : (prefixWord ++ tailWord_958143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958143).length < 2 ^ (prefixWord ++ tailWord_958143).sum := by decide
  have hdescent : baseEnd_958143 < baseStart_958143 := by decide
  rcases family_descends (prefixWord ++ tailWord_958143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958177 : List Nat := [1, 2, 3, 1, 5, 2, 1, 2, 2, 3]
def baseStart_958177 : Nat := 118140960795 + 958177 * 2 ^ 59
def prefixEnd_958177 : Nat := 4983230072969 + 3 ^ 40 * 958177 * 2
def baseEnd_958177 : Nat := 328003568722135241187287

theorem tailTrace_958177 : CollatzResearch.WordTrace tailWord_958177 prefixEnd_958177 328003568722135241187287 := by
  unfold tailWord_958177
  simp only [CollatzResearch.WordTrace]
  refine ⟨34947586249695847448376785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23298390833130564965584523 34947586249695847448376785)
  ·
    refine ⟨26210689687271885586282589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34947586249695847448376785 26210689687271885586282589)
    ·
      refine ⟨9829008632726957094855971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26210689687271885586282589 9829008632726957094855971)
      ·
        refine ⟨14743512949090435642283957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9829008632726957094855971 14743512949090435642283957)
        ·
          refine ⟨1382204338977228341464121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14743512949090435642283957 1382204338977228341464121)
          ·
            refine ⟨1036653254232921256098091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1382204338977228341464121 1036653254232921256098091)
            ·
              refine ⟨1554979881349381884147137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1036653254232921256098091 1554979881349381884147137)
              ·
                refine ⟨1166234911012036413110353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1554979881349381884147137 1166234911012036413110353)
                ·
                  refine ⟨874676183259027309832765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1166234911012036413110353 874676183259027309832765)
                  ·
                    refine ⟨328003568722135241187287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 874676183259027309832765 328003568722135241187287)
                    ·
                      rfl

theorem cell22_958177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 2, 2, 3].length) (baseStart_958177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_958177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_958177 prefixEnd_958177 := by exact prefixLift 958177
  have htrace : WordTrace (prefixWord ++ tailWord_958177) baseStart_958177 baseEnd_958177 := by
    simpa [prefixWord, tailWord_958177, baseEnd_958177] using wordTrace_append hprefix tailTrace_958177
  have hstable : (prefixWord ++ tailWord_958177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958177).length < 2 ^ (prefixWord ++ tailWord_958177).sum := by decide
  have hdescent : baseEnd_958177 < baseStart_958177 := by decide
  rcases family_descends (prefixWord ++ tailWord_958177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958186 : List Nat := [3, 1, 3, 1, 1, 1, 2, 1, 1, 8]
def baseStart_958186 : Nat := 118140960795 + 958186 * 2 ^ 59
def prefixEnd_958186 : Nat := 4983230072969 + 3 ^ 40 * 958186 * 2
def baseEnd_958186 : Nat := 328006649606062217712259

theorem tailTrace_958186 : CollatzResearch.WordTrace tailWord_958186 prefixEnd_958186 328006649606062217712259 := by
  unfold tailWord_958186
  simp only [CollatzResearch.WordTrace]
  refine ⟨8736978626665810496363603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23298609671108827990302941 8736978626665810496363603)
  ·
    refine ⟨13105467939998715744545405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8736978626665810496363603 13105467939998715744545405)
    ·
      refine ⟨4914550477499518404204527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13105467939998715744545405 4914550477499518404204527)
      ·
        refine ⟨7371825716249277606306791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4914550477499518404204527 7371825716249277606306791)
        ·
          refine ⟨11057738574373916409460187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7371825716249277606306791 11057738574373916409460187)
          ·
            refine ⟨16586607861560874614190281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11057738574373916409460187 16586607861560874614190281)
            ·
              refine ⟨12439955896170655960642711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16586607861560874614190281 12439955896170655960642711)
              ·
                refine ⟨18659933844255983940964067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12439955896170655960642711 18659933844255983940964067)
                ·
                  refine ⟨27989900766383975911446101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18659933844255983940964067 27989900766383975911446101)
                  ·
                    refine ⟨328006649606062217712259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 27989900766383975911446101 328006649606062217712259)
                    ·
                      rfl

theorem cell22_958186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_958186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_958186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_958186 prefixEnd_958186 := by exact prefixLift 958186
  have htrace : WordTrace (prefixWord ++ tailWord_958186) baseStart_958186 baseEnd_958186 := by
    simpa [prefixWord, tailWord_958186, baseEnd_958186] using wordTrace_append hprefix tailTrace_958186
  have hstable : (prefixWord ++ tailWord_958186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958186).length < 2 ^ (prefixWord ++ tailWord_958186).sum := by decide
  have hdescent : baseEnd_958186 < baseStart_958186 := by decide
  rcases family_descends (prefixWord ++ tailWord_958186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958188 : List Nat := [2, 2, 1, 1, 2, 2, 3, 3, 3, 3]
def baseStart_958188 : Nat := 118140960795 + 958188 * 2 ^ 59
def prefixEnd_958188 : Nat := 4983230072969 + 3 ^ 40 * 958188 * 2
def baseEnd_958188 : Nat := 328007334246934879162253

theorem tailTrace_958188 : CollatzResearch.WordTrace tailWord_958188 prefixEnd_958188 328007334246934879162253 := by
  unfold tailWord_958188
  simp only [CollatzResearch.WordTrace]
  refine ⟨17473993726327998163513609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23298658301770664218018145 17473993726327998163513609)
  ·
    refine ⟨13105495294745998622635207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17473993726327998163513609 13105495294745998622635207)
    ·
      refine ⟨19658242942118997933952811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13105495294745998622635207 19658242942118997933952811)
      ·
        refine ⟨29487364413178496900929217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19658242942118997933952811 29487364413178496900929217)
        ·
          refine ⟨22115523309883872675696913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29487364413178496900929217 22115523309883872675696913)
          ·
            refine ⟨16586642482412904506772685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22115523309883872675696913 16586642482412904506772685)
            ·
              refine ⟨6219990930904839190039757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16586642482412904506772685 6219990930904839190039757)
              ·
                refine ⟨2332496599089314696264909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6219990930904839190039757 2332496599089314696264909)
                ·
                  refine ⟨874686224658493011099341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2332496599089314696264909 874686224658493011099341)
                  ·
                    refine ⟨328007334246934879162253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 874686224658493011099341 328007334246934879162253)
                    ·
                      rfl

theorem cell22_958188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 3].length) (baseStart_958188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_958188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_958188 prefixEnd_958188 := by exact prefixLift 958188
  have htrace : WordTrace (prefixWord ++ tailWord_958188) baseStart_958188 baseEnd_958188 := by
    simpa [prefixWord, tailWord_958188, baseEnd_958188] using wordTrace_append hprefix tailTrace_958188
  have hstable : (prefixWord ++ tailWord_958188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958188).length < 2 ^ (prefixWord ++ tailWord_958188).sum := by decide
  have hdescent : baseEnd_958188 < baseStart_958188 := by decide
  rcases family_descends (prefixWord ++ tailWord_958188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958222 : List Nat := [4, 1, 1, 2, 1, 1, 5, 3, 1, 3]
def baseStart_958222 : Nat := 118140960795 + 958222 * 2 ^ 59
def prefixEnd_958222 : Nat := 4983230072969 + 3 ^ 40 * 958222 * 2
def baseEnd_958222 : Nat := 328018973141770123812149

theorem tailTrace_958222 : CollatzResearch.WordTrace tailWord_958222 prefixEnd_958222 328018973141770123812149 := by
  unfold tailWord_958222
  simp only [CollatzResearch.WordTrace]
  refine ⟨4368653441816602516720615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23299485023021880089176613 4368653441816602516720615)
  ·
    refine ⟨6552980162724903775080923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4368653441816602516720615 6552980162724903775080923)
    ·
      refine ⟨9829470244087355662621385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6552980162724903775080923 9829470244087355662621385)
      ·
        refine ⟨7372102683065516746966039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9829470244087355662621385 7372102683065516746966039)
        ·
          refine ⟨11058154024598275120449059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7372102683065516746966039 11058154024598275120449059)
          ·
            refine ⟨16587231036897412680673589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11058154024598275120449059 16587231036897412680673589)
            ·
              refine ⟨1555052909709132438813149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16587231036897412680673589 1555052909709132438813149)
              ·
                refine ⟨583144841140924664554931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1555052909709132438813149 583144841140924664554931)
                ·
                  refine ⟨874717261711386996832397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 583144841140924664554931 874717261711386996832397)
                  ·
                    refine ⟨328018973141770123812149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 874717261711386996832397 328018973141770123812149)
                    ·
                      rfl

theorem cell22_958222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 3, 1, 3].length) (baseStart_958222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_958222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_958222 prefixEnd_958222 := by exact prefixLift 958222
  have htrace : WordTrace (prefixWord ++ tailWord_958222) baseStart_958222 baseEnd_958222 := by
    simpa [prefixWord, tailWord_958222, baseEnd_958222] using wordTrace_append hprefix tailTrace_958222
  have hstable : (prefixWord ++ tailWord_958222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958222).length < 2 ^ (prefixWord ++ tailWord_958222).sum := by decide
  have hdescent : baseEnd_958222 < baseStart_958222 := by decide
  rcases family_descends (prefixWord ++ tailWord_958222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958325 : List Nat := [1, 3, 4, 1, 1, 1, 5, 6]
def baseStart_958325 : Nat := 118140960795 + 958325 * 2 ^ 59
def prefixEnd_958325 : Nat := 4983230072969 + 3 ^ 40 * 958325 * 2
def baseEnd_958325 : Nat := 36450470238523576498537

theorem tailTrace_958325 : CollatzResearch.WordTrace tailWord_958325 prefixEnd_958325 36450470238523576498537 := by
  unfold tailWord_958325
  simp only [CollatzResearch.WordTrace]
  refine ⟨34952984253159668724764429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23301989502106445816509619 34952984253159668724764429)
  ·
    refine ⟨13107369094934875771786661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34952984253159668724764429 13107369094934875771786661)
    ·
      refine ⟨2457631705300289207209999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13107369094934875771786661 2457631705300289207209999)
      ·
        refine ⟨3686447557950433810814999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2457631705300289207209999 3686447557950433810814999)
        ·
          refine ⟨5529671336925650716222499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3686447557950433810814999 5529671336925650716222499)
          ·
            refine ⟨8294507005388476074333749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5529671336925650716222499 8294507005388476074333749)
            ·
              refine ⟨777610031755169631968789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8294507005388476074333749 777610031755169631968789)
              ·
                refine ⟨36450470238523576498537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 777610031755169631968789 36450470238523576498537)
                ·
                  rfl

theorem cell22_958325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 6].length) (baseStart_958325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_958325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_958325 prefixEnd_958325 := by exact prefixLift 958325
  have htrace : WordTrace (prefixWord ++ tailWord_958325) baseStart_958325 baseEnd_958325 := by
    simpa [prefixWord, tailWord_958325, baseEnd_958325] using wordTrace_append hprefix tailTrace_958325
  have hstable : (prefixWord ++ tailWord_958325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958325).length < 2 ^ (prefixWord ++ tailWord_958325).sum := by decide
  have hdescent : baseEnd_958325 < baseStart_958325 := by decide
  rcases family_descends (prefixWord ++ tailWord_958325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958346 : List Nat := [3, 1, 2, 4, 3, 1, 1, 2, 2, 3]
def baseStart_958346 : Nat := 118140960795 + 958346 * 2 ^ 59
def prefixEnd_958346 : Nat := 4983230072969 + 3 ^ 40 * 958346 * 2
def baseEnd_958346 : Nat := 328061420875875133711769

theorem tailTrace_958346 : CollatzResearch.WordTrace tailWord_958346 prefixEnd_958346 328061420875875133711769 := by
  unfold tailWord_958346
  simp only [CollatzResearch.WordTrace]
  refine ⟨8738437546520897327819723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23302500124055726207519261 8738437546520897327819723)
  ·
    refine ⟨13107656319781345991729585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8738437546520897327819723 13107656319781345991729585)
    ·
      refine ⟨9830742239836009493797189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13107656319781345991729585 9830742239836009493797189)
      ·
        refine ⟨1843264169969251780086973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9830742239836009493797189 1843264169969251780086973)
        ·
          refine ⟨691224063738469417532615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1843264169969251780086973 691224063738469417532615)
          ·
            refine ⟨1036836095607704126298923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 691224063738469417532615 1036836095607704126298923)
            ·
              refine ⟨1555254143411556189448385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1036836095607704126298923 1555254143411556189448385)
              ·
                refine ⟨1166440607558667142086289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1555254143411556189448385 1166440607558667142086289)
                ·
                  refine ⟨874830455669000356564717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1166440607558667142086289 874830455669000356564717)
                  ·
                    refine ⟨328061420875875133711769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 874830455669000356564717 328061420875875133711769)
                    ·
                      rfl

theorem cell22_958346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 2, 2, 3].length) (baseStart_958346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_958346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_958346 prefixEnd_958346 := by exact prefixLift 958346
  have htrace : WordTrace (prefixWord ++ tailWord_958346) baseStart_958346 baseEnd_958346 := by
    simpa [prefixWord, tailWord_958346, baseEnd_958346] using wordTrace_append hprefix tailTrace_958346
  have hstable : (prefixWord ++ tailWord_958346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958346).length < 2 ^ (prefixWord ++ tailWord_958346).sum := by decide
  have hdescent : baseEnd_958346 < baseStart_958346 := by decide
  rcases family_descends (prefixWord ++ tailWord_958346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958357 : List Nat := [1, 3, 2, 1, 1, 3, 1, 6, 1, 3]
def baseStart_958357 : Nat := 118140960795 + 958357 * 2 ^ 59
def prefixEnd_958357 : Nat := 4983230072969 + 3 ^ 40 * 958357 * 2
def baseEnd_958357 : Nat := 328065186400674771686735

theorem tailTrace_958357 : CollatzResearch.WordTrace tailWord_958357 prefixEnd_958357 328065186400674771686735 := by
  unfold tailWord_958357
  simp only [CollatzResearch.WordTrace]
  refine ⟨34954151389043738189929325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23302767592695825459952883 34954151389043738189929325)
  ·
    refine ⟨13107806770891401821223497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34954151389043738189929325 13107806770891401821223497)
    ·
      refine ⟨9830855078168551365917623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13107806770891401821223497 9830855078168551365917623)
      ·
        refine ⟨14746282617252827048876435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9830855078168551365917623 14746282617252827048876435)
        ·
          refine ⟨22119423925879240573314653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14746282617252827048876435 22119423925879240573314653)
          ·
            refine ⟨8294783972204715214992995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22119423925879240573314653 8294783972204715214992995)
            ·
              refine ⟨12442175958307072822489493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8294783972204715214992995 12442175958307072822489493)
              ·
                refine ⟨583226998045644038554195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12442175958307072822489493 583226998045644038554195)
                ·
                  refine ⟨874840497068466057831293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 583226998045644038554195 874840497068466057831293)
                  ·
                    refine ⟨328065186400674771686735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 874840497068466057831293 328065186400674771686735)
                    ·
                      rfl

theorem cell22_958357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 6, 1, 3].length) (baseStart_958357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_958357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_958357 prefixEnd_958357 := by exact prefixLift 958357
  have htrace : WordTrace (prefixWord ++ tailWord_958357) baseStart_958357 baseEnd_958357 := by
    simpa [prefixWord, tailWord_958357, baseEnd_958357] using wordTrace_append hprefix tailTrace_958357
  have hstable : (prefixWord ++ tailWord_958357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958357).length < 2 ^ (prefixWord ++ tailWord_958357).sum := by decide
  have hdescent : baseEnd_958357 < baseStart_958357 := by decide
  rcases family_descends (prefixWord ++ tailWord_958357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958376 : List Nat := [2, 1, 6, 2, 2, 1, 2, 6]
def baseStart_958376 : Nat := 118140960795 + 958376 * 2 ^ 59
def prefixEnd_958376 : Nat := 4983230072969 + 3 ^ 40 * 958376 * 2
def baseEnd_958376 : Nat := 36452410054329450606853

theorem tailTrace_958376 : CollatzResearch.WordTrace tailWord_958376 prefixEnd_958376 36452410054329450606853 := by
  unfold tailWord_958376
  simp only [CollatzResearch.WordTrace]
  refine ⟨17477422187987452217435491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23303229583983269623247321 17477422187987452217435491)
  ·
    refine ⟨26216133281981178326153237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17477422187987452217435491 26216133281981178326153237)
    ·
      refine ⟨1228881247592867734038433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 26216133281981178326153237 1228881247592867734038433)
      ·
        refine ⟨921660935694650800528825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1228881247592867734038433 921660935694650800528825)
        ·
          refine ⟨691245701770988100396619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 921660935694650800528825 691245701770988100396619)
          ·
            refine ⟨1036868552656482150594929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 691245701770988100396619 1036868552656482150594929)
            ·
              refine ⟨777651414492361612946197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1036868552656482150594929 777651414492361612946197)
              ·
                refine ⟨36452410054329450606853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 777651414492361612946197 36452410054329450606853)
                ·
                  rfl

theorem cell22_958376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 6].length) (baseStart_958376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_958376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_958376 prefixEnd_958376 := by exact prefixLift 958376
  have htrace : WordTrace (prefixWord ++ tailWord_958376) baseStart_958376 baseEnd_958376 := by
    simpa [prefixWord, tailWord_958376, baseEnd_958376] using wordTrace_append hprefix tailTrace_958376
  have hstable : (prefixWord ++ tailWord_958376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958376).length < 2 ^ (prefixWord ++ tailWord_958376).sum := by decide
  have hdescent : baseEnd_958376 < baseStart_958376 := by decide
  rcases family_descends (prefixWord ++ tailWord_958376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958400 : List Nat := [2, 1, 1, 2, 3, 2, 1, 5, 1, 4]
def baseStart_958400 : Nat := 118140960795 + 958400 * 2 ^ 59
def prefixEnd_958400 : Nat := 4983230072969 + 3 ^ 40 * 958400 * 2
def baseEnd_958400 : Nat := 328079906179436992861603

theorem tailTrace_958400 : CollatzResearch.WordTrace tailWord_958400 prefixEnd_958400 328079906179436992861603 := by
  unfold tailWord_958400
  simp only [CollatzResearch.WordTrace]
  refine ⟨17477859863943978266872327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23303813151925304355829769 17477859863943978266872327)
  ·
    refine ⟨26216789795915967400308491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17477859863943978266872327 26216789795915967400308491)
    ·
      refine ⟨39325184693873951100462737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26216789795915967400308491 39325184693873951100462737)
      ·
        refine ⟨29493888520405463325347053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39325184693873951100462737 29493888520405463325347053)
        ·
          refine ⟨11060208195152048747005145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29493888520405463325347053 11060208195152048747005145)
          ·
            refine ⟨8295156146364036560253859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11060208195152048747005145 8295156146364036560253859)
            ·
              refine ⟨12442734219546054840380789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8295156146364036560253859 12442734219546054840380789)
              ·
                refine ⟨1166506333082442641285699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12442734219546054840380789 1166506333082442641285699)
                ·
                  refine ⟨1749759499623663961928549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1166506333082442641285699 1749759499623663961928549)
                  ·
                    refine ⟨328079906179436992861603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1749759499623663961928549 328079906179436992861603)
                    ·
                      rfl

theorem cell22_958400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 5, 1, 4].length) (baseStart_958400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_958400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_958400 prefixEnd_958400 := by exact prefixLift 958400
  have htrace : WordTrace (prefixWord ++ tailWord_958400) baseStart_958400 baseEnd_958400 := by
    simpa [prefixWord, tailWord_958400, baseEnd_958400] using wordTrace_append hprefix tailTrace_958400
  have hstable : (prefixWord ++ tailWord_958400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958400).length < 2 ^ (prefixWord ++ tailWord_958400).sum := by decide
  have hdescent : baseEnd_958400 < baseStart_958400 := by decide
  rcases family_descends (prefixWord ++ tailWord_958400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958434 : List Nat := [3, 3, 3, 1, 2, 1, 1, 1, 3, 4]
def baseStart_958434 : Nat := 118140960795 + 958434 * 2 ^ 59
def prefixEnd_958434 : Nat := 4983230072969 + 3 ^ 40 * 958434 * 2
def baseEnd_958434 : Nat := 328091545074272237511499

theorem tailTrace_958434 : CollatzResearch.WordTrace tailWord_958434 prefixEnd_958434 328091545074272237511499 := by
  unfold tailWord_958434
  simp only [CollatzResearch.WordTrace]
  refine ⟨8739239952441195085120589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23304639873176520226988237 8739239952441195085120589)
  ·
    refine ⟨3277214982165448156920221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8739239952441195085120589 3277214982165448156920221)
    ·
      refine ⟨1228955618312043058845083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3277214982165448156920221 1228955618312043058845083)
      ·
        refine ⟨1843433427468064588267625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1228955618312043058845083 1843433427468064588267625)
        ·
          refine ⟨1382575070601048441200719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1843433427468064588267625 1382575070601048441200719)
          ·
            refine ⟨2073862605901572661801079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1382575070601048441200719 2073862605901572661801079)
            ·
              refine ⟨3110793908852358992701619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2073862605901572661801079 3110793908852358992701619)
              ·
                refine ⟨4666190863278538489052429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3110793908852358992701619 4666190863278538489052429)
                ·
                  refine ⟨1749821573729451933394661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4666190863278538489052429 1749821573729451933394661)
                  ·
                    refine ⟨328091545074272237511499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1749821573729451933394661 328091545074272237511499)
                    ·
                      rfl

theorem cell22_958434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_958434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_958434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_958434 prefixEnd_958434 := by exact prefixLift 958434
  have htrace : WordTrace (prefixWord ++ tailWord_958434) baseStart_958434 baseEnd_958434 := by
    simpa [prefixWord, tailWord_958434, baseEnd_958434] using wordTrace_append hprefix tailTrace_958434
  have hstable : (prefixWord ++ tailWord_958434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958434).length < 2 ^ (prefixWord ++ tailWord_958434).sum := by decide
  have hdescent : baseEnd_958434 < baseStart_958434 := by decide
  rcases family_descends (prefixWord ++ tailWord_958434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958492 : List Nat := [2, 2, 3, 1, 3, 1, 1, 1, 5, 3]
def baseStart_958492 : Nat := 118140960795 + 958492 * 2 ^ 59
def prefixEnd_958492 : Nat := 4983230072969 + 3 ^ 40 * 958492 * 2
def baseEnd_958492 : Nat := 328111399659579419561321

theorem tailTrace_958492 : CollatzResearch.WordTrace tailWord_958492 prefixEnd_958492 328111399659579419561321 := by
  unfold tailWord_958492
  simp only [CollatzResearch.WordTrace]
  refine ⟨17479537621777328123046865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23306050162369770830729153 17479537621777328123046865)
  ·
    refine ⟨13109653216332996092285149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17479537621777328123046865 13109653216332996092285149)
    ·
      refine ⟨4916119956124873534606931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13109653216332996092285149 4916119956124873534606931)
      ·
        refine ⟨7374179934187310301910397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4916119956124873534606931 7374179934187310301910397)
        ·
          refine ⟨2765317475320241363216399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7374179934187310301910397 2765317475320241363216399)
          ·
            refine ⟨4147976212980362044824599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2765317475320241363216399 4147976212980362044824599)
            ·
              refine ⟨6221964319470543067236899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4147976212980362044824599 6221964319470543067236899)
              ·
                refine ⟨9332946479205814600855349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6221964319470543067236899 9332946479205814600855349)
                ·
                  refine ⟨874963732425545118830189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9332946479205814600855349 874963732425545118830189)
                  ·
                    refine ⟨328111399659579419561321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 874963732425545118830189 328111399659579419561321)
                    ·
                      rfl

theorem cell22_958492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_958492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_958492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_958492 prefixEnd_958492 := by exact prefixLift 958492
  have htrace : WordTrace (prefixWord ++ tailWord_958492) baseStart_958492 baseEnd_958492 := by
    simpa [prefixWord, tailWord_958492, baseEnd_958492] using wordTrace_append hprefix tailTrace_958492
  have hstable : (prefixWord ++ tailWord_958492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958492).length < 2 ^ (prefixWord ++ tailWord_958492).sum := by decide
  have hdescent : baseEnd_958492 < baseStart_958492 := by decide
  rcases family_descends (prefixWord ++ tailWord_958492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958526 : List Nat := [4, 2, 1, 3, 2, 1, 2, 1, 3, 3]
def baseStart_958526 : Nat := 118140960795 + 958526 * 2 ^ 59
def prefixEnd_958526 : Nat := 4983230072969 + 3 ^ 40 * 958526 * 2
def baseEnd_958526 : Nat := 328123038554414664211217

theorem tailTrace_958526 : CollatzResearch.WordTrace tailWord_958526 prefixEnd_958526 328123038554414664211217 := by
  unfold tailWord_958526
  simp only [CollatzResearch.WordTrace]
  refine ⟨4370039415678935006603929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23306876883620986701887621 4370039415678935006603929)
  ·
    refine ⟨3277529561759201254952947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4370039415678935006603929 3277529561759201254952947)
    ·
      refine ⟨4916294342638801882429421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3277529561759201254952947 4916294342638801882429421)
      ·
        refine ⟨1843610378489550705911033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4916294342638801882429421 1843610378489550705911033)
        ·
          refine ⟨1382707783867163029433275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1843610378489550705911033 1382707783867163029433275)
          ·
            refine ⟨2074061675800744544149913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1382707783867163029433275 2074061675800744544149913)
            ·
              refine ⟨1555546256850558408112435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2074061675800744544149913 1555546256850558408112435)
              ·
                refine ⟨2333319385275837612168653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1555546256850558408112435 2333319385275837612168653)
                ·
                  refine ⟨874994769478439104563245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2333319385275837612168653 874994769478439104563245)
                  ·
                    refine ⟨328123038554414664211217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 874994769478439104563245 328123038554414664211217)
                    ·
                      rfl

theorem cell22_958526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_958526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_958526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_958526 prefixEnd_958526 := by exact prefixLift 958526
  have htrace : WordTrace (prefixWord ++ tailWord_958526) baseStart_958526 baseEnd_958526 := by
    simpa [prefixWord, tailWord_958526, baseEnd_958526] using wordTrace_append hprefix tailTrace_958526
  have hstable : (prefixWord ++ tailWord_958526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958526).length < 2 ^ (prefixWord ++ tailWord_958526).sum := by decide
  have hdescent : baseEnd_958526 < baseStart_958526 := by decide
  rcases family_descends (prefixWord ++ tailWord_958526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958552 : List Nat := [2, 1, 2, 2, 1, 4, 1, 4, 1, 4]
def baseStart_958552 : Nat := 118140960795 + 958552 * 2 ^ 59
def prefixEnd_958552 : Nat := 4983230072969 + 3 ^ 40 * 958552 * 2
def baseEnd_958552 : Nat := 328131938885759263061137

theorem tailTrace_958552 : CollatzResearch.WordTrace tailWord_958552 prefixEnd_958552 328131938885759263061137 := by
  unfold tailWord_958552
  simp only [CollatzResearch.WordTrace]
  refine ⟨17480631811668643246638955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23307509082224857662185273 17480631811668643246638955)
  ·
    refine ⟨26220947717502964869958433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17480631811668643246638955 26220947717502964869958433)
    ·
      refine ⟨19665710788127223652468825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26220947717502964869958433 19665710788127223652468825)
      ·
        refine ⟨14749283091095417739351619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19665710788127223652468825 14749283091095417739351619)
        ·
          refine ⟨22123924636643126609027429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14749283091095417739351619 22123924636643126609027429)
          ·
            refine ⟨4148235869370586239192643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22123924636643126609027429 4148235869370586239192643)
            ·
              refine ⟨6222353804055879358788965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4148235869370586239192643 6222353804055879358788965)
              ·
                refine ⟨1166691338260477379772931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6222353804055879358788965 1166691338260477379772931)
                ·
                  refine ⟨1750037007390716069659397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1166691338260477379772931 1750037007390716069659397)
                  ·
                    refine ⟨328131938885759263061137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1750037007390716069659397 328131938885759263061137)
                    ·
                      rfl

theorem cell22_958552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 4, 1, 4].length) (baseStart_958552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_958552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_958552 prefixEnd_958552 := by exact prefixLift 958552
  have htrace : WordTrace (prefixWord ++ tailWord_958552) baseStart_958552 baseEnd_958552 := by
    simpa [prefixWord, tailWord_958552, baseEnd_958552] using wordTrace_append hprefix tailTrace_958552
  have hstable : (prefixWord ++ tailWord_958552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958552).length < 2 ^ (prefixWord ++ tailWord_958552).sum := by decide
  have hdescent : baseEnd_958552 < baseStart_958552 := by decide
  rcases family_descends (prefixWord ++ tailWord_958552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958595 : List Nat := [1, 1, 1, 3, 3, 3, 1, 9]
def baseStart_958595 : Nat := 118140960795 + 958595 * 2 ^ 59
def prefixEnd_958595 : Nat := 4983230072969 + 3 ^ 40 * 958595 * 2
def baseEnd_958595 : Nat := 36460739851613498248445

theorem tailTrace_958595 : CollatzResearch.WordTrace tailWord_958595 prefixEnd_958595 36460739851613498248445 := by
  unfold tailWord_958595
  simp only [CollatzResearch.WordTrace]
  refine ⟨34962831962181504837093239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23308554641454336558062159 34962831962181504837093239)
  ·
    refine ⟨52444247943272257255639859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34962831962181504837093239 52444247943272257255639859)
    ·
      refine ⟨78666371914908385883459789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52444247943272257255639859 78666371914908385883459789)
      ·
        refine ⟨29499889468090644706297421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78666371914908385883459789 29499889468090644706297421)
        ·
          refine ⟨11062458550533991764861533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29499889468090644706297421 11062458550533991764861533)
          ·
            refine ⟨4148421956450246911823075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11062458550533991764861533 4148421956450246911823075)
            ·
              refine ⟨6222632934675370367734613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4148421956450246911823075 6222632934675370367734613)
              ·
                refine ⟨36460739851613498248445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6222632934675370367734613 36460739851613498248445)
                ·
                  rfl

theorem cell22_958595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 9].length) (baseStart_958595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_958595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_958595 prefixEnd_958595 := by exact prefixLift 958595
  have htrace : WordTrace (prefixWord ++ tailWord_958595) baseStart_958595 baseEnd_958595 := by
    simpa [prefixWord, tailWord_958595, baseEnd_958595] using wordTrace_append hprefix tailTrace_958595
  have hstable : (prefixWord ++ tailWord_958595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958595).length < 2 ^ (prefixWord ++ tailWord_958595).sum := by decide
  have hdescent : baseEnd_958595 < baseStart_958595 := by decide
  rcases family_descends (prefixWord ++ tailWord_958595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958732 : List Nat := [2, 2, 1, 2, 2, 2, 1, 3, 1, 6]
def baseStart_958732 : Nat := 118140960795 + 958732 * 2 ^ 59
def prefixEnd_958732 : Nat := 4983230072969 + 3 ^ 40 * 958732 * 2
def baseEnd_958732 : Nat := 328193556564298793560585

theorem tailTrace_958732 : CollatzResearch.WordTrace tailWord_958732 prefixEnd_958732 328193556564298793560585 := by
  unfold tailWord_958732
  simp only [CollatzResearch.WordTrace]
  refine ⟨17483914381342588617415225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23311885841790118156553633 17483914381342588617415225)
  ·
    refine ⟨13112935786006941463061419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17483914381342588617415225 13112935786006941463061419)
    ·
      refine ⟨19669403679010412194592129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13112935786006941463061419 19669403679010412194592129)
      ·
        refine ⟨14752052759257809145944097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19669403679010412194592129 14752052759257809145944097)
        ·
          refine ⟨11064039569443356859458073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14752052759257809145944097 11064039569443356859458073)
          ·
            refine ⟨8298029677082517644593555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11064039569443356859458073 8298029677082517644593555)
            ·
              refine ⟨12447044515623776466890333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8298029677082517644593555 12447044515623776466890333)
              ·
                refine ⟨4667641693358916175083875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12447044515623776466890333 4667641693358916175083875)
                ·
                  refine ⟨7001462540038374262625813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4667641693358916175083875 7001462540038374262625813)
                  ·
                    refine ⟨328193556564298793560585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7001462540038374262625813 328193556564298793560585)
                    ·
                      rfl

theorem cell22_958732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 1, 6].length) (baseStart_958732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_958732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_958732 prefixEnd_958732 := by exact prefixLift 958732
  have htrace : WordTrace (prefixWord ++ tailWord_958732) baseStart_958732 baseEnd_958732 := by
    simpa [prefixWord, tailWord_958732, baseEnd_958732] using wordTrace_append hprefix tailTrace_958732
  have hstable : (prefixWord ++ tailWord_958732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958732).length < 2 ^ (prefixWord ++ tailWord_958732).sum := by decide
  have hdescent : baseEnd_958732 < baseStart_958732 := by decide
  rcases family_descends (prefixWord ++ tailWord_958732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958734 : List Nat := [4, 1, 1, 2, 1, 2, 1, 1, 6, 3]
def baseStart_958734 : Nat := 118140960795 + 958734 * 2 ^ 59
def prefixEnd_958734 : Nat := 4983230072969 + 3 ^ 40 * 958734 * 2
def baseEnd_958734 : Nat := 328194241205171455010579

theorem tailTrace_958734 : CollatzResearch.WordTrace tailWord_958734 prefixEnd_958734 328194241205171455010579 := by
  unfold tailWord_958734
  simp only [CollatzResearch.WordTrace]
  refine ⟨4370987713584741447050407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23311934472451954384268837 4370987713584741447050407)
  ·
    refine ⟨6556481570377112170575611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4370987713584741447050407 6556481570377112170575611)
    ·
      refine ⟨9834722355565668255863417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6556481570377112170575611 9834722355565668255863417)
      ·
        refine ⟨7376041766674251191897563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9834722355565668255863417 7376041766674251191897563)
        ·
          refine ⟨11064062650011376787846345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7376041766674251191897563 11064062650011376787846345)
          ·
            refine ⟨8298046987508532590884759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11064062650011376787846345 8298046987508532590884759)
            ·
              refine ⟨12447070481262798886327139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8298046987508532590884759 12447070481262798886327139)
              ·
                refine ⟨18670605721894198329490709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12447070481262798886327139 18670605721894198329490709)
                ·
                  refine ⟨875184643213790546694877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 18670605721894198329490709 875184643213790546694877)
                  ·
                    refine ⟨328194241205171455010579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 875184643213790546694877 328194241205171455010579)
                    ·
                      rfl

theorem cell22_958734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 6, 3].length) (baseStart_958734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_958734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_958734 prefixEnd_958734 := by exact prefixLift 958734
  have htrace : WordTrace (prefixWord ++ tailWord_958734) baseStart_958734 baseEnd_958734 := by
    simpa [prefixWord, tailWord_958734, baseEnd_958734] using wordTrace_append hprefix tailTrace_958734
  have hstable : (prefixWord ++ tailWord_958734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958734).length < 2 ^ (prefixWord ++ tailWord_958734).sum := by decide
  have hdescent : baseEnd_958734 < baseStart_958734 := by decide
  rcases family_descends (prefixWord ++ tailWord_958734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958792 : List Nat := [2, 1, 3, 1, 1, 2, 2, 1, 9]
def baseStart_958792 : Nat := 118140960795 + 958792 * 2 ^ 59
def prefixEnd_958792 : Nat := 4983230072969 + 3 ^ 40 * 958792 * 2
def baseEnd_958792 : Nat := 109404698596826212353467

theorem tailTrace_958792 : CollatzResearch.WordTrace tailWord_958792 prefixEnd_958792 109404698596826212353467 := by
  unfold tailWord_958792
  simp only [CollatzResearch.WordTrace]
  refine ⟨17485008571233903741007315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23313344761645204988009753 17485008571233903741007315)
  ·
    refine ⟨26227512856850855611510973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17485008571233903741007315 26227512856850855611510973)
    ·
      refine ⟨9835317321319070854316615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26227512856850855611510973 9835317321319070854316615)
      ·
        refine ⟨14752975981978606281474923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9835317321319070854316615 14752975981978606281474923)
        ·
          refine ⟨22129463972967909422212385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14752975981978606281474923 22129463972967909422212385)
          ·
            refine ⟨16597097979725932066659289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22129463972967909422212385 16597097979725932066659289)
            ·
              refine ⟨12447823484794449049994467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16597097979725932066659289 12447823484794449049994467)
              ·
                refine ⟨18671735227191673574991701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12447823484794449049994467 18671735227191673574991701)
                ·
                  refine ⟨109404698596826212353467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 18671735227191673574991701 109404698596826212353467)
                  ·
                    rfl

theorem cell22_958792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 9].length) (baseStart_958792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_958792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_958792 prefixEnd_958792 := by exact prefixLift 958792
  have htrace : WordTrace (prefixWord ++ tailWord_958792) baseStart_958792 baseEnd_958792 := by
    simpa [prefixWord, tailWord_958792, baseEnd_958792] using wordTrace_append hprefix tailTrace_958792
  have hstable : (prefixWord ++ tailWord_958792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958792).length < 2 ^ (prefixWord ++ tailWord_958792).sum := by decide
  have hdescent : baseEnd_958792 < baseStart_958792 := by decide
  rcases family_descends (prefixWord ++ tailWord_958792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958824 : List Nat := [2, 1, 4, 2, 2, 1, 1, 1, 1, 7]
def baseStart_958824 : Nat := 118140960795 + 958824 * 2 ^ 59
def prefixEnd_958824 : Nat := 4983230072969 + 3 ^ 40 * 958824 * 2
def baseEnd_958824 : Nat := 328225050044441220260303

theorem tailTrace_958824 : CollatzResearch.WordTrace tailWord_958824 prefixEnd_958824 328225050044441220260303 := by
  unfold tailWord_958824
  simp only [CollatzResearch.WordTrace]
  refine ⟨17485592139175938473589763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23314122852234584631453017 17485592139175938473589763)
  ·
    refine ⟨26228388208763907710384645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17485592139175938473589763 26228388208763907710384645)
    ·
      refine ⟨4917822789143232695697121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26228388208763907710384645 4917822789143232695697121)
      ·
        refine ⟨3688367091857424521772841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4917822789143232695697121 3688367091857424521772841)
        ·
          refine ⟨2766275318893068391329631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3688367091857424521772841 2766275318893068391329631)
          ·
            refine ⟨4149412978339602586994447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2766275318893068391329631 4149412978339602586994447)
            ·
              refine ⟨6224119467509403880491671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4149412978339602586994447 6224119467509403880491671)
              ·
                refine ⟨9336179201264105820737507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6224119467509403880491671 9336179201264105820737507)
                ·
                  refine ⟨14004268801896158731106261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9336179201264105820737507 14004268801896158731106261)
                  ·
                    refine ⟨328225050044441220260303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14004268801896158731106261 328225050044441220260303)
                    ·
                      rfl

theorem cell22_958824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_958824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_958824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_958824 prefixEnd_958824 := by exact prefixLift 958824
  have htrace : WordTrace (prefixWord ++ tailWord_958824) baseStart_958824 baseEnd_958824 := by
    simpa [prefixWord, tailWord_958824, baseEnd_958824] using wordTrace_append hprefix tailTrace_958824
  have hstable : (prefixWord ++ tailWord_958824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958824).length < 2 ^ (prefixWord ++ tailWord_958824).sum := by decide
  have hdescent : baseEnd_958824 < baseStart_958824 := by decide
  rcases family_descends (prefixWord ++ tailWord_958824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958826 : List Nat := [3, 1, 3, 3, 1, 1, 2, 3, 5]
def baseStart_958826 : Nat := 118140960795 + 958826 * 2 ^ 59
def prefixEnd_958826 : Nat := 4983230072969 + 3 ^ 40 * 958826 * 2
def baseEnd_958826 : Nat := 109408578228437960570099

theorem tailTrace_958826 : CollatzResearch.WordTrace tailWord_958826 prefixEnd_958826 109408578228437960570099 := by
  unfold tailWord_958826
  simp only [CollatzResearch.WordTrace]
  refine ⟨8742814306086157822188083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23314171482896420859168221 8742814306086157822188083)
  ·
    refine ⟨13114221459129236733282125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8742814306086157822188083 13114221459129236733282125)
    ·
      refine ⟨4917833047173463774980797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13114221459129236733282125 4917833047173463774980797)
      ·
        refine ⟨1844187392690048915617799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4917833047173463774980797 1844187392690048915617799)
        ·
          refine ⟨2766281089035073373426699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1844187392690048915617799 2766281089035073373426699)
          ·
            refine ⟨4149421633552610060140049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2766281089035073373426699 4149421633552610060140049)
            ·
              refine ⟨3112066225164457545105037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4149421633552610060140049 3112066225164457545105037)
              ·
                refine ⟨1167024834436671579414389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3112066225164457545105037 1167024834436671579414389)
                ·
                  refine ⟨109408578228437960570099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1167024834436671579414389 109408578228437960570099)
                  ·
                    rfl

theorem cell22_958826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 3, 5].length) (baseStart_958826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_958826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_958826 prefixEnd_958826 := by exact prefixLift 958826
  have htrace : WordTrace (prefixWord ++ tailWord_958826) baseStart_958826 baseEnd_958826 := by
    simpa [prefixWord, tailWord_958826, baseEnd_958826] using wordTrace_append hprefix tailTrace_958826
  have hstable : (prefixWord ++ tailWord_958826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958826).length < 2 ^ (prefixWord ++ tailWord_958826).sum := by decide
  have hdescent : baseEnd_958826 < baseStart_958826 := by decide
  rcases family_descends (prefixWord ++ tailWord_958826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958856 : List Nat := [2, 1, 3, 3, 1, 1, 3, 3, 1, 4]
def baseStart_958856 : Nat := 118140960795 + 958856 * 2 ^ 59
def prefixEnd_958856 : Nat := 4983230072969 + 3 ^ 40 * 958856 * 2
def baseEnd_958856 : Nat := 328236004298403803460205

theorem tailTrace_958856 : CollatzResearch.WordTrace tailWord_958856 prefixEnd_958856 328236004298403803460205 := by
  unfold tailWord_958856
  simp only [CollatzResearch.WordTrace]
  refine ⟨17486175707117973206172211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23314900942823964274896281 17486175707117973206172211)
  ·
    refine ⟨26229263560676959809258317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17486175707117973206172211 26229263560676959809258317)
    ·
      refine ⟨9835973835253859928471869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26229263560676959809258317 9835973835253859928471869)
      ·
        refine ⟨3688490188220197473176951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9835973835253859928471869 3688490188220197473176951)
        ·
          refine ⟨5532735282330296209765427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3688490188220197473176951 5532735282330296209765427)
          ·
            refine ⟨8299102923495444314648141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5532735282330296209765427 8299102923495444314648141)
            ·
              refine ⟨3112163596310791617993053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8299102923495444314648141 3112163596310791617993053)
              ·
                refine ⟨1167061348616546856747395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3112163596310791617993053 1167061348616546856747395)
                ·
                  refine ⟨1750592022924820285121093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1167061348616546856747395 1750592022924820285121093)
                  ·
                    refine ⟨328236004298403803460205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1750592022924820285121093 328236004298403803460205)
                    ·
                      rfl

theorem cell22_958856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_958856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_958856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_958856 prefixEnd_958856 := by exact prefixLift 958856
  have htrace : WordTrace (prefixWord ++ tailWord_958856) baseStart_958856 baseEnd_958856 := by
    simpa [prefixWord, tailWord_958856, baseEnd_958856] using wordTrace_append hprefix tailTrace_958856
  have hstable : (prefixWord ++ tailWord_958856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958856).length < 2 ^ (prefixWord ++ tailWord_958856).sum := by decide
  have hdescent : baseEnd_958856 < baseStart_958856 := by decide
  rcases family_descends (prefixWord ++ tailWord_958856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958871 : List Nat := [1, 1, 3, 3, 1, 1, 4, 4, 4]
def baseStart_958871 : Nat := 118140960795 + 958871 * 2 ^ 59
def prefixEnd_958871 : Nat := 4983230072969 + 3 ^ 40 * 958871 * 2
def baseEnd_958871 : Nat := 109413713034982921445053

theorem tailTrace_958871 : CollatzResearch.WordTrace tailWord_958871 prefixEnd_958871 109413713034982921445053 := by
  unfold tailWord_958871
  simp only [CollatzResearch.WordTrace]
  refine ⟨34972898509181603974140467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23315265672787735982760311 34972898509181603974140467)
  ·
    refine ⟨52459347763772405961210701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34972898509181603974140467 52459347763772405961210701)
    ·
      refine ⟨19672255411414652235454013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52459347763772405961210701 19672255411414652235454013)
      ·
        refine ⟨7377095779280494588295255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19672255411414652235454013 7377095779280494588295255)
        ·
          refine ⟨11065643668920741882442883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7377095779280494588295255 11065643668920741882442883)
          ·
            refine ⟨16598465503381112823664325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11065643668920741882442883 16598465503381112823664325)
            ·
              refine ⟨3112212281883958654437061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16598465503381112823664325 3112212281883958654437061)
              ·
                refine ⟨583539802853242247706949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3112212281883958654437061 583539802853242247706949)
                ·
                  refine ⟨109413713034982921445053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 583539802853242247706949 109413713034982921445053)
                  ·
                    rfl

theorem cell22_958871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 4, 4].length) (baseStart_958871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_958871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_958871 prefixEnd_958871 := by exact prefixLift 958871
  have htrace : WordTrace (prefixWord ++ tailWord_958871) baseStart_958871 baseEnd_958871 := by
    simpa [prefixWord, tailWord_958871, baseEnd_958871] using wordTrace_append hprefix tailTrace_958871
  have hstable : (prefixWord ++ tailWord_958871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958871).length < 2 ^ (prefixWord ++ tailWord_958871).sum := by decide
  have hdescent : baseEnd_958871 < baseStart_958871 := by decide
  rcases family_descends (prefixWord ++ tailWord_958871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958884 : List Nat := [2, 3, 1, 2, 1, 1, 3, 2, 1, 6]
def baseStart_958884 : Nat := 118140960795 + 958884 * 2 ^ 59
def prefixEnd_958884 : Nat := 4983230072969 + 3 ^ 40 * 958884 * 2
def baseEnd_958884 : Nat := 328245589270621063760119

theorem tailTrace_958884 : CollatzResearch.WordTrace tailWord_958884 prefixEnd_958884 328245589270621063760119 := by
  unfold tailWord_958884
  simp only [CollatzResearch.WordTrace]
  refine ⟨17486686329067253597181853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23315581772089671462909137 17486686329067253597181853)
  ·
    refine ⟨6557507373400220098943195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17486686329067253597181853 6557507373400220098943195)
    ·
      refine ⟨9836261060100330148414793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6557507373400220098943195 9836261060100330148414793)
      ·
        refine ⟨7377195795075247611311095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9836261060100330148414793 7377195795075247611311095)
        ·
          refine ⟨11065793692612871416966643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7377195795075247611311095 11065793692612871416966643)
          ·
            refine ⟨16598690538919307125449965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11065793692612871416966643 16598690538919307125449965)
            ·
              refine ⟨6224508952094740172043737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16598690538919307125449965 6224508952094740172043737)
              ·
                refine ⟨4668381714071055129032803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6224508952094740172043737 4668381714071055129032803)
                ·
                  refine ⟨7002572571106582693549205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4668381714071055129032803 7002572571106582693549205)
                  ·
                    refine ⟨328245589270621063760119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7002572571106582693549205 328245589270621063760119)
                    ·
                      rfl

theorem cell22_958884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_958884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_958884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_958884 prefixEnd_958884 := by exact prefixLift 958884
  have htrace : WordTrace (prefixWord ++ tailWord_958884) baseStart_958884 baseEnd_958884 := by
    simpa [prefixWord, tailWord_958884, baseEnd_958884] using wordTrace_append hprefix tailTrace_958884
  have hstable : (prefixWord ++ tailWord_958884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958884).length < 2 ^ (prefixWord ++ tailWord_958884).sum := by decide
  have hdescent : baseEnd_958884 < baseStart_958884 := by decide
  rcases family_descends (prefixWord ++ tailWord_958884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958959 : List Nat := [1, 1, 2, 1, 4, 1, 1, 2, 4, 5]
def baseStart_958959 : Nat := 118140960795 + 958959 * 2 ^ 59
def prefixEnd_958959 : Nat := 4983230072969 + 3 ^ 40 * 958959 * 2
def baseEnd_958959 : Nat := 328271263303345868134889

theorem tailTrace_958959 : CollatzResearch.WordTrace tailWord_958959 prefixEnd_958959 328271263303345868134889 := by
  unfold tailWord_958959
  simp only [CollatzResearch.WordTrace]
  refine ⟨34976108132862795003343931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23317405421908530002229287 34976108132862795003343931)
  ·
    refine ⟨52464162199294192505015897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34976108132862795003343931 52464162199294192505015897)
    ·
      refine ⟨39348121649470644378761923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52464162199294192505015897 39348121649470644378761923)
      ·
        refine ⟨59022182474205966568142885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39348121649470644378761923 59022182474205966568142885)
        ·
          refine ⟨11066659213913618731526791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59022182474205966568142885 11066659213913618731526791)
          ·
            refine ⟨16599988820870428097290187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11066659213913618731526791 16599988820870428097290187)
            ·
              refine ⟨24899983231305642145935281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16599988820870428097290187 24899983231305642145935281)
              ·
                refine ⟨18674987423479231609451461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24899983231305642145935281 18674987423479231609451461)
                ·
                  refine ⟨3501560141902355926772149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18674987423479231609451461 3501560141902355926772149)
                  ·
                    refine ⟨328271263303345868134889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3501560141902355926772149 328271263303345868134889)
                    ·
                      rfl

theorem cell22_958959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 5].length) (baseStart_958959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_958959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_958959 prefixEnd_958959 := by exact prefixLift 958959
  have htrace : WordTrace (prefixWord ++ tailWord_958959) baseStart_958959 baseEnd_958959 := by
    simpa [prefixWord, tailWord_958959, baseEnd_958959] using wordTrace_append hprefix tailTrace_958959
  have hstable : (prefixWord ++ tailWord_958959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958959).length < 2 ^ (prefixWord ++ tailWord_958959).sum := by decide
  have hdescent : baseEnd_958959 < baseStart_958959 := by decide
  rcases family_descends (prefixWord ++ tailWord_958959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959053 : List Nat := [1, 6, 1, 1, 2, 1, 1, 2, 1, 6]
def baseStart_959053 : Nat := 118140960795 + 959053 * 2 ^ 59
def prefixEnd_959053 : Nat := 4983230072969 + 3 ^ 40 * 959053 * 2
def baseEnd_959053 : Nat := 328303441424360956284601

theorem tailTrace_959053 : CollatzResearch.WordTrace tailWord_959053 prefixEnd_959053 328303441424360956284601 := by
  unfold tailWord_959053
  simp only [CollatzResearch.WordTrace]
  refine ⟨34979536594522249057265813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23319691063014832704843875 34979536594522249057265813)
  ·
    refine ⟨1639665777868230424559335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 34979536594522249057265813 1639665777868230424559335)
    ·
      refine ⟨2459498666802345636839003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1639665777868230424559335 2459498666802345636839003)
      ·
        refine ⟨3689248000203518455258505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2459498666802345636839003 3689248000203518455258505)
        ·
          refine ⟨2766936000152638841443879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3689248000203518455258505 2766936000152638841443879)
          ·
            refine ⟨4150404000228958262165819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2766936000152638841443879 4150404000228958262165819)
            ·
              refine ⟨6225606000343437393248729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4150404000228958262165819 6225606000343437393248729)
              ·
                refine ⟨4669204500257578044936547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6225606000343437393248729 4669204500257578044936547)
                ·
                  refine ⟨7003806750386367067404821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4669204500257578044936547 7003806750386367067404821)
                  ·
                    refine ⟨328303441424360956284601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7003806750386367067404821 328303441424360956284601)
                    ·
                      rfl

theorem cell22_959053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_959053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_959053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_959053 prefixEnd_959053 := by exact prefixLift 959053
  have htrace : WordTrace (prefixWord ++ tailWord_959053) baseStart_959053 baseEnd_959053 := by
    simpa [prefixWord, tailWord_959053, baseEnd_959053] using wordTrace_append hprefix tailTrace_959053
  have hstable : (prefixWord ++ tailWord_959053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959053).length < 2 ^ (prefixWord ++ tailWord_959053).sum := by decide
  have hdescent : baseEnd_959053 < baseStart_959053 := by decide
  rcases family_descends (prefixWord ++ tailWord_959053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959068 : List Nat := [2, 2, 4, 1, 3, 1, 1, 8]
def baseStart_959068 : Nat := 118140960795 + 959068 * 2 ^ 59
def prefixEnd_959068 : Nat := 4983230072969 + 3 ^ 40 * 959068 * 2
def baseEnd_959068 : Nat := 36478730692322879684395

theorem tailTrace_959068 : CollatzResearch.WordTrace tailWord_959068 prefixEnd_959068 36478730692322879684395 := by
  unfold tailWord_959068
  simp only [CollatzResearch.WordTrace]
  refine ⟨17490041844733953309530929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23320055792978604412707905 17490041844733953309530929)
  ·
    refine ⟨13117531383550464982148197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17490041844733953309530929 13117531383550464982148197)
    ·
      refine ⟨2459537134415712184152787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13117531383550464982148197 2459537134415712184152787)
      ·
        refine ⟨3689305701623568276229181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2459537134415712184152787 3689305701623568276229181)
        ·
          refine ⟨1383489638108838103585943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3689305701623568276229181 1383489638108838103585943)
          ·
            refine ⟨2075234457163257155378915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1383489638108838103585943 2075234457163257155378915)
            ·
              refine ⟨3112851685744885733068373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2075234457163257155378915 3112851685744885733068373)
              ·
                refine ⟨36478730692322879684395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3112851685744885733068373 36478730692322879684395)
                ·
                  rfl

theorem cell22_959068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 8].length) (baseStart_959068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_959068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_959068 prefixEnd_959068 := by exact prefixLift 959068
  have htrace : WordTrace (prefixWord ++ tailWord_959068) baseStart_959068 baseEnd_959068 := by
    simpa [prefixWord, tailWord_959068, baseEnd_959068] using wordTrace_append hprefix tailTrace_959068
  have hstable : (prefixWord ++ tailWord_959068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959068).length < 2 ^ (prefixWord ++ tailWord_959068).sum := by decide
  have hdescent : baseEnd_959068 < baseStart_959068 := by decide
  rcases family_descends (prefixWord ++ tailWord_959068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959074 : List Nat := [3, 3, 2, 3, 1, 2, 1, 3, 4]
def baseStart_959074 : Nat := 118140960795 + 959074 * 2 ^ 59
def prefixEnd_959074 : Nat := 4983230072969 + 3 ^ 40 * 959074 * 2
def baseEnd_959074 : Nat := 109436876717841300503179

theorem tailTrace_959074 : CollatzResearch.WordTrace tailWord_959074 prefixEnd_959074 109436876717841300503179 := by
  unfold tailWord_959074
  simp only [CollatzResearch.WordTrace]
  refine ⟨8745075631861542410945069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23320201684964113095853517 8745075631861542410945069)
  ·
    refine ⟨3279403361948078404104401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8745075631861542410945069 3279403361948078404104401)
    ·
      refine ⟨2459552521461058803078301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3279403361948078404104401 2459552521461058803078301)
      ·
        refine ⟨922332195547897051154363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2459552521461058803078301 922332195547897051154363)
        ·
          refine ⟨1383498293321845576731545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 922332195547897051154363 1383498293321845576731545)
          ·
            refine ⟨1037623719991384182548659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1383498293321845576731545 1037623719991384182548659)
            ·
              refine ⟨1556435579987076273822989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1037623719991384182548659 1556435579987076273822989)
              ·
                refine ⟨583663342495153602683621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1556435579987076273822989 583663342495153602683621)
                ·
                  refine ⟨109436876717841300503179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 583663342495153602683621 109436876717841300503179)
                  ·
                    rfl

theorem cell22_959074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_959074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_959074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_959074 prefixEnd_959074 := by exact prefixLift 959074
  have htrace : WordTrace (prefixWord ++ tailWord_959074) baseStart_959074 baseEnd_959074 := by
    simpa [prefixWord, tailWord_959074, baseEnd_959074] using wordTrace_append hprefix tailTrace_959074
  have hstable : (prefixWord ++ tailWord_959074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959074).length < 2 ^ (prefixWord ++ tailWord_959074).sum := by decide
  have hdescent : baseEnd_959074 < baseStart_959074 := by decide
  rcases family_descends (prefixWord ++ tailWord_959074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959100 : List Nat := [2, 2, 2, 1, 1, 2, 2, 6, 1, 3]
def baseStart_959100 : Nat := 118140960795 + 959100 * 2 ^ 59
def prefixEnd_959100 : Nat := 4983230072969 + 3 ^ 40 * 959100 * 2
def baseEnd_959100 : Nat := 328319530484868500359457

theorem tailTrace_959100 : CollatzResearch.WordTrace tailWord_959100 prefixEnd_959100 328319530484868500359457 := by
  unfold tailWord_959100
  simp only [CollatzResearch.WordTrace]
  refine ⟨17490625412675988042113377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23320833883567984056151169 17490625412675988042113377)
  ·
    refine ⟨13117969059506991031585033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17490625412675988042113377 13117969059506991031585033)
    ·
      refine ⟨9838476794630243273688775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13117969059506991031585033 9838476794630243273688775)
      ·
        refine ⟨14757715191945364910533163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9838476794630243273688775 14757715191945364910533163)
        ·
          refine ⟨22136572787918047365799745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14757715191945364910533163 22136572787918047365799745)
          ·
            refine ⟨16602429590938535524349809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22136572787918047365799745 16602429590938535524349809)
            ·
              refine ⟨12451822193203901643262357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16602429590938535524349809 12451822193203901643262357)
              ·
                refine ⟨583679165306432889527923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12451822193203901643262357 583679165306432889527923)
                ·
                  refine ⟨875518747959649334291885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 583679165306432889527923 875518747959649334291885)
                  ·
                    refine ⟨328319530484868500359457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 875518747959649334291885 328319530484868500359457)
                    ·
                      rfl

theorem cell22_959100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 6, 1, 3].length) (baseStart_959100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_959100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_959100 prefixEnd_959100 := by exact prefixLift 959100
  have htrace : WordTrace (prefixWord ++ tailWord_959100) baseStart_959100 baseEnd_959100 := by
    simpa [prefixWord, tailWord_959100, baseEnd_959100] using wordTrace_append hprefix tailTrace_959100
  have hstable : (prefixWord ++ tailWord_959100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959100).length < 2 ^ (prefixWord ++ tailWord_959100).sum := by decide
  have hdescent : baseEnd_959100 < baseStart_959100 := by decide
  rcases family_descends (prefixWord ++ tailWord_959100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959106 : List Nat := [3, 4, 3, 1, 1, 1, 1, 3, 2, 3]
def baseStart_959106 : Nat := 118140960795 + 959106 * 2 ^ 59
def prefixEnd_959106 : Nat := 4983230072969 + 3 ^ 40 * 959106 * 2
def baseEnd_959106 : Nat := 328321584407486484709439

theorem tailTrace_959106 : CollatzResearch.WordTrace tailWord_959106 prefixEnd_959106 328321584407486484709439 := by
  unfold tailWord_959106
  simp only [CollatzResearch.WordTrace]
  refine ⟨8745367415832559777236293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23320979775553492739296781 8745367415832559777236293)
  ·
    refine ⟨1639756390468604958231805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8745367415832559777236293 1639756390468604958231805)
    ·
      refine ⟨614908646425726859336927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1639756390468604958231805 614908646425726859336927)
      ·
        refine ⟨922362969638590289005391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 614908646425726859336927 922362969638590289005391)
        ·
          refine ⟨1383544454457885433508087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 922362969638590289005391 1383544454457885433508087)
          ·
            refine ⟨2075316681686828150262131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1383544454457885433508087 2075316681686828150262131)
            ·
              refine ⟨3112975022530242225393197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2075316681686828150262131 3112975022530242225393197)
              ·
                refine ⟨1167365633448840834522449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3112975022530242225393197 1167365633448840834522449)
                ·
                  refine ⟨875524225086630625891837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1167365633448840834522449 875524225086630625891837)
                  ·
                    refine ⟨328321584407486484709439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 875524225086630625891837 328321584407486484709439)
                    ·
                      rfl

theorem cell22_959106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_959106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_959106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_959106 prefixEnd_959106 := by exact prefixLift 959106
  have htrace : WordTrace (prefixWord ++ tailWord_959106) baseStart_959106 baseEnd_959106 := by
    simpa [prefixWord, tailWord_959106, baseEnd_959106] using wordTrace_append hprefix tailTrace_959106
  have hstable : (prefixWord ++ tailWord_959106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959106).length < 2 ^ (prefixWord ++ tailWord_959106).sum := by decide
  have hdescent : baseEnd_959106 < baseStart_959106 := by decide
  rcases family_descends (prefixWord ++ tailWord_959106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959111 : List Nat := [1, 1, 4, 2, 1, 2, 2, 1, 1, 7]
def baseStart_959111 : Nat := 118140960795 + 959111 * 2 ^ 59
def prefixEnd_959111 : Nat := 4983230072969 + 3 ^ 40 * 959111 * 2
def baseEnd_959111 : Nat := 328323296009668138334423

theorem tailTrace_959111 : CollatzResearch.WordTrace tailWord_959111 prefixEnd_959111 328323296009668138334423 := by
  unfold tailWord_959111
  simp only [CollatzResearch.WordTrace]
  refine ⟨34981652028312124962877187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23321101352208083308584791 34981652028312124962877187)
  ·
    refine ⟨52472478042468187444315781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34981652028312124962877187 52472478042468187444315781)
    ·
      refine ⟨9838589632962785145809209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52472478042468187444315781 9838589632962785145809209)
      ·
        refine ⟨7378942224722088859356907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9838589632962785145809209 7378942224722088859356907)
        ·
          refine ⟨11068413337083133289035361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7378942224722088859356907 11068413337083133289035361)
          ·
            refine ⟨8301310002812349966776521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11068413337083133289035361 8301310002812349966776521)
            ·
              refine ⟨6225982502109262475082391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8301310002812349966776521 6225982502109262475082391)
              ·
                refine ⟨9338973753163893712623587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6225982502109262475082391 9338973753163893712623587)
                ·
                  refine ⟨14008460629745840568935381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9338973753163893712623587 14008460629745840568935381)
                  ·
                    refine ⟨328323296009668138334423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14008460629745840568935381 328323296009668138334423)
                    ·
                      rfl

theorem cell22_959111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_959111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_959111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_959111 prefixEnd_959111 := by exact prefixLift 959111
  have htrace : WordTrace (prefixWord ++ tailWord_959111) baseStart_959111 baseEnd_959111 := by
    simpa [prefixWord, tailWord_959111, baseEnd_959111] using wordTrace_append hprefix tailTrace_959111
  have hstable : (prefixWord ++ tailWord_959111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959111).length < 2 ^ (prefixWord ++ tailWord_959111).sum := by decide
  have hdescent : baseEnd_959111 < baseStart_959111 := by decide
  rcases family_descends (prefixWord ++ tailWord_959111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959203 : List Nat := [1, 1, 1, 7, 1, 2, 9]
def baseStart_959203 : Nat := 118140960795 + 959203 * 2 ^ 59
def prefixEnd_959203 : Nat := 4983230072969 + 3 ^ 40 * 959203 * 2
def baseEnd_959203 : Nat := 12161288499622613519783

theorem tailTrace_959203 : CollatzResearch.WordTrace tailWord_959203 prefixEnd_959203 12161288499622613519783 := by
  unfold tailWord_959203
  simp only [CollatzResearch.WordTrace]
  refine ⟨34985007543978824675226263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23323338362652549783484175 34985007543978824675226263)
  ·
    refine ⟨52477511315968237012839395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34985007543978824675226263 52477511315968237012839395)
    ·
      refine ⟨78716266973952355519259093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52477511315968237012839395 78716266973952355519259093)
      ·
        refine ⟨1844912507202008332482635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 78716266973952355519259093 1844912507202008332482635)
        ·
          refine ⟨2767368760803012498723953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1844912507202008332482635 2767368760803012498723953)
          ·
            refine ⟨2075526570602259374042965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2767368760803012498723953 2075526570602259374042965)
            ·
              refine ⟨12161288499622613519783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2075526570602259374042965 12161288499622613519783)
              ·
                rfl

theorem cell22_959203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 9].length) (baseStart_959203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_959203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_959203 prefixEnd_959203 := by exact prefixLift 959203
  have htrace : WordTrace (prefixWord ++ tailWord_959203) baseStart_959203 baseEnd_959203 := by
    simpa [prefixWord, tailWord_959203, baseEnd_959203] using wordTrace_append hprefix tailTrace_959203
  have hstable : (prefixWord ++ tailWord_959203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959203).length < 2 ^ (prefixWord ++ tailWord_959203).sum := by decide
  have hdescent : baseEnd_959203 < baseStart_959203 := by decide
  rcases family_descends (prefixWord ++ tailWord_959203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959269 : List Nat := [1, 3, 1, 2, 3, 1, 5, 2, 1, 3]
def baseStart_959269 : Nat := 118140960795 + 959269 * 2 ^ 59
def prefixEnd_959269 : Nat := 4983230072969 + 3 ^ 40 * 959269 * 2
def baseEnd_959269 : Nat := 328377382638608392883939

theorem tailTrace_959269 : CollatzResearch.WordTrace tailWord_959269 prefixEnd_959269 328377382638608392883939 := by
  unfold tailWord_959269
  simp only [CollatzResearch.WordTrace]
  refine ⟨34987414761739717947128861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23324943174493145298085907 34987414761739717947128861)
  ·
    refine ⟨13120280535652394230173323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34987414761739717947128861 13120280535652394230173323)
    ·
      refine ⟨19680420803478591345259985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13120280535652394230173323 19680420803478591345259985)
      ·
        refine ⟨14760315602608943508944989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19680420803478591345259985 14760315602608943508944989)
        ·
          refine ⟨5535118350978353815854371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14760315602608943508944989 5535118350978353815854371)
          ·
            refine ⟨8302677526467530723781557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5535118350978353815854371 8302677526467530723781557)
            ·
              refine ⟨778376018106331005354521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8302677526467530723781557 778376018106331005354521)
              ·
                refine ⟨583782013579748254015891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 778376018106331005354521 583782013579748254015891)
                ·
                  refine ⟨875673020369622381023837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 583782013579748254015891 875673020369622381023837)
                  ·
                    refine ⟨328377382638608392883939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 875673020369622381023837 328377382638608392883939)
                    ·
                      rfl

theorem cell22_959269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 2, 1, 3].length) (baseStart_959269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_959269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_959269 prefixEnd_959269 := by exact prefixLift 959269
  have htrace : WordTrace (prefixWord ++ tailWord_959269) baseStart_959269 baseEnd_959269 := by
    simpa [prefixWord, tailWord_959269, baseEnd_959269] using wordTrace_append hprefix tailTrace_959269
  have hstable : (prefixWord ++ tailWord_959269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959269).length < 2 ^ (prefixWord ++ tailWord_959269).sum := by decide
  have hdescent : baseEnd_959269 < baseStart_959269 := by decide
  rcases family_descends (prefixWord ++ tailWord_959269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959295 : List Nat := [1, 1, 2, 2, 5, 2, 1, 1, 3, 4]
def baseStart_959295 : Nat := 118140960795 + 959295 * 2 ^ 59
def prefixEnd_959295 : Nat := 4983230072969 + 3 ^ 40 * 959295 * 2
def baseEnd_959295 : Nat := 328386282969952991733859

theorem tailTrace_959295 : CollatzResearch.WordTrace tailWord_959295 prefixEnd_959295 328386282969952991733859 := by
  unfold tailWord_959295
  simp only [CollatzResearch.WordTrace]
  refine ⟨34988363059645524387575339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23325575373097016258383559 34988363059645524387575339)
  ·
    refine ⟨52482544589468286581363009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34988363059645524387575339 52482544589468286581363009)
    ·
      refine ⟨39361908442101214936022257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52482544589468286581363009 39361908442101214936022257)
      ·
        refine ⟨29521431331575911202016693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39361908442101214936022257 29521431331575911202016693)
        ·
          refine ⟨2767634187335241675189065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29521431331575911202016693 2767634187335241675189065)
          ·
            refine ⟨2075725640501431256391799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2767634187335241675189065 2075725640501431256391799)
            ·
              refine ⟨3113588460752146884587699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2075725640501431256391799 3113588460752146884587699)
              ·
                refine ⟨4670382691128220326881549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3113588460752146884587699 4670382691128220326881549)
                ·
                  refine ⟨1751393509173082622580581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4670382691128220326881549 1751393509173082622580581)
                  ·
                    refine ⟨328386282969952991733859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1751393509173082622580581 328386282969952991733859)
                    ·
                      rfl

theorem cell22_959295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 3, 4].length) (baseStart_959295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_959295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_959295 prefixEnd_959295 := by exact prefixLift 959295
  have htrace : WordTrace (prefixWord ++ tailWord_959295) baseStart_959295 baseEnd_959295 := by
    simpa [prefixWord, tailWord_959295, baseEnd_959295] using wordTrace_append hprefix tailTrace_959295
  have hstable : (prefixWord ++ tailWord_959295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959295).length < 2 ^ (prefixWord ++ tailWord_959295).sum := by decide
  have hdescent : baseEnd_959295 < baseStart_959295 := by decide
  rcases family_descends (prefixWord ++ tailWord_959295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959323 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 10, 4]
def baseStart_959323 : Nat := 118140960795 + 959323 * 2 ^ 59
def prefixEnd_959323 : Nat := 4983230072969 + 3 ^ 40 * 959323 * 2
def baseEnd_959323 : Nat := 328395867942170252033773

theorem tailTrace_959323 : CollatzResearch.WordTrace tailWord_959323 prefixEnd_959323 328395867942170252033773 := by
  unfold tailWord_959323
  simp only [CollatzResearch.WordTrace]
  refine ⟨34989384303544085169594623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23326256202362723446396415 34989384303544085169594623)
  ·
    refine ⟨52484076455316127754391935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34989384303544085169594623 52484076455316127754391935)
    ·
      refine ⟨78726114682974191631587903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52484076455316127754391935 78726114682974191631587903)
      ·
        refine ⟨118089172024461287447381855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78726114682974191631587903 118089172024461287447381855)
        ·
          refine ⟨177133758036691931171072783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118089172024461287447381855 177133758036691931171072783)
          ·
            refine ⟨265700637055037896756609175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177133758036691931171072783 265700637055037896756609175)
            ·
              refine ⟨398550955582556845134913763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265700637055037896756609175 398550955582556845134913763)
              ·
                refine ⟨597826433373835267702370645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 398550955582556845134913763 597826433373835267702370645)
                ·
                  refine ⟨1751444629024908010846789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 597826433373835267702370645 1751444629024908010846789)
                  ·
                    refine ⟨328395867942170252033773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1751444629024908010846789 328395867942170252033773)
                    ·
                      rfl

theorem cell22_959323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10, 4].length) (baseStart_959323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_959323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_959323 prefixEnd_959323 := by exact prefixLift 959323
  have htrace : WordTrace (prefixWord ++ tailWord_959323) baseStart_959323 baseEnd_959323 := by
    simpa [prefixWord, tailWord_959323, baseEnd_959323] using wordTrace_append hprefix tailTrace_959323
  have hstable : (prefixWord ++ tailWord_959323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959323).length < 2 ^ (prefixWord ++ tailWord_959323).sum := by decide
  have hdescent : baseEnd_959323 < baseStart_959323 := by decide
  rcases family_descends (prefixWord ++ tailWord_959323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959496 : List Nat := [2, 1, 3, 2, 1, 5, 2, 2, 4]
def baseStart_959496 : Nat := 118140960795 + 959496 * 2 ^ 59
def prefixEnd_959496 : Nat := 4983230072969 + 3 ^ 40 * 959496 * 2
def baseEnd_959496 : Nat := 109485029792551822486081

theorem tailTrace_959496 : CollatzResearch.WordTrace tailWord_959496 prefixEnd_959496 109485029792551822486081 := by
  unfold tailWord_959496
  simp only [CollatzResearch.WordTrace]
  refine ⟨17497847065958667857821171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23330462754611557143761561 17497847065958667857821171)
  ·
    refine ⟨26246770598938001786731757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17497847065958667857821171 26246770598938001786731757)
    ·
      refine ⟨9842538974601750670024409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26246770598938001786731757 9842538974601750670024409)
      ·
        refine ⟨7381904230951313002518307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9842538974601750670024409 7381904230951313002518307)
        ·
          refine ⟨11072856346426969503777461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7381904230951313002518307 11072856346426969503777461)
          ·
            refine ⟨1038080282477528390979137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11072856346426969503777461 1038080282477528390979137)
            ·
              refine ⟨778560211858146293234353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1038080282477528390979137 778560211858146293234353)
              ·
                refine ⟨583920158893609719925765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 778560211858146293234353 583920158893609719925765)
                ·
                  refine ⟨109485029792551822486081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 583920158893609719925765 109485029792551822486081)
                  ·
                    rfl

theorem cell22_959496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 2, 4].length) (baseStart_959496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_959496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_959496 prefixEnd_959496 := by exact prefixLift 959496
  have htrace : WordTrace (prefixWord ++ tailWord_959496) baseStart_959496 baseEnd_959496 := by
    simpa [prefixWord, tailWord_959496, baseEnd_959496] using wordTrace_append hprefix tailTrace_959496
  have hstable : (prefixWord ++ tailWord_959496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959496).length < 2 ^ (prefixWord ++ tailWord_959496).sum := by decide
  have hdescent : baseEnd_959496 < baseStart_959496 := by decide
  rcases family_descends (prefixWord ++ tailWord_959496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959524 : List Nat := [2, 3, 1, 4, 1, 2, 3, 6]
def baseStart_959524 : Nat := 118140960795 + 959524 * 2 ^ 59
def prefixEnd_959524 : Nat := 4983230072969 + 3 ^ 40 * 959524 * 2
def baseEnd_959524 : Nat := 36496074927763636417573

theorem tailTrace_959524 : CollatzResearch.WordTrace tailWord_959524 prefixEnd_959524 36496074927763636417573 := by
  unfold tailWord_959524
  simp only [CollatzResearch.WordTrace]
  refine ⟨17498357687907948248830813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23331143583877264331774417 17498357687907948248830813)
  ·
    refine ⟨6561884132965480593311555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17498357687907948248830813 6561884132965480593311555)
    ·
      refine ⟨9842826199448220889967333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6561884132965480593311555 9842826199448220889967333)
      ·
        refine ⟨1845529912396541416868875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9842826199448220889967333 1845529912396541416868875)
        ·
          refine ⟨2768294868594812125303313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1845529912396541416868875 2768294868594812125303313)
          ·
            refine ⟨2076221151446109093977485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2768294868594812125303313 2076221151446109093977485)
            ·
              refine ⟨778582931792290910241557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2076221151446109093977485 778582931792290910241557)
              ·
                refine ⟨36496074927763636417573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 778582931792290910241557 36496074927763636417573)
                ·
                  rfl

theorem cell22_959524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 6].length) (baseStart_959524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_959524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_959524 prefixEnd_959524 := by exact prefixLift 959524
  have htrace : WordTrace (prefixWord ++ tailWord_959524) baseStart_959524 baseEnd_959524 := by
    simpa [prefixWord, tailWord_959524, baseEnd_959524] using wordTrace_append hprefix tailTrace_959524
  have hstable : (prefixWord ++ tailWord_959524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959524).length < 2 ^ (prefixWord ++ tailWord_959524).sum := by decide
  have hdescent : baseEnd_959524 < baseStart_959524 := by decide
  rcases family_descends (prefixWord ++ tailWord_959524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959644 : List Nat := [2, 2, 3, 2, 1, 2, 1, 3, 2, 4]
def baseStart_959644 : Nat := 118140960795 + 959644 * 2 ^ 59
def prefixEnd_959644 : Nat := 4983230072969 + 3 ^ 40 * 959644 * 2
def baseEnd_959644 : Nat := 328505752802232414757789

theorem tailTrace_959644 : CollatzResearch.WordTrace tailWord_959644 prefixEnd_959644 328505752802232414757789 := by
  unfold tailWord_959644
  simp only [CollatzResearch.WordTrace]
  refine ⟨17500546067690578496014993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23334061423587437994686657 17500546067690578496014993)
  ·
    refine ⟨13125409550767933872011245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17500546067690578496014993 13125409550767933872011245)
    ·
      refine ⟨4922028581537975202004217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13125409550767933872011245 4922028581537975202004217)
      ·
        refine ⟨3691521436153481401503163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4922028581537975202004217 3691521436153481401503163)
        ·
          refine ⟨5537282154230222102254745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3691521436153481401503163 5537282154230222102254745)
          ·
            refine ⟨4152961615672666576691059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5537282154230222102254745 4152961615672666576691059)
            ·
              refine ⟨6229442423508999865036589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4152961615672666576691059 6229442423508999865036589)
              ·
                refine ⟨2336040908815874949388721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6229442423508999865036589 2336040908815874949388721)
                ·
                  refine ⟨1752030681611906212041541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2336040908815874949388721 1752030681611906212041541)
                  ·
                    refine ⟨328505752802232414757789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1752030681611906212041541 328505752802232414757789)
                    ·
                      rfl

theorem cell22_959644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_959644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_959644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_959644 prefixEnd_959644 := by exact prefixLift 959644
  have htrace : WordTrace (prefixWord ++ tailWord_959644) baseStart_959644 baseEnd_959644 := by
    simpa [prefixWord, tailWord_959644, baseEnd_959644] using wordTrace_append hprefix tailTrace_959644
  have hstable : (prefixWord ++ tailWord_959644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959644).length < 2 ^ (prefixWord ++ tailWord_959644).sum := by decide
  have hdescent : baseEnd_959644 < baseStart_959644 := by decide
  rcases family_descends (prefixWord ++ tailWord_959644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959646 : List Nat := [4, 3, 1, 1, 2, 2, 1, 2, 1, 5]
def baseStart_959646 : Nat := 118140960795 + 959646 * 2 ^ 59
def prefixEnd_959646 : Nat := 4983230072969 + 3 ^ 40 * 959646 * 2
def baseEnd_959646 : Nat := 328506437443105076207783

theorem tailTrace_959646 : CollatzResearch.WordTrace tailWord_959646 prefixEnd_959646 328506437443105076207783 := by
  unfold tailWord_959646
  simp only [CollatzResearch.WordTrace]
  refine ⟨4375145635171738916700349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23334110054249274222401861 4375145635171738916700349)
  ·
    refine ⟨1640679613189402093762631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4375145635171738916700349 1640679613189402093762631)
    ·
      refine ⟨2461019419784103140643947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1640679613189402093762631 2461019419784103140643947)
      ·
        refine ⟨3691529129676154710965921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2461019419784103140643947 3691529129676154710965921)
        ·
          refine ⟨2768646847257116033224441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3691529129676154710965921 2768646847257116033224441)
          ·
            refine ⟨2076485135442837024918331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2768646847257116033224441 2076485135442837024918331)
            ·
              refine ⟨3114727703164255537377497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2076485135442837024918331 3114727703164255537377497)
              ·
                refine ⟨2336045777373191653033123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3114727703164255537377497 2336045777373191653033123)
                ·
                  refine ⟨3504068666059787479549685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2336045777373191653033123 3504068666059787479549685)
                  ·
                    refine ⟨328506437443105076207783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3504068666059787479549685 328506437443105076207783)
                    ·
                      rfl

theorem cell22_959646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_959646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_959646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_959646 prefixEnd_959646 := by exact prefixLift 959646
  have htrace : WordTrace (prefixWord ++ tailWord_959646) baseStart_959646 baseEnd_959646 := by
    simpa [prefixWord, tailWord_959646, baseEnd_959646] using wordTrace_append hprefix tailTrace_959646
  have hstable : (prefixWord ++ tailWord_959646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959646).length < 2 ^ (prefixWord ++ tailWord_959646).sum := by decide
  have hdescent : baseEnd_959646 < baseStart_959646 := by decide
  rcases family_descends (prefixWord ++ tailWord_959646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959674 : List Nat := [3, 1, 1, 1, 2, 2, 1, 5, 3, 3]
def baseStart_959674 : Nat := 118140960795 + 959674 * 2 ^ 59
def prefixEnd_959674 : Nat := 4983230072969 + 3 ^ 40 * 959674 * 2
def baseEnd_959674 : Nat := 328516022415322336507697

theorem tailTrace_959674 : CollatzResearch.WordTrace tailWord_959674 prefixEnd_959674 328516022415322336507697 := by
  unfold tailWord_959674
  simp only [CollatzResearch.WordTrace]
  refine ⟨8750546581318118028905519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23334790883514981410414717 8750546581318118028905519)
  ·
    refine ⟨13125819871977177043358279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8750546581318118028905519 13125819871977177043358279)
    ·
      refine ⟨19688729807965765565037419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13125819871977177043358279 19688729807965765565037419)
      ·
        refine ⟨29533094711948648347556129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19688729807965765565037419 29533094711948648347556129)
        ·
          refine ⟨22149821033961486260667097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29533094711948648347556129 22149821033961486260667097)
          ·
            refine ⟨16612365775471114695500323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22149821033961486260667097 16612365775471114695500323)
            ·
              refine ⟨24918548663206672043250485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16612365775471114695500323 24918548663206672043250485)
              ·
                refine ⟨2336113937175625504054733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24918548663206672043250485 2336113937175625504054733)
                ·
                  refine ⟨876042726440859564020525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2336113937175625504054733 876042726440859564020525)
                  ·
                    refine ⟨328516022415322336507697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 876042726440859564020525 328516022415322336507697)
                    ·
                      rfl

theorem cell22_959674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 3, 3].length) (baseStart_959674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_959674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_959674 prefixEnd_959674 := by exact prefixLift 959674
  have htrace : WordTrace (prefixWord ++ tailWord_959674) baseStart_959674 baseEnd_959674 := by
    simpa [prefixWord, tailWord_959674, baseEnd_959674] using wordTrace_append hprefix tailTrace_959674
  have hstable : (prefixWord ++ tailWord_959674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959674).length < 2 ^ (prefixWord ++ tailWord_959674).sum := by decide
  have hdescent : baseEnd_959674 < baseStart_959674 := by decide
  rcases family_descends (prefixWord ++ tailWord_959674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959779 : List Nat := [1, 1, 1, 4, 2, 3, 1, 1, 4, 4]
def baseStart_959779 : Nat := 118140960795 + 959779 * 2 ^ 59
def prefixEnd_959779 : Nat := 4983230072969 + 3 ^ 40 * 959779 * 2
def baseEnd_959779 : Nat := 328551966061137062632375

theorem tailTrace_959779 : CollatzResearch.WordTrace tailWord_959779 prefixEnd_959779 328551966061137062632375 := by
  unfold tailWord_959779
  simp only [CollatzResearch.WordTrace]
  refine ⟨35006015989892075048194391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23337343993261383365462927 35006015989892075048194391)
  ·
    refine ⟨52509023984838112572291587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35006015989892075048194391 52509023984838112572291587)
    ·
      refine ⟨78763535977257168858437381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52509023984838112572291587 78763535977257168858437381)
      ·
        refine ⟨14768162995735719160957009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78763535977257168858437381 14768162995735719160957009)
        ·
          refine ⟨11076122246801789370717757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14768162995735719160957009 11076122246801789370717757)
          ·
            refine ⟨4153545842550671014019159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11076122246801789370717757 4153545842550671014019159)
            ·
              refine ⟨6230318763826006521028739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4153545842550671014019159 6230318763826006521028739)
              ·
                refine ⟨9345478145739009781543109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6230318763826006521028739 9345478145739009781543109)
                ·
                  refine ⟨1752277152326064334039333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9345478145739009781543109 1752277152326064334039333)
                  ·
                    refine ⟨328551966061137062632375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1752277152326064334039333 328551966061137062632375)
                    ·
                      rfl

theorem cell22_959779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 4, 4].length) (baseStart_959779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_959779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_959779 prefixEnd_959779 := by exact prefixLift 959779
  have htrace : WordTrace (prefixWord ++ tailWord_959779) baseStart_959779 baseEnd_959779 := by
    simpa [prefixWord, tailWord_959779, baseEnd_959779] using wordTrace_append hprefix tailTrace_959779
  have hstable : (prefixWord ++ tailWord_959779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959779).length < 2 ^ (prefixWord ++ tailWord_959779).sum := by decide
  have hdescent : baseEnd_959779 < baseStart_959779 := by decide
  rcases family_descends (prefixWord ++ tailWord_959779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959781 : List Nat := [1, 3, 1, 2, 4, 1, 2, 1, 4, 3]
def baseStart_959781 : Nat := 118140960795 + 959781 * 2 ^ 59
def prefixEnd_959781 : Nat := 4983230072969 + 3 ^ 40 * 959781 * 2
def baseEnd_959781 : Nat := 328552650702009724082369

theorem tailTrace_959781 : CollatzResearch.WordTrace tailWord_959781 prefixEnd_959781 328552650702009724082369 := by
  unfold tailWord_959781
  simp only [CollatzResearch.WordTrace]
  refine ⟨35006088935884829389767197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23337392623923219593178131 35006088935884829389767197)
  ·
    refine ⟨13127283350956811021162699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35006088935884829389767197 13127283350956811021162699)
    ·
      refine ⟨19690925026435216531744049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13127283350956811021162699 19690925026435216531744049)
      ·
        refine ⟨14768193769826412398808037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19690925026435216531744049 14768193769826412398808037)
        ·
          refine ⟨2769036331842452324776507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14768193769826412398808037 2769036331842452324776507)
          ·
            refine ⟨4153554497763678487164761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2769036331842452324776507 4153554497763678487164761)
            ·
              refine ⟨3115165873322758865373571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4153554497763678487164761 3115165873322758865373571)
              ·
                refine ⟨4672748809984138298060357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3115165873322758865373571 4672748809984138298060357)
                ·
                  refine ⟨876140401872025930886317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4672748809984138298060357 876140401872025930886317)
                  ·
                    refine ⟨328552650702009724082369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 876140401872025930886317 328552650702009724082369)
                    ·
                      rfl

theorem cell22_959781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 4, 3].length) (baseStart_959781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_959781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_959781 prefixEnd_959781 := by exact prefixLift 959781
  have htrace : WordTrace (prefixWord ++ tailWord_959781) baseStart_959781 baseEnd_959781 := by
    simpa [prefixWord, tailWord_959781, baseEnd_959781] using wordTrace_append hprefix tailTrace_959781
  have hstable : (prefixWord ++ tailWord_959781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959781).length < 2 ^ (prefixWord ++ tailWord_959781).sum := by decide
  have hdescent : baseEnd_959781 < baseStart_959781 := by decide
  rcases family_descends (prefixWord ++ tailWord_959781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959794 : List Nat := [3, 2, 1, 1, 4, 1, 1, 9]
def baseStart_959794 : Nat := 118140960795 + 959794 * 2 ^ 59
def prefixEnd_959794 : Nat := 4983230072969 + 3 ^ 40 * 959794 * 2
def baseEnd_959794 : Nat := 36506344540853558167481

theorem tailTrace_959794 : CollatzResearch.WordTrace tailWord_959794 prefixEnd_959794 36506344540853558167481 := by
  unfold tailWord_959794
  simp only [CollatzResearch.WordTrace]
  refine ⟨8751640771209433152497609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23337708723225155073326957 8751640771209433152497609)
  ·
    refine ⟨6563730578407074864373207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8751640771209433152497609 6563730578407074864373207)
    ·
      refine ⟨9845595867610612296559811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6563730578407074864373207 9845595867610612296559811)
      ·
        refine ⟨14768393801415918444839717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9845595867610612296559811 14768393801415918444839717)
        ·
          refine ⟨2769073837765484708407447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14768393801415918444839717 2769073837765484708407447)
          ·
            refine ⟨4153610756648227062611171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2769073837765484708407447 4153610756648227062611171)
            ·
              refine ⟨6230416134972340593916757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4153610756648227062611171 6230416134972340593916757)
              ·
                refine ⟨36506344540853558167481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6230416134972340593916757 36506344540853558167481)
                ·
                  rfl

theorem cell22_959794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 9].length) (baseStart_959794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_959794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_959794 prefixEnd_959794 := by exact prefixLift 959794
  have htrace : WordTrace (prefixWord ++ tailWord_959794) baseStart_959794 baseEnd_959794 := by
    simpa [prefixWord, tailWord_959794, baseEnd_959794] using wordTrace_append hprefix tailTrace_959794
  have hstable : (prefixWord ++ tailWord_959794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959794).length < 2 ^ (prefixWord ++ tailWord_959794).sum := by decide
  have hdescent : baseEnd_959794 < baseStart_959794 := by decide
  rcases family_descends (prefixWord ++ tailWord_959794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959796 : List Nat := [2, 5, 1, 1, 1, 1, 1, 2, 4, 4]
def baseStart_959796 : Nat := 118140960795 + 959796 * 2 ^ 59
def prefixEnd_959796 : Nat := 4983230072969 + 3 ^ 40 * 959796 * 2
def baseEnd_959796 : Nat := 328557785508554684957323

theorem tailTrace_959796 : CollatzResearch.WordTrace tailWord_959796 prefixEnd_959796 328557785508554684957323 := by
  unfold tailWord_959796
  simp only [CollatzResearch.WordTrace]
  refine ⟨17503318015415243475781621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23337757353886991301042161 17503318015415243475781621)
  ·
    refine ⟨1640936063945179075854527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17503318015415243475781621 1640936063945179075854527)
    ·
      refine ⟨2461404095917768613781791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1640936063945179075854527 2461404095917768613781791)
      ·
        refine ⟨3692106143876652920672687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2461404095917768613781791 3692106143876652920672687)
        ·
          refine ⟨5538159215814979381009031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3692106143876652920672687 5538159215814979381009031)
          ·
            refine ⟨8307238823722469071513547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5538159215814979381009031 8307238823722469071513547)
            ·
              refine ⟨12460858235583703607270321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8307238823722469071513547 12460858235583703607270321)
              ·
                refine ⟨9345643676687777705452741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12460858235583703607270321 9345643676687777705452741)
                ·
                  refine ⟨1752308189378958319772389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9345643676687777705452741 1752308189378958319772389)
                  ·
                    refine ⟨328557785508554684957323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1752308189378958319772389 328557785508554684957323)
                    ·
                      rfl

theorem cell22_959796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_959796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_959796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_959796 prefixEnd_959796 := by exact prefixLift 959796
  have htrace : WordTrace (prefixWord ++ tailWord_959796) baseStart_959796 baseEnd_959796 := by
    simpa [prefixWord, tailWord_959796, baseEnd_959796] using wordTrace_append hprefix tailTrace_959796
  have hstable : (prefixWord ++ tailWord_959796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959796).length < 2 ^ (prefixWord ++ tailWord_959796).sum := by decide
  have hdescent : baseEnd_959796 < baseStart_959796 := by decide
  rcases family_descends (prefixWord ++ tailWord_959796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959884 : List Nat := [2, 2, 1, 2, 1, 3, 1, 2, 8]
def baseStart_959884 : Nat := 118140960795 + 959884 * 2 ^ 59
def prefixEnd_959884 : Nat := 4983230072969 + 3 ^ 40 * 959884 * 2
def baseEnd_959884 : Nat := 109529303235650596252351

theorem tailTrace_959884 : CollatzResearch.WordTrace tailWord_959884 prefixEnd_959884 109529303235650596252351 := by
  unfold tailWord_959884
  simp only [CollatzResearch.WordTrace]
  refine ⟨17504922827255838990383353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23339897103007785320511137 17504922827255838990383353)
  ·
    refine ⟨13128692120441879242787515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17504922827255838990383353 13128692120441879242787515)
    ·
      refine ⟨19693038180662818864181273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13128692120441879242787515 19693038180662818864181273)
      ·
        refine ⟨14769778635497114148135955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19693038180662818864181273 14769778635497114148135955)
        ·
          refine ⟨22154667953245671222203933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14769778635497114148135955 22154667953245671222203933)
          ·
            refine ⟨8308000482467126708326475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22154667953245671222203933 8308000482467126708326475)
            ·
              refine ⟨12462000723700690062489713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8308000482467126708326475 12462000723700690062489713)
              ·
                refine ⟨9346500542775517546867285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12462000723700690062489713 9346500542775517546867285)
                ·
                  refine ⟨109529303235650596252351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9346500542775517546867285 109529303235650596252351)
                  ·
                    rfl

theorem cell22_959884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 8].length) (baseStart_959884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_959884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_959884 prefixEnd_959884 := by exact prefixLift 959884
  have htrace : WordTrace (prefixWord ++ tailWord_959884) baseStart_959884 baseEnd_959884 := by
    simpa [prefixWord, tailWord_959884, baseEnd_959884] using wordTrace_append hprefix tailTrace_959884
  have hstable : (prefixWord ++ tailWord_959884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959884).length < 2 ^ (prefixWord ++ tailWord_959884).sum := by decide
  have hdescent : baseEnd_959884 < baseStart_959884 := by decide
  rcases family_descends (prefixWord ++ tailWord_959884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959901 : List Nat := [1, 4, 2, 1, 3, 1, 1, 3, 6]
def baseStart_959901 : Nat := 118140960795 + 959901 * 2 ^ 59
def prefixEnd_959901 : Nat := 4983230072969 + 3 ^ 40 * 959901 * 2
def baseEnd_959901 : Nat := 109531243051456470360667

theorem tailTrace_959901 : CollatzResearch.WordTrace tailWord_959901 prefixEnd_959901 109531243051456470360667 := by
  unfold tailWord_959901
  simp only [CollatzResearch.WordTrace]
  refine ⟨35010465695450089884135557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23340310463633393256090371 35010465695450089884135557)
  ·
    refine ⟨6564462317896891853275417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35010465695450089884135557 6564462317896891853275417)
    ·
      refine ⟨4923346738422668889956563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6564462317896891853275417 4923346738422668889956563)
      ·
        refine ⟨7385020107634003334934845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4923346738422668889956563 7385020107634003334934845)
        ·
          refine ⟨2769382540362751250600567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7385020107634003334934845 2769382540362751250600567)
          ·
            refine ⟨4154073810544126875900851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2769382540362751250600567 4154073810544126875900851)
            ·
              refine ⟨6231110715816190313851277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4154073810544126875900851 6231110715816190313851277)
              ·
                refine ⟨2336666518431071367694229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6231110715816190313851277 2336666518431071367694229)
                ·
                  refine ⟨109531243051456470360667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2336666518431071367694229 109531243051456470360667)
                  ·
                    rfl

theorem cell22_959901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 6].length) (baseStart_959901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_959901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_959901 prefixEnd_959901 := by exact prefixLift 959901
  have htrace : WordTrace (prefixWord ++ tailWord_959901) baseStart_959901 baseEnd_959901 := by
    simpa [prefixWord, tailWord_959901, baseEnd_959901] using wordTrace_append hprefix tailTrace_959901
  have hstable : (prefixWord ++ tailWord_959901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959901).length < 2 ^ (prefixWord ++ tailWord_959901).sum := by decide
  have hdescent : baseEnd_959901 < baseStart_959901 := by decide
  rcases family_descends (prefixWord ++ tailWord_959901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959916 : List Nat := [2, 2, 1, 1, 1, 1, 7, 1, 1, 5]
def baseStart_959916 : Nat := 118140960795 + 959916 * 2 ^ 59
def prefixEnd_959916 : Nat := 4983230072969 + 3 ^ 40 * 959916 * 2
def baseEnd_959916 : Nat := 328598863960914371956955

theorem tailTrace_959916 : CollatzResearch.WordTrace tailWord_959916 prefixEnd_959916 328598863960914371956955 := by
  unfold tailWord_959916
  simp only [CollatzResearch.WordTrace]
  refine ⟨17505506395197873722965801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23340675193597164963954401 17505506395197873722965801)
  ·
    refine ⟨13129129796398405292224351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17505506395197873722965801 13129129796398405292224351)
    ·
      refine ⟨19693694694597607938336527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13129129796398405292224351 19693694694597607938336527)
      ·
        refine ⟨29540542041896411907504791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19693694694597607938336527 29540542041896411907504791)
        ·
          refine ⟨44310813062844617861257187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29540542041896411907504791 44310813062844617861257187)
          ·
            refine ⟨66466219594266926791885781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44310813062844617861257187 66466219594266926791885781)
            ·
              refine ⟨1557802021740631096684823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 66466219594266926791885781 1557802021740631096684823)
              ·
                refine ⟨2336703032610946645027235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1557802021740631096684823 2336703032610946645027235)
                ·
                  refine ⟨3505054548916419967540853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2336703032610946645027235 3505054548916419967540853)
                  ·
                    refine ⟨328598863960914371956955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3505054548916419967540853 328598863960914371956955)
                    ·
                      rfl

theorem cell22_959916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 5].length) (baseStart_959916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_959916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_959916 prefixEnd_959916 := by exact prefixLift 959916
  have htrace : WordTrace (prefixWord ++ tailWord_959916) baseStart_959916 baseEnd_959916 := by
    simpa [prefixWord, tailWord_959916, baseEnd_959916] using wordTrace_append hprefix tailTrace_959916
  have hstable : (prefixWord ++ tailWord_959916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959916).length < 2 ^ (prefixWord ++ tailWord_959916).sum := by decide
  have hdescent : baseEnd_959916 < baseStart_959916 := by decide
  rcases family_descends (prefixWord ++ tailWord_959916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959946 : List Nat := [3, 1, 2, 1, 2, 5, 8]
def baseStart_959946 : Nat := 118140960795 + 959946 * 2 ^ 59
def prefixEnd_959946 : Nat := 4983230072969 + 3 ^ 40 * 959946 * 2
def baseEnd_959946 : Nat := 12170708650889047915069

theorem tailTrace_959946 : CollatzResearch.WordTrace tailWord_959946 prefixEnd_959946 12170708650889047915069 := by
  unfold tailWord_959946
  simp only [CollatzResearch.WordTrace]
  refine ⟨8753026745071765642380923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23341404653524708379682461 8753026745071765642380923)
  ·
    refine ⟨13129540117607648463571385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8753026745071765642380923 13129540117607648463571385)
    ·
      refine ⟨9847155088205736347678539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13129540117607648463571385 9847155088205736347678539)
      ·
        refine ⟨14770732632308604521517809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9847155088205736347678539 14770732632308604521517809)
        ·
          refine ⟨11078049474231453391138357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14770732632308604521517809 11078049474231453391138357)
          ·
            refine ⟨1038567138209198755419221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11078049474231453391138357 1038567138209198755419221)
            ·
              refine ⟨12170708650889047915069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1038567138209198755419221 12170708650889047915069)
              ·
                rfl

theorem cell22_959946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 8].length) (baseStart_959946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_959946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_959946 prefixEnd_959946 := by exact prefixLift 959946
  have htrace : WordTrace (prefixWord ++ tailWord_959946) baseStart_959946 baseEnd_959946 := by
    simpa [prefixWord, tailWord_959946, baseEnd_959946] using wordTrace_append hprefix tailTrace_959946
  have hstable : (prefixWord ++ tailWord_959946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959946).length < 2 ^ (prefixWord ++ tailWord_959946).sum := by decide
  have hdescent : baseEnd_959946 < baseStart_959946 := by decide
  rcases family_descends (prefixWord ++ tailWord_959946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_959948 : List Nat := [2, 2, 1, 4, 2, 2, 1, 2, 2, 4]
def baseStart_959948 : Nat := 118140960795 + 959948 * 2 ^ 59
def prefixEnd_959948 : Nat := 4983230072969 + 3 ^ 40 * 959948 * 2
def baseEnd_959948 : Nat := 328609818214876955156857

theorem tailTrace_959948 : CollatzResearch.WordTrace tailWord_959948 prefixEnd_959948 328609818214876955156857 := by
  unfold tailWord_959948
  simp only [CollatzResearch.WordTrace]
  refine ⟨17506089963139908455548249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23341453284186544607397665 17506089963139908455548249)
  ·
    refine ⟨13129567472354931341661187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17506089963139908455548249 13129567472354931341661187)
    ·
      refine ⟨19694351208532397012491781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13129567472354931341661187 19694351208532397012491781)
      ·
        refine ⟨3692690851599824439842209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19694351208532397012491781 3692690851599824439842209)
        ·
          refine ⟨2769518138699868329881657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3692690851599824439842209 2769518138699868329881657)
          ·
            refine ⟨2077138604024901247411243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2769518138699868329881657 2077138604024901247411243)
            ·
              refine ⟨3115707906037351871116865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2077138604024901247411243 3115707906037351871116865)
              ·
                refine ⟨2336780929528013903337649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3115707906037351871116865 2336780929528013903337649)
                ·
                  refine ⟨1752585697146010427503237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2336780929528013903337649 1752585697146010427503237)
                  ·
                    refine ⟨328609818214876955156857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1752585697146010427503237 328609818214876955156857)
                    ·
                      rfl

theorem cell22_959948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 2, 4].length) (baseStart_959948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_959948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_959948 prefixEnd_959948 := by exact prefixLift 959948
  have htrace : WordTrace (prefixWord ++ tailWord_959948) baseStart_959948 baseEnd_959948 := by
    simpa [prefixWord, tailWord_959948, baseEnd_959948] using wordTrace_append hprefix tailTrace_959948
  have hstable : (prefixWord ++ tailWord_959948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_959948).length < 2 ^ (prefixWord ++ tailWord_959948).sum := by decide
  have hdescent : baseEnd_959948 < baseStart_959948 := by decide
  rcases family_descends (prefixWord ++ tailWord_959948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
