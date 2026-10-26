import V185TrunkScan23Chunk0452

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2680260 : List Nat := [2, 3, 3, 2, 1, 1, 2, 1, 4, 2, 2]
def baseStart_2680260 : Nat := 118140960795 + 2680260 * 2 ^ 59
def prefixEnd_2680260 : Nat := 4983230072969 + 3 ^ 40 * 2680260 * 2
def baseEnd_2680260 : Nat := 1376261659019788704123715

theorem tailTrace_2680260 : CollatzResearch.WordTrace tailWord_2680260 prefixEnd_2680260 1376261659019788704123715 := by
  unfold tailWord_2680260
  simp only [CollatzResearch.WordTrace]
  refine ⟨48878556634941623404807117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65171408846588831206409489 48878556634941623404807117)
  ·
    refine ⟨18329458738103108776802669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48878556634941623404807117 18329458738103108776802669)
    ·
      refine ⟨6873547026788665791301001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18329458738103108776802669 6873547026788665791301001)
      ·
        refine ⟨5155160270091499343475751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6873547026788665791301001 5155160270091499343475751)
        ·
          refine ⟨7732740405137249015213627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5155160270091499343475751 7732740405137249015213627)
          ·
            refine ⟨11599110607705873522820441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7732740405137249015213627 11599110607705873522820441)
            ·
              refine ⟨8699332955779405142115331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11599110607705873522820441 8699332955779405142115331)
              ·
                refine ⟨13048999433669107713172997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8699332955779405142115331 13048999433669107713172997)
                ·
                  refine ⟨2446687393812957696219937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13048999433669107713172997 2446687393812957696219937)
                  ·
                    refine ⟨1835015545359718272164953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2446687393812957696219937 1835015545359718272164953)
                    ·
                      refine ⟨1376261659019788704123715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1835015545359718272164953 1376261659019788704123715)
                      ·
                        rfl

theorem cell23_2680260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_2680260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2680260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2680260 prefixEnd_2680260 := by exact prefixLift 2680260
  have htrace : WordTrace (prefixWord ++ tailWord_2680260) baseStart_2680260 baseEnd_2680260 := by
    simpa [prefixWord, tailWord_2680260, baseEnd_2680260] using wordTrace_append hprefix tailTrace_2680260
  have hstable : (prefixWord ++ tailWord_2680260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680260).length < 2 ^ (prefixWord ++ tailWord_2680260).sum := by decide
  have hdescent : baseEnd_2680260 < baseStart_2680260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680266 : List Nat := [3, 1, 2, 1, 2, 5, 1, 1, 7]
def baseStart_2680266 : Nat := 118140960795 + 2680266 * 2 ^ 59
def prefixEnd_2680266 : Nat := 4983230072969 + 3 ^ 40 * 2680266 * 2
def baseEnd_2680266 : Nat := 152918304433746186738743

theorem tailTrace_2680266 : CollatzResearch.WordTrace tailWord_2680266 prefixEnd_2680266 152918304433746186738743 := by
  unfold tailWord_2680266
  simp only [CollatzResearch.WordTrace]
  refine ⟨24439333026965377458583163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65171554738574339889555101 24439333026965377458583163)
  ·
    refine ⟨36658999540448066187874745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24439333026965377458583163 36658999540448066187874745)
    ·
      refine ⟨27494249655336049640906059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36658999540448066187874745 27494249655336049640906059)
      ·
        refine ⟨41241374483004074461359089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27494249655336049640906059 41241374483004074461359089)
        ·
          refine ⟨30931030862253055846019317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41241374483004074461359089 30931030862253055846019317)
          ·
            refine ⟨2899784143336223985564311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30931030862253055846019317 2899784143336223985564311)
            ·
              refine ⟨4349676215004335978346467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2899784143336223985564311 4349676215004335978346467)
              ·
                refine ⟨6524514322506503967519701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4349676215004335978346467 6524514322506503967519701)
                ·
                  refine ⟨152918304433746186738743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6524514322506503967519701 152918304433746186738743)
                  ·
                    rfl

theorem cell23_2680266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 7].length) (baseStart_2680266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2680266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2680266 prefixEnd_2680266 := by exact prefixLift 2680266
  have htrace : WordTrace (prefixWord ++ tailWord_2680266) baseStart_2680266 baseEnd_2680266 := by
    simpa [prefixWord, tailWord_2680266, baseEnd_2680266] using wordTrace_append hprefix tailTrace_2680266
  have hstable : (prefixWord ++ tailWord_2680266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680266).length < 2 ^ (prefixWord ++ tailWord_2680266).sum := by decide
  have hdescent : baseEnd_2680266 < baseStart_2680266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680296 : List Nat := [2, 1, 4, 1, 1, 2, 4, 1, 2, 5]
def baseStart_2680296 : Nat := 118140960795 + 2680296 * 2 ^ 59
def prefixEnd_2680296 : Nat := 4983230072969 + 3 ^ 40 * 2680296 * 2
def baseEnd_2680296 : Nat := 458760048107783521091183

theorem tailTrace_2680296 : CollatzResearch.WordTrace tailWord_2680296 prefixEnd_2680296 458760048107783521091183 := by
  unfold tailWord_2680296
  simp only [CollatzResearch.WordTrace]
  refine ⟨48879213148876412478962371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65172284198501883305283161 48879213148876412478962371)
  ·
    refine ⟨73318819723314618718443557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48879213148876412478962371 73318819723314618718443557)
    ·
      refine ⟨13747278698121491009708167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73318819723314618718443557 13747278698121491009708167)
      ·
        refine ⟨20620918047182236514562251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13747278698121491009708167 20620918047182236514562251)
        ·
          refine ⟨30931377070773354771843377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20620918047182236514562251 30931377070773354771843377)
          ·
            refine ⟨23198532803080016078882533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30931377070773354771843377 23198532803080016078882533)
            ·
              refine ⟨4349724900577503014790475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23198532803080016078882533 4349724900577503014790475)
              ·
                refine ⟨6524587350866254522185713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4349724900577503014790475 6524587350866254522185713)
                ·
                  refine ⟨4893440513149690891639285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6524587350866254522185713 4893440513149690891639285)
                  ·
                    refine ⟨458760048107783521091183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4893440513149690891639285 458760048107783521091183)
                    ·
                      rfl

theorem cell23_2680296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_2680296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2680296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2680296 prefixEnd_2680296 := by exact prefixLift 2680296
  have htrace : WordTrace (prefixWord ++ tailWord_2680296) baseStart_2680296 baseEnd_2680296 := by
    simpa [prefixWord, tailWord_2680296, baseEnd_2680296] using wordTrace_append hprefix tailTrace_2680296
  have hstable : (prefixWord ++ tailWord_2680296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680296).length < 2 ^ (prefixWord ++ tailWord_2680296).sum := by decide
  have hdescent : baseEnd_2680296 < baseStart_2680296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680306 : List Nat := [3, 2, 1, 4, 1, 1, 1, 2, 1, 2, 5]
def baseStart_2680306 : Nat := 118140960795 + 2680306 * 2 ^ 59
def prefixEnd_2680306 : Nat := 4983230072969 + 3 ^ 40 * 2680306 * 2
def baseEnd_2680306 : Nat := 1376285279129895524148503

theorem tailTrace_2680306 : CollatzResearch.WordTrace tailWord_2680306 prefixEnd_2680306 1376285279129895524148503 := by
  unfold tailWord_2680306
  simp only [CollatzResearch.WordTrace]
  refine ⟨24439697756929149166447193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65172527351811064443859181 24439697756929149166447193)
  ·
    refine ⟨18329773317696861874835395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24439697756929149166447193 18329773317696861874835395)
    ·
      refine ⟨27494659976545292812253093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18329773317696861874835395 27494659976545292812253093)
      ·
        refine ⟨5155248745602242402297455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27494659976545292812253093 5155248745602242402297455)
        ·
          refine ⟨7732873118403363603446183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5155248745602242402297455 7732873118403363603446183)
          ·
            refine ⟨11599309677605045405169275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7732873118403363603446183 11599309677605045405169275)
            ·
              refine ⟨17398964516407568107753913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11599309677605045405169275 17398964516407568107753913)
              ·
                refine ⟨13049223387305676080815435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17398964516407568107753913 13049223387305676080815435)
                ·
                  refine ⟨19573835080958514121223153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13049223387305676080815435 19573835080958514121223153)
                  ·
                    refine ⟨14680376310718885590917365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19573835080958514121223153 14680376310718885590917365)
                    ·
                      refine ⟨1376285279129895524148503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14680376310718885590917365 1376285279129895524148503)
                      ·
                        rfl

theorem cell23_2680306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_2680306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2680306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2680306 prefixEnd_2680306 := by exact prefixLift 2680306
  have htrace : WordTrace (prefixWord ++ tailWord_2680306) baseStart_2680306 baseEnd_2680306 := by
    simpa [prefixWord, tailWord_2680306, baseEnd_2680306] using wordTrace_append hprefix tailTrace_2680306
  have hstable : (prefixWord ++ tailWord_2680306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680306).length < 2 ^ (prefixWord ++ tailWord_2680306).sum := by decide
  have hdescent : baseEnd_2680306 < baseStart_2680306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680316 : List Nat := [2, 2, 2, 1, 2, 1, 4, 2, 2, 1, 4]
def baseStart_2680316 : Nat := 118140960795 + 2680316 * 2 ^ 59
def prefixEnd_2680316 : Nat := 4983230072969 + 3 ^ 40 * 2680316 * 2
def baseEnd_2680316 : Nat := 1376290413936440485023457

theorem tailTrace_2680316 : CollatzResearch.WordTrace tailWord_2680316 prefixEnd_2680316 1376290413936440485023457 := by
  unfold tailWord_2680316
  simp only [CollatzResearch.WordTrace]
  refine ⟨48879577878840184186826401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65172770505120245582435201 48879577878840184186826401)
  ·
    refine ⟨36659683409130138140119801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48879577878840184186826401 36659683409130138140119801)
    ·
      refine ⟨27494762556847603605089851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36659683409130138140119801 27494762556847603605089851)
      ·
        refine ⟨41242143835271405407634777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27494762556847603605089851 41242143835271405407634777)
        ·
          refine ⟨30931607876453554055726083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41242143835271405407634777 30931607876453554055726083)
          ·
            refine ⟨46397411814680331083589125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30931607876453554055726083 46397411814680331083589125)
            ·
              refine ⟨8699514715252562078172961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46397411814680331083589125 8699514715252562078172961)
              ·
                refine ⟨6524636036439421558629721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8699514715252562078172961 6524636036439421558629721)
                ·
                  refine ⟨4893477027329566168972291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6524636036439421558629721 4893477027329566168972291)
                  ·
                    refine ⟨7340215540994349253458437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4893477027329566168972291 7340215540994349253458437)
                    ·
                      refine ⟨1376290413936440485023457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7340215540994349253458437 1376290413936440485023457)
                      ·
                        rfl

theorem cell23_2680316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_2680316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2680316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2680316 prefixEnd_2680316 := by exact prefixLift 2680316
  have htrace : WordTrace (prefixWord ++ tailWord_2680316) baseStart_2680316 baseEnd_2680316 := by
    simpa [prefixWord, tailWord_2680316, baseEnd_2680316] using wordTrace_append hprefix tailTrace_2680316
  have hstable : (prefixWord ++ tailWord_2680316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680316).length < 2 ^ (prefixWord ++ tailWord_2680316).sum := by decide
  have hdescent : baseEnd_2680316 < baseStart_2680316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680353 : List Nat := [1, 2, 3, 2, 2, 2, 3, 1, 2, 2, 3]
def baseStart_2680353 : Nat := 118140960795 + 2680353 * 2 ^ 59
def prefixEnd_2680353 : Nat := 4983230072969 + 3 ^ 40 * 2680353 * 2
def baseEnd_2680353 : Nat := 1376309412720656840260787

theorem tailTrace_2680353 : CollatzResearch.WordTrace tailWord_2680353 prefixEnd_2680353 1376309412720656840260787 := by
  unfold tailWord_2680353
  simp only [CollatzResearch.WordTrace]
  refine ⟨97760505258546323692749713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65173670172364215795166475 97760505258546323692749713)
  ·
    refine ⟨73320378943909742769562285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97760505258546323692749713 73320378943909742769562285)
    ·
      refine ⟨27495142103966153538585857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73320378943909742769562285 27495142103966153538585857)
      ·
        refine ⟨20621356577974615153939393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27495142103966153538585857 20621356577974615153939393)
        ·
          refine ⟨15466017433480961365454545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20621356577974615153939393 15466017433480961365454545)
          ·
            refine ⟨11599513075110721024090909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15466017433480961365454545 11599513075110721024090909)
            ·
              refine ⟨4349817403166520384034091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11599513075110721024090909 4349817403166520384034091)
              ·
                refine ⟨6524726104749780576051137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4349817403166520384034091 6524726104749780576051137)
                ·
                  refine ⟨4893544578562335432038353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6524726104749780576051137 4893544578562335432038353)
                  ·
                    refine ⟨3670158433921751574028765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4893544578562335432038353 3670158433921751574028765)
                    ·
                      refine ⟨1376309412720656840260787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3670158433921751574028765 1376309412720656840260787)
                      ·
                        rfl

theorem cell23_2680353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_2680353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2680353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2680353 prefixEnd_2680353 := by exact prefixLift 2680353
  have htrace : WordTrace (prefixWord ++ tailWord_2680353) baseStart_2680353 baseEnd_2680353 := by
    simpa [prefixWord, tailWord_2680353, baseEnd_2680353] using wordTrace_append hprefix tailTrace_2680353
  have hstable : (prefixWord ++ tailWord_2680353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680353).length < 2 ^ (prefixWord ++ tailWord_2680353).sum := by decide
  have hdescent : baseEnd_2680353 < baseStart_2680353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680373 : List Nat := [1, 3, 3, 1, 1, 5, 1, 2, 6]
def baseStart_2680373 : Nat := 118140960795 + 2680373 * 2 ^ 59
def prefixEnd_2680373 : Nat := 4983230072969 + 3 ^ 40 * 2680373 * 2
def baseEnd_2680373 : Nat := 152924409148194084667855

theorem tailTrace_2680373 : CollatzResearch.WordTrace tailWord_2680373 prefixEnd_2680373 152924409148194084667855 := by
  unfold tailWord_2680373
  simp only [CollatzResearch.WordTrace]
  refine ⟨97761234718473867108477773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65174156478982578072318515 97761234718473867108477773)
  ·
    refine ⟨36660463019427700165679165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97761234718473867108477773 36660463019427700165679165)
    ·
      refine ⟨13747673632285387562129687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36660463019427700165679165 13747673632285387562129687)
      ·
        refine ⟨20621510448428081343194531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13747673632285387562129687 20621510448428081343194531)
        ·
          refine ⟨30932265672642122014791797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20621510448428081343194531 30932265672642122014791797)
          ·
            refine ⟨2899899906810198938886731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30932265672642122014791797 2899899906810198938886731)
            ·
              refine ⟨4349849860215298408330097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2899899906810198938886731 4349849860215298408330097)
              ·
                refine ⟨3262387395161473806247573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4349849860215298408330097 3262387395161473806247573)
                ·
                  refine ⟨152924409148194084667855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3262387395161473806247573 152924409148194084667855)
                  ·
                    rfl

theorem cell23_2680373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 2, 6].length) (baseStart_2680373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2680373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2680373 prefixEnd_2680373 := by exact prefixLift 2680373
  have htrace : WordTrace (prefixWord ++ tailWord_2680373) baseStart_2680373 baseEnd_2680373 := by
    simpa [prefixWord, tailWord_2680373, baseEnd_2680373] using wordTrace_append hprefix tailTrace_2680373
  have hstable : (prefixWord ++ tailWord_2680373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680373).length < 2 ^ (prefixWord ++ tailWord_2680373).sum := by decide
  have hdescent : baseEnd_2680373 < baseStart_2680373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680383 : List Nat := [1, 1, 2, 2, 3, 3, 1, 3, 3, 1, 3]
def baseStart_2680383 : Nat := 118140960795 + 2680383 * 2 ^ 59
def prefixEnd_2680383 : Nat := 4983230072969 + 3 ^ 40 * 2680383 * 2
def baseEnd_2680383 : Nat := 1376324817140291722885649

theorem tailTrace_2680383 : CollatzResearch.WordTrace tailWord_2680383 prefixEnd_2680383 1376324817140291722885649 := by
  unfold tailWord_2680383
  simp only [CollatzResearch.WordTrace]
  refine ⟨97761599448437638816341803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65174399632291759210894535 97761599448437638816341803)
  ·
    refine ⟨146642399172656458224512705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97761599448437638816341803 146642399172656458224512705)
    ·
      refine ⟨109981799379492343668384529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146642399172656458224512705 109981799379492343668384529)
      ·
        refine ⟨82486349534619257751288397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109981799379492343668384529 82486349534619257751288397)
        ·
          refine ⟨30932381075482221656733149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82486349534619257751288397 30932381075482221656733149)
          ·
            refine ⟨11599642903305833121274931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30932381075482221656733149 11599642903305833121274931)
            ·
              refine ⟨17399464354958749681912397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11599642903305833121274931 17399464354958749681912397)
              ·
                refine ⟨6524799133109531130717149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17399464354958749681912397 6524799133109531130717149)
                ·
                  refine ⟨2446799674916074174018931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6524799133109531130717149 2446799674916074174018931)
                  ·
                    refine ⟨3670199512374111261028397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2446799674916074174018931 3670199512374111261028397)
                    ·
                      refine ⟨1376324817140291722885649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3670199512374111261028397 1376324817140291722885649)
                      ·
                        rfl

theorem cell23_2680383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 3, 1, 3].length) (baseStart_2680383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2680383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2680383 prefixEnd_2680383 := by exact prefixLift 2680383
  have htrace : WordTrace (prefixWord ++ tailWord_2680383) baseStart_2680383 baseEnd_2680383 := by
    simpa [prefixWord, tailWord_2680383, baseEnd_2680383] using wordTrace_append hprefix tailTrace_2680383
  have hstable : (prefixWord ++ tailWord_2680383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680383).length < 2 ^ (prefixWord ++ tailWord_2680383).sum := by decide
  have hdescent : baseEnd_2680383 < baseStart_2680383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680423 : List Nat := [1, 1, 5, 1, 1, 1, 4, 3, 1, 1, 4]
def baseStart_2680423 : Nat := 118140960795 + 2680423 * 2 ^ 59
def prefixEnd_2680423 : Nat := 4983230072969 + 3 ^ 40 * 2680423 * 2
def baseEnd_2680423 : Nat := 1376345356366471566385465

theorem tailTrace_2680423 : CollatzResearch.WordTrace tailWord_2680423 prefixEnd_2680423 1376345356366471566385465 := by
  unfold tailWord_2680423
  simp only [CollatzResearch.WordTrace]
  refine ⟨97763058368292725647797923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65175372245528483765198615 97763058368292725647797923)
  ·
    refine ⟨146644587552439088471696885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97763058368292725647797923 146644587552439088471696885)
    ·
      refine ⟨13747930083041164544221583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 146644587552439088471696885 13747930083041164544221583)
      ·
        refine ⟨20621895124561746816332375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13747930083041164544221583 20621895124561746816332375)
        ·
          refine ⟨30932842686842620224498563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20621895124561746816332375 30932842686842620224498563)
          ·
            refine ⟨46399264030263930336747845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30932842686842620224498563 46399264030263930336747845)
            ·
              refine ⟨8699862005674486938140221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46399264030263930336747845 8699862005674486938140221)
              ·
                refine ⟨3262448252127932601802583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8699862005674486938140221 3262448252127932601802583)
                ·
                  refine ⟨4893672378191898902703875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3262448252127932601802583 4893672378191898902703875)
                  ·
                    refine ⟨7340508567287848354055813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4893672378191898902703875 7340508567287848354055813)
                    ·
                      refine ⟨1376345356366471566385465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7340508567287848354055813 1376345356366471566385465)
                      ·
                        rfl

theorem cell23_2680423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_2680423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2680423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2680423 prefixEnd_2680423 := by exact prefixLift 2680423
  have htrace : WordTrace (prefixWord ++ tailWord_2680423) baseStart_2680423 baseEnd_2680423 := by
    simpa [prefixWord, tailWord_2680423, baseEnd_2680423] using wordTrace_append hprefix tailTrace_2680423
  have hstable : (prefixWord ++ tailWord_2680423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680423).length < 2 ^ (prefixWord ++ tailWord_2680423).sum := by decide
  have hdescent : baseEnd_2680423 < baseStart_2680423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680434 : List Nat := [3, 2, 1, 2, 3, 2, 3, 2, 1, 1, 3]
def baseStart_2680434 : Nat := 118140960795 + 2680434 * 2 ^ 59
def prefixEnd_2680434 : Nat := 4983230072969 + 3 ^ 40 * 2680434 * 2
def baseEnd_2680434 : Nat := 1376351004653671023347915

theorem tailTrace_2680434 : CollatzResearch.WordTrace tailWord_2680434 prefixEnd_2680434 1376351004653671023347915 := by
  unfold tailWord_2680434
  simp only [CollatzResearch.WordTrace]
  refine ⟨24440864892813218631612089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65175639714168583017632237 24440864892813218631612089)
  ·
    refine ⟨18330648669609913973709067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24440864892813218631612089 18330648669609913973709067)
    ·
      refine ⟨27495973004414870960563601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18330648669609913973709067 27495973004414870960563601)
      ·
        refine ⟨20621979753311153220422701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27495973004414870960563601 20621979753311153220422701)
        ·
          refine ⟨7733242407491682457658513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20621979753311153220422701 7733242407491682457658513)
          ·
            refine ⟨5799931805618761843243885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7733242407491682457658513 5799931805618761843243885)
            ·
              refine ⟨2174974427107035691216457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5799931805618761843243885 2174974427107035691216457)
              ·
                refine ⟨1631230820330276768412343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2174974427107035691216457 1631230820330276768412343)
                ·
                  refine ⟨2446846230495415152618515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1631230820330276768412343 2446846230495415152618515)
                  ·
                    refine ⟨3670269345743122728927773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2446846230495415152618515 3670269345743122728927773)
                    ·
                      refine ⟨1376351004653671023347915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3670269345743122728927773 1376351004653671023347915)
                      ·
                        rfl

theorem cell23_2680434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 2, 1, 1, 3].length) (baseStart_2680434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2680434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2680434 prefixEnd_2680434 := by exact prefixLift 2680434
  have htrace : WordTrace (prefixWord ++ tailWord_2680434) baseStart_2680434 baseEnd_2680434 := by
    simpa [prefixWord, tailWord_2680434, baseEnd_2680434] using wordTrace_append hprefix tailTrace_2680434
  have hstable : (prefixWord ++ tailWord_2680434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680434).length < 2 ^ (prefixWord ++ tailWord_2680434).sum := by decide
  have hdescent : baseEnd_2680434 < baseStart_2680434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680473 : List Nat := [1, 2, 1, 2, 1, 2, 2, 4, 4, 1, 3]
def baseStart_2680473 : Nat := 118140960795 + 2680473 * 2 ^ 59
def prefixEnd_2680473 : Nat := 4983230072969 + 3 ^ 40 * 2680473 * 2
def baseEnd_2680473 : Nat := 1376371030399196370760235

theorem tailTrace_2680473 : CollatzResearch.WordTrace tailWord_2680473 prefixEnd_2680473 1376371030399196370760235 := by
  unfold tailWord_2680473
  simp only [CollatzResearch.WordTrace]
  refine ⟨97764882018111584187118073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65176588012074389458078715 97764882018111584187118073)
  ·
    refine ⟨73323661513583688140338555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97764882018111584187118073 73323661513583688140338555)
    ·
      refine ⟨109985492270375532210507833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73323661513583688140338555 109985492270375532210507833)
      ·
        refine ⟨82489119202781649157880875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109985492270375532210507833 82489119202781649157880875)
        ·
          refine ⟨123733678804172473736821313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82489119202781649157880875 123733678804172473736821313)
          ·
            refine ⟨92800259103129355302615985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123733678804172473736821313 92800259103129355302615985)
            ·
              refine ⟨69600194327347016476961989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92800259103129355302615985 69600194327347016476961989)
              ·
                refine ⟨13050036436377565589430373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69600194327347016476961989 13050036436377565589430373)
                ·
                  refine ⟨2446881831820793548018195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13050036436377565589430373 2446881831820793548018195)
                  ·
                    refine ⟨3670322747731190322027293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2446881831820793548018195 3670322747731190322027293)
                    ·
                      refine ⟨1376371030399196370760235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3670322747731190322027293 1376371030399196370760235)
                      ·
                        rfl

theorem cell23_2680473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 4, 1, 3].length) (baseStart_2680473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2680473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2680473 prefixEnd_2680473 := by exact prefixLift 2680473
  have htrace : WordTrace (prefixWord ++ tailWord_2680473) baseStart_2680473 baseEnd_2680473 := by
    simpa [prefixWord, tailWord_2680473, baseEnd_2680473] using wordTrace_append hprefix tailTrace_2680473
  have hstable : (prefixWord ++ tailWord_2680473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680473).length < 2 ^ (prefixWord ++ tailWord_2680473).sum := by decide
  have hdescent : baseEnd_2680473 < baseStart_2680473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680496 : List Nat := [2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 4]
def baseStart_2680496 : Nat := 118140960795 + 2680496 * 2 ^ 59
def prefixEnd_2680496 : Nat := 4983230072969 + 3 ^ 40 * 2680496 * 2
def baseEnd_2680496 : Nat := 1376382840454249780772629

theorem tailTrace_2680496 : CollatzResearch.WordTrace tailWord_2680496 prefixEnd_2680496 1376382840454249780772629 := by
  unfold tailWord_2680496
  simp only [CollatzResearch.WordTrace]
  refine ⟨48882860448514129557602671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65177147264685506076803561 48882860448514129557602671)
  ·
    refine ⟨73324290672771194336404007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48882860448514129557602671 73324290672771194336404007)
    ·
      refine ⟨109986436009156791504606011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73324290672771194336404007 109986436009156791504606011)
      ·
        refine ⟨164979654013735187256909017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109986436009156791504606011 164979654013735187256909017)
        ·
          refine ⟨123734740510301390442681763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164979654013735187256909017 123734740510301390442681763)
          ·
            refine ⟨185602110765452085664022645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123734740510301390442681763 185602110765452085664022645)
            ·
              refine ⟨17400197884261133031002123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 185602110765452085664022645 17400197884261133031002123)
              ·
                refine ⟨26100296826391699546503185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17400197884261133031002123 26100296826391699546503185)
                ·
                  refine ⟨19575222619793774659877389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26100296826391699546503185 19575222619793774659877389)
                  ·
                    refine ⟨7340708482422665497454021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19575222619793774659877389 7340708482422665497454021)
                    ·
                      refine ⟨1376382840454249780772629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7340708482422665497454021 1376382840454249780772629)
                      ·
                        rfl

theorem cell23_2680496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 4].length) (baseStart_2680496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2680496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2680496 prefixEnd_2680496 := by exact prefixLift 2680496
  have htrace : WordTrace (prefixWord ++ tailWord_2680496) baseStart_2680496 baseEnd_2680496 := by
    simpa [prefixWord, tailWord_2680496, baseEnd_2680496] using wordTrace_append hprefix tailTrace_2680496
  have hstable : (prefixWord ++ tailWord_2680496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680496).length < 2 ^ (prefixWord ++ tailWord_2680496).sum := by decide
  have hdescent : baseEnd_2680496 < baseStart_2680496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680506 : List Nat := [3, 1, 1, 1, 2, 4, 1, 1, 1, 8]
def baseStart_2680506 : Nat := 118140960795 + 2680506 * 2 ^ 59
def prefixEnd_2680506 : Nat := 4983230072969 + 3 ^ 40 * 2680506 * 2
def baseEnd_2680506 : Nat := 458795991753598247215861

theorem tailTrace_2680506 : CollatzResearch.WordTrace tailWord_2680506 prefixEnd_2680506 458795991753598247215861 := by
  unfold tailWord_2680506
  simp only [CollatzResearch.WordTrace]
  refine ⟨24441521406748007705767343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65177390417994687215379581 24441521406748007705767343)
  ·
    refine ⟨36662282110122011558651015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24441521406748007705767343 36662282110122011558651015)
    ·
      refine ⟨54993423165183017337976523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36662282110122011558651015 54993423165183017337976523)
      ·
        refine ⟨82490134747774526006964785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54993423165183017337976523 82490134747774526006964785)
        ·
          refine ⟨61867601060830894505223589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82490134747774526006964785 61867601060830894505223589)
          ·
            refine ⟨11600175198905792719729423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61867601060830894505223589 11600175198905792719729423)
            ·
              refine ⟨17400262798358689079594135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11600175198905792719729423 17400262798358689079594135)
              ·
                refine ⟨26100394197538033619391203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17400262798358689079594135 26100394197538033619391203)
                ·
                  refine ⟨39150591296307050429086805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26100394197538033619391203 39150591296307050429086805)
                  ·
                    refine ⟨458795991753598247215861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 39150591296307050429086805 458795991753598247215861)
                    ·
                      rfl

theorem cell23_2680506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 1, 8].length) (baseStart_2680506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2680506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2680506 prefixEnd_2680506 := by exact prefixLift 2680506
  have htrace : WordTrace (prefixWord ++ tailWord_2680506) baseStart_2680506 baseEnd_2680506 := by
    simpa [prefixWord, tailWord_2680506, baseEnd_2680506] using wordTrace_append hprefix tailTrace_2680506
  have hstable : (prefixWord ++ tailWord_2680506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680506).length < 2 ^ (prefixWord ++ tailWord_2680506).sum := by decide
  have hdescent : baseEnd_2680506 < baseStart_2680506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680514 : List Nat := [3, 5, 1, 2, 1, 1, 3, 7]
def baseStart_2680514 : Nat := 118140960795 + 2680514 * 2 ^ 59
def prefixEnd_2680514 : Nat := 4983230072969 + 3 ^ 40 * 2680514 * 2
def baseEnd_2680514 : Nat := 50977484559482618901761

theorem tailTrace_2680514 : CollatzResearch.WordTrace tailWord_2680514 prefixEnd_2680514 50977484559482618901761 := by
  unfold tailWord_2680514
  simp only [CollatzResearch.WordTrace]
  refine ⟨24441594352740762047340149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65177584940642032126240397 24441594352740762047340149)
  ·
    refine ⟨2291399470569446441938139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24441594352740762047340149 2291399470569446441938139)
    ·
      refine ⟨3437099205854169662907209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2291399470569446441938139 3437099205854169662907209)
      ·
        refine ⟨2577824404390627247180407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3437099205854169662907209 2577824404390627247180407)
        ·
          refine ⟨3866736606585940870770611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2577824404390627247180407 3866736606585940870770611)
          ·
            refine ⟨5800104909878911306155917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3866736606585940870770611 5800104909878911306155917)
            ·
              refine ⟨2175039341204591739808469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5800104909878911306155917 2175039341204591739808469)
              ·
                refine ⟨50977484559482618901761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2175039341204591739808469 50977484559482618901761)
                ·
                  rfl

theorem cell23_2680514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 7].length) (baseStart_2680514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2680514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2680514 prefixEnd_2680514 := by exact prefixLift 2680514
  have htrace : WordTrace (prefixWord ++ tailWord_2680514) baseStart_2680514 baseEnd_2680514 := by
    simpa [prefixWord, tailWord_2680514, baseEnd_2680514] using wordTrace_append hprefix tailTrace_2680514
  have hstable : (prefixWord ++ tailWord_2680514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680514).length < 2 ^ (prefixWord ++ tailWord_2680514).sum := by decide
  have hdescent : baseEnd_2680514 < baseStart_2680514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680536 : List Nat := [2, 1, 2, 2, 3, 1, 1, 2, 9]
def baseStart_2680536 : Nat := 118140960795 + 2680536 * 2 ^ 59
def prefixEnd_2680536 : Nat := 4983230072969 + 3 ^ 40 * 2680536 * 2
def baseEnd_2680536 : Nat := 152933708853381069363605

theorem tailTrace_2680536 : CollatzResearch.WordTrace tailWord_2680536 prefixEnd_2680536 152933708853381069363605 := by
  unfold tailWord_2680536
  simp only [CollatzResearch.WordTrace]
  refine ⟨48883589908441672973330731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65178119877922230631107641 48883589908441672973330731)
  ·
    refine ⟨73325384862662509459996097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48883589908441672973330731 73325384862662509459996097)
    ·
      refine ⟨54994038646996882094997073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73325384862662509459996097 54994038646996882094997073)
      ·
        refine ⟨41245528985247661571247805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54994038646996882094997073 41245528985247661571247805)
        ·
          refine ⟨15467073369467873089217927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41245528985247661571247805 15467073369467873089217927)
          ·
            refine ⟨23200610054201809633826891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15467073369467873089217927 23200610054201809633826891)
            ·
              refine ⟨34800915081302714450740337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23200610054201809633826891 34800915081302714450740337)
              ·
                refine ⟨26100686310977035838055253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34800915081302714450740337 26100686310977035838055253)
                ·
                  refine ⟨152933708853381069363605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 26100686310977035838055253 152933708853381069363605)
                  ·
                    rfl

theorem cell23_2680536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 9].length) (baseStart_2680536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2680536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2680536 prefixEnd_2680536 := by exact prefixLift 2680536
  have htrace : WordTrace (prefixWord ++ tailWord_2680536) baseStart_2680536 baseEnd_2680536 := by
    simpa [prefixWord, tailWord_2680536, baseEnd_2680536] using wordTrace_append hprefix tailTrace_2680536
  have hstable : (prefixWord ++ tailWord_2680536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680536).length < 2 ^ (prefixWord ++ tailWord_2680536).sum := by decide
  have hdescent : baseEnd_2680536 < baseStart_2680536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680541 : List Nat := [1, 4, 3, 3, 1, 2, 1, 2, 2, 1, 3]
def baseStart_2680541 : Nat := 118140960795 + 2680541 * 2 ^ 59
def prefixEnd_2680541 : Nat := 4983230072969 + 3 ^ 40 * 2680541 * 2
def baseEnd_2680541 : Nat := 1376405947083702104709923

theorem tailTrace_2680541 : CollatzResearch.WordTrace tailWord_2680541 prefixEnd_2680541 1376405947083702104709923 := by
  unfold tailWord_2680541
  simp only [CollatzResearch.WordTrace]
  refine ⟨97767362181865231800593477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65178241454576821200395651 97767362181865231800593477)
  ·
    refine ⟨18331380409099730962611277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97767362181865231800593477 18331380409099730962611277)
    ·
      refine ⟨6874267653412399110979229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18331380409099730962611277 6874267653412399110979229)
      ·
        refine ⟨2577850370029649666617211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6874267653412399110979229 2577850370029649666617211)
        ·
          refine ⟨3866775555044474499925817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2577850370029649666617211 3866775555044474499925817)
          ·
            refine ⟨2900081666283355874944363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3866775555044474499925817 2900081666283355874944363)
            ·
              refine ⟨4350122499425033812416545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2900081666283355874944363 4350122499425033812416545)
              ·
                refine ⟨3262591874568775359312409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4350122499425033812416545 3262591874568775359312409)
                ·
                  refine ⟨2446943905926581519484307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3262591874568775359312409 2446943905926581519484307)
                  ·
                    refine ⟨3670415858889872279226461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2446943905926581519484307 3670415858889872279226461)
                    ·
                      refine ⟨1376405947083702104709923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3670415858889872279226461 1376405947083702104709923)
                      ·
                        rfl

theorem cell23_2680541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_2680541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2680541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2680541 prefixEnd_2680541 := by exact prefixLift 2680541
  have htrace : WordTrace (prefixWord ++ tailWord_2680541) baseStart_2680541 baseEnd_2680541 := by
    simpa [prefixWord, tailWord_2680541, baseEnd_2680541] using wordTrace_append hprefix tailTrace_2680541
  have hstable : (prefixWord ++ tailWord_2680541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680541).length < 2 ^ (prefixWord ++ tailWord_2680541).sum := by decide
  have hdescent : baseEnd_2680541 < baseStart_2680541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680563 : List Nat := [1, 1, 1, 2, 2, 3, 4, 1, 2, 3, 3]
def baseStart_2680563 : Nat := 118140960795 + 2680563 * 2 ^ 59
def prefixEnd_2680563 : Nat := 4983230072969 + 3 ^ 40 * 2680563 * 2
def baseEnd_2680563 : Nat := 1376417243658101018634821

theorem tailTrace_2680563 : CollatzResearch.WordTrace tailWord_2680563 prefixEnd_2680563 1376417243658101018634821 := by
  unfold tailWord_2680563
  simp only [CollatzResearch.WordTrace]
  refine ⟨97768164587785529557894343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65178776391857019705262895 97768164587785529557894343)
  ·
    refine ⟨146652246881678294336841515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97768164587785529557894343 146652246881678294336841515)
    ·
      refine ⟨219978370322517441505262273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146652246881678294336841515 219978370322517441505262273)
      ·
        refine ⟨164983777741888081128946705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219978370322517441505262273 164983777741888081128946705)
        ·
          refine ⟨123737833306416060846710029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164983777741888081128946705 123737833306416060846710029)
          ·
            refine ⟨46401687489906022817516261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123737833306416060846710029 46401687489906022817516261)
            ·
              refine ⟨8700316404357379278284299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46401687489906022817516261 8700316404357379278284299)
              ·
                refine ⟨13050474606536068917426449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8700316404357379278284299 13050474606536068917426449)
                ·
                  refine ⟨9787855954902051688069837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13050474606536068917426449 9787855954902051688069837)
                  ·
                    refine ⟨3670445983088269383026189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9787855954902051688069837 3670445983088269383026189)
                    ·
                      refine ⟨1376417243658101018634821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3670445983088269383026189 1376417243658101018634821)
                      ·
                        rfl

theorem cell23_2680563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 3, 3].length) (baseStart_2680563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2680563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2680563 prefixEnd_2680563 := by exact prefixLift 2680563
  have htrace : WordTrace (prefixWord ++ tailWord_2680563) baseStart_2680563 baseEnd_2680563 := by
    simpa [prefixWord, tailWord_2680563, baseEnd_2680563] using wordTrace_append hprefix tailTrace_2680563
  have hstable : (prefixWord ++ tailWord_2680563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680563).length < 2 ^ (prefixWord ++ tailWord_2680563).sum := by decide
  have hdescent : baseEnd_2680563 < baseStart_2680563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680576 : List Nat := [2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 7]
def baseStart_2680576 : Nat := 118140960795 + 2680576 * 2 ^ 59
def prefixEnd_2680576 : Nat := 4983230072969 + 3 ^ 40 * 2680576 * 2
def baseEnd_2680576 : Nat := 1376423918906609467772261

theorem tailTrace_2680576 : CollatzResearch.WordTrace tailWord_2680576 prefixEnd_2680576 1376423918906609467772261 := by
  unfold tailWord_2680576
  simp only [CollatzResearch.WordTrace]
  refine ⟨48884319368369216389058791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65179092491158955185411721 48884319368369216389058791)
  ·
    refine ⟨73326479052553824583588187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48884319368369216389058791 73326479052553824583588187)
    ·
      refine ⟨109989718578830736875382281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73326479052553824583588187 109989718578830736875382281)
      ·
        refine ⟨82492288934123052656536711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109989718578830736875382281 82492288934123052656536711)
        ·
          refine ⟨123738433401184578984805067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82492288934123052656536711 123738433401184578984805067)
          ·
            refine ⟨185607650101776868477207601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123738433401184578984805067 185607650101776868477207601)
            ·
              refine ⟨139205737576332651357905701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185607650101776868477207601 139205737576332651357905701)
              ·
                refine ⟨26101075795562372129607319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 139205737576332651357905701 26101075795562372129607319)
                ·
                  refine ⟨39151613693343558194410979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26101075795562372129607319 39151613693343558194410979)
                  ·
                    refine ⟨58727420540015337291616469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39151613693343558194410979 58727420540015337291616469)
                    ·
                      refine ⟨1376423918906609467772261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 58727420540015337291616469 1376423918906609467772261)
                      ·
                        rfl

theorem cell23_2680576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 7].length) (baseStart_2680576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2680576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2680576 prefixEnd_2680576 := by exact prefixLift 2680576
  have htrace : WordTrace (prefixWord ++ tailWord_2680576) baseStart_2680576 baseEnd_2680576 := by
    simpa [prefixWord, tailWord_2680576, baseEnd_2680576] using wordTrace_append hprefix tailTrace_2680576
  have hstable : (prefixWord ++ tailWord_2680576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680576).length < 2 ^ (prefixWord ++ tailWord_2680576).sum := by decide
  have hdescent : baseEnd_2680576 < baseStart_2680576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680603 : List Nat := [1, 1, 1, 1, 1, 1, 4, 6, 2, 1, 4]
def baseStart_2680603 : Nat := 118140960795 + 2680603 * 2 ^ 59
def prefixEnd_2680603 : Nat := 4983230072969 + 3 ^ 40 * 2680603 * 2
def baseEnd_2680603 : Nat := 1376437782884280862134637

theorem tailTrace_2680603 : CollatzResearch.WordTrace tailWord_2680603 prefixEnd_2680603 1376437782884280862134637 := by
  unfold tailWord_2680603
  simp only [CollatzResearch.WordTrace]
  refine ⟨97769623507640616389350463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65179749005093744259566975 97769623507640616389350463)
  ·
    refine ⟨146654435261460924584025695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97769623507640616389350463 146654435261460924584025695)
    ·
      refine ⟨219981652892191386876038543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146654435261460924584025695 219981652892191386876038543)
      ·
        refine ⟨329972479338287080314057815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219981652892191386876038543 329972479338287080314057815)
        ·
          refine ⟨494958719007430620471086723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329972479338287080314057815 494958719007430620471086723)
          ·
            refine ⟨742438078511145930706630085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 494958719007430620471086723 742438078511145930706630085)
            ·
              refine ⟨139207139720839862007493141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 742438078511145930706630085 139207139720839862007493141)
              ·
                refine ⟨6525334674414368531601241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 139207139720839862007493141 6525334674414368531601241)
                ·
                  refine ⟨4894001005810776398700931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6525334674414368531601241 4894001005810776398700931)
                  ·
                    refine ⟨7341001508716164598051397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4894001005810776398700931 7341001508716164598051397)
                    ·
                      refine ⟨1376437782884280862134637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7341001508716164598051397 1376437782884280862134637)
                      ·
                        rfl

theorem cell23_2680603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 2, 1, 4].length) (baseStart_2680603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2680603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2680603 prefixEnd_2680603 := by exact prefixLift 2680603
  have htrace : WordTrace (prefixWord ++ tailWord_2680603) baseStart_2680603 baseEnd_2680603 := by
    simpa [prefixWord, tailWord_2680603, baseEnd_2680603] using wordTrace_append hprefix tailTrace_2680603
  have hstable : (prefixWord ++ tailWord_2680603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680603).length < 2 ^ (prefixWord ++ tailWord_2680603).sum := by decide
  have hdescent : baseEnd_2680603 < baseStart_2680603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680637 : List Nat := [1, 4, 1, 4, 1, 2, 2, 1, 2, 1, 4]
def baseStart_2680637 : Nat := 118140960795 + 2680637 * 2 ^ 59
def prefixEnd_2680637 : Nat := 4983230072969 + 3 ^ 40 * 2680637 * 2
def baseEnd_2680637 : Nat := 1376455241226533729109481

theorem tailTrace_2680637 : CollatzResearch.WordTrace tailWord_2680637 prefixEnd_2680637 1376455241226533729109481 := by
  unfold tailWord_2680637
  simp only [CollatzResearch.WordTrace]
  refine ⟨97770863589517440196088165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65180575726344960130725443 97770863589517440196088165)
  ·
    refine ⟨18332036923034520036766531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97770863589517440196088165 18332036923034520036766531)
    ·
      refine ⟨27498055384551780055149797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18332036923034520036766531 27498055384551780055149797)
      ·
        refine ⟨5155885384603458760340587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27498055384551780055149797 5155885384603458760340587)
        ·
          refine ⟨7733828076905188140510881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5155885384603458760340587 7733828076905188140510881)
          ·
            refine ⟨5800371057678891105383161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7733828076905188140510881 5800371057678891105383161)
            ·
              refine ⟨4350278293259168329037371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5800371057678891105383161 4350278293259168329037371)
              ·
                refine ⟨6525417439888752493556057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4350278293259168329037371 6525417439888752493556057)
                ·
                  refine ⟨4894063079916564370167043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6525417439888752493556057 4894063079916564370167043)
                  ·
                    refine ⟨7341094619874846555250565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4894063079916564370167043 7341094619874846555250565)
                    ·
                      refine ⟨1376455241226533729109481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7341094619874846555250565 1376455241226533729109481)
                      ·
                        rfl

theorem cell23_2680637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_2680637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2680637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2680637 prefixEnd_2680637 := by exact prefixLift 2680637
  have htrace : WordTrace (prefixWord ++ tailWord_2680637) baseStart_2680637 baseEnd_2680637 := by
    simpa [prefixWord, tailWord_2680637, baseEnd_2680637] using wordTrace_append hprefix tailTrace_2680637
  have hstable : (prefixWord ++ tailWord_2680637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680637).length < 2 ^ (prefixWord ++ tailWord_2680637).sum := by decide
  have hdescent : baseEnd_2680637 < baseStart_2680637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680660 : List Nat := [2, 4, 1, 1, 3, 1, 1, 4, 6]
def baseStart_2680660 : Nat := 118140960795 + 2680660 * 2 ^ 59
def prefixEnd_2680660 : Nat := 4983230072969 + 3 ^ 40 * 2680660 * 2
def baseEnd_2680660 : Nat := 152940783475731904346875

theorem tailTrace_2680660 : CollatzResearch.WordTrace tailWord_2680660 prefixEnd_2680660 152940783475731904346875 := by
  unfold tailWord_2680660
  simp only [CollatzResearch.WordTrace]
  refine ⟨48885851234217057562087717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65181134978956076749450289 48885851234217057562087717)
  ·
    refine ⟨9166097106415698292891447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48885851234217057562087717 9166097106415698292891447)
    ·
      refine ⟨13749145659623547439337171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9166097106415698292891447 13749145659623547439337171)
      ·
        refine ⟨20623718489435321159005757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13749145659623547439337171 20623718489435321159005757)
        ·
          refine ⟨7733894433538245434627159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20623718489435321159005757 7733894433538245434627159)
          ·
            refine ⟨11600841650307368151940739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7733894433538245434627159 11600841650307368151940739)
            ·
              refine ⟨17401262475461052227911109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11600841650307368151940739 17401262475461052227911109)
              ·
                refine ⟨3262736714148947292733333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17401262475461052227911109 3262736714148947292733333)
                ·
                  refine ⟨152940783475731904346875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3262736714148947292733333 152940783475731904346875)
                  ·
                    rfl

theorem cell23_2680660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 4, 6].length) (baseStart_2680660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2680660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2680660 prefixEnd_2680660 := by exact prefixLift 2680660
  have htrace : WordTrace (prefixWord ++ tailWord_2680660) baseStart_2680660 baseEnd_2680660 := by
    simpa [prefixWord, tailWord_2680660, baseEnd_2680660] using wordTrace_append hprefix tailTrace_2680660
  have hstable : (prefixWord ++ tailWord_2680660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680660).length < 2 ^ (prefixWord ++ tailWord_2680660).sum := by decide
  have hdescent : baseEnd_2680660 < baseStart_2680660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680673 : List Nat := [1, 2, 3, 1, 1, 1, 3, 1, 5, 5]
def baseStart_2680673 : Nat := 118140960795 + 2680673 * 2 ^ 59
def prefixEnd_2680673 : Nat := 4983230072969 + 3 ^ 40 * 2680673 * 2
def baseEnd_2680673 : Nat := 458824575510031862753105

theorem tailTrace_2680673 : CollatzResearch.WordTrace tailWord_2680673 prefixEnd_2680673 458824575510031862753105 := by
  unfold tailWord_2680673
  simp only [CollatzResearch.WordTrace]
  refine ⟨97772176617387018344398673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65181451078258012229599115 97772176617387018344398673)
  ·
    refine ⟨73329132463040263758299005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97772176617387018344398673 73329132463040263758299005)
    ·
      refine ⟨27498424673640098909362127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73329132463040263758299005 27498424673640098909362127)
      ·
        refine ⟨41247637010460148364043191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27498424673640098909362127 41247637010460148364043191)
        ·
          refine ⟨61871455515690222546064787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41247637010460148364043191 61871455515690222546064787)
          ·
            refine ⟨92807183273535333819097181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61871455515690222546064787 92807183273535333819097181)
            ·
              refine ⟨34802693727575750182161443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92807183273535333819097181 34802693727575750182161443)
              ·
                refine ⟨52204040591363625273242165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34802693727575750182161443 52204040591363625273242165)
                ·
                  refine ⟨4894128805440339869366453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52204040591363625273242165 4894128805440339869366453)
                  ·
                    refine ⟨458824575510031862753105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4894128805440339869366453 458824575510031862753105)
                    ·
                      rfl

theorem cell23_2680673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 5, 5].length) (baseStart_2680673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2680673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2680673 prefixEnd_2680673 := by exact prefixLift 2680673
  have htrace : WordTrace (prefixWord ++ tailWord_2680673) baseStart_2680673 baseEnd_2680673 := by
    simpa [prefixWord, tailWord_2680673, baseEnd_2680673] using wordTrace_append hprefix tailTrace_2680673
  have hstable : (prefixWord ++ tailWord_2680673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680673).length < 2 ^ (prefixWord ++ tailWord_2680673).sum := by decide
  have hdescent : baseEnd_2680673 < baseStart_2680673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680690 : List Nat := [3, 2, 1, 2, 1, 1, 1, 6, 1, 5]
def baseStart_2680690 : Nat := 118140960795 + 2680690 * 2 ^ 59
def prefixEnd_2680690 : Nat := 4983230072969 + 3 ^ 40 * 2680690 * 2
def baseEnd_2680690 : Nat := 458827485233740673915579

theorem tailTrace_2680690 : CollatzResearch.WordTrace tailWord_2680690 prefixEnd_2680690 458827485233740673915579 := by
  unfold tailWord_2680690
  simp only [CollatzResearch.WordTrace]
  refine ⟨24443199164581357561941881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65181864438883620165178349 24443199164581357561941881)
  ·
    refine ⟨18332399373436018171456411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24443199164581357561941881 18332399373436018171456411)
    ·
      refine ⟨27498599060154027257184617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18332399373436018171456411 27498599060154027257184617)
      ·
        refine ⟨20623949295115520442888463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27498599060154027257184617 20623949295115520442888463)
        ·
          refine ⟨30935923942673280664332695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20623949295115520442888463 30935923942673280664332695)
          ·
            refine ⟨46403885914009920996499043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30935923942673280664332695 46403885914009920996499043)
            ·
              refine ⟨69605828871014881494748565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46403885914009920996499043 69605828871014881494748565)
              ·
                refine ⟨3262773228328822570066339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 69605828871014881494748565 3262773228328822570066339)
                ·
                  refine ⟨4894159842493233855099509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3262773228328822570066339 4894159842493233855099509)
                  ·
                    refine ⟨458827485233740673915579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4894159842493233855099509 458827485233740673915579)
                    ·
                      rfl

theorem cell23_2680690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 6, 1, 5].length) (baseStart_2680690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2680690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2680690 prefixEnd_2680690 := by exact prefixLift 2680690
  have htrace : WordTrace (prefixWord ++ tailWord_2680690) baseStart_2680690 baseEnd_2680690 := by
    simpa [prefixWord, tailWord_2680690, baseEnd_2680690] using wordTrace_append hprefix tailTrace_2680690
  have hstable : (prefixWord ++ tailWord_2680690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680690).length < 2 ^ (prefixWord ++ tailWord_2680690).sum := by decide
  have hdescent : baseEnd_2680690 < baseStart_2680690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680704 : List Nat := [2, 1, 1, 2, 1, 2, 6, 3, 1, 1, 3]
def baseStart_2680704 : Nat := 118140960795 + 2680704 * 2 ^ 59
def prefixEnd_2680704 : Nat := 4983230072969 + 3 ^ 40 * 2680704 * 2
def baseEnd_2680704 : Nat := 1376489644430384966971673

theorem tailTrace_2680704 : CollatzResearch.WordTrace tailWord_2680704 prefixEnd_2680704 1376489644430384966971673 := by
  unfold tailWord_2680704
  simp only [CollatzResearch.WordTrace]
  refine ⟨48886653640137355319388583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65182204853516473759184777 48886653640137355319388583)
  ·
    refine ⟨73329980460206032979082875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48886653640137355319388583 73329980460206032979082875)
    ·
      refine ⟨109994970690309049468624313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73329980460206032979082875 109994970690309049468624313)
      ·
        refine ⟨82496228017731787101468235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109994970690309049468624313 82496228017731787101468235)
        ·
          refine ⟨123744342026597680652202353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82496228017731787101468235 123744342026597680652202353)
          ·
            refine ⟨92808256519948260489151765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123744342026597680652202353 92808256519948260489151765)
            ·
              refine ⟨4350387024372574710428989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 92808256519948260489151765 4350387024372574710428989)
              ·
                refine ⟨1631395134139715516410871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4350387024372574710428989 1631395134139715516410871)
                ·
                  refine ⟨2447092701209573274616307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1631395134139715516410871 2447092701209573274616307)
                  ·
                    refine ⟨3670639051814359911924461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2447092701209573274616307 3670639051814359911924461)
                    ·
                      refine ⟨1376489644430384966971673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3670639051814359911924461 1376489644430384966971673)
                      ·
                        rfl

theorem cell23_2680704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 3, 1, 1, 3].length) (baseStart_2680704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2680704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2680704 prefixEnd_2680704 := by exact prefixLift 2680704
  have htrace : WordTrace (prefixWord ++ tailWord_2680704) baseStart_2680704 baseEnd_2680704 := by
    simpa [prefixWord, tailWord_2680704, baseEnd_2680704] using wordTrace_append hprefix tailTrace_2680704
  have hstable : (prefixWord ++ tailWord_2680704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680704).length < 2 ^ (prefixWord ++ tailWord_2680704).sum := by decide
  have hdescent : baseEnd_2680704 < baseStart_2680704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680707 : List Nat := [1, 1, 1, 3, 4, 2, 4, 1, 1, 5]
def baseStart_2680707 : Nat := 118140960795 + 2680707 * 2 ^ 59
def prefixEnd_2680707 : Nat := 4983230072969 + 3 ^ 40 * 2680707 * 2
def baseEnd_2680707 : Nat := 458830394957449485078053

theorem tailTrace_2680707 : CollatzResearch.WordTrace tailWord_2680707 prefixEnd_2680707 458830394957449485078053 := by
  unfold tailWord_2680707
  simp only [CollatzResearch.WordTrace]
  refine ⟨97773416699263842151136375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65182277799509228100757583 97773416699263842151136375)
  ·
    refine ⟨146660125048895763226704563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97773416699263842151136375 146660125048895763226704563)
    ·
      refine ⟨219990187573343644840056845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146660125048895763226704563 219990187573343644840056845)
      ·
        refine ⟨82496320340003866815021317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 219990187573343644840056845 82496320340003866815021317)
        ·
          refine ⟨15468060063750725027816497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82496320340003866815021317 15468060063750725027816497)
          ·
            refine ⟨11601045047813043770862373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15468060063750725027816497 11601045047813043770862373)
            ·
              refine ⟨2175195946464945707036695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11601045047813043770862373 2175195946464945707036695)
              ·
                refine ⟨3262793919697418560555043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2175195946464945707036695 3262793919697418560555043)
                ·
                  refine ⟨4894190879546127840832565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3262793919697418560555043 4894190879546127840832565)
                  ·
                    refine ⟨458830394957449485078053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4894190879546127840832565 458830394957449485078053)
                    ·
                      rfl

theorem cell23_2680707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 1, 1, 5].length) (baseStart_2680707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2680707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2680707 prefixEnd_2680707 := by exact prefixLift 2680707
  have htrace : WordTrace (prefixWord ++ tailWord_2680707) baseStart_2680707 baseEnd_2680707 := by
    simpa [prefixWord, tailWord_2680707, baseEnd_2680707] using wordTrace_append hprefix tailTrace_2680707
  have hstable : (prefixWord ++ tailWord_2680707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680707).length < 2 ^ (prefixWord ++ tailWord_2680707).sum := by decide
  have hdescent : baseEnd_2680707 < baseStart_2680707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680730 : List Nat := [3, 1, 1, 4, 2, 1, 1, 1, 3, 1, 5]
def baseStart_2680730 : Nat := 118140960795 + 2680730 * 2 ^ 59
def prefixEnd_2680730 : Nat := 4983230072969 + 3 ^ 40 * 2680730 * 2
def baseEnd_2680730 : Nat := 1376502994927401865246553

theorem tailTrace_2680730 : CollatzResearch.WordTrace tailWord_2680730 prefixEnd_2680730 1376502994927401865246553 := by
  unfold tailWord_2680730
  simp only [CollatzResearch.WordTrace]
  refine ⟨24443563894545129269805911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65182837052120344719482429 24443563894545129269805911)
  ·
    refine ⟨36665345841817693904708867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24443563894545129269805911 36665345841817693904708867)
    ·
      refine ⟨54998018762726540857063301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36665345841817693904708867 54998018762726540857063301)
      ·
        refine ⟨10312128518011226410699369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54998018762726540857063301 10312128518011226410699369)
        ·
          refine ⟨7734096388508419808024527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10312128518011226410699369 7734096388508419808024527)
          ·
            refine ⟨11601144582762629712036791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7734096388508419808024527 11601144582762629712036791)
            ·
              refine ⟨17401716874143944568055187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11601144582762629712036791 17401716874143944568055187)
              ·
                refine ⟨26102575311215916852082781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17401716874143944568055187 26102575311215916852082781)
                ·
                  refine ⟨9788465741705968819531043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26102575311215916852082781 9788465741705968819531043)
                  ·
                    refine ⟨14682698612558953229296565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9788465741705968819531043 14682698612558953229296565)
                    ·
                      refine ⟨1376502994927401865246553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14682698612558953229296565 1376502994927401865246553)
                      ·
                        rfl

theorem cell23_2680730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_2680730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2680730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2680730 prefixEnd_2680730 := by exact prefixLift 2680730
  have htrace : WordTrace (prefixWord ++ tailWord_2680730) baseStart_2680730 baseEnd_2680730 := by
    simpa [prefixWord, tailWord_2680730, baseEnd_2680730] using wordTrace_append hprefix tailTrace_2680730
  have hstable : (prefixWord ++ tailWord_2680730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680730).length < 2 ^ (prefixWord ++ tailWord_2680730).sum := by decide
  have hdescent : baseEnd_2680730 < baseStart_2680730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680740 : List Nat := [2, 3, 1, 2, 1, 4, 1, 1, 1, 1, 6]
def baseStart_2680740 : Nat := 118140960795 + 2680740 * 2 ^ 59
def prefixEnd_2680740 : Nat := 4983230072969 + 3 ^ 40 * 2680740 * 2
def baseEnd_2680740 : Nat := 1376508129733946826121507

theorem tailTrace_2680740 : CollatzResearch.WordTrace tailWord_2680740 prefixEnd_2680740 1376508129733946826121507 := by
  unfold tailWord_2680740
  simp only [CollatzResearch.WordTrace]
  refine ⟨48887310154072144393543837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65183080205429525858058449 48887310154072144393543837)
  ·
    refine ⟨18332741307777054147578939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48887310154072144393543837 18332741307777054147578939)
    ·
      refine ⟨27499111961665581221368409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18332741307777054147578939 27499111961665581221368409)
      ·
        refine ⟨20624333971249185916026307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27499111961665581221368409 20624333971249185916026307)
        ·
          refine ⟨30936500956873778874039461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20624333971249185916026307 30936500956873778874039461)
          ·
            refine ⟨5800593929413833538882399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30936500956873778874039461 5800593929413833538882399)
            ·
              refine ⟨8700890894120750308323599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5800593929413833538882399 8700890894120750308323599)
              ·
                refine ⟨13051336341181125462485399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8700890894120750308323599 13051336341181125462485399)
                ·
                  refine ⟨19577004511771688193728099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13051336341181125462485399 19577004511771688193728099)
                  ·
                    refine ⟨29365506767657532290592149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19577004511771688193728099 29365506767657532290592149)
                    ·
                      refine ⟨1376508129733946826121507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29365506767657532290592149 1376508129733946826121507)
                      ·
                        rfl

theorem cell23_2680740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_2680740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2680740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2680740 prefixEnd_2680740 := by exact prefixLift 2680740
  have htrace : WordTrace (prefixWord ++ tailWord_2680740) baseStart_2680740 baseEnd_2680740 := by
    simpa [prefixWord, tailWord_2680740, baseEnd_2680740] using wordTrace_append hprefix tailTrace_2680740
  have hstable : (prefixWord ++ tailWord_2680740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680740).length < 2 ^ (prefixWord ++ tailWord_2680740).sum := by decide
  have hdescent : baseEnd_2680740 < baseStart_2680740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680760 : List Nat := [2, 1, 2, 1, 2, 3, 2, 1, 3, 3, 3]
def baseStart_2680760 : Nat := 118140960795 + 2680760 * 2 ^ 59
def prefixEnd_2680760 : Nat := 4983230072969 + 3 ^ 40 * 2680760 * 2
def baseEnd_2680760 : Nat := 1376518399347036747871415

theorem tailTrace_2680760 : CollatzResearch.WordTrace tailWord_2680760 prefixEnd_2680760 1376518399347036747871415 := by
  unfold tailWord_2680760
  simp only [CollatzResearch.WordTrace]
  refine ⟨48887674884035916101407867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65183566512047888135210489 48887674884035916101407867)
  ·
    refine ⟨73331512326053874152111801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48887674884035916101407867 73331512326053874152111801)
    ·
      refine ⟨54998634244540405614083851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73331512326053874152111801 54998634244540405614083851)
      ·
        refine ⟨82497951366810608421125777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54998634244540405614083851 82497951366810608421125777)
        ·
          refine ⟨61873463525107956315844333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82497951366810608421125777 61873463525107956315844333)
          ·
            refine ⟨23202548821915483618441625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61873463525107956315844333 23202548821915483618441625)
            ·
              refine ⟨17401911616436612713831219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23202548821915483618441625 17401911616436612713831219)
              ·
                refine ⟨26102867424654919070746829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17401911616436612713831219 26102867424654919070746829)
                ·
                  refine ⟨9788575284245594651530061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26102867424654919070746829 9788575284245594651530061)
                  ·
                    refine ⟨3670715731592097994323773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9788575284245594651530061 3670715731592097994323773)
                    ·
                      refine ⟨1376518399347036747871415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3670715731592097994323773 1376518399347036747871415)
                      ·
                        rfl

theorem cell23_2680760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 3, 3, 3].length) (baseStart_2680760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2680760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2680760 prefixEnd_2680760 := by exact prefixLift 2680760
  have htrace : WordTrace (prefixWord ++ tailWord_2680760) baseStart_2680760 baseEnd_2680760 := by
    simpa [prefixWord, tailWord_2680760, baseEnd_2680760] using wordTrace_append hprefix tailTrace_2680760
  have hstable : (prefixWord ++ tailWord_2680760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680760).length < 2 ^ (prefixWord ++ tailWord_2680760).sum := by decide
  have hdescent : baseEnd_2680760 < baseStart_2680760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680764 : List Nat := [2, 2, 2, 5, 1, 1, 2, 1, 1, 1, 5]
def baseStart_2680764 : Nat := 118140960795 + 2680764 * 2 ^ 59
def prefixEnd_2680764 : Nat := 4983230072969 + 3 ^ 40 * 2680764 * 2
def baseEnd_2680764 : Nat := 1376520453269654732221397

theorem tailTrace_2680764 : CollatzResearch.WordTrace tailWord_2680764 prefixEnd_2680764 1376520453269654732221397 := by
  unfold tailWord_2680764
  simp only [CollatzResearch.WordTrace]
  refine ⟨48887747830028670442980673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65183663773371560590640897 48887747830028670442980673)
  ·
    refine ⟨36665810872521502832235505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48887747830028670442980673 36665810872521502832235505)
    ·
      refine ⟨27499358154391127124176629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36665810872521502832235505 27499358154391127124176629)
      ·
        refine ⟨2578064826974168167891559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27499358154391127124176629 2578064826974168167891559)
        ·
          refine ⟨3867097240461252251837339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2578064826974168167891559 3867097240461252251837339)
          ·
            refine ⟨5800645860691878377756009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3867097240461252251837339 5800645860691878377756009)
            ·
              refine ⟨4350484395518908783317007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5800645860691878377756009 4350484395518908783317007)
              ·
                refine ⟨6525726593278363174975511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4350484395518908783317007 6525726593278363174975511)
                ·
                  refine ⟨9788589889917544762463267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6525726593278363174975511 9788589889917544762463267)
                  ·
                    refine ⟨14682884834876317143694901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9788589889917544762463267 14682884834876317143694901)
                    ·
                      refine ⟨1376520453269654732221397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14682884834876317143694901 1376520453269654732221397)
                      ·
                        rfl

theorem cell23_2680764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_2680764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2680764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2680764 prefixEnd_2680764 := by exact prefixLift 2680764
  have htrace : WordTrace (prefixWord ++ tailWord_2680764) baseStart_2680764 baseEnd_2680764 := by
    simpa [prefixWord, tailWord_2680764, baseEnd_2680764] using wordTrace_append hprefix tailTrace_2680764
  have hstable : (prefixWord ++ tailWord_2680764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680764).length < 2 ^ (prefixWord ++ tailWord_2680764).sum := by decide
  have hdescent : baseEnd_2680764 < baseStart_2680764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680840 : List Nat := [2, 1, 3, 2, 1, 2, 2, 3, 7]
def baseStart_2680840 : Nat := 118140960795 + 2680840 * 2 ^ 59
def prefixEnd_2680840 : Nat := 4983230072969 + 3 ^ 40 * 2680840 * 2
def baseEnd_2680840 : Nat := 152951053088821826096783

theorem tailTrace_2680840 : CollatzResearch.WordTrace tailWord_2680840 prefixEnd_2680840 152951053088821826096783 := by
  unfold tailWord_2680840
  simp only [CollatzResearch.WordTrace]
  refine ⟨48889133803891002932863987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65185511738521337243818649 48889133803891002932863987)
  ·
    refine ⟨73333700705836504399295981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48889133803891002932863987 73333700705836504399295981)
    ·
      refine ⟨27500137764688689149735993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73333700705836504399295981 27500137764688689149735993)
      ·
        refine ⟨20625103323516516862301995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27500137764688689149735993 20625103323516516862301995)
        ·
          refine ⟨30937654985274775293452993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20625103323516516862301995 30937654985274775293452993)
          ·
            refine ⟨23203241238956081470089745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30937654985274775293452993 23203241238956081470089745)
            ·
              refine ⟨17402430929217061102567309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23203241238956081470089745 17402430929217061102567309)
              ·
                refine ⟨6525911598456397913462741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17402430929217061102567309 6525911598456397913462741)
                ·
                  refine ⟨152951053088821826096783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6525911598456397913462741 152951053088821826096783)
                  ·
                    rfl

theorem cell23_2680840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 7].length) (baseStart_2680840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2680840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2680840 prefixEnd_2680840 := by exact prefixLift 2680840
  have htrace : WordTrace (prefixWord ++ tailWord_2680840) baseStart_2680840 baseEnd_2680840 := by
    simpa [prefixWord, tailWord_2680840, baseEnd_2680840] using wordTrace_append hprefix tailTrace_2680840
  have hstable : (prefixWord ++ tailWord_2680840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680840).length < 2 ^ (prefixWord ++ tailWord_2680840).sum := by decide
  have hdescent : baseEnd_2680840 < baseStart_2680840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680872 : List Nat := [2, 1, 5, 3, 2, 1, 2, 1, 1, 3, 2]
def baseStart_2680872 : Nat := 118140960795 + 2680872 * 2 ^ 59
def prefixEnd_2680872 : Nat := 4983230072969 + 3 ^ 40 * 2680872 * 2
def baseEnd_2680872 : Nat := 1376575909180340309670901

theorem tailTrace_2680872 : CollatzResearch.WordTrace tailWord_2680872 prefixEnd_2680872 1376575909180340309670901 := by
  unfold tailWord_2680872
  simp only [CollatzResearch.WordTrace]
  refine ⟨48889717371833037665446435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65186289829110716887261913 48889717371833037665446435)
  ·
    refine ⟨73334576057749556498169653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48889717371833037665446435 73334576057749556498169653)
    ·
      refine ⟨6875116505414020921703405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73334576057749556498169653 6875116505414020921703405)
      ·
        refine ⟨2578168689530257845638777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6875116505414020921703405 2578168689530257845638777)
        ·
          refine ⟨1933626517147693384229083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2578168689530257845638777 1933626517147693384229083)
          ·
            refine ⟨2900439775721540076343625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1933626517147693384229083 2900439775721540076343625)
            ·
              refine ⟨2175329831791155057257719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2900439775721540076343625 2175329831791155057257719)
              ·
                refine ⟨3262994747686732585886579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2175329831791155057257719 3262994747686732585886579)
                ·
                  refine ⟨4894492121530098878829869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3262994747686732585886579 4894492121530098878829869)
                  ·
                    refine ⟨1835434545573787079561201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4894492121530098878829869 1835434545573787079561201)
                    ·
                      refine ⟨1376575909180340309670901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1835434545573787079561201 1376575909180340309670901)
                      ·
                        rfl

theorem cell23_2680872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_2680872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2680872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2680872 prefixEnd_2680872 := by exact prefixLift 2680872
  have htrace : WordTrace (prefixWord ++ tailWord_2680872) baseStart_2680872 baseEnd_2680872 := by
    simpa [prefixWord, tailWord_2680872, baseEnd_2680872] using wordTrace_append hprefix tailTrace_2680872
  have hstable : (prefixWord ++ tailWord_2680872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680872).length < 2 ^ (prefixWord ++ tailWord_2680872).sum := by decide
  have hdescent : baseEnd_2680872 < baseStart_2680872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680874 : List Nat := [3, 1, 4, 1, 2, 1, 1, 5, 5]
def baseStart_2680874 : Nat := 118140960795 + 2680874 * 2 ^ 59
def prefixEnd_2680874 : Nat := 4983230072969 + 3 ^ 40 * 2680874 * 2
def baseEnd_2680874 : Nat := 152952992904627700205099

theorem tailTrace_2680874 : CollatzResearch.WordTrace tailWord_2680874 prefixEnd_2680874 152952992904627700205099 := by
  unfold tailWord_2680874
  simp only [CollatzResearch.WordTrace]
  refine ⟨24444876922414707418116419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65186338459772553114977117 24444876922414707418116419)
  ·
    refine ⟨36667315383622061127174629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24444876922414707418116419 36667315383622061127174629)
    ·
      refine ⟨6875121634429136461345243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36667315383622061127174629 6875121634429136461345243)
      ·
        refine ⟨10312682451643704692017865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6875121634429136461345243 10312682451643704692017865)
        ·
          refine ⟨7734511838732778519013399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10312682451643704692017865 7734511838732778519013399)
          ·
            refine ⟨11601767758099167778520099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7734511838732778519013399 11601767758099167778520099)
            ·
              refine ⟨17402651637148751667780149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11601767758099167778520099 17402651637148751667780149)
              ·
                refine ⟨1631498590982695468854389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17402651637148751667780149 1631498590982695468854389)
                ·
                  refine ⟨152952992904627700205099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1631498590982695468854389 152952992904627700205099)
                  ·
                    rfl

theorem cell23_2680874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 5, 5].length) (baseStart_2680874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2680874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2680874 prefixEnd_2680874 := by exact prefixLift 2680874
  have htrace : WordTrace (prefixWord ++ tailWord_2680874) baseStart_2680874 baseEnd_2680874 := by
    simpa [prefixWord, tailWord_2680874, baseEnd_2680874] using wordTrace_append hprefix tailTrace_2680874
  have hstable : (prefixWord ++ tailWord_2680874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680874).length < 2 ^ (prefixWord ++ tailWord_2680874).sum := by decide
  have hdescent : baseEnd_2680874 < baseStart_2680874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680944 : List Nat := [2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 3]
def baseStart_2680944 : Nat := 118140960795 + 2680944 * 2 ^ 59
def prefixEnd_2680944 : Nat := 4983230072969 + 3 ^ 40 * 2680944 * 2
def baseEnd_2680944 : Nat := 1376612879787464027970569

theorem tailTrace_2680944 : CollatzResearch.WordTrace tailWord_2680944 prefixEnd_2680944 1376612879787464027970569 := by
  unfold tailWord_2680944
  simp only [CollatzResearch.WordTrace]
  refine ⟨48891030399702615813756943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65188040532936821085009257 48891030399702615813756943)
  ·
    refine ⟨73336545599553923720635415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48891030399702615813756943 73336545599553923720635415)
    ·
      refine ⟨110004818399330885580953123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73336545599553923720635415 110004818399330885580953123)
      ·
        refine ⟨165007227598996328371429685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110004818399330885580953123 165007227598996328371429685)
        ·
          refine ⟨15469427587405905784821533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 165007227598996328371429685 15469427587405905784821533)
          ·
            refine ⟨5801035345277214669308075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15469427587405905784821533 5801035345277214669308075)
            ·
              refine ⟨8701553017915822003962113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5801035345277214669308075 8701553017915822003962113)
              ·
                refine ⟨6526164763436866502971585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8701553017915822003962113 6526164763436866502971585)
                ·
                  refine ⟨4894623572577649877228689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6526164763436866502971585 4894623572577649877228689)
                  ·
                    refine ⟨3670967679433237407921517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4894623572577649877228689 3670967679433237407921517)
                    ·
                      refine ⟨1376612879787464027970569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3670967679433237407921517 1376612879787464027970569)
                      ·
                        rfl

theorem cell23_2680944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 3].length) (baseStart_2680944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2680944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2680944 prefixEnd_2680944 := by exact prefixLift 2680944
  have htrace : WordTrace (prefixWord ++ tailWord_2680944) baseStart_2680944 baseEnd_2680944 := by
    simpa [prefixWord, tailWord_2680944, baseEnd_2680944] using wordTrace_append hprefix tailTrace_2680944
  have hstable : (prefixWord ++ tailWord_2680944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680944).length < 2 ^ (prefixWord ++ tailWord_2680944).sum := by decide
  have hdescent : baseEnd_2680944 < baseStart_2680944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2680960 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 2, 9]
def baseStart_2680960 : Nat := 118140960795 + 2680960 * 2 ^ 59
def prefixEnd_2680960 : Nat := 4983230072969 + 3 ^ 40 * 2680960 * 2
def baseEnd_2680960 : Nat := 458873698492645321790165

theorem tailTrace_2680960 : CollatzResearch.WordTrace tailWord_2680960 prefixEnd_2680960 458873698492645321790165 := by
  unfold tailWord_2680960
  simp only [CollatzResearch.WordTrace]
  refine ⟨48891322183673633180048167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65188429578231510906730889 48891322183673633180048167)
  ·
    refine ⟨73336983275510449770072251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48891322183673633180048167 73336983275510449770072251)
    ·
      refine ⟨110005474913265674655108377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73336983275510449770072251 110005474913265674655108377)
      ·
        refine ⟨82504106184949255991331283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110005474913265674655108377 82504106184949255991331283)
        ·
          refine ⟨123756159277423883986996925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82504106184949255991331283 123756159277423883986996925)
          ·
            refine ⟨46408559729033956495123847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123756159277423883986996925 46408559729033956495123847)
            ·
              refine ⟨69612839593550934742685771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46408559729033956495123847 69612839593550934742685771)
              ·
                refine ⟨104419259390326402114028657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69612839593550934742685771 104419259390326402114028657)
                ·
                  refine ⟨78314444542744801585521493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104419259390326402114028657 78314444542744801585521493)
                  ·
                    refine ⟨458873698492645321790165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 78314444542744801585521493 458873698492645321790165)
                    ·
                      rfl

theorem cell23_2680960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 2, 9].length) (baseStart_2680960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2680960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2680960 prefixEnd_2680960 := by exact prefixLift 2680960
  have htrace : WordTrace (prefixWord ++ tailWord_2680960) baseStart_2680960 baseEnd_2680960 := by
    simpa [prefixWord, tailWord_2680960, baseEnd_2680960] using wordTrace_append hprefix tailTrace_2680960
  have hstable : (prefixWord ++ tailWord_2680960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2680960).length < 2 ^ (prefixWord ++ tailWord_2680960).sum := by decide
  have hdescent : baseEnd_2680960 < baseStart_2680960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2680960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681002 : List Nat := [3, 1, 5, 1, 2, 2, 2, 2, 1, 4]
def baseStart_2681002 : Nat := 118140960795 + 2681002 * 2 ^ 59
def prefixEnd_2681002 : Nat := 4983230072969 + 3 ^ 40 * 2681002 * 2
def baseEnd_2681002 : Nat := 458880887221808267015101

theorem tailTrace_2681002 : CollatzResearch.WordTrace tailWord_2681002 prefixEnd_2681002 458880887221808267015101 := by
  unfold tailWord_2681002
  simp only [CollatzResearch.WordTrace]
  refine ⟨24446044058298776883281315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65189450822130071688750173 24446044058298776883281315)
  ·
    refine ⟨36669066087448165324921973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24446044058298776883281315 36669066087448165324921973)
    ·
      refine ⟨3437724945698265499211435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36669066087448165324921973 3437724945698265499211435)
      ·
        refine ⟨5156587418547398248817153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3437724945698265499211435 5156587418547398248817153)
        ·
          refine ⟨3867440563910548686612865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5156587418547398248817153 3867440563910548686612865)
          ·
            refine ⟨2900580422932911514959649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3867440563910548686612865 2900580422932911514959649)
            ·
              refine ⟨2175435317199683636219737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2900580422932911514959649 2175435317199683636219737)
              ·
                refine ⟨1631576487899762727164803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2175435317199683636219737 1631576487899762727164803)
                ·
                  refine ⟨2447364731849644090747205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1631576487899762727164803 2447364731849644090747205)
                  ·
                    refine ⟨458880887221808267015101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2447364731849644090747205 458880887221808267015101)
                    ·
                      rfl

theorem cell23_2681002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_2681002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2681002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2681002 prefixEnd_2681002 := by exact prefixLift 2681002
  have htrace : WordTrace (prefixWord ++ tailWord_2681002) baseStart_2681002 baseEnd_2681002 := by
    simpa [prefixWord, tailWord_2681002, baseEnd_2681002] using wordTrace_append hprefix tailTrace_2681002
  have hstable : (prefixWord ++ tailWord_2681002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681002).length < 2 ^ (prefixWord ++ tailWord_2681002).sum := by decide
  have hdescent : baseEnd_2681002 < baseStart_2681002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681017 : List Nat := [1, 2, 1, 4, 1, 2, 2, 1, 3, 1, 5]
def baseStart_2681017 : Nat := 118140960795 + 2681017 * 2 ^ 59
def prefixEnd_2681017 : Nat := 4983230072969 + 3 ^ 40 * 2681017 * 2
def baseEnd_2681017 : Nat := 1376650363875242242357733

theorem tailTrace_2681017 : CollatzResearch.WordTrace tailWord_2681017 prefixEnd_2681017 1376650363875242242357733 := by
  unfold tailWord_2681017
  simp only [CollatzResearch.WordTrace]
  refine ⟨97784723328140765094921305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65189815552093843396614203 97784723328140765094921305)
  ·
    refine ⟨73338542496105573821190979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97784723328140765094921305 73338542496105573821190979)
    ·
      refine ⟨110007813744158360731786469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73338542496105573821190979 110007813744158360731786469)
      ·
        refine ⟨20626465077029692637209963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110007813744158360731786469 20626465077029692637209963)
        ·
          refine ⟨30939697615544538955814945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20626465077029692637209963 30939697615544538955814945)
          ·
            refine ⟨23204773211658404216861209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30939697615544538955814945 23204773211658404216861209)
            ·
              refine ⟨17403579908743803162645907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23204773211658404216861209 17403579908743803162645907)
              ·
                refine ⟨26105369863115704743968861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17403579908743803162645907 26105369863115704743968861)
                ·
                  refine ⟨9789513698668389278988323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26105369863115704743968861 9789513698668389278988323)
                  ·
                    refine ⟨14684270548002583918482485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9789513698668389278988323 14684270548002583918482485)
                    ·
                      refine ⟨1376650363875242242357733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14684270548002583918482485 1376650363875242242357733)
                      ·
                        rfl

theorem cell23_2681017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_2681017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2681017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2681017 prefixEnd_2681017 := by exact prefixLift 2681017
  have htrace : WordTrace (prefixWord ++ tailWord_2681017) baseStart_2681017 baseEnd_2681017 := by
    simpa [prefixWord, tailWord_2681017, baseEnd_2681017] using wordTrace_append hprefix tailTrace_2681017
  have hstable : (prefixWord ++ tailWord_2681017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681017).length < 2 ^ (prefixWord ++ tailWord_2681017).sum := by decide
  have hdescent : baseEnd_2681017 < baseStart_2681017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681024 : List Nat := [2, 1, 1, 2, 5, 2, 2, 1, 1, 6]
def baseStart_2681024 : Nat := 118140960795 + 2681024 * 2 ^ 59
def prefixEnd_2681024 : Nat := 4983230072969 + 3 ^ 40 * 2681024 * 2
def baseEnd_2681024 : Nat := 458884652746607904990067

theorem tailTrace_2681024 : CollatzResearch.WordTrace tailWord_2681024 prefixEnd_2681024 458884652746607904990067 := by
  unfold tailWord_2681024
  simp only [CollatzResearch.WordTrace]
  refine ⟨48892489319557702645213063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65189985759410270193617417 48892489319557702645213063)
  ·
    refine ⟨73338733979336553967819595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48892489319557702645213063 73338733979336553967819595)
    ·
      refine ⟨110008100969004830951729393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73338733979336553967819595 110008100969004830951729393)
      ·
        refine ⟨82506075726753623213797045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110008100969004830951729393 82506075726753623213797045)
        ·
          refine ⟨7734944599383152176293473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82506075726753623213797045 7734944599383152176293473)
          ·
            refine ⟨5801208449537364132220105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7734944599383152176293473 5801208449537364132220105)
            ·
              refine ⟨4350906337153023099165079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5801208449537364132220105 4350906337153023099165079)
              ·
                refine ⟨6526359505729534648747619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4350906337153023099165079 6526359505729534648747619)
                ·
                  refine ⟨9789539258594301973121429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6526359505729534648747619 9789539258594301973121429)
                  ·
                    refine ⟨458884652746607904990067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9789539258594301973121429 458884652746607904990067)
                    ·
                      rfl

theorem cell23_2681024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 1, 6].length) (baseStart_2681024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2681024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2681024 prefixEnd_2681024 := by exact prefixLift 2681024
  have htrace : WordTrace (prefixWord ++ tailWord_2681024) baseStart_2681024 baseEnd_2681024 := by
    simpa [prefixWord, tailWord_2681024, baseEnd_2681024] using wordTrace_append hprefix tailTrace_2681024
  have hstable : (prefixWord ++ tailWord_2681024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681024).length < 2 ^ (prefixWord ++ tailWord_2681024).sum := by decide
  have hdescent : baseEnd_2681024 < baseStart_2681024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681034 : List Nat := [3, 1, 2, 1, 3, 1, 1, 3, 3, 2, 3]
def baseStart_2681034 : Nat := 118140960795 + 2681034 * 2 ^ 59
def prefixEnd_2681034 : Nat := 4983230072969 + 3 ^ 40 * 2681034 * 2
def baseEnd_2681034 : Nat := 1376659093046368675845155

theorem tailTrace_2681034 : CollatzResearch.WordTrace tailWord_2681034 prefixEnd_2681034 1376659093046368675845155 := by
  unfold tailWord_2681034
  simp only [CollatzResearch.WordTrace]
  refine ⟨24446335842269794249572539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65190228912719451332193437 24446335842269794249572539)
  ·
    refine ⟨36669503763404691374358809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24446335842269794249572539 36669503763404691374358809)
    ·
      refine ⟨27502127822553518530769107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36669503763404691374358809 27502127822553518530769107)
      ·
        refine ⟨41253191733830277796153661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27502127822553518530769107 41253191733830277796153661)
        ·
          refine ⟨15469946900186354173557623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41253191733830277796153661 15469946900186354173557623)
          ·
            refine ⟨23204920350279531260336435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15469946900186354173557623 23204920350279531260336435)
            ·
              refine ⟨34807380525419296890504653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23204920350279531260336435 34807380525419296890504653)
              ·
                refine ⟨13052767697032236333939245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34807380525419296890504653 13052767697032236333939245)
                ·
                  refine ⟨4894787886387088625227217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13052767697032236333939245 4894787886387088625227217)
                  ·
                    refine ⟨3671090914790316468920413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4894787886387088625227217 3671090914790316468920413)
                    ·
                      refine ⟨1376659093046368675845155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3671090914790316468920413 1376659093046368675845155)
                      ·
                        rfl

theorem cell23_2681034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 3, 2, 3].length) (baseStart_2681034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2681034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2681034 prefixEnd_2681034 := by exact prefixLift 2681034
  have htrace : WordTrace (prefixWord ++ tailWord_2681034) baseStart_2681034 baseEnd_2681034 := by
    simpa [prefixWord, tailWord_2681034, baseEnd_2681034] using wordTrace_append hprefix tailTrace_2681034
  have hstable : (prefixWord ++ tailWord_2681034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681034).length < 2 ^ (prefixWord ++ tailWord_2681034).sum := by decide
  have hdescent : baseEnd_2681034 < baseStart_2681034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681045 : List Nat := [1, 3, 2, 4, 3, 1, 2, 1, 1, 5]
def baseStart_2681045 : Nat := 118140960795 + 2681045 * 2 ^ 59
def prefixEnd_2681045 : Nat := 4983230072969 + 3 ^ 40 * 2681045 * 2
def baseEnd_2681045 : Nat := 458888247111189377602535

theorem tailTrace_2681045 : CollatzResearch.WordTrace tailWord_2681045 prefixEnd_2681045 458888247111189377602535 := by
  unfold tailWord_2681045
  simp only [CollatzResearch.WordTrace]
  refine ⟨97785744572039325876940589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65190496381359550584627059 97785744572039325876940589)
  ·
    refine ⟨36669654214514747203852721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97785744572039325876940589 36669654214514747203852721)
    ·
      refine ⟨27502240660886060402889541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36669654214514747203852721 27502240660886060402889541)
      ·
        refine ⟨5156670123916136325541789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27502240660886060402889541 5156670123916136325541789)
        ·
          refine ⟨1933751296468551122078171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5156670123916136325541789 1933751296468551122078171)
          ·
            refine ⟨2900626944702826683117257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1933751296468551122078171 2900626944702826683117257)
            ·
              refine ⟨2175470208527120012337943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2900626944702826683117257 2175470208527120012337943)
              ·
                refine ⟨3263205312790680018506915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2175470208527120012337943 3263205312790680018506915)
                ·
                  refine ⟨4894807969186020027760373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3263205312790680018506915 4894807969186020027760373)
                  ·
                    refine ⟨458888247111189377602535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4894807969186020027760373 458888247111189377602535)
                    ·
                      rfl

theorem cell23_2681045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 1, 1, 5].length) (baseStart_2681045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2681045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2681045 prefixEnd_2681045 := by exact prefixLift 2681045
  have htrace : WordTrace (prefixWord ++ tailWord_2681045) baseStart_2681045 baseEnd_2681045 := by
    simpa [prefixWord, tailWord_2681045, baseEnd_2681045] using wordTrace_append hprefix tailTrace_2681045
  have hstable : (prefixWord ++ tailWord_2681045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681045).length < 2 ^ (prefixWord ++ tailWord_2681045).sum := by decide
  have hdescent : baseEnd_2681045 < baseStart_2681045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681048 : List Nat := [2, 1, 2, 2, 4, 3, 2, 1, 1, 1, 4]
def baseStart_2681048 : Nat := 118140960795 + 2681048 * 2 ^ 59
def prefixEnd_2681048 : Nat := 4983230072969 + 3 ^ 40 * 2681048 * 2
def baseEnd_2681048 : Nat := 1376666281775531621070091

theorem tailTrace_2681048 : CollatzResearch.WordTrace tailWord_2681048 prefixEnd_2681048 1376666281775531621070091 := by
  unfold tailWord_2681048
  simp only [CollatzResearch.WordTrace]
  refine ⟨48892926995514228694649899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65190569327352304926199865 48892926995514228694649899)
  ·
    refine ⟨73339390493271343041974849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48892926995514228694649899 73339390493271343041974849)
    ·
      refine ⟨55004542869953507281481137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73339390493271343041974849 55004542869953507281481137)
      ·
        refine ⟨41253407152465130461110853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55004542869953507281481137 41253407152465130461110853)
        ·
          refine ⟨7735013841087211961458285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41253407152465130461110853 7735013841087211961458285)
          ·
            refine ⟨2900630190407704485546857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7735013841087211961458285 2900630190407704485546857)
            ·
              refine ⟨2175472642805778364160143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2900630190407704485546857 2175472642805778364160143)
              ·
                refine ⟨3263208964208667546240215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2175472642805778364160143 3263208964208667546240215)
                ·
                  refine ⟨4894813446313001319360323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3263208964208667546240215 4894813446313001319360323)
                  ·
                    refine ⟨7342220169469501979040485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4894813446313001319360323 7342220169469501979040485)
                    ·
                      refine ⟨1376666281775531621070091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7342220169469501979040485 1376666281775531621070091)
                      ·
                        rfl

theorem cell23_2681048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 1, 1, 1, 4].length) (baseStart_2681048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2681048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2681048 prefixEnd_2681048 := by exact prefixLift 2681048
  have htrace : WordTrace (prefixWord ++ tailWord_2681048) baseStart_2681048 baseEnd_2681048 := by
    simpa [prefixWord, tailWord_2681048, baseEnd_2681048] using wordTrace_append hprefix tailTrace_2681048
  have hstable : (prefixWord ++ tailWord_2681048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681048).length < 2 ^ (prefixWord ++ tailWord_2681048).sum := by decide
  have hdescent : baseEnd_2681048 < baseStart_2681048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681182 : List Nat := [4, 4, 2, 1, 1, 1, 1, 1, 2, 6]
def baseStart_2681182 : Nat := 118140960795 + 2681182 * 2 ^ 59
def prefixEnd_2681182 : Nat := 4983230072969 + 3 ^ 40 * 2681182 * 2
def baseEnd_2681182 : Nat := 458911696061078032264825

theorem tailTrace_2681182 : CollatzResearch.WordTrace tailWord_2681182 prefixEnd_2681182 458911696061078032264825 := by
  unfold tailWord_2681182
  simp only [CollatzResearch.WordTrace]
  refine ⟨12223842671567874784334725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65193827581695332183118533 12223842671567874784334725)
  ·
    refine ⟨2291970500918976522062761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12223842671567874784334725 2291970500918976522062761)
    ·
      refine ⟨1718977875689232391547071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2291970500918976522062761 1718977875689232391547071)
      ·
        refine ⟨2578466813533848587320607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1718977875689232391547071 2578466813533848587320607)
        ·
          refine ⟨3867700220300772880980911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2578466813533848587320607 3867700220300772880980911)
          ·
            refine ⟨5801550330451159321471367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3867700220300772880980911 5801550330451159321471367)
            ·
              refine ⟨8702325495676738982207051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5801550330451159321471367 8702325495676738982207051)
              ·
                refine ⟨13053488243515108473310577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8702325495676738982207051 13053488243515108473310577)
                ·
                  refine ⟨9790116182636331354982933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13053488243515108473310577 9790116182636331354982933)
                  ·
                    refine ⟨458911696061078032264825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9790116182636331354982933 458911696061078032264825)
                    ·
                      rfl

theorem cell23_2681182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_2681182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2681182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2681182 prefixEnd_2681182 := by exact prefixLift 2681182
  have htrace : WordTrace (prefixWord ++ tailWord_2681182) baseStart_2681182 baseEnd_2681182 := by
    simpa [prefixWord, tailWord_2681182, baseEnd_2681182] using wordTrace_append hprefix tailTrace_2681182
  have hstable : (prefixWord ++ tailWord_2681182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681182).length < 2 ^ (prefixWord ++ tailWord_2681182).sum := by decide
  have hdescent : baseEnd_2681182 < baseStart_2681182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681211 : List Nat := [1, 1, 1, 1, 1, 7, 3, 1, 2, 1, 4]
def baseStart_2681211 : Nat := 118140960795 + 2681211 * 2 ^ 59
def prefixEnd_2681211 : Nat := 4983230072969 + 3 ^ 40 * 2681211 * 2
def baseEnd_2681211 : Nat := 1376749979122214483331841

theorem tailTrace_2681211 : CollatzResearch.WordTrace tailWord_2681211 prefixEnd_2681211 1376749979122214483331841 := by
  unfold tailWord_2681211
  simp only [CollatzResearch.WordTrace]
  refine ⟨97791799089437936227483487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65194532726291957484988991 97791799089437936227483487)
  ·
    refine ⟨146687698634156904341225231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97791799089437936227483487 146687698634156904341225231)
    ·
      refine ⟨220031547951235356511837847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146687698634156904341225231 220031547951235356511837847)
      ·
        refine ⟨330047321926853034767756771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220031547951235356511837847 330047321926853034767756771)
        ·
          refine ⟨495070982890279552151635157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330047321926853034767756771 495070982890279552151635157)
          ·
            refine ⟨11603226161490927003553949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 495070982890279552151635157 11603226161490927003553949)
            ·
              refine ⟨4351209810559097626332731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11603226161490927003553949 4351209810559097626332731)
              ·
                refine ⟨6526814715838646439499097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4351209810559097626332731 6526814715838646439499097)
                ·
                  refine ⟨4895111036878984829624323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6526814715838646439499097 4895111036878984829624323)
                  ·
                    refine ⟨7342666555318477244436485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4895111036878984829624323 7342666555318477244436485)
                    ·
                      refine ⟨1376749979122214483331841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7342666555318477244436485 1376749979122214483331841)
                      ·
                        rfl

theorem cell23_2681211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 2, 1, 4].length) (baseStart_2681211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2681211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2681211 prefixEnd_2681211 := by exact prefixLift 2681211
  have htrace : WordTrace (prefixWord ++ tailWord_2681211) baseStart_2681211 baseEnd_2681211 := by
    simpa [prefixWord, tailWord_2681211, baseEnd_2681211] using wordTrace_append hprefix tailTrace_2681211
  have hstable : (prefixWord ++ tailWord_2681211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681211).length < 2 ^ (prefixWord ++ tailWord_2681211).sum := by decide
  have hdescent : baseEnd_2681211 < baseStart_2681211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681224 : List Nat := [2, 1, 3, 3, 1, 1, 1, 1, 1, 3, 6]
def baseStart_2681224 : Nat := 118140960795 + 2681224 * 2 ^ 59
def prefixEnd_2681224 : Nat := 4983230072969 + 3 ^ 40 * 2681224 * 2
def baseEnd_2681224 : Nat := 1376756654370722932469281

theorem tailTrace_2681224 : CollatzResearch.WordTrace tailWord_2681224 prefixEnd_2681224 1376756654370722932469281 := by
  unfold tailWord_2681224
  simp only [CollatzResearch.WordTrace]
  refine ⟨48896136619195419723853363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65194848825593892965137817 48896136619195419723853363)
  ·
    refine ⟨73344204928793129585780045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48896136619195419723853363 73344204928793129585780045)
    ·
      refine ⟨27504076848297423594667517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73344204928793129585780045 27504076848297423594667517)
      ·
        refine ⟨10314028818111533848000319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27504076848297423594667517 10314028818111533848000319)
        ·
          refine ⟨15471043227167300772000479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10314028818111533848000319 15471043227167300772000479)
          ·
            refine ⟨23206564840750951158000719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15471043227167300772000479 23206564840750951158000719)
            ·
              refine ⟨34809847261126426737001079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23206564840750951158000719 34809847261126426737001079)
              ·
                refine ⟨52214770891689640105501619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34809847261126426737001079 52214770891689640105501619)
                ·
                  refine ⟨78322156337534460158252429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52214770891689640105501619 78322156337534460158252429)
                  ·
                    refine ⟨29370808626575422559344661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 78322156337534460158252429 29370808626575422559344661)
                    ·
                      refine ⟨1376756654370722932469281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29370808626575422559344661 1376756654370722932469281)
                      ·
                        rfl

theorem cell23_2681224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_2681224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2681224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2681224 prefixEnd_2681224 := by exact prefixLift 2681224
  have htrace : WordTrace (prefixWord ++ tailWord_2681224) baseStart_2681224 baseEnd_2681224 := by
    simpa [prefixWord, tailWord_2681224, baseEnd_2681224] using wordTrace_append hprefix tailTrace_2681224
  have hstable : (prefixWord ++ tailWord_2681224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681224).length < 2 ^ (prefixWord ++ tailWord_2681224).sum := by decide
  have hdescent : baseEnd_2681224 < baseStart_2681224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681264 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 7, 5]
def baseStart_2681264 : Nat := 118140960795 + 2681264 * 2 ^ 59
def prefixEnd_2681264 : Nat := 4983230072969 + 3 ^ 40 * 2681264 * 2
def baseEnd_2681264 : Nat := 458925731198967591989699

theorem tailTrace_2681264 : CollatzResearch.WordTrace tailWord_2681264 prefixEnd_2681264 458925731198967591989699 := by
  unfold tailWord_2681264
  simp only [CollatzResearch.WordTrace]
  refine ⟨48896866079122963139581423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65195821438830617519441897 48896866079122963139581423)
  ·
    refine ⟨73345299118684444709372135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48896866079122963139581423 73345299118684444709372135)
    ·
      refine ⟨110017948678026667064058203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73345299118684444709372135 110017948678026667064058203)
      ·
        refine ⟨165026923017040000596087305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110017948678026667064058203 165026923017040000596087305)
        ·
          refine ⟨123770192262780000447065479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165026923017040000596087305 123770192262780000447065479)
          ·
            refine ⟨185655288394170000670598219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123770192262780000447065479 185655288394170000670598219)
            ·
              refine ⟨278482932591255001005897329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185655288394170000670598219 278482932591255001005897329)
              ·
                refine ⟨208862199443441250754422997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 278482932591255001005897329 208862199443441250754422997)
                ·
                  refine ⟨4895207799455654314556789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 208862199443441250754422997 4895207799455654314556789)
                  ·
                    refine ⟨458925731198967591989699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4895207799455654314556789 458925731198967591989699)
                    ·
                      rfl

theorem cell23_2681264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 7, 5].length) (baseStart_2681264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2681264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2681264 prefixEnd_2681264 := by exact prefixLift 2681264
  have htrace : WordTrace (prefixWord ++ tailWord_2681264) baseStart_2681264 baseEnd_2681264 := by
    simpa [prefixWord, tailWord_2681264, baseEnd_2681264] using wordTrace_append hprefix tailTrace_2681264
  have hstable : (prefixWord ++ tailWord_2681264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681264).length < 2 ^ (prefixWord ++ tailWord_2681264).sum := by decide
  have hdescent : baseEnd_2681264 < baseStart_2681264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681278 : List Nat := [4, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3]
def baseStart_2681278 : Nat := 118140960795 + 2681278 * 2 ^ 59
def prefixEnd_2681278 : Nat := 4983230072969 + 3 ^ 40 * 2681278 * 2
def baseEnd_2681278 : Nat := 1376784382326065721194033

theorem tailTrace_2681278 : CollatzResearch.WordTrace tailWord_2681278 prefixEnd_2681278 1376784382326065721194033 := by
  unfold tailWord_2681278
  simp only [CollatzResearch.WordTrace]
  refine ⟨12224280347524400833771561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65196161853463471113448325 12224280347524400833771561)
  ·
    refine ⟨9168210260643300625328671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12224280347524400833771561 9168210260643300625328671)
    ·
      refine ⟨13752315390964950937993007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9168210260643300625328671 13752315390964950937993007)
      ·
        refine ⟨20628473086447426406989511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13752315390964950937993007 20628473086447426406989511)
        ·
          refine ⟨30942709629671139610484267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20628473086447426406989511 30942709629671139610484267)
          ·
            refine ⟨46414064444506709415726401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30942709629671139610484267 46414064444506709415726401)
            ·
              refine ⟨34810548333380032061794801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46414064444506709415726401 34810548333380032061794801)
              ·
                refine ⟨26107911250035024046346101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34810548333380032061794801 26107911250035024046346101)
                ·
                  refine ⟨2447616679690783504344947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26107911250035024046346101 2447616679690783504344947)
                  ·
                    refine ⟨3671425019536175256517421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2447616679690783504344947 3671425019536175256517421)
                    ·
                      refine ⟨1376784382326065721194033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3671425019536175256517421 1376784382326065721194033)
                      ·
                        rfl

theorem cell23_2681278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_2681278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2681278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2681278 prefixEnd_2681278 := by exact prefixLift 2681278
  have htrace : WordTrace (prefixWord ++ tailWord_2681278) baseStart_2681278 baseEnd_2681278 := by
    simpa [prefixWord, tailWord_2681278, baseEnd_2681278] using wordTrace_append hprefix tailTrace_2681278
  have hstable : (prefixWord ++ tailWord_2681278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681278).length < 2 ^ (prefixWord ++ tailWord_2681278).sum := by decide
  have hdescent : baseEnd_2681278 < baseStart_2681278 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681288 : List Nat := [2, 1, 3, 1, 3, 2, 1, 1, 4, 3, 2]
def baseStart_2681288 : Nat := 118140960795 + 2681288 * 2 ^ 59
def prefixEnd_2681288 : Nat := 4983230072969 + 3 ^ 40 * 2681288 * 2
def baseEnd_2681288 : Nat := 1376789517132610682068987

theorem tailTrace_2681288 : CollatzResearch.WordTrace tailWord_2681288 prefixEnd_2681288 1376789517132610682068987 := by
  unfold tailWord_2681288
  simp only [CollatzResearch.WordTrace]
  refine ⟨48897303755079489189018259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65196405006772652252024345 48897303755079489189018259)
  ·
    refine ⟨73345955632619233783527389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48897303755079489189018259 73345955632619233783527389)
    ·
      refine ⟨27504733362232212668822771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73345955632619233783527389 27504733362232212668822771)
      ·
        refine ⟨41257100043348319003234157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27504733362232212668822771 41257100043348319003234157)
        ·
          refine ⟨15471412516255619626212809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41257100043348319003234157 15471412516255619626212809)
          ·
            refine ⟨11603559387191714719659607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15471412516255619626212809 11603559387191714719659607)
            ·
              refine ⟨17405339080787572079489411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11603559387191714719659607 17405339080787572079489411)
              ·
                refine ⟨26108008621181358119234117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17405339080787572079489411 26108008621181358119234117)
                ·
                  refine ⟨4895251616471504647356397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26108008621181358119234117 4895251616471504647356397)
                  ·
                    refine ⟨1835719356176814242758649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4895251616471504647356397 1835719356176814242758649)
                    ·
                      refine ⟨1376789517132610682068987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1835719356176814242758649 1376789517132610682068987)
                      ·
                        rfl

theorem cell23_2681288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 4, 3, 2].length) (baseStart_2681288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2681288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2681288 prefixEnd_2681288 := by exact prefixLift 2681288
  have htrace : WordTrace (prefixWord ++ tailWord_2681288) baseStart_2681288 baseEnd_2681288 := by
    simpa [prefixWord, tailWord_2681288, baseEnd_2681288] using wordTrace_append hprefix tailTrace_2681288
  have hstable : (prefixWord ++ tailWord_2681288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681288).length < 2 ^ (prefixWord ++ tailWord_2681288).sum := by decide
  have hdescent : baseEnd_2681288 < baseStart_2681288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681315 : List Nat := [1, 1, 1, 6, 3, 2, 1, 2, 1, 5]
def baseStart_2681315 : Nat := 118140960795 + 2681315 * 2 ^ 59
def prefixEnd_2681315 : Nat := 4983230072969 + 3 ^ 40 * 2681315 * 2
def baseEnd_2681315 : Nat := 458934460370094025477121

theorem tailTrace_2681315 : CollatzResearch.WordTrace tailWord_2681315 prefixEnd_2681315 458934460370094025477121 := by
  unfold tailWord_2681315
  simp only [CollatzResearch.WordTrace]
  refine ⟨97795592281061161989269399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65197061520707441326179599 97795592281061161989269399)
  ·
    refine ⟨146693388421591742983904099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97795592281061161989269399 146693388421591742983904099)
    ·
      refine ⟨220040082632387614475856149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146693388421591742983904099 220040082632387614475856149)
      ·
        refine ⟨10314378873393169428555757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 220040082632387614475856149 10314378873393169428555757)
        ·
          refine ⟨3867892077522438535708409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10314378873393169428555757 3867892077522438535708409)
          ·
            refine ⟨2900919058141828901781307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3867892077522438535708409 2900919058141828901781307)
            ·
              refine ⟨4351378587212743352671961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2900919058141828901781307 4351378587212743352671961)
              ·
                refine ⟨3263533940409557514503971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4351378587212743352671961 3263533940409557514503971)
                ·
                  refine ⟨4895300910614336271755957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3263533940409557514503971 4895300910614336271755957)
                  ·
                    refine ⟨458934460370094025477121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4895300910614336271755957 458934460370094025477121)
                    ·
                      rfl

theorem cell23_2681315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 2, 1, 5].length) (baseStart_2681315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2681315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2681315 prefixEnd_2681315 := by exact prefixLift 2681315
  have htrace : WordTrace (prefixWord ++ tailWord_2681315) baseStart_2681315 baseEnd_2681315 := by
    simpa [prefixWord, tailWord_2681315, baseEnd_2681315] using wordTrace_append hprefix tailTrace_2681315
  have hstable : (prefixWord ++ tailWord_2681315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681315).length < 2 ^ (prefixWord ++ tailWord_2681315).sum := by decide
  have hdescent : baseEnd_2681315 < baseStart_2681315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681324 : List Nat := [2, 2, 1, 1, 2, 1, 3, 11]
def baseStart_2681324 : Nat := 118140960795 + 2681324 * 2 ^ 59
def prefixEnd_2681324 : Nat := 4983230072969 + 3 ^ 40 * 2681324 * 2
def baseEnd_2681324 : Nat := 50992888979117501526623

theorem tailTrace_2681324 : CollatzResearch.WordTrace tailWord_2681324 prefixEnd_2681324 50992888979117501526623 := by
  unfold tailWord_2681324
  simp only [CollatzResearch.WordTrace]
  refine ⟨48897960269014278263173513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65197280358685704350898017 48897960269014278263173513)
  ·
    refine ⟨36673470201760708697380135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48897960269014278263173513 36673470201760708697380135)
    ·
      refine ⟨55010205302641063046070203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36673470201760708697380135 55010205302641063046070203)
      ·
        refine ⟨82515307953961594569105305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55010205302641063046070203 82515307953961594569105305)
        ·
          refine ⟨61886480965471195926828979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82515307953961594569105305 61886480965471195926828979)
          ·
            refine ⟨92829721448206793890243469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61886480965471195926828979 92829721448206793890243469)
            ·
              refine ⟨34811145543077547708841301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92829721448206793890243469 34811145543077547708841301)
              ·
                refine ⟨50992888979117501526623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 34811145543077547708841301 50992888979117501526623)
                ·
                  rfl

theorem cell23_2681324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 11].length) (baseStart_2681324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2681324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2681324 prefixEnd_2681324 := by exact prefixLift 2681324
  have htrace : WordTrace (prefixWord ++ tailWord_2681324) baseStart_2681324 baseEnd_2681324 := by
    simpa [prefixWord, tailWord_2681324, baseEnd_2681324] using wordTrace_append hprefix tailTrace_2681324
  have hstable : (prefixWord ++ tailWord_2681324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681324).length < 2 ^ (prefixWord ++ tailWord_2681324).sum := by decide
  have hdescent : baseEnd_2681324 < baseStart_2681324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681331 : List Nat := [1, 1, 1, 2, 2, 2, 5, 2, 1, 2, 4]
def baseStart_2681331 : Nat := 118140960795 + 2681331 * 2 ^ 59
def prefixEnd_2681331 : Nat := 4983230072969 + 3 ^ 40 * 2681331 * 2
def baseEnd_2681331 : Nat := 1376811596800754013831289

theorem tailTrace_2681331 : CollatzResearch.WordTrace tailWord_2681331 prefixEnd_2681331 1376811596800754013831289 := by
  unfold tailWord_2681331
  simp only [CollatzResearch.WordTrace]
  refine ⟨97796175849003196721851847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65197450566002131147901231 97796175849003196721851847)
  ·
    refine ⟨146694263773504795082777771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97796175849003196721851847 146694263773504795082777771)
    ·
      refine ⟨220041395660257192624166657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146694263773504795082777771 220041395660257192624166657)
      ·
        refine ⟨165031046745192894468124993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220041395660257192624166657 165031046745192894468124993)
        ·
          refine ⟨123773285058894670851093745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165031046745192894468124993 123773285058894670851093745)
          ·
            refine ⟨92829963794171003138320309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123773285058894670851093745 92829963794171003138320309)
            ·
              refine ⟨8702809105703531544217529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 92829963794171003138320309 8702809105703531544217529)
              ·
                refine ⟨6527106829277648658163147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8702809105703531544217529 6527106829277648658163147)
                ·
                  refine ⟨9790660243916472987244721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6527106829277648658163147 9790660243916472987244721)
                  ·
                    refine ⟨7342995182937354740433541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9790660243916472987244721 7342995182937354740433541)
                    ·
                      refine ⟨1376811596800754013831289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7342995182937354740433541 1376811596800754013831289)
                      ·
                        rfl

theorem cell23_2681331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 2, 4].length) (baseStart_2681331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2681331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2681331 prefixEnd_2681331 := by exact prefixLift 2681331
  have htrace : WordTrace (prefixWord ++ tailWord_2681331) baseStart_2681331 baseEnd_2681331 := by
    simpa [prefixWord, tailWord_2681331, baseEnd_2681331] using wordTrace_append hprefix tailTrace_2681331
  have hstable : (prefixWord ++ tailWord_2681331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681331).length < 2 ^ (prefixWord ++ tailWord_2681331).sum := by decide
  have hdescent : baseEnd_2681331 < baseStart_2681331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681344 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 8]
def baseStart_2681344 : Nat := 118140960795 + 2681344 * 2 ^ 59
def prefixEnd_2681344 : Nat := 4983230072969 + 3 ^ 40 * 2681344 * 2
def baseEnd_2681344 : Nat := 1376818272049262462968729

theorem tailTrace_2681344 : CollatzResearch.WordTrace tailWord_2681344 prefixEnd_2681344 1376818272049262462968729 := by
  unfold tailWord_2681344
  simp only [CollatzResearch.WordTrace]
  refine ⟨48898324998978049971037543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65197766665304066628050057 48898324998978049971037543)
  ·
    refine ⟨73347487498467074956556315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48898324998978049971037543 73347487498467074956556315)
    ·
      refine ⟨110021231247700612434834473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73347487498467074956556315 110021231247700612434834473)
      ·
        refine ⟨82515923435775459326125855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110021231247700612434834473 82515923435775459326125855)
        ·
          refine ⟨123773885153663188989188783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82515923435775459326125855 123773885153663188989188783)
          ·
            refine ⟨185660827730494783483783175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123773885153663188989188783 185660827730494783483783175)
            ·
              refine ⟨278491241595742175225674763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185660827730494783483783175 278491241595742175225674763)
              ·
                refine ⟨417736862393613262838512145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 278491241595742175225674763 417736862393613262838512145)
                ·
                  refine ⟨313302646795209947128884109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 417736862393613262838512145 313302646795209947128884109)
                  ·
                    refine ⟨117488492548203730173331541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 313302646795209947128884109 117488492548203730173331541)
                    ·
                      refine ⟨1376818272049262462968729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 117488492548203730173331541 1376818272049262462968729)
                      ·
                        rfl

theorem cell23_2681344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 8].length) (baseStart_2681344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2681344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2681344 prefixEnd_2681344 := by exact prefixLift 2681344
  have htrace : WordTrace (prefixWord ++ tailWord_2681344) baseStart_2681344 baseEnd_2681344 := by
    simpa [prefixWord, tailWord_2681344, baseEnd_2681344] using wordTrace_append hprefix tailTrace_2681344
  have hstable : (prefixWord ++ tailWord_2681344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681344).length < 2 ^ (prefixWord ++ tailWord_2681344).sum := by decide
  have hdescent : baseEnd_2681344 < baseStart_2681344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681345 : List Nat := [1, 2, 4, 1, 3, 2, 2, 2, 2, 4]
def baseStart_2681345 : Nat := 118140960795 + 2681345 * 2 ^ 59
def prefixEnd_2681345 : Nat := 4983230072969 + 3 ^ 40 * 2681345 * 2
def baseEnd_2681345 : Nat := 458939595176638986352075

theorem tailTrace_2681345 : CollatzResearch.WordTrace tailWord_2681345 prefixEnd_2681345 458939595176638986352075 := by
  unfold tailWord_2681345
  simp only [CollatzResearch.WordTrace]
  refine ⟨97796686470952477112861489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65197790980634984741907659 97796686470952477112861489)
  ·
    refine ⟨73347514853214357834646117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97796686470952477112861489 73347514853214357834646117)
    ·
      refine ⟨13752659034977692093996147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73347514853214357834646117 13752659034977692093996147)
      ·
        refine ⟨20628988552466538140994221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13752659034977692093996147 20628988552466538140994221)
        ·
          refine ⟨7735870707174951802872833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20628988552466538140994221 7735870707174951802872833)
          ·
            refine ⟨5801903030381213852154625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7735870707174951802872833 5801903030381213852154625)
            ·
              refine ⟨4351427272785910389115969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5801903030381213852154625 4351427272785910389115969)
              ·
                refine ⟨3263570454589432791836977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4351427272785910389115969 3263570454589432791836977)
                ·
                  refine ⟨2447677840942074593877733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3263570454589432791836977 2447677840942074593877733)
                  ·
                    refine ⟨458939595176638986352075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2447677840942074593877733 458939595176638986352075)
                    ·
                      rfl

theorem cell23_2681345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_2681345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2681345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2681345 prefixEnd_2681345 := by exact prefixLift 2681345
  have htrace : WordTrace (prefixWord ++ tailWord_2681345) baseStart_2681345 baseEnd_2681345 := by
    simpa [prefixWord, tailWord_2681345, baseEnd_2681345] using wordTrace_append hprefix tailTrace_2681345
  have hstable : (prefixWord ++ tailWord_2681345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681345).length < 2 ^ (prefixWord ++ tailWord_2681345).sum := by decide
  have hdescent : baseEnd_2681345 < baseStart_2681345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681358 : List Nat := [4, 1, 1, 2, 3, 3, 1, 8]
def baseStart_2681358 : Nat := 118140960795 + 2681358 * 2 ^ 59
def prefixEnd_2681358 : Nat := 4983230072969 + 3 ^ 40 * 2681358 * 2
def baseEnd_2681358 : Nat := 50993535584386126229395

theorem tailTrace_2681358 : CollatzResearch.WordTrace tailWord_2681358 prefixEnd_2681358 50993535584386126229395 := by
  unfold tailWord_2681358
  simp only [CollatzResearch.WordTrace]
  refine ⟨12224645077488172541635591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65198107079936920222056485 12224645077488172541635591)
  ·
    refine ⟨18336967616232258812453387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12224645077488172541635591 18336967616232258812453387)
    ·
      refine ⟨27505451424348388218680081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18336967616232258812453387 27505451424348388218680081)
      ·
        refine ⟨20629088568261291164010061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27505451424348388218680081 20629088568261291164010061)
        ·
          refine ⟨7735908213097984186503773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20629088568261291164010061 7735908213097984186503773)
          ·
            refine ⟨2900965579911744069938915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7735908213097984186503773 2900965579911744069938915)
            ·
              refine ⟨4351448369867616104908373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2900965579911744069938915 4351448369867616104908373)
              ·
                refine ⟨50993535584386126229395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4351448369867616104908373 50993535584386126229395)
                ·
                  rfl

theorem cell23_2681358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 8].length) (baseStart_2681358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2681358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2681358 prefixEnd_2681358 := by exact prefixLift 2681358
  have htrace : WordTrace (prefixWord ++ tailWord_2681358) baseStart_2681358 baseEnd_2681358 := by
    simpa [prefixWord, tailWord_2681358, baseEnd_2681358] using wordTrace_append hprefix tailTrace_2681358
  have hstable : (prefixWord ++ tailWord_2681358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681358).length < 2 ^ (prefixWord ++ tailWord_2681358).sum := by decide
  have hdescent : baseEnd_2681358 < baseStart_2681358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681368 : List Nat := [2, 1, 2, 3, 3, 1, 1, 3, 1, 3, 3]
def baseStart_2681368 : Nat := 118140960795 + 2681368 * 2 ^ 59
def prefixEnd_2681368 : Nat := 4983230072969 + 3 ^ 40 * 2681368 * 2
def baseEnd_2681368 : Nat := 1376830595584970369068619

theorem tailTrace_2681368 : CollatzResearch.WordTrace tailWord_2681368 prefixEnd_2681368 1376830595584970369068619 := by
  unfold tailWord_2681368
  simp only [CollatzResearch.WordTrace]
  refine ⟨48898762674934576020474379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65198350233246101360632505 48898762674934576020474379)
  ·
    refine ⟨73348144012401864030711569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48898762674934576020474379 73348144012401864030711569)
    ·
      refine ⟨55011108009301398023033677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73348144012401864030711569 55011108009301398023033677)
      ·
        refine ⟨20629165503488024258637629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55011108009301398023033677 20629165503488024258637629)
        ·
          refine ⟨7735937063808009096989111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20629165503488024258637629 7735937063808009096989111)
          ·
            refine ⟨11603905595712013645483667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7735937063808009096989111 11603905595712013645483667)
            ·
              refine ⟨17405858393568020468225501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11603905595712013645483667 17405858393568020468225501)
              ·
                refine ⟨6527196897588007675584563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17405858393568020468225501 6527196897588007675584563)
                ·
                  refine ⟨9790795346382011513376845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6527196897588007675584563 9790795346382011513376845)
                  ·
                    refine ⟨3671548254893254317516317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9790795346382011513376845 3671548254893254317516317)
                    ·
                      refine ⟨1376830595584970369068619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3671548254893254317516317 1376830595584970369068619)
                      ·
                        rfl

theorem cell23_2681368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_2681368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2681368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2681368 prefixEnd_2681368 := by exact prefixLift 2681368
  have htrace : WordTrace (prefixWord ++ tailWord_2681368) baseStart_2681368 baseEnd_2681368 := by
    simpa [prefixWord, tailWord_2681368, baseEnd_2681368] using wordTrace_append hprefix tailTrace_2681368
  have hstable : (prefixWord ++ tailWord_2681368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681368).length < 2 ^ (prefixWord ++ tailWord_2681368).sum := by decide
  have hdescent : baseEnd_2681368 < baseStart_2681368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681395 : List Nat := [1, 1, 1, 2, 4, 2, 3, 3, 1, 3, 2]
def baseStart_2681395 : Nat := 118140960795 + 2681395 * 2 ^ 59
def prefixEnd_2681395 : Nat := 4983230072969 + 3 ^ 40 * 2681395 * 2
def baseEnd_2681395 : Nat := 1376844459562641763430995

theorem tailTrace_2681395 : CollatzResearch.WordTrace tailWord_2681395 prefixEnd_2681395 1376844459562641763430995 := by
  unfold tailWord_2681395
  simp only [CollatzResearch.WordTrace]
  refine ⟨97798510120771335652181639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65199006747180890434787759 97798510120771335652181639)
  ·
    refine ⟨146697765181157003478272459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97798510120771335652181639 146697765181157003478272459)
    ·
      refine ⟨220046647771735505217408689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146697765181157003478272459 220046647771735505217408689)
      ·
        refine ⟨165034985828801628913056517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220046647771735505217408689 165034985828801628913056517)
        ·
          refine ⟨30944059842900305421198097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165034985828801628913056517 30944059842900305421198097)
          ·
            refine ⟨23208044882175229065898573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30944059842900305421198097 23208044882175229065898573)
            ·
              refine ⟨8703016830815710899711965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23208044882175229065898573 8703016830815710899711965)
              ·
                refine ⟨3263631311555891587391987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8703016830815710899711965 3263631311555891587391987)
                ·
                  refine ⟨4895446967333837381087981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3263631311555891587391987 4895446967333837381087981)
                  ·
                    refine ⟨1835792612750189017907993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4895446967333837381087981 1835792612750189017907993)
                    ·
                      refine ⟨1376844459562641763430995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1835792612750189017907993 1376844459562641763430995)
                      ·
                        rfl

theorem cell23_2681395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 3, 1, 3, 2].length) (baseStart_2681395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2681395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2681395 prefixEnd_2681395 := by exact prefixLift 2681395
  have htrace : WordTrace (prefixWord ++ tailWord_2681395) baseStart_2681395 baseEnd_2681395 := by
    simpa [prefixWord, tailWord_2681395, baseEnd_2681395] using wordTrace_append hprefix tailTrace_2681395
  have hstable : (prefixWord ++ tailWord_2681395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681395).length < 2 ^ (prefixWord ++ tailWord_2681395).sum := by decide
  have hdescent : baseEnd_2681395 < baseStart_2681395 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681396 : List Nat := [2, 5, 1, 3, 2, 1, 1, 2, 2, 4]
def baseStart_2681396 : Nat := 118140960795 + 2681396 * 2 ^ 59
def prefixEnd_2681396 : Nat := 4983230072969 + 3 ^ 40 * 2681396 * 2
def baseEnd_2681396 : Nat := 458948324347765419839497

theorem tailTrace_2681396 : CollatzResearch.WordTrace tailWord_2681396 prefixEnd_2681396 458948324347765419839497 := by
  unfold tailWord_2681396
  simp only [CollatzResearch.WordTrace]
  refine ⟨48899273296883856411484021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65199031062511808548645361 48899273296883856411484021)
  ·
    refine ⟨4584306871582861538576627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48899273296883856411484021 4584306871582861538576627)
    ·
      refine ⟨6876460307374292307864941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4584306871582861538576627 6876460307374292307864941)
      ·
        refine ⟨2578672615265359615449353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6876460307374292307864941 2578672615265359615449353)
        ·
          refine ⟨1934004461449019711587015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2578672615265359615449353 1934004461449019711587015)
          ·
            refine ⟨2901006692173529567380523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1934004461449019711587015 2901006692173529567380523)
            ·
              refine ⟨4351510038260294351070785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2901006692173529567380523 4351510038260294351070785)
              ·
                refine ⟨3263632528695220763303089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4351510038260294351070785 3263632528695220763303089)
                ·
                  refine ⟨2447724396521415572477317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3263632528695220763303089 2447724396521415572477317)
                  ·
                    refine ⟨458948324347765419839497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2447724396521415572477317 458948324347765419839497)
                    ·
                      rfl

theorem cell23_2681396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_2681396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2681396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2681396 prefixEnd_2681396 := by exact prefixLift 2681396
  have htrace : WordTrace (prefixWord ++ tailWord_2681396) baseStart_2681396 baseEnd_2681396 := by
    simpa [prefixWord, tailWord_2681396, baseEnd_2681396] using wordTrace_append hprefix tailTrace_2681396
  have hstable : (prefixWord ++ tailWord_2681396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681396).length < 2 ^ (prefixWord ++ tailWord_2681396).sum := by decide
  have hdescent : baseEnd_2681396 < baseStart_2681396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681401 : List Nat := [1, 2, 1, 5, 1, 1, 1, 1, 4, 6]
def baseStart_2681401 : Nat := 118140960795 + 2681401 * 2 ^ 59
def prefixEnd_2681401 : Nat := 4983230072969 + 3 ^ 40 * 2681401 * 2
def baseEnd_2681401 : Nat := 458949180148856246651989

theorem tailTrace_2681401 : CollatzResearch.WordTrace tailWord_2681401 prefixEnd_2681401 458949180148856246651989 := by
  unfold tailWord_2681401
  simp only [CollatzResearch.WordTrace]
  refine ⟨97798728958749598676900057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65199152639166399117933371 97798728958749598676900057)
  ·
    refine ⟨73349046719062199007675043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97798728958749598676900057 73349046719062199007675043)
    ·
      refine ⟨110023570078593298511512565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73349046719062199007675043 110023570078593298511512565)
      ·
        refine ⟨10314709694868121735454303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 110023570078593298511512565 10314709694868121735454303)
        ·
          refine ⟨15472064542302182603181455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10314709694868121735454303 15472064542302182603181455)
          ·
            refine ⟨23208096813453273904772183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15472064542302182603181455 23208096813453273904772183)
            ·
              refine ⟨34812145220179910857158275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23208096813453273904772183 34812145220179910857158275)
              ·
                refine ⟨52218217830269866285737413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34812145220179910857158275 52218217830269866285737413)
                ·
                  refine ⟨9790915843175599928575765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52218217830269866285737413 9790915843175599928575765)
                  ·
                    refine ⟨458949180148856246651989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9790915843175599928575765 458949180148856246651989)
                    ·
                      rfl

theorem cell23_2681401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 6].length) (baseStart_2681401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2681401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2681401 prefixEnd_2681401 := by exact prefixLift 2681401
  have htrace : WordTrace (prefixWord ++ tailWord_2681401) baseStart_2681401 baseEnd_2681401 := by
    simpa [prefixWord, tailWord_2681401, baseEnd_2681401] using wordTrace_append hprefix tailTrace_2681401
  have hstable : (prefixWord ++ tailWord_2681401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681401).length < 2 ^ (prefixWord ++ tailWord_2681401).sum := by decide
  have hdescent : baseEnd_2681401 < baseStart_2681401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681402 : List Nat := [3, 1, 1, 1, 3, 5, 1, 2, 2, 1, 3]
def baseStart_2681402 : Nat := 118140960795 + 2681402 * 2 ^ 59
def prefixEnd_2681402 : Nat := 4983230072969 + 3 ^ 40 * 2681402 * 2
def baseEnd_2681402 : Nat := 1376848053927223236043463

theorem tailTrace_2681402 : CollatzResearch.WordTrace tailWord_2681402 prefixEnd_2681402 1376848053927223236043463 := by
  unfold tailWord_2681402
  simp only [CollatzResearch.WordTrace]
  refine ⟨24449691357936493961921615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65199176954497317231790973 24449691357936493961921615)
  ·
    refine ⟨36674537036904740942882423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24449691357936493961921615 36674537036904740942882423)
    ·
      refine ⟨55011805555357111414323635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36674537036904740942882423 55011805555357111414323635)
      ·
        refine ⟨82517708333035667121485453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55011805555357111414323635 82517708333035667121485453)
        ·
          refine ⟨30944140624888375170557045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82517708333035667121485453 30944140624888375170557045)
          ·
            refine ⟨2901013183583285172239723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30944140624888375170557045 2901013183583285172239723)
            ·
              refine ⟨4351519775374927758359585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2901013183583285172239723 4351519775374927758359585)
              ·
                refine ⟨3263639831531195818769689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4351519775374927758359585 3263639831531195818769689)
                ·
                  refine ⟨2447729873648396864077267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3263639831531195818769689 2447729873648396864077267)
                  ·
                    refine ⟨3671594810472595296115901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2447729873648396864077267 3671594810472595296115901)
                    ·
                      refine ⟨1376848053927223236043463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3671594810472595296115901 1376848053927223236043463)
                      ·
                        rfl

theorem cell23_2681402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 2, 2, 1, 3].length) (baseStart_2681402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2681402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2681402 prefixEnd_2681402 := by exact prefixLift 2681402
  have htrace : WordTrace (prefixWord ++ tailWord_2681402) baseStart_2681402 baseEnd_2681402 := by
    simpa [prefixWord, tailWord_2681402, baseEnd_2681402] using wordTrace_append hprefix tailTrace_2681402
  have hstable : (prefixWord ++ tailWord_2681402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681402).length < 2 ^ (prefixWord ++ tailWord_2681402).sum := by decide
  have hdescent : baseEnd_2681402 < baseStart_2681402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681408 : List Nat := [2, 1, 1, 2, 2, 2, 2, 2, 3, 4, 2]
def baseStart_2681408 : Nat := 118140960795 + 2681408 * 2 ^ 59
def prefixEnd_2681408 : Nat := 4983230072969 + 3 ^ 40 * 2681408 * 2
def baseEnd_2681408 : Nat := 1376851134811150212568435

theorem tailTrace_2681408 : CollatzResearch.WordTrace tailWord_2681408 prefixEnd_2681408 1376851134811150212568435 := by
  unfold tailWord_2681408
  simp only [CollatzResearch.WordTrace]
  refine ⟨48899492134862119436202439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65199322846482825914936585 48899492134862119436202439)
  ·
    refine ⟨73349238202293179154303659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48899492134862119436202439 73349238202293179154303659)
    ·
      refine ⟨110023857303439768731455489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73349238202293179154303659 110023857303439768731455489)
      ·
        refine ⟨82517892977579826548591617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110023857303439768731455489 82517892977579826548591617)
        ·
          refine ⟨61888419733184869911443713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82517892977579826548591617 61888419733184869911443713)
          ·
            refine ⟨46416314799888652433582785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61888419733184869911443713 46416314799888652433582785)
            ·
              refine ⟨34812236099916489325187089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46416314799888652433582785 34812236099916489325187089)
              ·
                refine ⟨26109177074937366993890317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34812236099916489325187089 26109177074937366993890317)
                ·
                  refine ⟨9790941403101512622708869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26109177074937366993890317 9790941403101512622708869)
                  ·
                    refine ⟨1835801513081533616757913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9790941403101512622708869 1835801513081533616757913)
                    ·
                      refine ⟨1376851134811150212568435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1835801513081533616757913 1376851134811150212568435)
                      ·
                        rfl

theorem cell23_2681408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 3, 4, 2].length) (baseStart_2681408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2681408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2681408 prefixEnd_2681408 := by exact prefixLift 2681408
  have htrace : WordTrace (prefixWord ++ tailWord_2681408) baseStart_2681408 baseEnd_2681408 := by
    simpa [prefixWord, tailWord_2681408, baseEnd_2681408] using wordTrace_append hprefix tailTrace_2681408
  have hstable : (prefixWord ++ tailWord_2681408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681408).length < 2 ^ (prefixWord ++ tailWord_2681408).sum := by decide
  have hdescent : baseEnd_2681408 < baseStart_2681408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681411 : List Nat := [1, 1, 1, 3, 1, 2, 1, 3, 1, 6, 3]
def baseStart_2681411 : Nat := 118140960795 + 2681411 * 2 ^ 59
def prefixEnd_2681411 : Nat := 4983230072969 + 3 ^ 40 * 2681411 * 2
def baseEnd_2681411 : Nat := 1376852675253113700830921

theorem tailTrace_2681411 : CollatzResearch.WordTrace tailWord_2681411 prefixEnd_2681411 1376852675253113700830921 := by
  unfold tailWord_2681411
  simp only [CollatzResearch.WordTrace]
  refine ⟨97799093688713370384764087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65199395792475580256509391 97799093688713370384764087)
  ·
    refine ⟨146698640533070055577146131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97799093688713370384764087 146698640533070055577146131)
    ·
      refine ⟨220047960799605083365719197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146698640533070055577146131 220047960799605083365719197)
      ·
        refine ⟨82517985299851906262144699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 220047960799605083365719197 82517985299851906262144699)
        ·
          refine ⟨123776977949777859393217049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82517985299851906262144699 123776977949777859393217049)
          ·
            refine ⟨92832733462333394544912787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123776977949777859393217049 92832733462333394544912787)
            ·
              refine ⟨139249100193500091817369181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92832733462333394544912787 139249100193500091817369181)
              ·
                refine ⟨52218412572562534431513443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139249100193500091817369181 52218412572562534431513443)
                ·
                  refine ⟨78327618858843801647270165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52218412572562534431513443 78327618858843801647270165)
                  ·
                    refine ⟨3671607134008303202215789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 78327618858843801647270165 3671607134008303202215789)
                    ·
                      refine ⟨1376852675253113700830921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3671607134008303202215789 1376852675253113700830921)
                      ·
                        rfl

theorem cell23_2681411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 6, 3].length) (baseStart_2681411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2681411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2681411 prefixEnd_2681411 := by exact prefixLift 2681411
  have htrace : WordTrace (prefixWord ++ tailWord_2681411) baseStart_2681411 baseEnd_2681411 := by
    simpa [prefixWord, tailWord_2681411, baseEnd_2681411] using wordTrace_append hprefix tailTrace_2681411
  have hstable : (prefixWord ++ tailWord_2681411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681411).length < 2 ^ (prefixWord ++ tailWord_2681411).sum := by decide
  have hdescent : baseEnd_2681411 < baseStart_2681411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681425 : List Nat := [1, 2, 2, 1, 3, 3, 3, 1, 1, 4, 2]
def baseStart_2681425 : Nat := 118140960795 + 2681425 * 2 ^ 59
def prefixEnd_2681425 : Nat := 4983230072969 + 3 ^ 40 * 2681425 * 2
def baseEnd_2681425 : Nat := 1376859863982276646055857

theorem tailTrace_2681425 : CollatzResearch.WordTrace tailWord_2681425 prefixEnd_2681425 1376859863982276646055857 := by
  unfold tailWord_2681425
  simp only [CollatzResearch.WordTrace]
  refine ⟨97799604310662650775773729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65199736207108433850515819 97799604310662650775773729)
  ·
    refine ⟨73349703232996988081830297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97799604310662650775773729 73349703232996988081830297)
    ·
      refine ⟨55012277424747741061372723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73349703232996988081830297 55012277424747741061372723)
      ·
        refine ⟨82518416137121611592059085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55012277424747741061372723 82518416137121611592059085)
        ·
          refine ⟨30944406051420604347022157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82518416137121611592059085 30944406051420604347022157)
          ·
            refine ⟨11604152269282726630133309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30944406051420604347022157 11604152269282726630133309)
            ·
              refine ⟨4351557100981022486299991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11604152269282726630133309 4351557100981022486299991)
              ·
                refine ⟨6527335651471533729449987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4351557100981022486299991 6527335651471533729449987)
                ·
                  refine ⟨9791003477207300594174981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6527335651471533729449987 9791003477207300594174981)
                  ·
                    refine ⟨1835813151976368861407809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9791003477207300594174981 1835813151976368861407809)
                    ·
                      refine ⟨1376859863982276646055857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1835813151976368861407809 1376859863982276646055857)
                      ·
                        rfl

theorem cell23_2681425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 4, 2].length) (baseStart_2681425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2681425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2681425 prefixEnd_2681425 := by exact prefixLift 2681425
  have htrace : WordTrace (prefixWord ++ tailWord_2681425) baseStart_2681425 baseEnd_2681425 := by
    simpa [prefixWord, tailWord_2681425, baseEnd_2681425] using wordTrace_append hprefix tailTrace_2681425
  have hstable : (prefixWord ++ tailWord_2681425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681425).length < 2 ^ (prefixWord ++ tailWord_2681425).sum := by decide
  have hdescent : baseEnd_2681425 < baseStart_2681425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681431 : List Nat := [1, 1, 3, 2, 2, 2, 1, 4, 7]
def baseStart_2681431 : Nat := 118140960795 + 2681431 * 2 ^ 59
def prefixEnd_2681431 : Nat := 4983230072969 + 3 ^ 40 * 2681431 * 2
def baseEnd_2681431 : Nat := 152984771651800402508981

theorem tailTrace_2681431 : CollatzResearch.WordTrace tailWord_2681431 prefixEnd_2681431 152984771651800402508981 := by
  unfold tailWord_2681431
  simp only [CollatzResearch.WordTrace]
  refine ⟨97799823148640913800492147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65199882099093942533661431 97799823148640913800492147)
  ·
    refine ⟨146699734722961370700738221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97799823148640913800492147 146699734722961370700738221)
    ·
      refine ⟨55012400521110514012776833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146699734722961370700738221 55012400521110514012776833)
      ·
        refine ⟨41259300390832885509582625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55012400521110514012776833 41259300390832885509582625)
        ·
          refine ⟨30944475293124664132186969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41259300390832885509582625 30944475293124664132186969)
          ·
            refine ⟨23208356469843498099140227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30944475293124664132186969 23208356469843498099140227)
            ·
              refine ⟨34812534704765247148710341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23208356469843498099140227 34812534704765247148710341)
              ·
                refine ⟨6527350257143483840383189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34812534704765247148710341 6527350257143483840383189)
                ·
                  refine ⟨152984771651800402508981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6527350257143483840383189 152984771651800402508981)
                  ·
                    rfl

theorem cell23_2681431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 7].length) (baseStart_2681431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2681431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2681431 prefixEnd_2681431 := by exact prefixLift 2681431
  have htrace : WordTrace (prefixWord ++ tailWord_2681431) baseStart_2681431 baseEnd_2681431 := by
    simpa [prefixWord, tailWord_2681431, baseEnd_2681431] using wordTrace_append hprefix tailTrace_2681431
  have hstable : (prefixWord ++ tailWord_2681431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681431).length < 2 ^ (prefixWord ++ tailWord_2681431).sum := by decide
  have hdescent : baseEnd_2681431 < baseStart_2681431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681476 : List Nat := [2, 3, 2, 1, 3, 3, 2, 1, 2, 2, 2]
def baseStart_2681476 : Nat := 118140960795 + 2681476 * 2 ^ 59
def prefixEnd_2681476 : Nat := 4983230072969 + 3 ^ 40 * 2681476 * 2
def baseEnd_2681476 : Nat := 1376886051495655946518123

theorem tailTrace_2681476 : CollatzResearch.WordTrace tailWord_2681476 prefixEnd_2681476 1376886051495655946518123 := by
  unfold tailWord_2681476
  simp only [CollatzResearch.WordTrace]
  refine ⟨48900732216738943242940141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65200976288985257657253521 48900732216738943242940141)
  ·
    refine ⟨18337774581277103716102553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48900732216738943242940141 18337774581277103716102553)
    ·
      refine ⟨13753330935957827787076915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18337774581277103716102553 13753330935957827787076915)
      ·
        refine ⟨20629996403936741680615373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13753330935957827787076915 20629996403936741680615373)
        ·
          refine ⟨7736248651476278130230765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20629996403936741680615373 7736248651476278130230765)
          ·
            refine ⟨2901093244303604298836537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7736248651476278130230765 2901093244303604298836537)
            ·
              refine ⟨2175819933227703224127403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2901093244303604298836537 2175819933227703224127403)
              ·
                refine ⟨3263729899841554836191105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2175819933227703224127403 3263729899841554836191105)
                ·
                  refine ⟨2447797424881166127143329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3263729899841554836191105 2447797424881166127143329)
                  ·
                    refine ⟨1835848068660874595357497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2447797424881166127143329 1835848068660874595357497)
                    ·
                      refine ⟨1376886051495655946518123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1835848068660874595357497 1376886051495655946518123)
                      ·
                        rfl

theorem cell23_2681476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 1, 2, 2, 2].length) (baseStart_2681476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2681476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2681476 prefixEnd_2681476 := by exact prefixLift 2681476
  have htrace : WordTrace (prefixWord ++ tailWord_2681476) baseStart_2681476 baseEnd_2681476 := by
    simpa [prefixWord, tailWord_2681476, baseEnd_2681476] using wordTrace_append hprefix tailTrace_2681476
  have hstable : (prefixWord ++ tailWord_2681476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681476).length < 2 ^ (prefixWord ++ tailWord_2681476).sum := by decide
  have hdescent : baseEnd_2681476 < baseStart_2681476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681582 : List Nat := [4, 1, 2, 1, 1, 3, 1, 3, 3, 1, 3]
def baseStart_2681582 : Nat := 118140960795 + 2681582 * 2 ^ 59
def prefixEnd_2681582 : Nat := 4983230072969 + 3 ^ 40 * 2681582 * 2
def baseEnd_2681582 : Nat := 1376940480445032531792635

theorem tailTrace_2681582 : CollatzResearch.WordTrace tailWord_2681582 prefixEnd_2681582 1376940480445032531792635 := by
  unfold tailWord_2681582
  simp only [CollatzResearch.WordTrace]
  refine ⟨12225666321386733323654875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65203553714062577726159333 12225666321386733323654875)
  ·
    refine ⟨18338499482080099985482313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12225666321386733323654875 18338499482080099985482313)
    ·
      refine ⟨13753874611560074989111735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18338499482080099985482313 13753874611560074989111735)
      ·
        refine ⟨20630811917340112483667603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13753874611560074989111735 20630811917340112483667603)
        ·
          refine ⟨30946217876010168725501405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20630811917340112483667603 30946217876010168725501405)
          ·
            refine ⟨11604831703503813272063027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30946217876010168725501405 11604831703503813272063027)
            ·
              refine ⟨17407247555255719908094541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11604831703503813272063027 17407247555255719908094541)
              ·
                refine ⟨6527717833220894965535453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17407247555255719908094541 6527717833220894965535453)
                ·
                  refine ⟨2447894187457835612075795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6527717833220894965535453 2447894187457835612075795)
                  ·
                    refine ⟨3671841281186753418113693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2447894187457835612075795 3671841281186753418113693)
                    ·
                      refine ⟨1376940480445032531792635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3671841281186753418113693 1376940480445032531792635)
                      ·
                        rfl

theorem cell23_2681582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_2681582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2681582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2681582 prefixEnd_2681582 := by exact prefixLift 2681582
  have htrace : WordTrace (prefixWord ++ tailWord_2681582) baseStart_2681582 baseEnd_2681582 := by
    simpa [prefixWord, tailWord_2681582, baseEnd_2681582] using wordTrace_append hprefix tailTrace_2681582
  have hstable : (prefixWord ++ tailWord_2681582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681582).length < 2 ^ (prefixWord ++ tailWord_2681582).sum := by decide
  have hdescent : baseEnd_2681582 < baseStart_2681582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681602 : List Nat := [3, 4, 1, 1, 1, 2, 1, 4, 1, 5]
def baseStart_2681602 : Nat := 118140960795 + 2681602 * 2 ^ 59
def prefixEnd_2681602 : Nat := 4983230072969 + 3 ^ 40 * 2681602 * 2
def baseEnd_2681602 : Nat := 458983583352707484514181

theorem tailTrace_2681602 : CollatzResearch.WordTrace tailWord_2681602 prefixEnd_2681602 458983583352707484514181 := by
  unfold tailWord_2681602
  simp only [CollatzResearch.WordTrace]
  refine ⟨24451515007755352501241765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65204040020680940003311373 24451515007755352501241765)
  ·
    refine ⟨4584659063954128593982831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24451515007755352501241765 4584659063954128593982831)
    ·
      refine ⟨6876988595931192890974247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4584659063954128593982831 6876988595931192890974247)
      ·
        refine ⟨10315482893896789336461371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6876988595931192890974247 10315482893896789336461371)
        ·
          refine ⟨15473224340845184004692057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10315482893896789336461371 15473224340845184004692057)
          ·
            refine ⟨11604918255633888003519043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15473224340845184004692057 11604918255633888003519043)
            ·
              refine ⟨17407377383450832005278565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11604918255633888003519043 17407377383450832005278565)
              ·
                refine ⟨3263883259397031000989731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17407377383450832005278565 3263883259397031000989731)
                ·
                  refine ⟨4895824889095546501484597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3263883259397031000989731 4895824889095546501484597)
                  ·
                    refine ⟨458983583352707484514181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4895824889095546501484597 458983583352707484514181)
                    ·
                      rfl

theorem cell23_2681602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_2681602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2681602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2681602 prefixEnd_2681602 := by exact prefixLift 2681602
  have htrace : WordTrace (prefixWord ++ tailWord_2681602) baseStart_2681602 baseEnd_2681602 := by
    simpa [prefixWord, tailWord_2681602, baseEnd_2681602] using wordTrace_append hprefix tailTrace_2681602
  have hstable : (prefixWord ++ tailWord_2681602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681602).length < 2 ^ (prefixWord ++ tailWord_2681602).sum := by decide
  have hdescent : baseEnd_2681602 < baseStart_2681602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681628 : List Nat := [2, 2, 3, 1, 1, 3, 11]
def baseStart_2681628 : Nat := 118140960795 + 2681628 * 2 ^ 59
def prefixEnd_2681628 : Nat := 4983230072969 + 3 ^ 40 * 2681628 * 2
def baseEnd_2681628 : Nat := 16999556796977029034783

theorem tailTrace_2681628 : CollatzResearch.WordTrace tailWord_2681628 prefixEnd_2681628 16999556796977029034783 := by
  unfold tailWord_2681628
  simp only [CollatzResearch.WordTrace]
  refine ⟨48903504164463608222706769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65204672219284810963609025 48903504164463608222706769)
  ·
    refine ⟨36677628123347706167030077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48903504164463608222706769 36677628123347706167030077)
    ·
      refine ⟨13754110546255389812636279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36677628123347706167030077 13754110546255389812636279)
      ·
        refine ⟨20631165819383084718954419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13754110546255389812636279 20631165819383084718954419)
        ·
          refine ⟨30946748729074627078431629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20631165819383084718954419 30946748729074627078431629)
          ·
            refine ⟨11605030773402985154411861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30946748729074627078431629 11605030773402985154411861)
            ·
              refine ⟨16999556796977029034783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 11605030773402985154411861 16999556796977029034783)
              ·
                rfl

theorem cell23_2681628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 11].length) (baseStart_2681628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2681628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2681628 prefixEnd_2681628 := by exact prefixLift 2681628
  have htrace : WordTrace (prefixWord ++ tailWord_2681628) baseStart_2681628 baseEnd_2681628 := by
    simpa [prefixWord, tailWord_2681628, baseEnd_2681628] using wordTrace_append hprefix tailTrace_2681628
  have hstable : (prefixWord ++ tailWord_2681628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681628).length < 2 ^ (prefixWord ++ tailWord_2681628).sum := by decide
  have hdescent : baseEnd_2681628 < baseStart_2681628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681655 : List Nat := [1, 1, 3, 1, 2, 1, 4, 3, 1, 3, 3]
def baseStart_2681655 : Nat := 118140960795 + 2681655 * 2 ^ 59
def prefixEnd_2681655 : Nat := 4983230072969 + 3 ^ 40 * 2681655 * 2
def baseEnd_2681655 : Nat := 1376977964532810746179799

theorem tailTrace_2681655 : CollatzResearch.WordTrace tailWord_2681655 prefixEnd_2681655 1376977964532810746179799 := by
  unfold tailWord_2681655
  simp only [CollatzResearch.WordTrace]
  refine ⟨97807993099829400056646419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65205328733219600037764279 97807993099829400056646419)
  ·
    refine ⟨146711989649744100084969629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97807993099829400056646419 146711989649744100084969629)
    ·
      refine ⟨55016996118654037531863611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146711989649744100084969629 55016996118654037531863611)
      ·
        refine ⟨82525494177981056297795417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55016996118654037531863611 82525494177981056297795417)
        ·
          refine ⟨61894120633485792223346563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82525494177981056297795417 61894120633485792223346563)
          ·
            refine ⟨92841180950228688335019845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61894120633485792223346563 92841180950228688335019845)
            ·
              refine ⟨17407721428167879062816221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92841180950228688335019845 17407721428167879062816221)
              ·
                refine ⟨6527895535562954648556083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17407721428167879062816221 6527895535562954648556083)
                ·
                  refine ⟨9791843303344431972834125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6527895535562954648556083 9791843303344431972834125)
                  ·
                    refine ⟨3671941238754161989812797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9791843303344431972834125 3671941238754161989812797)
                    ·
                      refine ⟨1376977964532810746179799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3671941238754161989812797 1376977964532810746179799)
                      ·
                        rfl

theorem cell23_2681655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 3, 3].length) (baseStart_2681655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2681655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2681655 prefixEnd_2681655 := by exact prefixLift 2681655
  have htrace : WordTrace (prefixWord ++ tailWord_2681655) baseStart_2681655 baseEnd_2681655 := by
    simpa [prefixWord, tailWord_2681655, baseEnd_2681655] using wordTrace_append hprefix tailTrace_2681655
  have hstable : (prefixWord ++ tailWord_2681655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681655).length < 2 ^ (prefixWord ++ tailWord_2681655).sum := by decide
  have hdescent : baseEnd_2681655 < baseStart_2681655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681688 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 3, 8]
def baseStart_2681688 : Nat := 118140960795 + 2681688 * 2 ^ 59
def prefixEnd_2681688 : Nat := 4983230072969 + 3 ^ 40 * 2681688 * 2
def baseEnd_2681688 : Nat := 458998303131469705689049

theorem tailTrace_2681688 : CollatzResearch.WordTrace tailWord_2681688 prefixEnd_2681688 458998303131469705689049 := by
  unfold tailWord_2681688
  simp only [CollatzResearch.WordTrace]
  refine ⟨48904598354354923346298859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65206131139139897795065145 48904598354354923346298859)
  ·
    refine ⟨73356897531532385019448289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48904598354354923346298859 73356897531532385019448289)
    ·
      refine ⟨55017673148649288764586217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73356897531532385019448289 55017673148649288764586217)
      ·
        refine ⟨41263254861486966573439663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55017673148649288764586217 41263254861486966573439663)
        ·
          refine ⟨61894882292230449860159495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41263254861486966573439663 61894882292230449860159495)
          ·
            refine ⟨92842323438345674790239243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61894882292230449860159495 92842323438345674790239243)
            ·
              refine ⟨139263485157518512185358865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92842323438345674790239243 139263485157518512185358865)
              ·
                refine ⟨104447613868138884139019149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139263485157518512185358865 104447613868138884139019149)
                ·
                  refine ⟨39167855200552081552132181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104447613868138884139019149 39167855200552081552132181)
                  ·
                    refine ⟨458998303131469705689049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 39167855200552081552132181 458998303131469705689049)
                    ·
                      rfl

theorem cell23_2681688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 3, 8].length) (baseStart_2681688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2681688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2681688 prefixEnd_2681688 := by exact prefixLift 2681688
  have htrace : WordTrace (prefixWord ++ tailWord_2681688) baseStart_2681688 baseEnd_2681688 := by
    simpa [prefixWord, tailWord_2681688, baseEnd_2681688] using wordTrace_append hprefix tailTrace_2681688
  have hstable : (prefixWord ++ tailWord_2681688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681688).length < 2 ^ (prefixWord ++ tailWord_2681688).sum := by decide
  have hdescent : baseEnd_2681688 < baseStart_2681688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681689 : List Nat := [1, 2, 1, 2, 2, 5, 2, 2, 2, 1, 3]
def baseStart_2681689 : Nat := 118140960795 + 2681689 * 2 ^ 59
def prefixEnd_2681689 : Nat := 4983230072969 + 3 ^ 40 * 2681689 * 2
def baseEnd_2681689 : Nat := 1376995422875063613154643

theorem tailTrace_2681689 : CollatzResearch.WordTrace tailWord_2681689 prefixEnd_2681689 1376995422875063613154643 := by
  unfold tailWord_2681689
  simp only [CollatzResearch.WordTrace]
  refine ⟨97809233181706223863384121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65206155454470815908922747 97809233181706223863384121)
  ·
    refine ⟨73356924886279667897538091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97809233181706223863384121 73356924886279667897538091)
    ·
      refine ⟨110035387329419501846307137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73356924886279667897538091 110035387329419501846307137)
      ·
        refine ⟨82526540497064626384730353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110035387329419501846307137 82526540497064626384730353)
        ·
          refine ⟨61894905372798469788547765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82526540497064626384730353 61894905372798469788547765)
          ·
            refine ⟨5802647378699856542676353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61894905372798469788547765 5802647378699856542676353)
            ·
              refine ⟨4351985534024892407007265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5802647378699856542676353 4351985534024892407007265)
              ·
                refine ⟨3263989150518669305255449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4351985534024892407007265 3263989150518669305255449)
                ·
                  refine ⟨2447991862889001978941587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3263989150518669305255449 2447991862889001978941587)
                  ·
                    refine ⟨3671987794333502968412381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2447991862889001978941587 3671987794333502968412381)
                    ·
                      refine ⟨1376995422875063613154643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3671987794333502968412381 1376995422875063613154643)
                      ·
                        rfl

theorem cell23_2681689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 2, 2, 1, 3].length) (baseStart_2681689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2681689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2681689 prefixEnd_2681689 := by exact prefixLift 2681689
  have htrace : WordTrace (prefixWord ++ tailWord_2681689) baseStart_2681689 baseEnd_2681689 := by
    simpa [prefixWord, tailWord_2681689, baseEnd_2681689] using wordTrace_append hprefix tailTrace_2681689
  have hstable : (prefixWord ++ tailWord_2681689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681689).length < 2 ^ (prefixWord ++ tailWord_2681689).sum := by decide
  have hdescent : baseEnd_2681689 < baseStart_2681689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681712 : List Nat := [2, 1, 1, 1, 4, 1, 3, 3, 1, 4, 2]
def baseStart_2681712 : Nat := 118140960795 + 2681712 * 2 ^ 59
def prefixEnd_2681712 : Nat := 4983230072969 + 3 ^ 40 * 2681712 * 2
def baseEnd_2681712 : Nat := 1377007232930117023167037

theorem tailTrace_2681712 : CollatzResearch.WordTrace tailWord_2681712 prefixEnd_2681712 1377007232930117023167037 := by
  unfold tailWord_2681712
  simp only [CollatzResearch.WordTrace]
  refine ⟨48905036030311449395735695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65206714707081932527647593 48905036030311449395735695)
  ·
    refine ⟨73357554045467174093603543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48905036030311449395735695 73357554045467174093603543)
    ·
      refine ⟨110036331068200761140405315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73357554045467174093603543 110036331068200761140405315)
      ·
        refine ⟨165054496602301141710607973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110036331068200761140405315 165054496602301141710607973)
        ·
          refine ⟨30947718112931464070738995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165054496602301141710607973 30947718112931464070738995)
          ·
            refine ⟨46421577169397196106108493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30947718112931464070738995 46421577169397196106108493)
            ·
              refine ⟨17408091438523948539790685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46421577169397196106108493 17408091438523948539790685)
              ·
                refine ⟨6528034289446480702421507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17408091438523948539790685 6528034289446480702421507)
                ·
                  refine ⟨9792051434169721053632261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6528034289446480702421507 9792051434169721053632261)
                  ·
                    refine ⟨1836009643906822697556049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9792051434169721053632261 1836009643906822697556049)
                    ·
                      refine ⟨1377007232930117023167037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1836009643906822697556049 1377007232930117023167037)
                      ·
                        rfl

theorem cell23_2681712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 1, 4, 2].length) (baseStart_2681712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2681712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2681712 prefixEnd_2681712 := by exact prefixLift 2681712
  have htrace : WordTrace (prefixWord ++ tailWord_2681712) baseStart_2681712 baseEnd_2681712 := by
    simpa [prefixWord, tailWord_2681712, baseEnd_2681712] using wordTrace_append hprefix tailTrace_2681712
  have hstable : (prefixWord ++ tailWord_2681712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681712).length < 2 ^ (prefixWord ++ tailWord_2681712).sum := by decide
  have hdescent : baseEnd_2681712 < baseStart_2681712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681815 : List Nat := [1, 1, 3, 2, 1, 1, 2, 2, 2, 4, 4]
def baseStart_2681815 : Nat := 118140960795 + 2681815 * 2 ^ 59
def prefixEnd_2681815 : Nat := 4983230072969 + 3 ^ 40 * 2681815 * 2
def baseEnd_2681815 : Nat := 1377060121437530120179063

theorem tailTrace_2681815 : CollatzResearch.WordTrace tailWord_2681815 prefixEnd_2681815 1377060121437530120179063 := by
  unfold tailWord_2681815
  simp only [CollatzResearch.WordTrace]
  refine ⟨97813828779249747382470899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65209219186166498254980599 97813828779249747382470899)
  ·
    refine ⟨146720743168874621073706349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97813828779249747382470899 146720743168874621073706349)
    ·
      refine ⟨55020278688327982902639881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146720743168874621073706349 55020278688327982902639881)
      ·
        refine ⟨41265209016245987176979911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55020278688327982902639881 41265209016245987176979911)
        ·
          refine ⟨61897813524368980765469867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41265209016245987176979911 61897813524368980765469867)
          ·
            refine ⟨92846720286553471148204801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61897813524368980765469867 92846720286553471148204801)
            ·
              refine ⟨69635040214915103361153601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92846720286553471148204801 69635040214915103361153601)
              ·
                refine ⟨52226280161186327520865201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69635040214915103361153601 52226280161186327520865201)
                ·
                  refine ⟨39169710120889745640648901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52226280161186327520865201 39169710120889745640648901)
                  ·
                    refine ⟨7344320647666827307621669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39169710120889745640648901 7344320647666827307621669)
                    ·
                      refine ⟨1377060121437530120179063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7344320647666827307621669 1377060121437530120179063)
                      ·
                        rfl

theorem cell23_2681815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_2681815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2681815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2681815 prefixEnd_2681815 := by exact prefixLift 2681815
  have htrace : WordTrace (prefixWord ++ tailWord_2681815) baseStart_2681815 baseEnd_2681815 := by
    simpa [prefixWord, tailWord_2681815, baseEnd_2681815] using wordTrace_append hprefix tailTrace_2681815
  have hstable : (prefixWord ++ tailWord_2681815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681815).length < 2 ^ (prefixWord ++ tailWord_2681815).sum := by decide
  have hdescent : baseEnd_2681815 < baseStart_2681815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681839 : List Nat := [1, 1, 2, 1, 4, 4, 2, 1, 2, 2, 3]
def baseStart_2681839 : Nat := 118140960795 + 2681839 * 2 ^ 59
def prefixEnd_2681839 : Nat := 4983230072969 + 3 ^ 40 * 2681839 * 2
def baseEnd_2681839 : Nat := 1377072444973238026278953

theorem tailTrace_2681839 : CollatzResearch.WordTrace tailWord_2681839 prefixEnd_2681839 1377072444973238026278953 := by
  unfold tailWord_2681839
  simp only [CollatzResearch.WordTrace]
  refine ⟨97814704131162799481344571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65209802754108532987563047 97814704131162799481344571)
  ·
    refine ⟨146722056196744199222016857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97814704131162799481344571 146722056196744199222016857)
    ·
      refine ⟨110041542147558149416512643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146722056196744199222016857 110041542147558149416512643)
      ·
        refine ⟨165062313221337224124768965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110041542147558149416512643 165062313221337224124768965)
        ·
          refine ⟨30949183729000729523394181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165062313221337224124768965 30949183729000729523394181)
          ·
            refine ⟨5802971949187636785636409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30949183729000729523394181 5802971949187636785636409)
            ·
              refine ⟨4352228961890727589227307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5802971949187636785636409 4352228961890727589227307)
              ·
                refine ⟨6528343442836091383840961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4352228961890727589227307 6528343442836091383840961)
                ·
                  refine ⟨4896257582127068537880721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6528343442836091383840961 4896257582127068537880721)
                  ·
                    refine ⟨3672193186595301403410541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4896257582127068537880721 3672193186595301403410541)
                    ·
                      refine ⟨1377072444973238026278953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3672193186595301403410541 1377072444973238026278953)
                      ·
                        rfl

theorem cell23_2681839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 2, 2, 3].length) (baseStart_2681839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2681839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2681839 prefixEnd_2681839 := by exact prefixLift 2681839
  have htrace : WordTrace (prefixWord ++ tailWord_2681839) baseStart_2681839 baseEnd_2681839 := by
    simpa [prefixWord, tailWord_2681839, baseEnd_2681839] using wordTrace_append hprefix tailTrace_2681839
  have hstable : (prefixWord ++ tailWord_2681839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681839).length < 2 ^ (prefixWord ++ tailWord_2681839).sum := by decide
  have hdescent : baseEnd_2681839 < baseStart_2681839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681865 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 2, 4, 5]
def baseStart_2681865 : Nat := 118140960795 + 2681865 * 2 ^ 59
def prefixEnd_2681865 : Nat := 4983230072969 + 3 ^ 40 * 2681865 * 2
def baseEnd_2681865 : Nat := 1377085795470254924553833

theorem tailTrace_2681865 : CollatzResearch.WordTrace tailWord_2681865 prefixEnd_2681865 1377085795470254924553833 := by
  unfold tailWord_2681865
  simp only [CollatzResearch.WordTrace]
  refine ⟨97815652429068605921791049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65210434952712403947860699 97815652429068605921791049)
  ·
    refine ⟨73361739321801454441343287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97815652429068605921791049 73361739321801454441343287)
    ·
      refine ⟨110042608982702181662014931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73361739321801454441343287 110042608982702181662014931)
      ·
        refine ⟨165063913474053272493022397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110042608982702181662014931 165063913474053272493022397)
        ·
          refine ⟨61898967552769977184883399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165063913474053272493022397 61898967552769977184883399)
          ·
            refine ⟨92848451329154965777325099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61898967552769977184883399 92848451329154965777325099)
            ·
              refine ⟨139272676993732448665987649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92848451329154965777325099 139272676993732448665987649)
              ·
                refine ⟨104454507745299336499490737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139272676993732448665987649 104454507745299336499490737)
                ·
                  refine ⟨78340880808974502374618053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104454507745299336499490737 78340880808974502374618053)
                  ·
                    refine ⟨14688915151682719195240885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 78340880808974502374618053 14688915151682719195240885)
                    ·
                      refine ⟨1377085795470254924553833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14688915151682719195240885 1377085795470254924553833)
                      ·
                        rfl

theorem cell23_2681865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 4, 5].length) (baseStart_2681865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2681865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2681865 prefixEnd_2681865 := by exact prefixLift 2681865
  have htrace : WordTrace (prefixWord ++ tailWord_2681865) baseStart_2681865 baseEnd_2681865 := by
    simpa [prefixWord, tailWord_2681865, baseEnd_2681865] using wordTrace_append hprefix tailTrace_2681865
  have hstable : (prefixWord ++ tailWord_2681865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681865).length < 2 ^ (prefixWord ++ tailWord_2681865).sum := by decide
  have hdescent : baseEnd_2681865 < baseStart_2681865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681977 : List Nat := [1, 2, 1, 3, 5, 1, 3, 2, 1, 2, 2]
def baseStart_2681977 : Nat := 118140960795 + 2681977 * 2 ^ 59
def prefixEnd_2681977 : Nat := 4983230072969 + 3 ^ 40 * 2681977 * 2
def baseEnd_2681977 : Nat := 1377143305303558486353319

theorem tailTrace_2681977 : CollatzResearch.WordTrace tailWord_2681977 prefixEnd_2681977 1377143305303558486353319 := by
  unfold tailWord_2681977
  simp only [CollatzResearch.WordTrace]
  refine ⟨97819737404662849049868185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65213158269775232699912123 97819737404662849049868185)
  ·
    refine ⟨73364803053497136787401139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97819737404662849049868185 73364803053497136787401139)
    ·
      refine ⟨110047204580245705181101709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73364803053497136787401139 110047204580245705181101709)
      ·
        refine ⟨41267701717592139442913141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110047204580245705181101709 41267701717592139442913141)
        ·
          refine ⟨3868847036024263072773107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41267701717592139442913141 3868847036024263072773107)
          ·
            refine ⟨5803270554036394609159661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3868847036024263072773107 5803270554036394609159661)
            ·
              refine ⟨2176226457763647978434873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5803270554036394609159661 2176226457763647978434873)
              ·
                refine ⟨1632169843322735983826155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2176226457763647978434873 1632169843322735983826155)
                ·
                  refine ⟨2448254764984103975739233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1632169843322735983826155 2448254764984103975739233)
                  ·
                    refine ⟨1836191073738077981804425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2448254764984103975739233 1836191073738077981804425)
                    ·
                      refine ⟨1377143305303558486353319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1836191073738077981804425 1377143305303558486353319)
                      ·
                        rfl

theorem cell23_2681977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 2, 1, 2, 2].length) (baseStart_2681977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2681977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2681977 prefixEnd_2681977 := by exact prefixLift 2681977
  have htrace : WordTrace (prefixWord ++ tailWord_2681977) baseStart_2681977 baseEnd_2681977 := by
    simpa [prefixWord, tailWord_2681977, baseEnd_2681977] using wordTrace_append hprefix tailTrace_2681977
  have hstable : (prefixWord ++ tailWord_2681977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681977).length < 2 ^ (prefixWord ++ tailWord_2681977).sum := by decide
  have hdescent : baseEnd_2681977 < baseStart_2681977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2681993 : List Nat := [1, 2, 1, 1, 4, 3, 4, 1, 2, 1, 3]
def baseStart_2681993 : Nat := 118140960795 + 2681993 * 2 ^ 59
def prefixEnd_2681993 : Nat := 4983230072969 + 3 ^ 40 * 2681993 * 2
def baseEnd_2681993 : Nat := 1377151520994030423753245

theorem tailTrace_2681993 : CollatzResearch.WordTrace tailWord_2681993 prefixEnd_2681993 1377151520994030423753245 := by
  unfold tailWord_2681993
  simp only [CollatzResearch.WordTrace]
  refine ⟨97820320972604883782450633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65213547315069922521633755 97820320972604883782450633)
  ·
    refine ⟨73365240729453662836837975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97820320972604883782450633 73365240729453662836837975)
    ·
      refine ⟨110047861094180494255256963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73365240729453662836837975 110047861094180494255256963)
      ·
        refine ⟨165071791641270741382885445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110047861094180494255256963 165071791641270741382885445)
        ·
          refine ⟨30950960932738264009291021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165071791641270741382885445 30950960932738264009291021)
          ·
            refine ⟨11606610349776849003484133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30950960932738264009291021 11606610349776849003484133)
            ·
              refine ⟨2176239440583159188153275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11606610349776849003484133 2176239440583159188153275)
              ·
                refine ⟨3264359160874738782229913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2176239440583159188153275 3264359160874738782229913)
                ·
                  refine ⟨2448269370656054086672435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3264359160874738782229913 2448269370656054086672435)
                  ·
                    refine ⟨3672404055984081130008653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2448269370656054086672435 3672404055984081130008653)
                    ·
                      refine ⟨1377151520994030423753245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3672404055984081130008653 1377151520994030423753245)
                      ·
                        rfl

theorem cell23_2681993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 1, 2, 1, 3].length) (baseStart_2681993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2681993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2681993 prefixEnd_2681993 := by exact prefixLift 2681993
  have htrace : WordTrace (prefixWord ++ tailWord_2681993) baseStart_2681993 baseEnd_2681993 := by
    simpa [prefixWord, tailWord_2681993, baseEnd_2681993] using wordTrace_append hprefix tailTrace_2681993
  have hstable : (prefixWord ++ tailWord_2681993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2681993).length < 2 ^ (prefixWord ++ tailWord_2681993).sum := by decide
  have hdescent : baseEnd_2681993 < baseStart_2681993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2681993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682016 : List Nat := [2, 1, 1, 4, 2, 1, 3, 2, 1, 4, 2]
def baseStart_2682016 : Nat := 118140960795 + 2682016 * 2 ^ 59
def prefixEnd_2682016 : Nat := 4983230072969 + 3 ^ 40 * 2682016 * 2
def baseEnd_2682016 : Nat := 1377163331049083833765639

theorem tailTrace_2682016 : CollatzResearch.WordTrace tailWord_2682016 prefixEnd_2682016 1377163331049083833765639 := by
  unfold tailWord_2682016
  simp only [CollatzResearch.WordTrace]
  refine ⟨48910579925760779355268951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65214106567681039140358601 48910579925760779355268951)
  ·
    refine ⟨73365869888641169032903427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48910579925760779355268951 73365869888641169032903427)
    ·
      refine ⟨110048804832961753549355141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73365869888641169032903427 110048804832961753549355141)
      ·
        refine ⟨20634150906180328790504089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110048804832961753549355141 20634150906180328790504089)
        ·
          refine ⟨15475613179635246592878067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20634150906180328790504089 15475613179635246592878067)
          ·
            refine ⟨23213419769452869889317101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15475613179635246592878067 23213419769452869889317101)
            ·
              refine ⟨8705032413544826208493913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23213419769452869889317101 8705032413544826208493913)
              ·
                refine ⟨6528774310158619656370435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8705032413544826208493913 6528774310158619656370435)
                ·
                  refine ⟨9793161465237929484555653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6528774310158619656370435 9793161465237929484555653)
                  ·
                    refine ⟨1836217774732111778354185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9793161465237929484555653 1836217774732111778354185)
                    ·
                      refine ⟨1377163331049083833765639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1836217774732111778354185 1377163331049083833765639)
                      ·
                        rfl

theorem cell23_2682016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 1, 4, 2].length) (baseStart_2682016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2682016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2682016 prefixEnd_2682016 := by exact prefixLift 2682016
  have htrace : WordTrace (prefixWord ++ tailWord_2682016) baseStart_2682016 baseEnd_2682016 := by
    simpa [prefixWord, tailWord_2682016, baseEnd_2682016] using wordTrace_append hprefix tailTrace_2682016
  have hstable : (prefixWord ++ tailWord_2682016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682016).length < 2 ^ (prefixWord ++ tailWord_2682016).sum := by decide
  have hdescent : baseEnd_2682016 < baseStart_2682016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682020 : List Nat := [2, 3, 1, 2, 3, 2, 3, 1, 1, 3, 2]
def baseStart_2682020 : Nat := 118140960795 + 2682020 * 2 ^ 59
def prefixEnd_2682020 : Nat := 4983230072969 + 3 ^ 40 * 2682020 * 2
def baseEnd_2682020 : Nat := 1377165384971701818115621

theorem tailTrace_2682020 : CollatzResearch.WordTrace tailWord_2682020 prefixEnd_2682020 1377165384971701818115621 := by
  unfold tailWord_2682020
  simp only [CollatzResearch.WordTrace]
  refine ⟨48910652871753533696841757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65214203829004711595789009 48910652871753533696841757)
  ·
    refine ⟨18341494826907575136315659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48910652871753533696841757 18341494826907575136315659)
    ·
      refine ⟨27512242240361362704473489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18341494826907575136315659 27512242240361362704473489)
      ·
        refine ⟨20634181680271022028355117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27512242240361362704473489 20634181680271022028355117)
        ·
          refine ⟨7737818130101633260633169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20634181680271022028355117 7737818130101633260633169)
          ·
            refine ⟨5803363597576224945474877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7737818130101633260633169 5803363597576224945474877)
            ·
              refine ⟨2176261349091084354553079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5803363597576224945474877 2176261349091084354553079)
              ·
                refine ⟨3264392023636626531829619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2176261349091084354553079 3264392023636626531829619)
                ·
                  refine ⟨4896588035454939797744429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3264392023636626531829619 4896588035454939797744429)
                  ·
                    refine ⟨1836220513295602424154161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4896588035454939797744429 1836220513295602424154161)
                    ·
                      refine ⟨1377165384971701818115621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1836220513295602424154161 1377165384971701818115621)
                      ·
                        rfl

theorem cell23_2682020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 1, 1, 3, 2].length) (baseStart_2682020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2682020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2682020 prefixEnd_2682020 := by exact prefixLift 2682020
  have htrace : WordTrace (prefixWord ++ tailWord_2682020) baseStart_2682020 baseEnd_2682020 := by
    simpa [prefixWord, tailWord_2682020, baseEnd_2682020] using wordTrace_append hprefix tailTrace_2682020
  have hstable : (prefixWord ++ tailWord_2682020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682020).length < 2 ^ (prefixWord ++ tailWord_2682020).sum := by decide
  have hdescent : baseEnd_2682020 < baseStart_2682020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682042 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 2, 1, 8]
def baseStart_2682042 : Nat := 118140960795 + 2682042 * 2 ^ 59
def prefixEnd_2682042 : Nat := 4983230072969 + 3 ^ 40 * 2682042 * 2
def baseEnd_2682042 : Nat := 1377176681546100732040519

theorem tailTrace_2682042 : CollatzResearch.WordTrace tailWord_2682042 prefixEnd_2682042 1377176681546100732040519 := by
  unfold tailWord_2682042
  simp only [CollatzResearch.WordTrace]
  refine ⟨24455527037356841287746095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65214738766284910100656253 24455527037356841287746095)
  ·
    refine ⟨36683290556035261931619143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24455527037356841287746095 36683290556035261931619143)
    ·
      refine ⟨55024935834052892897428715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36683290556035261931619143 55024935834052892897428715)
      ·
        refine ⟨82537403751079339346143073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55024935834052892897428715 82537403751079339346143073)
        ·
          refine ⟨61903052813309504509607305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82537403751079339346143073 61903052813309504509607305)
          ·
            refine ⟨46427289609982128382205479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61903052813309504509607305 46427289609982128382205479)
            ·
              refine ⟨69640934414973192573308219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46427289609982128382205479 69640934414973192573308219)
              ·
                refine ⟨104461401622459788859962329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69640934414973192573308219 104461401622459788859962329)
                ·
                  refine ⟨78346051216844841644971747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104461401622459788859962329 78346051216844841644971747)
                  ·
                    refine ⟨117519076825267262467457621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 78346051216844841644971747 117519076825267262467457621)
                    ·
                      refine ⟨1377176681546100732040519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 117519076825267262467457621 1377176681546100732040519)
                      ·
                        rfl

theorem cell23_2682042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 2, 1, 8].length) (baseStart_2682042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2682042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2682042 prefixEnd_2682042 := by exact prefixLift 2682042
  have htrace : WordTrace (prefixWord ++ tailWord_2682042) baseStart_2682042 baseEnd_2682042 := by
    simpa [prefixWord, tailWord_2682042, baseEnd_2682042] using wordTrace_append hprefix tailTrace_2682042
  have hstable : (prefixWord ++ tailWord_2682042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682042).length < 2 ^ (prefixWord ++ tailWord_2682042).sum := by decide
  have hdescent : baseEnd_2682042 < baseStart_2682042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682046 : List Nat := [4, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4]
def baseStart_2682046 : Nat := 118140960795 + 2682046 * 2 ^ 59
def prefixEnd_2682046 : Nat := 4983230072969 + 3 ^ 40 * 2682046 * 2
def baseEnd_2682046 : Nat := 1377178735468718716390501

theorem tailTrace_2682046 : CollatzResearch.WordTrace tailWord_2682046 prefixEnd_2682046 1377178735468718716390501 := by
  unfold tailWord_2682046
  simp only [CollatzResearch.WordTrace]
  refine ⟨12227781755176609229266249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65214836027608582556086661 12227781755176609229266249)
  ·
    refine ⟨9170836316382456921949687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12227781755176609229266249 9170836316382456921949687)
    ·
      refine ⟨13756254474573685382924531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9170836316382456921949687 13756254474573685382924531)
      ·
        refine ⟨20634381711860528074386797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13756254474573685382924531 20634381711860528074386797)
        ·
          refine ⟨7737893141947698027895049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20634381711860528074386797 7737893141947698027895049)
          ·
            refine ⟨5803419856460773520921287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7737893141947698027895049 5803419856460773520921287)
            ·
              refine ⟨8705129784691160281381931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5803419856460773520921287 8705129784691160281381931)
              ·
                refine ⟨13057694677036740422072897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8705129784691160281381931 13057694677036740422072897)
                ·
                  refine ⟨9793271007777555316554673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13057694677036740422072897 9793271007777555316554673)
                  ·
                    refine ⟨7344953255833166487416005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9793271007777555316554673 7344953255833166487416005)
                    ·
                      refine ⟨1377178735468718716390501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7344953255833166487416005 1377178735468718716390501)
                      ·
                        rfl

theorem cell23_2682046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_2682046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2682046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2682046 prefixEnd_2682046 := by exact prefixLift 2682046
  have htrace : WordTrace (prefixWord ++ tailWord_2682046) baseStart_2682046 baseEnd_2682046 := by
    simpa [prefixWord, tailWord_2682046, baseEnd_2682046] using wordTrace_append hprefix tailTrace_2682046
  have hstable : (prefixWord ++ tailWord_2682046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682046).length < 2 ^ (prefixWord ++ tailWord_2682046).sum := by decide
  have hdescent : baseEnd_2682046 < baseStart_2682046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682106 : List Nat := [3, 1, 1, 1, 1, 4, 1, 3, 2, 4, 2]
def baseStart_2682106 : Nat := 118140960795 + 2682106 * 2 ^ 59
def prefixEnd_2682106 : Nat := 4983230072969 + 3 ^ 40 * 2682106 * 2
def baseEnd_2682106 : Nat := 1377209544307988481640225

theorem tailTrace_2682106 : CollatzResearch.WordTrace tailWord_2682106 prefixEnd_2682106 1377209544307988481640225 := by
  unfold tailWord_2682106
  simp only [CollatzResearch.WordTrace]
  refine ⟨24456110605298876020328543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65216294947463669387542781 24456110605298876020328543)
  ·
    refine ⟨36684165907948314030492815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24456110605298876020328543 36684165907948314030492815)
    ·
      refine ⟨55026248861922471045739223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36684165907948314030492815 55026248861922471045739223)
      ·
        refine ⟨82539373292883706568608835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55026248861922471045739223 82539373292883706568608835)
        ·
          refine ⟨123809059939325559852913253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82539373292883706568608835 123809059939325559852913253)
          ·
            refine ⟨23214198738623542472421235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123809059939325559852913253 23214198738623542472421235)
            ·
              refine ⟨34821298107935313708631853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23214198738623542472421235 34821298107935313708631853)
              ·
                refine ⟨13057986790475742640736945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34821298107935313708631853 13057986790475742640736945)
                ·
                  refine ⟨9793490092856806980552709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13057986790475742640736945 9793490092856806980552709)
                  ·
                    refine ⟨1836279392410651308853633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9793490092856806980552709 1836279392410651308853633)
                    ·
                      refine ⟨1377209544307988481640225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1836279392410651308853633 1377209544307988481640225)
                      ·
                        rfl

theorem cell23_2682106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 2, 4, 2].length) (baseStart_2682106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2682106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2682106 prefixEnd_2682106 := by exact prefixLift 2682106
  have htrace : WordTrace (prefixWord ++ tailWord_2682106) baseStart_2682106 baseEnd_2682106 := by
    simpa [prefixWord, tailWord_2682106, baseEnd_2682106] using wordTrace_append hprefix tailTrace_2682106
  have hstable : (prefixWord ++ tailWord_2682106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682106).length < 2 ^ (prefixWord ++ tailWord_2682106).sum := by decide
  have hdescent : baseEnd_2682106 < baseStart_2682106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682126 : List Nat := [4, 1, 1, 2, 1, 3, 2, 1, 1, 4, 3]
def baseStart_2682126 : Nat := 118140960795 + 2682126 * 2 ^ 59
def prefixEnd_2682126 : Nat := 4983230072969 + 3 ^ 40 * 2682126 * 2
def baseEnd_2682126 : Nat := 1377219813921078403390133

theorem tailTrace_2682126 : CollatzResearch.WordTrace tailWord_2682126 prefixEnd_2682126 1377219813921078403390133 := by
  unfold tailWord_2682126
  simp only [CollatzResearch.WordTrace]
  refine ⟨12228146485140380937130279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65216781254082031664694821 12228146485140380937130279)
  ·
    refine ⟨18342219727710571405695419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12228146485140380937130279 18342219727710571405695419)
    ·
      refine ⟨27513329591565857108543129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18342219727710571405695419 27513329591565857108543129)
      ·
        refine ⟨20634997193674392831407347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27513329591565857108543129 20634997193674392831407347)
        ·
          refine ⟨30952495790511589247111021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20634997193674392831407347 30952495790511589247111021)
          ·
            refine ⟨11607185921441845967666633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30952495790511589247111021 11607185921441845967666633)
            ·
              refine ⟨8705389441081384475749975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11607185921441845967666633 8705389441081384475749975)
              ·
                refine ⟨13058084161622076713624963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8705389441081384475749975 13058084161622076713624963)
                ·
                  refine ⟨19587126242433115070437445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13058084161622076713624963 19587126242433115070437445)
                  ·
                    refine ⟨3672586170456209075707021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19587126242433115070437445 3672586170456209075707021)
                    ·
                      refine ⟨1377219813921078403390133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3672586170456209075707021 1377219813921078403390133)
                      ·
                        rfl

theorem cell23_2682126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_2682126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2682126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2682126 prefixEnd_2682126 := by exact prefixLift 2682126
  have htrace : WordTrace (prefixWord ++ tailWord_2682126) baseStart_2682126 baseEnd_2682126 := by
    simpa [prefixWord, tailWord_2682126, baseEnd_2682126] using wordTrace_append hprefix tailTrace_2682126
  have hstable : (prefixWord ++ tailWord_2682126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682126).length < 2 ^ (prefixWord ++ tailWord_2682126).sum := by decide
  have hdescent : baseEnd_2682126 < baseStart_2682126 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682143 : List Nat := [1, 1, 2, 4, 4, 1, 1, 2, 2, 2, 3]
def baseStart_2682143 : Nat := 118140960795 + 2682143 * 2 ^ 59
def prefixEnd_2682143 : Nat := 4983230072969 + 3 ^ 40 * 2682143 * 2
def baseEnd_2682143 : Nat := 1377228543092204836877555

theorem tailTrace_2682143 : CollatzResearch.WordTrace tailWord_2682143 prefixEnd_2682143 1377228543092204836877555 := by
  unfold tailWord_2682143
  simp only [CollatzResearch.WordTrace]
  refine ⟨97825791922061459400411083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65217194614707639600274055 97825791922061459400411083)
  ·
    refine ⟨146738687883092189100616625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97825791922061459400411083 146738687883092189100616625)
    ·
      refine ⟨110054015912319141825462469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146738687883092189100616625 110054015912319141825462469)
      ·
        refine ⟨20635127983559839092274213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110054015912319141825462469 20635127983559839092274213)
        ·
          refine ⟨3869086496917469829801415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20635127983559839092274213 3869086496917469829801415)
          ·
            refine ⟨5803629745376204744702123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3869086496917469829801415 5803629745376204744702123)
            ·
              refine ⟨8705444618064307117053185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5803629745376204744702123 8705444618064307117053185)
              ·
                refine ⟨6529083463548230337789889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8705444618064307117053185 6529083463548230337789889)
                ·
                  refine ⟨4896812597661172753342417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6529083463548230337789889 4896812597661172753342417)
                  ·
                    refine ⟨3672609448245879565006813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4896812597661172753342417 3672609448245879565006813)
                    ·
                      refine ⟨1377228543092204836877555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3672609448245879565006813 1377228543092204836877555)
                      ·
                        rfl

theorem cell23_2682143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_2682143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2682143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2682143 prefixEnd_2682143 := by exact prefixLift 2682143
  have htrace : WordTrace (prefixWord ++ tailWord_2682143) baseStart_2682143 baseEnd_2682143 := by
    simpa [prefixWord, tailWord_2682143, baseEnd_2682143] using wordTrace_append hprefix tailTrace_2682143
  have hstable : (prefixWord ++ tailWord_2682143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682143).length < 2 ^ (prefixWord ++ tailWord_2682143).sum := by decide
  have hdescent : baseEnd_2682143 < baseStart_2682143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682159 : List Nat := [1, 1, 2, 1, 2, 1, 3, 4, 3, 5]
def baseStart_2682159 : Nat := 118140960795 + 2682159 * 2 ^ 59
def prefixEnd_2682159 : Nat := 4983230072969 + 3 ^ 40 * 2682159 * 2
def baseEnd_2682159 : Nat := 459078919594225591425827

theorem tailTrace_2682159 : CollatzResearch.WordTrace tailWord_2682159 prefixEnd_2682159 459078919594225591425827 := by
  unfold tailWord_2682159
  simp only [CollatzResearch.WordTrace]
  refine ⟨97826375490003494132993531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65217583660002329421995687 97826375490003494132993531)
  ·
    refine ⟨146739563235005241199490297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97826375490003494132993531 146739563235005241199490297)
    ·
      refine ⟨110054672426253930899617723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146739563235005241199490297 110054672426253930899617723)
      ·
        refine ⟨165082008639380896349426585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110054672426253930899617723 165082008639380896349426585)
        ·
          refine ⟨123811506479535672262069939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165082008639380896349426585 123811506479535672262069939)
          ·
            refine ⟨185717259719303508393104909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123811506479535672262069939 185717259719303508393104909)
            ·
              refine ⟨69643972394738815647414341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 185717259719303508393104909 69643972394738815647414341)
              ·
                refine ⟨13058244824013527933890189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69643972394738815647414341 13058244824013527933890189)
                ·
                  refine ⟨4896841809005072975208821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13058244824013527933890189 4896841809005072975208821)
                  ·
                    refine ⟨459078919594225591425827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4896841809005072975208821 459078919594225591425827)
                    ·
                      rfl

theorem cell23_2682159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 3, 5].length) (baseStart_2682159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2682159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2682159 prefixEnd_2682159 := by exact prefixLift 2682159
  have htrace : WordTrace (prefixWord ++ tailWord_2682159) baseStart_2682159 baseEnd_2682159 := by
    simpa [prefixWord, tailWord_2682159, baseEnd_2682159] using wordTrace_append hprefix tailTrace_2682159
  have hstable : (prefixWord ++ tailWord_2682159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682159).length < 2 ^ (prefixWord ++ tailWord_2682159).sum := by decide
  have hdescent : baseEnd_2682159 < baseStart_2682159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682163 : List Nat := [1, 1, 1, 2, 5, 4, 2, 1, 6]
def baseStart_2682163 : Nat := 118140960795 + 2682163 * 2 ^ 59
def prefixEnd_2682163 : Nat := 4983230072969 + 3 ^ 40 * 2682163 * 2
def baseEnd_2682163 : Nat := 153026534745032750958607

theorem tailTrace_2682163 : CollatzResearch.WordTrace tailWord_2682163 prefixEnd_2682163 153026534745032750958607 := by
  unfold tailWord_2682163
  simp only [CollatzResearch.WordTrace]
  refine ⟨97826521381989002816139143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65217680921326001877426095 97826521381989002816139143)
  ·
    refine ⟨146739782072983504224208715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97826521381989002816139143 146739782072983504224208715)
    ·
      refine ⟨220109673109475256336313073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146739782072983504224208715 220109673109475256336313073)
      ·
        refine ⟨165082254832106442252234805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220109673109475256336313073 165082254832106442252234805)
        ·
          refine ⟨15476461390509978961147013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 165082254832106442252234805 15476461390509978961147013)
          ·
            refine ⟨2901836510720621055215065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15476461390509978961147013 2901836510720621055215065)
            ·
              refine ⟨2176377383040465791411299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2901836510720621055215065 2176377383040465791411299)
              ·
                refine ⟨3264566074560698687116949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2176377383040465791411299 3264566074560698687116949)
                ·
                  refine ⟨153026534745032750958607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3264566074560698687116949 153026534745032750958607)
                  ·
                    rfl

theorem cell23_2682163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 1, 6].length) (baseStart_2682163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2682163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2682163 prefixEnd_2682163 := by exact prefixLift 2682163
  have htrace : WordTrace (prefixWord ++ tailWord_2682163) baseStart_2682163 baseEnd_2682163 := by
    simpa [prefixWord, tailWord_2682163, baseEnd_2682163] using wordTrace_append hprefix tailTrace_2682163
  have hstable : (prefixWord ++ tailWord_2682163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682163).length < 2 ^ (prefixWord ++ tailWord_2682163).sum := by decide
  have hdescent : baseEnd_2682163 < baseStart_2682163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682183 : List Nat := [1, 1, 4, 1, 2, 3, 1, 3, 2, 3, 2]
def baseStart_2682183 : Nat := 118140960795 + 2682183 * 2 ^ 59
def prefixEnd_2682183 : Nat := 4983230072969 + 3 ^ 40 * 2682183 * 2
def baseEnd_2682183 : Nat := 1377249082318384680377371

theorem tailTrace_2682183 : CollatzResearch.WordTrace tailWord_2682183 prefixEnd_2682183 1377249082318384680377371 := by
  unfold tailWord_2682183
  simp only [CollatzResearch.WordTrace]
  refine ⟨97827250841916546231867203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65218167227944364154578135 97827250841916546231867203)
  ·
    refine ⟨146740876262874819347800805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97827250841916546231867203 146740876262874819347800805)
    ·
      refine ⟨27513914299289028627712651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146740876262874819347800805 27513914299289028627712651)
      ·
        refine ⟨41270871448933542941568977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27513914299289028627712651 41270871448933542941568977)
        ·
          refine ⟨30953153586700157206176733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41270871448933542941568977 30953153586700157206176733)
          ·
            refine ⟨11607432595012558952316275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30953153586700157206176733 11607432595012558952316275)
            ·
              refine ⟨17411148892518838428474413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11607432595012558952316275 17411148892518838428474413)
              ·
                refine ⟨6529180834694564410677905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17411148892518838428474413 6529180834694564410677905)
                ·
                  refine ⟨4896885626020923308008429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6529180834694564410677905 4896885626020923308008429)
                  ·
                    refine ⟨1836332109757846240503161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4896885626020923308008429 1836332109757846240503161)
                    ·
                      refine ⟨1377249082318384680377371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1836332109757846240503161 1377249082318384680377371)
                      ·
                        rfl

theorem cell23_2682183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 2, 3, 2].length) (baseStart_2682183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2682183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2682183 prefixEnd_2682183 := by exact prefixLift 2682183
  have htrace : WordTrace (prefixWord ++ tailWord_2682183) baseStart_2682183 baseEnd_2682183 := by
    simpa [prefixWord, tailWord_2682183, baseEnd_2682183] using wordTrace_append hprefix tailTrace_2682183
  have hstable : (prefixWord ++ tailWord_2682183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682183).length < 2 ^ (prefixWord ++ tailWord_2682183).sum := by decide
  have hdescent : baseEnd_2682183 < baseStart_2682183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682190 : List Nat := [4, 1, 1, 1, 1, 1, 4, 5, 1, 1, 3]
def baseStart_2682190 : Nat := 118140960795 + 2682190 * 2 ^ 59
def prefixEnd_2682190 : Nat := 4983230072969 + 3 ^ 40 * 2682190 * 2
def baseEnd_2682190 : Nat := 1377252676682966152989839

theorem tailTrace_2682190 : CollatzResearch.WordTrace tailWord_2682190 prefixEnd_2682190 1377252676682966152989839 := by
  unfold tailWord_2682190
  simp only [CollatzResearch.WordTrace]
  refine ⟨12228438269111398303421503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65218337435260790951581349 12228438269111398303421503)
  ·
    refine ⟨18342657403667097455132255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12228438269111398303421503 18342657403667097455132255)
    ·
      refine ⟨27513986105500646182698383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18342657403667097455132255 27513986105500646182698383)
      ·
        refine ⟨41270979158250969274047575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27513986105500646182698383 41270979158250969274047575)
        ·
          refine ⟨61906468737376453911071363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41270979158250969274047575 61906468737376453911071363)
          ·
            refine ⟨92859703106064680866607045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61906468737376453911071363 92859703106064680866607045)
            ·
              refine ⟨17411194332387127662488821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92859703106064680866607045 17411194332387127662488821)
              ·
                refine ⟨1632299468661293218358327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17411194332387127662488821 1632299468661293218358327)
                ·
                  refine ⟨2448449202991939827537491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1632299468661293218358327 2448449202991939827537491)
                  ·
                    refine ⟨3672673804487909741306237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2448449202991939827537491 3672673804487909741306237)
                    ·
                      refine ⟨1377252676682966152989839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3672673804487909741306237 1377252676682966152989839)
                      ·
                        rfl

theorem cell23_2682190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 5, 1, 1, 3].length) (baseStart_2682190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2682190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2682190 prefixEnd_2682190 := by exact prefixLift 2682190
  have htrace : WordTrace (prefixWord ++ tailWord_2682190) baseStart_2682190 baseEnd_2682190 := by
    simpa [prefixWord, tailWord_2682190, baseEnd_2682190] using wordTrace_append hprefix tailTrace_2682190
  have hstable : (prefixWord ++ tailWord_2682190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682190).length < 2 ^ (prefixWord ++ tailWord_2682190).sum := by decide
  have hdescent : baseEnd_2682190 < baseStart_2682190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682193 : List Nat := [1, 2, 2, 1, 4, 1, 5, 1, 1, 5]
def baseStart_2682193 : Nat := 118140960795 + 2682193 * 2 ^ 59
def prefixEnd_2682193 : Nat := 4983230072969 + 3 ^ 40 * 2682193 * 2
def baseEnd_2682193 : Nat := 459084739041643213750775

theorem tailTrace_2682193 : CollatzResearch.WordTrace tailWord_2682193 prefixEnd_2682193 459084739041643213750775 := by
  unfold tailWord_2682193
  simp only [CollatzResearch.WordTrace]
  refine ⟨97827615571880317939731233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65218410381253545293154155 97827615571880317939731233)
  ·
    refine ⟨73370711678910238454798425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97827615571880317939731233 73370711678910238454798425)
    ·
      refine ⟨55028033759182678841098819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73370711678910238454798425 55028033759182678841098819)
      ·
        refine ⟨82542050638774018261648229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55028033759182678841098819 82542050638774018261648229)
        ·
          refine ⟨15476634494770128424059043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82542050638774018261648229 15476634494770128424059043)
          ·
            refine ⟨23214951742155192636088565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15476634494770128424059043 23214951742155192636088565)
            ·
              refine ⟨2176401725827049309633303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23214951742155192636088565 2176401725827049309633303)
              ·
                refine ⟨3264602588740573964449955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2176401725827049309633303 3264602588740573964449955)
                ·
                  refine ⟨4896903883110860946674933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3264602588740573964449955 4896903883110860946674933)
                  ·
                    refine ⟨459084739041643213750775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4896903883110860946674933 459084739041643213750775)
                    ·
                      rfl

theorem cell23_2682193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 1, 1, 5].length) (baseStart_2682193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2682193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2682193 prefixEnd_2682193 := by exact prefixLift 2682193
  have htrace : WordTrace (prefixWord ++ tailWord_2682193) baseStart_2682193 baseEnd_2682193 := by
    simpa [prefixWord, tailWord_2682193, baseEnd_2682193] using wordTrace_append hprefix tailTrace_2682193
  have hstable : (prefixWord ++ tailWord_2682193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682193).length < 2 ^ (prefixWord ++ tailWord_2682193).sum := by decide
  have hdescent : baseEnd_2682193 < baseStart_2682193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682209 : List Nat := [1, 2, 3, 1, 1, 1, 1, 3, 3, 1, 6]
def baseStart_2682209 : Nat := 118140960795 + 2682209 * 2 ^ 59
def prefixEnd_2682209 : Nat := 4983230072969 + 3 ^ 40 * 2682209 * 2
def baseEnd_2682209 : Nat := 1377262432815401578652251

theorem tailTrace_2682209 : CollatzResearch.WordTrace tailWord_2682209 prefixEnd_2682209 1377262432815401578652251 := by
  unfold tailWord_2682209
  simp only [CollatzResearch.WordTrace]
  refine ⟨97828199139822352672313681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65218799426548235114875787 97828199139822352672313681)
  ·
    refine ⟨73371149354866764504235261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97828199139822352672313681 73371149354866764504235261)
    ·
      refine ⟨27514181008075036689088223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73371149354866764504235261 27514181008075036689088223)
      ·
        refine ⟨41271271512112555033632335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27514181008075036689088223 41271271512112555033632335)
        ·
          refine ⟨61906907268168832550448503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41271271512112555033632335 61906907268168832550448503)
          ·
            refine ⟨92860360902253248825672755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61906907268168832550448503 92860360902253248825672755)
            ·
              refine ⟨139290541353379873238509133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92860360902253248825672755 139290541353379873238509133)
              ·
                refine ⟨52233953007517452464440925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139290541353379873238509133 52233953007517452464440925)
                ·
                  refine ⟨19587732377819044674165347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52233953007517452464440925 19587732377819044674165347)
                  ·
                    refine ⟨29381598566728567011248021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19587732377819044674165347 29381598566728567011248021)
                    ·
                      refine ⟨1377262432815401578652251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29381598566728567011248021 1377262432815401578652251)
                      ·
                        rfl

theorem cell23_2682209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_2682209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2682209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2682209 prefixEnd_2682209 := by exact prefixLift 2682209
  have htrace : WordTrace (prefixWord ++ tailWord_2682209) baseStart_2682209 baseEnd_2682209 := by
    simpa [prefixWord, tailWord_2682209, baseEnd_2682209] using wordTrace_append hprefix tailTrace_2682209
  have hstable : (prefixWord ++ tailWord_2682209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682209).length < 2 ^ (prefixWord ++ tailWord_2682209).sum := by decide
  have hdescent : baseEnd_2682209 < baseStart_2682209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682236 : List Nat := [2, 2, 2, 1, 1, 1, 7, 7]
def baseStart_2682236 : Nat := 118140960795 + 2682236 * 2 ^ 59
def prefixEnd_2682236 : Nat := 4983230072969 + 3 ^ 40 * 2682236 * 2
def baseEnd_2682236 : Nat := 51010233214558258259801

theorem tailTrace_2682236 : CollatzResearch.WordTrace tailWord_2682236 prefixEnd_2682236 51010233214558258259801 := by
  unfold tailWord_2682236
  simp only [CollatzResearch.WordTrace]
  refine ⟨48914591955362268141773281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65219455940483024189031041 48914591955362268141773281)
  ·
    refine ⟨36685943966521701106329961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48914591955362268141773281 36685943966521701106329961)
    ·
      refine ⟨27514457974891275829747471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36685943966521701106329961 27514457974891275829747471)
      ·
        refine ⟨41271686962336913744621207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27514457974891275829747471 41271686962336913744621207)
        ·
          refine ⟨61907530443505370616931811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41271686962336913744621207 61907530443505370616931811)
          ·
            refine ⟨92861295665258055925397717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61907530443505370616931811 92861295665258055925397717)
            ·
              refine ⟨2176436617154485685751509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 92861295665258055925397717 2176436617154485685751509)
              ·
                refine ⟨51010233214558258259801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2176436617154485685751509 51010233214558258259801)
                ·
                  rfl

theorem cell23_2682236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 7].length) (baseStart_2682236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2682236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2682236 prefixEnd_2682236 := by exact prefixLift 2682236
  have htrace : WordTrace (prefixWord ++ tailWord_2682236) baseStart_2682236 baseEnd_2682236 := by
    simpa [prefixWord, tailWord_2682236, baseEnd_2682236] using wordTrace_append hprefix tailTrace_2682236
  have hstable : (prefixWord ++ tailWord_2682236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682236).length < 2 ^ (prefixWord ++ tailWord_2682236).sum := by decide
  have hdescent : baseEnd_2682236 < baseStart_2682236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682247 : List Nat := [1, 1, 4, 2, 2, 2, 1, 5, 1, 2, 2]
def baseStart_2682247 : Nat := 118140960795 + 2682247 * 2 ^ 59
def prefixEnd_2682247 : Nat := 4983230072969 + 3 ^ 40 * 2682247 * 2
def baseEnd_2682247 : Nat := 1377281945080272429977077

theorem tailTrace_2682247 : CollatzResearch.WordTrace tailWord_2682247 prefixEnd_2682247 1377281945080272429977077 := by
  unfold tailWord_2682247
  simp only [CollatzResearch.WordTrace]
  refine ⟨97829585113684685162196995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65219723409123123441464663 97829585113684685162196995)
  ·
    refine ⟨146744377670527027743295493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97829585113684685162196995 146744377670527027743295493)
    ·
      refine ⟨27514570813223817701867905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146744377670527027743295493 27514570813223817701867905)
      ·
        refine ⟨20635928109917863276400929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27514570813223817701867905 20635928109917863276400929)
        ·
          refine ⟨15476946082438397457300697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20635928109917863276400929 15476946082438397457300697)
          ·
            refine ⟨11607709561828798092975523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15476946082438397457300697 11607709561828798092975523)
            ·
              refine ⟨17411564342743197139463285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11607709561828798092975523 17411564342743197139463285)
              ·
                refine ⟨1632334157132174731824683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17411564342743197139463285 1632334157132174731824683)
                ·
                  refine ⟨2448501235698262097737025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1632334157132174731824683 2448501235698262097737025)
                  ·
                    refine ⟨1836375926773696573302769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2448501235698262097737025 1836375926773696573302769)
                    ·
                      refine ⟨1377281945080272429977077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1836375926773696573302769 1377281945080272429977077)
                      ·
                        rfl

theorem cell23_2682247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 5, 1, 2, 2].length) (baseStart_2682247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2682247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2682247 prefixEnd_2682247 := by exact prefixLift 2682247
  have htrace : WordTrace (prefixWord ++ tailWord_2682247) baseStart_2682247 baseEnd_2682247 := by
    simpa [prefixWord, tailWord_2682247, baseEnd_2682247] using wordTrace_append hprefix tailTrace_2682247
  have hstable : (prefixWord ++ tailWord_2682247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682247).length < 2 ^ (prefixWord ++ tailWord_2682247).sum := by decide
  have hdescent : baseEnd_2682247 < baseStart_2682247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682303 : List Nat := [1, 1, 2, 2, 2, 1, 1, 6, 1, 4, 2]
def baseStart_2682303 : Nat := 118140960795 + 2682303 * 2 ^ 59
def prefixEnd_2682303 : Nat := 4983230072969 + 3 ^ 40 * 2682303 * 2
def baseEnd_2682303 : Nat := 1377310699996924210876819

theorem tailTrace_2682303 : CollatzResearch.WordTrace tailWord_2682303 prefixEnd_2682303 1377310699996924210876819 := by
  unfold tailWord_2682303
  simp only [CollatzResearch.WordTrace]
  refine ⟨97831627601481806726235563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65221085067654537817490375 97831627601481806726235563)
  ·
    refine ⟨146747441402222710089353345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97831627601481806726235563 146747441402222710089353345)
    ·
      refine ⟨110060581051667032567015009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146747441402222710089353345 110060581051667032567015009)
      ·
        refine ⟨82545435788750274425261257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110060581051667032567015009 82545435788750274425261257)
        ·
          refine ⟨61909076841562705818945943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82545435788750274425261257 61909076841562705818945943)
          ·
            refine ⟨92863615262344058728418915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61909076841562705818945943 92863615262344058728418915)
            ·
              refine ⟨139295422893516088092628373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92863615262344058728418915 139295422893516088092628373)
              ·
                refine ⟨6529472948133566629341955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 139295422893516088092628373 6529472948133566629341955)
                ·
                  refine ⟨9794209422200349944012933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6529472948133566629341955 9794209422200349944012933)
                  ·
                    refine ⟨1836414266662565614502425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9794209422200349944012933 1836414266662565614502425)
                    ·
                      refine ⟨1377310699996924210876819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1836414266662565614502425 1377310699996924210876819)
                      ·
                        rfl

theorem cell23_2682303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 4, 2].length) (baseStart_2682303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2682303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2682303 prefixEnd_2682303 := by exact prefixLift 2682303
  have htrace : WordTrace (prefixWord ++ tailWord_2682303) baseStart_2682303 baseEnd_2682303 := by
    simpa [prefixWord, tailWord_2682303, baseEnd_2682303] using wordTrace_append hprefix tailTrace_2682303
  have hstable : (prefixWord ++ tailWord_2682303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682303).length < 2 ^ (prefixWord ++ tailWord_2682303).sum := by decide
  have hdescent : baseEnd_2682303 < baseStart_2682303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682337 : List Nat := [1, 2, 3, 1, 2, 4, 1, 3, 2, 2, 2]
def baseStart_2682337 : Nat := 118140960795 + 2682337 * 2 ^ 59
def prefixEnd_2682337 : Nat := 4983230072969 + 3 ^ 40 * 2682337 * 2
def baseEnd_2682337 : Nat := 1377328158339177077851663

theorem tailTrace_2682337 : CollatzResearch.WordTrace tailWord_2682337 prefixEnd_2682337 1377328158339177077851663 := by
  unfold tailWord_2682337
  simp only [CollatzResearch.WordTrace]
  refine ⟨97832867683358630532973265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65221911788905753688648843 97832867683358630532973265)
  ·
    refine ⟨73374650762518972899729949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97832867683358630532973265 73374650762518972899729949)
    ·
      refine ⟨27515494035944614837398731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73374650762518972899729949 27515494035944614837398731)
      ·
        refine ⟨41273241053916922256098097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27515494035944614837398731 41273241053916922256098097)
        ·
          refine ⟨30954930790437691692073573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41273241053916922256098097 30954930790437691692073573)
          ·
            refine ⟨5804049523207067192263795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30954930790437691692073573 5804049523207067192263795)
            ·
              refine ⟨8706074284810600788395693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5804049523207067192263795 8706074284810600788395693)
              ·
                refine ⟨3264777856803975295648385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8706074284810600788395693 3264777856803975295648385)
                ·
                  refine ⟨2448583392602981471736289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3264777856803975295648385 2448583392602981471736289)
                  ·
                    refine ⟨1836437544452236103802217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2448583392602981471736289 1836437544452236103802217)
                    ·
                      refine ⟨1377328158339177077851663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1836437544452236103802217 1377328158339177077851663)
                      ·
                        rfl

theorem cell23_2682337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 3, 2, 2, 2].length) (baseStart_2682337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2682337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2682337 prefixEnd_2682337 := by exact prefixLift 2682337
  have htrace : WordTrace (prefixWord ++ tailWord_2682337) baseStart_2682337 baseEnd_2682337 := by
    simpa [prefixWord, tailWord_2682337, baseEnd_2682337] using wordTrace_append hprefix tailTrace_2682337
  have hstable : (prefixWord ++ tailWord_2682337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682337).length < 2 ^ (prefixWord ++ tailWord_2682337).sum := by decide
  have hdescent : baseEnd_2682337 < baseStart_2682337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682410 : List Nat := [3, 1, 4, 1, 1, 1, 1, 2, 1, 6, 2]
def baseStart_2682410 : Nat := 118140960795 + 2682410 * 2 ^ 59
def prefixEnd_2682410 : Nat := 4983230072969 + 3 ^ 40 * 2682410 * 2
def baseEnd_2682410 : Nat := 1377365642426955292238827

theorem tailTrace_2682410 : CollatzResearch.WordTrace tailWord_2682410 prefixEnd_2682410 1377365642426955292238827 := by
  unfold tailWord_2682410
  simp only [CollatzResearch.WordTrace]
  refine ⟨24458882553023541000095171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65223686808062776000253789 24458882553023541000095171)
  ·
    refine ⟨36688323829535311500142757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24458882553023541000095171 36688323829535311500142757)
    ·
      refine ⟨6879060718037870906276767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36688323829535311500142757 6879060718037870906276767)
      ·
        refine ⟨10318591077056806359415151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6879060718037870906276767 10318591077056806359415151)
        ·
          refine ⟨15477886615585209539122727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10318591077056806359415151 15477886615585209539122727)
          ·
            refine ⟨23216829923377814308684091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15477886615585209539122727 23216829923377814308684091)
            ·
              refine ⟨34825244885066721463026137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23216829923377814308684091 34825244885066721463026137)
              ·
                refine ⟨26118933663800041097269603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34825244885066721463026137 26118933663800041097269603)
                ·
                  refine ⟨39178400495700061645904405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26118933663800041097269603 39178400495700061645904405)
                  ·
                    refine ⟨1836487523235940389651769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 39178400495700061645904405 1836487523235940389651769)
                    ·
                      refine ⟨1377365642426955292238827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1836487523235940389651769 1377365642426955292238827)
                      ·
                        rfl

theorem cell23_2682410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_2682410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2682410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2682410 prefixEnd_2682410 := by exact prefixLift 2682410
  have htrace : WordTrace (prefixWord ++ tailWord_2682410) baseStart_2682410 baseEnd_2682410 := by
    simpa [prefixWord, tailWord_2682410, baseEnd_2682410] using wordTrace_append hprefix tailTrace_2682410
  have hstable : (prefixWord ++ tailWord_2682410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682410).length < 2 ^ (prefixWord ++ tailWord_2682410).sum := by decide
  have hdescent : baseEnd_2682410 < baseStart_2682410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682416 : List Nat := [2, 1, 1, 1, 2, 3, 1, 4, 8]
def baseStart_2682416 : Nat := 118140960795 + 2682416 * 2 ^ 59
def prefixEnd_2682416 : Nat := 4983230072969 + 3 ^ 40 * 2682416 * 2
def baseEnd_2682416 : Nat := 153040969256764696529311

theorem tailTrace_2682416 : CollatzResearch.WordTrace tailWord_2682416 prefixEnd_2682416 153040969256764696529311 := by
  unfold tailWord_2682416
  simp only [CollatzResearch.WordTrace]
  refine ⟨48917874525036213512549551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65223832700048284683399401 48917874525036213512549551)
  ·
    refine ⟨73376811787554320268824327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48917874525036213512549551 73376811787554320268824327)
    ·
      refine ⟨110065217681331480403236491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73376811787554320268824327 110065217681331480403236491)
      ·
        refine ⟨165097826521997220604854737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110065217681331480403236491 165097826521997220604854737)
        ·
          refine ⟨123823369891497915453641053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165097826521997220604854737 123823369891497915453641053)
          ·
            refine ⟨46433763709311718295115395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123823369891497915453641053 46433763709311718295115395)
            ·
              refine ⟨69650645563967577442673093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46433763709311718295115395 69650645563967577442673093)
              ·
                refine ⟨13059496043243920770501205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69650645563967577442673093 13059496043243920770501205)
                ·
                  refine ⟨153040969256764696529311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13059496043243920770501205 153040969256764696529311)
                  ·
                    rfl

theorem cell23_2682416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 8].length) (baseStart_2682416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2682416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2682416 prefixEnd_2682416 := by exact prefixLift 2682416
  have htrace : WordTrace (prefixWord ++ tailWord_2682416) baseStart_2682416 baseEnd_2682416 := by
    simpa [prefixWord, tailWord_2682416, baseEnd_2682416] using wordTrace_append hprefix tailTrace_2682416
  have hstable : (prefixWord ++ tailWord_2682416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682416).length < 2 ^ (prefixWord ++ tailWord_2682416).sum := by decide
  have hdescent : baseEnd_2682416 < baseStart_2682416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682433 : List Nat := [1, 2, 5, 1, 1, 1, 3, 1, 8]
def baseStart_2682433 : Nat := 118140960795 + 2682433 * 2 ^ 59
def prefixEnd_2682433 : Nat := 4983230072969 + 3 ^ 40 * 2682433 * 2
def baseEnd_2682433 : Nat := 153041939164667633583469

theorem tailTrace_2682433 : CollatzResearch.WordTrace tailWord_2682433 prefixEnd_2682433 153041939164667633583469 := by
  unfold tailWord_2682433
  simp only [CollatzResearch.WordTrace]
  refine ⟨97836369091010838928467953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65224246060673892618978635 97836369091010838928467953)
  ·
    refine ⟨73377276818258129196350965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97836369091010838928467953 73377276818258129196350965)
    ·
      refine ⟨6879119701711699612157903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73377276818258129196350965 6879119701711699612157903)
      ·
        refine ⟨10318679552567549418236855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6879119701711699612157903 10318679552567549418236855)
        ·
          refine ⟨15478019328851324127355283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10318679552567549418236855 15478019328851324127355283)
          ·
            refine ⟨23217028993276986191032925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15478019328851324127355283 23217028993276986191032925)
            ·
              refine ⟨8706385872478869821637347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23217028993276986191032925 8706385872478869821637347)
              ·
                refine ⟨13059578808718304732456021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8706385872478869821637347 13059578808718304732456021)
                ·
                  refine ⟨153041939164667633583469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13059578808718304732456021 153041939164667633583469)
                  ·
                    rfl

theorem cell23_2682433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 8].length) (baseStart_2682433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2682433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2682433 prefixEnd_2682433 := by exact prefixLift 2682433
  have htrace : WordTrace (prefixWord ++ tailWord_2682433) baseStart_2682433 baseEnd_2682433 := by
    simpa [prefixWord, tailWord_2682433, baseEnd_2682433] using wordTrace_append hprefix tailTrace_2682433
  have hstable : (prefixWord ++ tailWord_2682433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682433).length < 2 ^ (prefixWord ++ tailWord_2682433).sum := by decide
  have hdescent : baseEnd_2682433 < baseStart_2682433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682480 : List Nat := [2, 1, 1, 1, 6, 1, 2, 3, 1, 5]
def baseStart_2682480 : Nat := 118140960795 + 2682480 * 2 ^ 59
def prefixEnd_2682480 : Nat := 4983230072969 + 3 ^ 40 * 2682480 * 2
def baseEnd_2682480 : Nat := 459133862024256672787835

theorem tailTrace_2682480 : CollatzResearch.WordTrace tailWord_2682480 prefixEnd_2682480 459133862024256672787835 := by
  unfold tailWord_2682480
  simp only [CollatzResearch.WordTrace]
  refine ⟨48919041660920282977714447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65225388881227043970285929 48919041660920282977714447)
  ·
    refine ⟨73378562491380424466571671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48919041660920282977714447 73378562491380424466571671)
    ·
      refine ⟨110067843737070636699857507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73378562491380424466571671 110067843737070636699857507)
      ·
        refine ⟨165101765605605955049786261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110067843737070636699857507 165101765605605955049786261)
        ·
          refine ⟨7739145262762779142958731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 165101765605605955049786261 7739145262762779142958731)
          ·
            refine ⟨11608717894144168714438097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7739145262762779142958731 11608717894144168714438097)
            ·
              refine ⟨8706538420608126535828573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11608717894144168714438097 8706538420608126535828573)
              ·
                refine ⟨3264951907728047450935715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8706538420608126535828573 3264951907728047450935715)
                ·
                  refine ⟨4897427861592071176403573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3264951907728047450935715 4897427861592071176403573)
                  ·
                    refine ⟨459133862024256672787835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4897427861592071176403573 459133862024256672787835)
                    ·
                      rfl

theorem cell23_2682480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 3, 1, 5].length) (baseStart_2682480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2682480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2682480 prefixEnd_2682480 := by exact prefixLift 2682480
  have htrace : WordTrace (prefixWord ++ tailWord_2682480) baseStart_2682480 baseEnd_2682480 := by
    simpa [prefixWord, tailWord_2682480, baseEnd_2682480] using wordTrace_append hprefix tailTrace_2682480
  have hstable : (prefixWord ++ tailWord_2682480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682480).length < 2 ^ (prefixWord ++ tailWord_2682480).sum := by decide
  have hdescent : baseEnd_2682480 < baseStart_2682480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682514 : List Nat := [3, 2, 3, 1, 3, 2, 1, 2, 1, 5]
def baseStart_2682514 : Nat := 118140960795 + 2682514 * 2 ^ 59
def prefixEnd_2682514 : Nat := 4983230072969 + 3 ^ 40 * 2682514 * 2
def baseEnd_2682514 : Nat := 459139681471674295112783

theorem tailTrace_2682514 : CollatzResearch.WordTrace tailWord_2682514 prefixEnd_2682514 459139681471674295112783 := by
  unfold tailWord_2682514
  simp only [CollatzResearch.WordTrace]
  refine ⟨24459830850929347440541649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65226215602478259841444397 24459830850929347440541649)
  ·
    refine ⟨18344873138197010580406237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24459830850929347440541649 18344873138197010580406237)
    ·
      refine ⟨6879327426823878967652339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18344873138197010580406237 6879327426823878967652339)
      ·
        refine ⟨10318991140235818451478509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6879327426823878967652339 10318991140235818451478509)
        ·
          refine ⟨3869621677588431919304441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10318991140235818451478509 3869621677588431919304441)
          ·
            refine ⟨2902216258191323939478331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3869621677588431919304441 2902216258191323939478331)
            ·
              refine ⟨4353324387286985909217497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2902216258191323939478331 4353324387286985909217497)
              ·
                refine ⟨3264993290465239431913123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4353324387286985909217497 3264993290465239431913123)
                ·
                  refine ⟨4897489935697859147869685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3264993290465239431913123 4897489935697859147869685)
                  ·
                    refine ⟨459139681471674295112783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4897489935697859147869685 459139681471674295112783)
                    ·
                      rfl

theorem cell23_2682514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_2682514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2682514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2682514 prefixEnd_2682514 := by exact prefixLift 2682514
  have htrace : WordTrace (prefixWord ++ tailWord_2682514) baseStart_2682514 baseEnd_2682514 := by
    simpa [prefixWord, tailWord_2682514, baseEnd_2682514] using wordTrace_append hprefix tailTrace_2682514
  have hstable : (prefixWord ++ tailWord_2682514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682514).length < 2 ^ (prefixWord ++ tailWord_2682514).sum := by decide
  have hdescent : baseEnd_2682514 < baseStart_2682514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682517 : List Nat := [1, 3, 2, 1, 1, 1, 1, 6, 3, 2, 2]
def baseStart_2682517 : Nat := 118140960795 + 2682517 * 2 ^ 59
def prefixEnd_2682517 : Nat := 4983230072969 + 3 ^ 40 * 2682517 * 2
def baseEnd_2682517 : Nat := 1377420584856986373600835

theorem tailTrace_2682517 : CollatzResearch.WordTrace tailWord_2682517 prefixEnd_2682517 1377420584856986373600835 := by
  unfold tailWord_2682517
  simp only [CollatzResearch.WordTrace]
  refine ⟨97839432822706521274525805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65226288548471014183017203 97839432822706521274525805)
  ·
    refine ⟨36689787308514945477947177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97839432822706521274525805 36689787308514945477947177)
    ·
      refine ⟨27517340481386209108460383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36689787308514945477947177 27517340481386209108460383)
      ·
        refine ⟨41276010722079313662690575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27517340481386209108460383 41276010722079313662690575)
        ·
          refine ⟨61914016083118970494035863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41276010722079313662690575 61914016083118970494035863)
          ·
            refine ⟨92871024124678455741053795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61914016083118970494035863 92871024124678455741053795)
            ·
              refine ⟨139306536187017683611580693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92871024124678455741053795 139306536187017683611580693)
              ·
                refine ⟨6529993883766453919292845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 139306536187017683611580693 6529993883766453919292845)
                ·
                  refine ⟨2448747706412420219734817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6529993883766453919292845 2448747706412420219734817)
                  ·
                    refine ⟨1836560779809315164801113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2448747706412420219734817 1836560779809315164801113)
                    ·
                      refine ⟨1377420584856986373600835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1836560779809315164801113 1377420584856986373600835)
                      ·
                        rfl

theorem cell23_2682517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 3, 2, 2].length) (baseStart_2682517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2682517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2682517 prefixEnd_2682517 := by exact prefixLift 2682517
  have htrace : WordTrace (prefixWord ++ tailWord_2682517) baseStart_2682517 baseEnd_2682517 := by
    simpa [prefixWord, tailWord_2682517, baseEnd_2682517] using wordTrace_append hprefix tailTrace_2682517
  have hstable : (prefixWord ++ tailWord_2682517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682517).length < 2 ^ (prefixWord ++ tailWord_2682517).sum := by decide
  have hdescent : baseEnd_2682517 < baseStart_2682517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682527 : List Nat := [1, 1, 2, 7, 1, 1, 1, 2, 1, 6]
def baseStart_2682527 : Nat := 118140960795 + 2682527 * 2 ^ 59
def prefixEnd_2682527 : Nat := 4983230072969 + 3 ^ 40 * 2682527 * 2
def baseEnd_2682527 : Nat := 459141906554510444825263

theorem tailTrace_2682527 : CollatzResearch.WordTrace tailWord_2682527 prefixEnd_2682527 459141906554510444825263 := by
  unfold tailWord_2682527
  simp only [CollatzResearch.WordTrace]
  refine ⟨97839797552670292982389835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65226531701780195321593223 97839797552670292982389835)
  ·
    refine ⟨146759696329005439473584753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97839797552670292982389835 146759696329005439473584753)
    ·
      refine ⟨110069772246754079605188565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146759696329005439473584753 110069772246754079605188565)
      ·
        refine ⟨2579760287033298740746607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 110069772246754079605188565 2579760287033298740746607)
        ·
          refine ⟨3869640430549948111119911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2579760287033298740746607 3869640430549948111119911)
          ·
            refine ⟨5804460645824922166679867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3869640430549948111119911 5804460645824922166679867)
            ·
              refine ⟨8706690968737383250019801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5804460645824922166679867 8706690968737383250019801)
              ·
                refine ⟨6530018226553037437514851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8706690968737383250019801 6530018226553037437514851)
                ·
                  refine ⟨9795027339829556156272277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6530018226553037437514851 9795027339829556156272277)
                  ·
                    refine ⟨459141906554510444825263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9795027339829556156272277 459141906554510444825263)
                    ·
                      rfl

theorem cell23_2682527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 6].length) (baseStart_2682527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2682527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2682527 prefixEnd_2682527 := by exact prefixLift 2682527
  have htrace : WordTrace (prefixWord ++ tailWord_2682527) baseStart_2682527 baseEnd_2682527 := by
    simpa [prefixWord, tailWord_2682527, baseEnd_2682527] using wordTrace_append hprefix tailTrace_2682527
  have hstable : (prefixWord ++ tailWord_2682527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682527).length < 2 ^ (prefixWord ++ tailWord_2682527).sum := by decide
  have hdescent : baseEnd_2682527 < baseStart_2682527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682551 : List Nat := [1, 1, 3, 1, 5, 2, 1, 4, 1, 2, 2]
def baseStart_2682551 : Nat := 118140960795 + 2682551 * 2 ^ 59
def prefixEnd_2682551 : Nat := 4983230072969 + 3 ^ 40 * 2682551 * 2
def baseEnd_2682551 : Nat := 1377438043199239240575679

theorem tailTrace_2682551 : CollatzResearch.WordTrace tailWord_2682551 prefixEnd_2682551 1377438043199239240575679 := by
  unfold tailWord_2682551
  simp only [CollatzResearch.WordTrace]
  refine ⟨97840672904583345081263507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65227115269722230054175671 97840672904583345081263507)
  ·
    refine ⟨146761009356875017621895261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97840672904583345081263507 146761009356875017621895261)
    ·
      refine ⟨55035378508828131608210723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146761009356875017621895261 55035378508828131608210723)
      ·
        refine ⟨82553067763242197412316085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55035378508828131608210723 82553067763242197412316085)
        ·
          refine ⟨7739350102803956007404633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82553067763242197412316085 7739350102803956007404633)
          ·
            refine ⟨5804512577102967005553475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7739350102803956007404633 5804512577102967005553475)
            ·
              refine ⟨8706768865654450508330213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5804512577102967005553475 8706768865654450508330213)
              ·
                refine ⟨1632519162310209470311915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8706768865654450508330213 1632519162310209470311915)
                ·
                  refine ⟨2448778743465314205467873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1632519162310209470311915 2448778743465314205467873)
                  ·
                    refine ⟨1836584057598985654100905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2448778743465314205467873 1836584057598985654100905)
                    ·
                      refine ⟨1377438043199239240575679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1836584057598985654100905 1377438043199239240575679)
                      ·
                        rfl

theorem cell23_2682551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 4, 1, 2, 2].length) (baseStart_2682551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2682551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2682551 prefixEnd_2682551 := by exact prefixLift 2682551
  have htrace : WordTrace (prefixWord ++ tailWord_2682551) baseStart_2682551 baseEnd_2682551 := by
    simpa [prefixWord, tailWord_2682551, baseEnd_2682551] using wordTrace_append hprefix tailTrace_2682551
  have hstable : (prefixWord ++ tailWord_2682551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682551).length < 2 ^ (prefixWord ++ tailWord_2682551).sum := by decide
  have hdescent : baseEnd_2682551 < baseStart_2682551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682553 : List Nat := [1, 2, 1, 4, 1, 1, 3, 1, 2, 7]
def baseStart_2682553 : Nat := 118140960795 + 2682553 * 2 ^ 59
def prefixEnd_2682553 : Nat := 4983230072969 + 3 ^ 40 * 2682553 * 2
def baseEnd_2682553 : Nat := 459146356720182744250223

theorem tailTrace_2682553 : CollatzResearch.WordTrace tailWord_2682553 prefixEnd_2682553 459146356720182744250223 := by
  unfold tailWord_2682553
  simp only [CollatzResearch.WordTrace]
  refine ⟨97840745850576099422836313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65227163900384066281890875 97840745850576099422836313)
  ·
    refine ⟨73380559387932074567127235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97840745850576099422836313 73380559387932074567127235)
    ·
      refine ⟨110070839081898111850690853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73380559387932074567127235 110070839081898111850690853)
      ·
        refine ⟨20638282327855895972004535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110070839081898111850690853 20638282327855895972004535)
        ·
          refine ⟨30957423491783843958006803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20638282327855895972004535 30957423491783843958006803)
          ·
            refine ⟨46436135237675765937010205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30957423491783843958006803 46436135237675765937010205)
            ·
              refine ⟨17413550714128412226378827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46436135237675765937010205 17413550714128412226378827)
              ·
                refine ⟨26120326071192618339568241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17413550714128412226378827 26120326071192618339568241)
                ·
                  refine ⟨19590244553394463754676181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26120326071192618339568241 19590244553394463754676181)
                  ·
                    refine ⟨459146356720182744250223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19590244553394463754676181 459146356720182744250223)
                    ·
                      rfl

theorem cell23_2682553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 7].length) (baseStart_2682553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2682553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2682553 prefixEnd_2682553 := by exact prefixLift 2682553
  have htrace : WordTrace (prefixWord ++ tailWord_2682553) baseStart_2682553 baseEnd_2682553 := by
    simpa [prefixWord, tailWord_2682553, baseEnd_2682553] using wordTrace_append hprefix tailTrace_2682553
  have hstable : (prefixWord ++ tailWord_2682553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682553).length < 2 ^ (prefixWord ++ tailWord_2682553).sum := by decide
  have hdescent : baseEnd_2682553 < baseStart_2682553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682567 : List Nat := [1, 1, 4, 1, 1, 1, 3, 5, 2, 1, 3]
def baseStart_2682567 : Nat := 118140960795 + 2682567 * 2 ^ 59
def prefixEnd_2682567 : Nat := 4983230072969 + 3 ^ 40 * 2682567 * 2
def baseEnd_2682567 : Nat := 1377446258889711177975605

theorem tailTrace_2682567 : CollatzResearch.WordTrace tailWord_2682567 prefixEnd_2682567 1377446258889711177975605 := by
  unfold tailWord_2682567
  simp only [CollatzResearch.WordTrace]
  refine ⟨97841256472525379813845955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65227504315016919875897303 97841256472525379813845955)
  ·
    refine ⟨146761884708788069720768933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97841256472525379813845955 146761884708788069720768933)
    ·
      refine ⟨27517853382897763072644175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146761884708788069720768933 27517853382897763072644175)
      ·
        refine ⟨41276780074346644608966263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27517853382897763072644175 41276780074346644608966263)
        ·
          refine ⟨61915170111519966913449395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41276780074346644608966263 61915170111519966913449395)
          ·
            refine ⟨92872755167279950370174093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61915170111519966913449395 92872755167279950370174093)
            ·
              refine ⟨34827283187729981388815285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92872755167279950370174093 34827283187729981388815285)
              ·
                refine ⟨3265057798849685755201433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34827283187729981388815285 3265057798849685755201433)
                ·
                  refine ⟨2448793349137264316401075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3265057798849685755201433 2448793349137264316401075)
                  ·
                    refine ⟨3673190023705896474601613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2448793349137264316401075 3673190023705896474601613)
                    ·
                      refine ⟨1377446258889711177975605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3673190023705896474601613 1377446258889711177975605)
                      ·
                        rfl

theorem cell23_2682567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 5, 2, 1, 3].length) (baseStart_2682567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2682567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2682567 prefixEnd_2682567 := by exact prefixLift 2682567
  have htrace : WordTrace (prefixWord ++ tailWord_2682567) baseStart_2682567 baseEnd_2682567 := by
    simpa [prefixWord, tailWord_2682567, baseEnd_2682567] using wordTrace_append hprefix tailTrace_2682567
  have hstable : (prefixWord ++ tailWord_2682567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682567).length < 2 ^ (prefixWord ++ tailWord_2682567).sum := by decide
  have hdescent : baseEnd_2682567 < baseStart_2682567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682577 : List Nat := [1, 2, 2, 1, 2, 4, 2, 1, 3, 3, 2]
def baseStart_2682577 : Nat := 118140960795 + 2682577 * 2 ^ 59
def prefixEnd_2682577 : Nat := 4983230072969 + 3 ^ 40 * 2682577 * 2
def baseEnd_2682577 : Nat := 1377451393696256138850559

theorem tailTrace_2682577 : CollatzResearch.WordTrace tailWord_2682577 prefixEnd_2682577 1377451393696256138850559 := by
  unfold tailWord_2682577
  simp only [CollatzResearch.WordTrace]
  refine ⟨97841621202489151521709985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65227747468326101014473323 97841621202489151521709985)
  ·
    refine ⟨73381215901866863641282489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97841621202489151521709985 73381215901866863641282489)
    ·
      refine ⟨55035911926400147730961867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73381215901866863641282489 55035911926400147730961867)
      ·
        refine ⟨82553867889600221596442801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55035911926400147730961867 82553867889600221596442801)
        ·
          refine ⟨61915400917200166197332101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82553867889600221596442801 61915400917200166197332101)
          ·
            refine ⟨11609137671975031161999769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61915400917200166197332101 11609137671975031161999769)
            ·
              refine ⟨8706853253981273371499827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11609137671975031161999769 8706853253981273371499827)
              ·
                refine ⟨13060279880971910057249741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8706853253981273371499827 13060279880971910057249741)
                ·
                  refine ⟨4897604955364466271468653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13060279880971910057249741 4897604955364466271468653)
                  ·
                    refine ⟨1836601858261674851800745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4897604955364466271468653 1836601858261674851800745)
                    ·
                      refine ⟨1377451393696256138850559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1836601858261674851800745 1377451393696256138850559)
                      ·
                        rfl

theorem cell23_2682577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 3, 3, 2].length) (baseStart_2682577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2682577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2682577 prefixEnd_2682577 := by exact prefixLift 2682577
  have htrace : WordTrace (prefixWord ++ tailWord_2682577) baseStart_2682577 baseEnd_2682577 := by
    simpa [prefixWord, tailWord_2682577, baseEnd_2682577] using wordTrace_append hprefix tailTrace_2682577
  have hstable : (prefixWord ++ tailWord_2682577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682577).length < 2 ^ (prefixWord ++ tailWord_2682577).sum := by decide
  have hdescent : baseEnd_2682577 < baseStart_2682577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682583 : List Nat := [1, 1, 3, 2, 1, 3, 1, 2, 1, 8]
def baseStart_2682583 : Nat := 118140960795 + 2682583 * 2 ^ 59
def prefixEnd_2682583 : Nat := 4983230072969 + 3 ^ 40 * 2682583 * 2
def baseEnd_2682583 : Nat := 459151491526727705125177

theorem tailTrace_2682583 : CollatzResearch.WordTrace tailWord_2682583 prefixEnd_2682583 459151491526727705125177 := by
  unfold tailWord_2682583
  simp only [CollatzResearch.WordTrace]
  refine ⟨97841840040467414546428403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65227893360311609697618935 97841840040467414546428403)
  ·
    refine ⟨146762760060701121819642605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97841840040467414546428403 146762760060701121819642605)
    ·
      refine ⟨55036035022762920682365977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146762760060701121819642605 55036035022762920682365977)
      ·
        refine ⟨41277026267072190511774483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55036035022762920682365977 41277026267072190511774483)
        ·
          refine ⟨61915539400608285767661725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41277026267072190511774483 61915539400608285767661725)
          ·
            refine ⟨23218327275228107162873147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61915539400608285767661725 23218327275228107162873147)
            ·
              refine ⟨34827490912842160744309721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23218327275228107162873147 34827490912842160744309721)
              ·
                refine ⟨26120618184631620558232291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34827490912842160744309721 26120618184631620558232291)
                ·
                  refine ⟨39180927276947430837348437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26120618184631620558232291 39180927276947430837348437)
                  ·
                    refine ⟨459151491526727705125177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 39180927276947430837348437 459151491526727705125177)
                    ·
                      rfl

theorem cell23_2682583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 8].length) (baseStart_2682583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2682583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2682583 prefixEnd_2682583 := by exact prefixLift 2682583
  have htrace : WordTrace (prefixWord ++ tailWord_2682583) baseStart_2682583 baseEnd_2682583 := by
    simpa [prefixWord, tailWord_2682583, baseEnd_2682583] using wordTrace_append hprefix tailTrace_2682583
  have hstable : (prefixWord ++ tailWord_2682583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682583).length < 2 ^ (prefixWord ++ tailWord_2682583).sum := by decide
  have hdescent : baseEnd_2682583 < baseStart_2682583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682588 : List Nat := [2, 2, 5, 1, 2, 2, 2, 1, 1, 2, 3]
def baseStart_2682588 : Nat := 118140960795 + 2682588 * 2 ^ 59
def prefixEnd_2682588 : Nat := 4983230072969 + 3 ^ 40 * 2682588 * 2
def baseEnd_2682588 : Nat := 1377457041983455595813009

theorem tailTrace_2682588 : CollatzResearch.WordTrace tailWord_2682588 prefixEnd_2682588 1377457041983455595813009 := by
  unfold tailWord_2682588
  simp only [CollatzResearch.WordTrace]
  refine ⟨48921011202724650200180209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65228014936966200266906945 48921011202724650200180209)
  ·
    refine ⟨36690758402043487650135157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48921011202724650200180209 36690758402043487650135157)
    ·
      refine ⟨3439758600191576967200171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36690758402043487650135157 3439758600191576967200171)
      ·
        refine ⟨5159637900287365450800257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3439758600191576967200171 5159637900287365450800257)
        ·
          refine ⟨3869728425215524088100193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5159637900287365450800257 3869728425215524088100193)
          ·
            refine ⟨2902296318911643066075145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3869728425215524088100193 2902296318911643066075145)
            ·
              refine ⟨2176722239183732299556359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2902296318911643066075145 2176722239183732299556359)
              ·
                refine ⟨3265083358775598449334539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2176722239183732299556359 3265083358775598449334539)
                ·
                  refine ⟨4897625038163397674001809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3265083358775598449334539 4897625038163397674001809)
                  ·
                    refine ⟨3673218778622548255501357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4897625038163397674001809 3673218778622548255501357)
                    ·
                      refine ⟨1377457041983455595813009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3673218778622548255501357 1377457041983455595813009)
                      ·
                        rfl

theorem cell23_2682588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_2682588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2682588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2682588 prefixEnd_2682588 := by exact prefixLift 2682588
  have htrace : WordTrace (prefixWord ++ tailWord_2682588) baseStart_2682588 baseEnd_2682588 := by
    simpa [prefixWord, tailWord_2682588, baseEnd_2682588] using wordTrace_append hprefix tailTrace_2682588
  have hstable : (prefixWord ++ tailWord_2682588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682588).length < 2 ^ (prefixWord ++ tailWord_2682588).sum := by decide
  have hdescent : baseEnd_2682588 < baseStart_2682588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682600 : List Nat := [2, 1, 4, 1, 3, 1, 1, 2, 2, 6]
def baseStart_2682600 : Nat := 118140960795 + 2682600 * 2 ^ 59
def prefixEnd_2682600 : Nat := 4983230072969 + 3 ^ 40 * 2682600 * 2
def baseEnd_2682600 : Nat := 459154401250436516287651

theorem tailTrace_2682600 : CollatzResearch.WordTrace tailWord_2682600 prefixEnd_2682600 459154401250436516287651 := by
  unfold tailWord_2682600
  simp only [CollatzResearch.WordTrace]
  refine ⟨48921230040702913224898627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65228306720937217633198169 48921230040702913224898627)
  ·
    refine ⟨73381845061054369837347941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48921230040702913224898627 73381845061054369837347941)
    ·
      refine ⟨13759095948947694344502739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73381845061054369837347941 13759095948947694344502739)
      ·
        refine ⟨20638643923421541516754109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13759095948947694344502739 20638643923421541516754109)
        ·
          refine ⟨7739491471283078068782791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20638643923421541516754109 7739491471283078068782791)
          ·
            refine ⟨11609237206924617103174187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7739491471283078068782791 11609237206924617103174187)
            ·
              refine ⟨17413855810386925654761281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11609237206924617103174187 17413855810386925654761281)
              ·
                refine ⟨13060391857790194241070961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17413855810386925654761281 13060391857790194241070961)
                ·
                  refine ⟨9795293893342645680803221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13060391857790194241070961 9795293893342645680803221)
                  ·
                    refine ⟨459154401250436516287651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9795293893342645680803221 459154401250436516287651)
                    ·
                      rfl

theorem cell23_2682600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_2682600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2682600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2682600 prefixEnd_2682600 := by exact prefixLift 2682600
  have htrace : WordTrace (prefixWord ++ tailWord_2682600) baseStart_2682600 baseEnd_2682600 := by
    simpa [prefixWord, tailWord_2682600, baseEnd_2682600] using wordTrace_append hprefix tailTrace_2682600
  have hstable : (prefixWord ++ tailWord_2682600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682600).length < 2 ^ (prefixWord ++ tailWord_2682600).sum := by decide
  have hdescent : baseEnd_2682600 < baseStart_2682600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682620 : List Nat := [2, 2, 2, 1, 3, 1, 1, 3, 2, 2, 4]
def baseStart_2682620 : Nat := 118140960795 + 2682620 * 2 ^ 59
def prefixEnd_2682620 : Nat := 4983230072969 + 3 ^ 40 * 2682620 * 2
def baseEnd_2682620 : Nat := 1377473473364399470612861

theorem tailTrace_2682620 : CollatzResearch.WordTrace tailWord_2682620 prefixEnd_2682620 1377473473364399470612861 := by
  unfold tailWord_2682620
  simp only [CollatzResearch.WordTrace]
  refine ⟨48921594770666684932762657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65228793027555579910350209 48921594770666684932762657)
  ·
    refine ⟨36691196078000013699571993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48921594770666684932762657 36691196078000013699571993)
    ·
      refine ⟨27518397058500010274678995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36691196078000013699571993 27518397058500010274678995)
      ·
        refine ⟨41277595587750015412018493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27518397058500010274678995 41277595587750015412018493)
        ·
          refine ⟨15479098345406255779506935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41277595587750015412018493 15479098345406255779506935)
          ·
            refine ⟨23218647518109383669260403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15479098345406255779506935 23218647518109383669260403)
            ·
              refine ⟨34827971277164075503890605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23218647518109383669260403 34827971277164075503890605)
              ·
                refine ⟨13060489228936528313958977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34827971277164075503890605 13060489228936528313958977)
                ·
                  refine ⟨9795366921702396235469233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13060489228936528313958977 9795366921702396235469233)
                  ·
                    refine ⟨7346525191276797176601925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9795366921702396235469233 7346525191276797176601925)
                    ·
                      refine ⟨1377473473364399470612861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7346525191276797176601925 1377473473364399470612861)
                      ·
                        rfl

theorem cell23_2682620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_2682620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2682620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2682620 prefixEnd_2682620 := by exact prefixLift 2682620
  have htrace : WordTrace (prefixWord ++ tailWord_2682620) baseStart_2682620 baseEnd_2682620 := by
    simpa [prefixWord, tailWord_2682620, baseEnd_2682620] using wordTrace_append hprefix tailTrace_2682620
  have hstable : (prefixWord ++ tailWord_2682620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682620).length < 2 ^ (prefixWord ++ tailWord_2682620).sum := by decide
  have hdescent : baseEnd_2682620 < baseStart_2682620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682675 : List Nat := [1, 1, 1, 2, 8, 1, 2, 1, 2, 2, 2]
def baseStart_2682675 : Nat := 118140960795 + 2682675 * 2 ^ 59
def prefixEnd_2682675 : Nat := 4983230072969 + 3 ^ 40 * 2682675 * 2
def baseEnd_2682675 : Nat := 1377501714800396755425109

theorem tailTrace_2682675 : CollatzResearch.WordTrace tailWord_2682675 prefixEnd_2682675 1377501714800396755425109 := by
  unfold tailWord_2682675
  simp only [CollatzResearch.WordTrace]
  refine ⟨97845195556134114258777479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65230130370756076172518319 97845195556134114258777479)
  ·
    refine ⟨146767793334201171388166219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97845195556134114258777479 146767793334201171388166219)
    ·
      refine ⟨220151690001301757082249329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146767793334201171388166219 220151690001301757082249329)
      ·
        refine ⟨165113767500976317811686997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220151690001301757082249329 165113767500976317811686997)
        ·
          refine ⟨1934926962902066224355707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 165113767500976317811686997 1934926962902066224355707)
          ·
            refine ⟨2902390444353099336533561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1934926962902066224355707 2902390444353099336533561)
            ·
              refine ⟨2176792833264824502400171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2902390444353099336533561 2176792833264824502400171)
              ·
                refine ⟨3265189249897236753600257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2176792833264824502400171 3265189249897236753600257)
                ·
                  refine ⟨2448891937422927565200193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3265189249897236753600257 2448891937422927565200193)
                  ·
                    refine ⟨1836668953067195673900145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2448891937422927565200193 1836668953067195673900145)
                    ·
                      refine ⟨1377501714800396755425109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1836668953067195673900145 1377501714800396755425109)
                      ·
                        rfl

theorem cell23_2682675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 1, 2, 2, 2].length) (baseStart_2682675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2682675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2682675 prefixEnd_2682675 := by exact prefixLift 2682675
  have htrace : WordTrace (prefixWord ++ tailWord_2682675) baseStart_2682675 baseEnd_2682675 := by
    simpa [prefixWord, tailWord_2682675, baseEnd_2682675] using wordTrace_append hprefix tailTrace_2682675
  have hstable : (prefixWord ++ tailWord_2682675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682675).length < 2 ^ (prefixWord ++ tailWord_2682675).sum := by decide
  have hdescent : baseEnd_2682675 < baseStart_2682675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682697 : List Nat := [1, 2, 1, 1, 2, 4, 4, 1, 2, 1, 4]
def baseStart_2682697 : Nat := 118140960795 + 2682697 * 2 ^ 59
def prefixEnd_2682697 : Nat := 4983230072969 + 3 ^ 40 * 2682697 * 2
def baseEnd_2682697 : Nat := 1377513011374795669350007

theorem tailTrace_2682697 : CollatzResearch.WordTrace tailWord_2682697 prefixEnd_2682697 1377513011374795669350007 := by
  unfold tailWord_2682697
  simp only [CollatzResearch.WordTrace]
  refine ⟨97845997962054412016078345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65230665308036274677385563 97845997962054412016078345)
  ·
    refine ⟨73384498471540809012058759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97845997962054412016078345 73384498471540809012058759)
    ·
      refine ⟨110076747707311213518088139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73384498471540809012058759 110076747707311213518088139)
      ·
        refine ⟨165115121560966820277132209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110076747707311213518088139 165115121560966820277132209)
        ·
          refine ⟨123836341170725115207849157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165115121560966820277132209 123836341170725115207849157)
          ·
            refine ⟨23219313969510959101471717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123836341170725115207849157 23219313969510959101471717)
            ·
              refine ⟨4353621369283304831525947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23219313969510959101471717 4353621369283304831525947)
              ·
                refine ⟨6530432053924957247288921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4353621369283304831525947 6530432053924957247288921)
                ·
                  refine ⟨4897824040443717935466691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6530432053924957247288921 4897824040443717935466691)
                  ·
                    refine ⟨7346736060665576903200037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4897824040443717935466691 7346736060665576903200037)
                    ·
                      refine ⟨1377513011374795669350007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7346736060665576903200037 1377513011374795669350007)
                      ·
                        rfl

theorem cell23_2682697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 2, 1, 4].length) (baseStart_2682697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2682697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2682697 prefixEnd_2682697 := by exact prefixLift 2682697
  have htrace : WordTrace (prefixWord ++ tailWord_2682697) baseStart_2682697 baseEnd_2682697 := by
    simpa [prefixWord, tailWord_2682697, baseEnd_2682697] using wordTrace_append hprefix tailTrace_2682697
  have hstable : (prefixWord ++ tailWord_2682697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682697).length < 2 ^ (prefixWord ++ tailWord_2682697).sum := by decide
  have hdescent : baseEnd_2682697 < baseStart_2682697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682781 : List Nat := [1, 4, 2, 1, 2, 3, 2, 1, 3, 1, 3]
def baseStart_2682781 : Nat := 118140960795 + 2682781 * 2 ^ 59
def prefixEnd_2682781 : Nat := 4983230072969 + 3 ^ 40 * 2682781 * 2
def baseEnd_2682781 : Nat := 1377556143749773340699621

theorem tailTrace_2682781 : CollatzResearch.WordTrace tailWord_2682781 prefixEnd_2682781 1377556143749773340699621 := by
  unfold tailWord_2682781
  simp only [CollatzResearch.WordTrace]
  refine ⟨97849061693750094362136197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65232707795833396241424131 97849061693750094362136197)
  ·
    refine ⟨18346699067578142692900537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97849061693750094362136197 18346699067578142692900537)
    ·
      refine ⟨13760024300683607019675403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18346699067578142692900537 13760024300683607019675403)
      ·
        refine ⟨20640036451025410529513105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13760024300683607019675403 20640036451025410529513105)
        ·
          refine ⟨15480027338269057897134829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20640036451025410529513105 15480027338269057897134829)
          ·
            refine ⟨5805010251850896711425561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15480027338269057897134829 5805010251850896711425561)
            ·
              refine ⟨4353757688888172533569171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5805010251850896711425561 4353757688888172533569171)
              ·
                refine ⟨6530636533332258800353757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4353757688888172533569171 6530636533332258800353757)
                ·
                  refine ⟨2448988699999597050132659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6530636533332258800353757 2448988699999597050132659)
                  ·
                    refine ⟨3673483049999395575198989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2448988699999597050132659 3673483049999395575198989)
                    ·
                      refine ⟨1377556143749773340699621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3673483049999395575198989 1377556143749773340699621)
                      ·
                        rfl

theorem cell23_2682781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_2682781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2682781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2682781 prefixEnd_2682781 := by exact prefixLift 2682781
  have htrace : WordTrace (prefixWord ++ tailWord_2682781) baseStart_2682781 baseEnd_2682781 := by
    simpa [prefixWord, tailWord_2682781, baseEnd_2682781] using wordTrace_append hprefix tailTrace_2682781
  have hstable : (prefixWord ++ tailWord_2682781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682781).length < 2 ^ (prefixWord ++ tailWord_2682781).sum := by decide
  have hdescent : baseEnd_2682781 < baseStart_2682781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682814 : List Nat := [4, 2, 1, 1, 1, 3, 1, 2, 4, 4]
def baseStart_2682814 : Nat := 118140960795 + 2682814 * 2 ^ 59
def prefixEnd_2682814 : Nat := 4983230072969 + 3 ^ 40 * 2682814 * 2
def baseEnd_2682814 : Nat := 459191029537123903862323

theorem tailTrace_2682814 : CollatzResearch.WordTrace tailWord_2682814 prefixEnd_2682814 459191029537123903862323 := by
  unfold tailWord_2682814
  simp only [CollatzResearch.WordTrace]
  refine ⟨12231283162828817624760937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65233510201753693998724997 12231283162828817624760937)
  ·
    refine ⟨9173462372121613218570703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12231283162828817624760937 9173462372121613218570703)
    ·
      refine ⟨13760193558182419827856055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9173462372121613218570703 13760193558182419827856055)
      ·
        refine ⟨20640290337273629741784083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13760193558182419827856055 20640290337273629741784083)
        ·
          refine ⟨30960435505910444612676125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20640290337273629741784083 30960435505910444612676125)
          ·
            refine ⟨11610163314716416729753547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30960435505910444612676125 11610163314716416729753547)
            ·
              refine ⟨17415244972074625094630321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11610163314716416729753547 17415244972074625094630321)
              ·
                refine ⟨13061433729055968820972741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17415244972074625094630321 13061433729055968820972741)
                ·
                  refine ⟨2449018824197994153932389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13061433729055968820972741 2449018824197994153932389)
                  ·
                    refine ⟨459191029537123903862323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2449018824197994153932389 459191029537123903862323)
                    ·
                      rfl

theorem cell23_2682814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_2682814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2682814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2682814 prefixEnd_2682814 := by exact prefixLift 2682814
  have htrace : WordTrace (prefixWord ++ tailWord_2682814) baseStart_2682814 baseEnd_2682814 := by
    simpa [prefixWord, tailWord_2682814, baseEnd_2682814] using wordTrace_append hprefix tailTrace_2682814
  have hstable : (prefixWord ++ tailWord_2682814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682814).length < 2 ^ (prefixWord ++ tailWord_2682814).sum := by decide
  have hdescent : baseEnd_2682814 < baseStart_2682814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682824 : List Nat := [2, 1, 3, 1, 4, 2, 2, 1, 1, 1, 5]
def baseStart_2682824 : Nat := 118140960795 + 2682824 * 2 ^ 59
def prefixEnd_2682824 : Nat := 4983230072969 + 3 ^ 40 * 2682824 * 2
def baseEnd_2682824 : Nat := 1377578223417916672461923

theorem tailTrace_2682824 : CollatzResearch.WordTrace tailWord_2682824 prefixEnd_2682824 1377578223417916672461923 := by
  unfold tailWord_2682824
  simp only [CollatzResearch.WordTrace]
  refine ⟨48925315016297156352975763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65233753355062875137301017 48925315016297156352975763)
  ·
    refine ⟨73387972524445734529463645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48925315016297156352975763 73387972524445734529463645)
    ·
      refine ⟨27520489696667150448548867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73387972524445734529463645 27520489696667150448548867)
      ·
        refine ⟨41280734545000725672823301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27520489696667150448548867 41280734545000725672823301)
        ·
          refine ⟨7740137727187636063654369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41280734545000725672823301 7740137727187636063654369)
          ·
            refine ⟨5805103295390727047740777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7740137727187636063654369 5805103295390727047740777)
            ·
              refine ⟨4353827471543045285805583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5805103295390727047740777 4353827471543045285805583)
              ·
                refine ⟨6530741207314567928708375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4353827471543045285805583 6530741207314567928708375)
                ·
                  refine ⟨9796111810971851893062563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6530741207314567928708375 9796111810971851893062563)
                  ·
                    refine ⟨14694167716457777839593845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9796111810971851893062563 14694167716457777839593845)
                    ·
                      refine ⟨1377578223417916672461923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14694167716457777839593845 1377578223417916672461923)
                      ·
                        rfl

theorem cell23_2682824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 1, 1, 5].length) (baseStart_2682824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2682824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2682824 prefixEnd_2682824 := by exact prefixLift 2682824
  have htrace : WordTrace (prefixWord ++ tailWord_2682824) baseStart_2682824 baseEnd_2682824 := by
    simpa [prefixWord, tailWord_2682824, baseEnd_2682824] using wordTrace_append hprefix tailTrace_2682824
  have hstable : (prefixWord ++ tailWord_2682824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682824).length < 2 ^ (prefixWord ++ tailWord_2682824).sum := by decide
  have hdescent : baseEnd_2682824 < baseStart_2682824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682911 : List Nat := [1, 1, 2, 4, 1, 2, 4, 1, 1, 4, 2]
def baseStart_2682911 : Nat := 118140960795 + 2682911 * 2 ^ 59
def prefixEnd_2682911 : Nat := 4983230072969 + 3 ^ 40 * 2682911 * 2
def baseEnd_2682911 : Nat := 1377622896234857832074023

theorem tailTrace_2682911 : CollatzResearch.WordTrace tailWord_2682911 prefixEnd_2682911 1377622896234857832074023 := by
  unfold tailWord_2682911
  simp only [CollatzResearch.WordTrace]
  refine ⟨97853803183279126564368587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65235868788852751042912391 97853803183279126564368587)
  ·
    refine ⟨146780704774918689846552881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97853803183279126564368587 146780704774918689846552881)
    ·
      refine ⟨110085528581189017384914661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146780704774918689846552881 110085528581189017384914661)
      ·
        refine ⟨20641036608972940759671499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110085528581189017384914661 20641036608972940759671499)
        ·
          refine ⟨30961554913459411139507249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20641036608972940759671499 30961554913459411139507249)
          ·
            refine ⟨23221166185094558354630437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30961554913459411139507249 23221166185094558354630437)
            ·
              refine ⟨4353968659705229691493207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23221166185094558354630437 4353968659705229691493207)
              ·
                refine ⟨6530952989557844537239811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4353968659705229691493207 6530952989557844537239811)
                ·
                  refine ⟨9796429484336766805859717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6530952989557844537239811 9796429484336766805859717)
                  ·
                    refine ⟨1836830528313143776098697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9796429484336766805859717 1836830528313143776098697)
                    ·
                      refine ⟨1377622896234857832074023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1836830528313143776098697 1377622896234857832074023)
                      ·
                        rfl

theorem cell23_2682911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 4, 2].length) (baseStart_2682911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2682911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2682911 prefixEnd_2682911 := by exact prefixLift 2682911
  have htrace : WordTrace (prefixWord ++ tailWord_2682911) baseStart_2682911 baseEnd_2682911 := by
    simpa [prefixWord, tailWord_2682911, baseEnd_2682911] using wordTrace_append hprefix tailTrace_2682911
  have hstable : (prefixWord ++ tailWord_2682911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682911).length < 2 ^ (prefixWord ++ tailWord_2682911).sum := by decide
  have hdescent : baseEnd_2682911 < baseStart_2682911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682914 : List Nat := [3, 3, 1, 1, 1, 2, 1, 2, 2, 4, 3]
def baseStart_2682914 : Nat := 118140960795 + 2682914 * 2 ^ 59
def prefixEnd_2682914 : Nat := 4983230072969 + 3 ^ 40 * 2682914 * 2
def baseEnd_2682914 : Nat := 1377624436676821320336509

theorem tailTrace_2682914 : CollatzResearch.WordTrace tailWord_2682914 prefixEnd_2682914 1377624436676821320336509 := by
  unfold tailWord_2682914
  simp only [CollatzResearch.WordTrace]
  refine ⟨24463478150567064519181949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65235941734845505384485197 24463478150567064519181949)
  ·
    refine ⟨9173804306462649194693231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24463478150567064519181949 9173804306462649194693231)
    ·
      refine ⟨13760706459693973792039847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9173804306462649194693231 13760706459693973792039847)
      ·
        refine ⟨20641059689540960688059771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13760706459693973792039847 20641059689540960688059771)
        ·
          refine ⟨30961589534311441032089657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20641059689540960688059771 30961589534311441032089657)
          ·
            refine ⟨23221192150733580774067243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30961589534311441032089657 23221192150733580774067243)
            ·
              refine ⟨34831788226100371161100865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23221192150733580774067243 34831788226100371161100865)
              ·
                refine ⟨26123841169575278370825649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34831788226100371161100865 26123841169575278370825649)
                ·
                  refine ⟨19592880877181458778119237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26123841169575278370825649 19592880877181458778119237)
                  ·
                    refine ⟨3673665164471523520897357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19592880877181458778119237 3673665164471523520897357)
                    ·
                      refine ⟨1377624436676821320336509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3673665164471523520897357 1377624436676821320336509)
                      ·
                        rfl

theorem cell23_2682914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_2682914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2682914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2682914 prefixEnd_2682914 := by exact prefixLift 2682914
  have htrace : WordTrace (prefixWord ++ tailWord_2682914) baseStart_2682914 baseEnd_2682914 := by
    simpa [prefixWord, tailWord_2682914, baseEnd_2682914] using wordTrace_append hprefix tailTrace_2682914
  have hstable : (prefixWord ++ tailWord_2682914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682914).length < 2 ^ (prefixWord ++ tailWord_2682914).sum := by decide
  have hdescent : baseEnd_2682914 < baseStart_2682914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682917 : List Nat := [1, 3, 1, 2, 2, 3, 1, 1, 9]
def baseStart_2682917 : Nat := 118140960795 + 2682917 * 2 ^ 59
def prefixEnd_2682917 : Nat := 4983230072969 + 3 ^ 40 * 2682917 * 2
def baseEnd_2682917 : Nat := 153069553013198312066555

theorem tailTrace_2682917 : CollatzResearch.WordTrace tailWord_2682917 prefixEnd_2682917 153069553013198312066555 := by
  unfold tailWord_2682917
  simp only [CollatzResearch.WordTrace]
  refine ⟨97854022021257389589087005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65236014680838259726058003 97854022021257389589087005)
  ·
    refine ⟨36695258257971521095907627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97854022021257389589087005 36695258257971521095907627)
    ·
      refine ⟨55042887386957281643861441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36695258257971521095907627 55042887386957281643861441)
      ·
        refine ⟨41282165540217961232896081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55042887386957281643861441 41282165540217961232896081)
        ·
          refine ⟨30961624155163470924672061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41282165540217961232896081 30961624155163470924672061)
          ·
            refine ⟨11610609058186301596752023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30961624155163470924672061 11610609058186301596752023)
            ·
              refine ⟨17415913587279452395128035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11610609058186301596752023 17415913587279452395128035)
              ·
                refine ⟨26123870380919178592692053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17415913587279452395128035 26123870380919178592692053)
                ·
                  refine ⟨153069553013198312066555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 26123870380919178592692053 153069553013198312066555)
                  ·
                    rfl

theorem cell23_2682917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 9].length) (baseStart_2682917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2682917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2682917 prefixEnd_2682917 := by exact prefixLift 2682917
  have htrace : WordTrace (prefixWord ++ tailWord_2682917) baseStart_2682917 baseEnd_2682917 := by
    simpa [prefixWord, tailWord_2682917, baseEnd_2682917] using wordTrace_append hprefix tailTrace_2682917
  have hstable : (prefixWord ++ tailWord_2682917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682917).length < 2 ^ (prefixWord ++ tailWord_2682917).sum := by decide
  have hdescent : baseEnd_2682917 < baseStart_2682917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682934 : List Nat := [5, 1, 2, 1, 1, 1, 1, 2, 9]
def baseStart_2682934 : Nat := 118140960795 + 2682934 * 2 ^ 59
def prefixEnd_2682934 : Nat := 4983230072969 + 3 ^ 40 * 2682934 * 2
def baseEnd_2682934 : Nat := 153070522921101249120713

theorem tailTrace_2682934 : CollatzResearch.WordTrace tailWord_2682934 prefixEnd_2682934 153070522921101249120713 := by
  unfold tailWord_2682934
  simp only [CollatzResearch.WordTrace]
  refine ⟨6115915128887237593278491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65236428041463867661637237 6115915128887237593278491)
  ·
    refine ⟨9173872693330856389917737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6115915128887237593278491 9173872693330856389917737)
    ·
      refine ⟨6880404519998142292438303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9173872693330856389917737 6880404519998142292438303)
      ·
        refine ⟨10320606779997213438657455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6880404519998142292438303 10320606779997213438657455)
        ·
          refine ⟨15480910169995820157986183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10320606779997213438657455 15480910169995820157986183)
          ·
            refine ⟨23221365254993730236979275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15480910169995820157986183 23221365254993730236979275)
            ·
              refine ⟨34832047882490595355468913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23221365254993730236979275 34832047882490595355468913)
              ·
                refine ⟨26124035911867946516601685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34832047882490595355468913 26124035911867946516601685)
                ·
                  refine ⟨153070522921101249120713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 26124035911867946516601685 153070522921101249120713)
                  ·
                    rfl

theorem cell23_2682934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 9].length) (baseStart_2682934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2682934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2682934 prefixEnd_2682934 := by exact prefixLift 2682934
  have htrace : WordTrace (prefixWord ++ tailWord_2682934) baseStart_2682934 baseEnd_2682934 := by
    simpa [prefixWord, tailWord_2682934, baseEnd_2682934] using wordTrace_append hprefix tailTrace_2682934
  have hstable : (prefixWord ++ tailWord_2682934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682934).length < 2 ^ (prefixWord ++ tailWord_2682934).sum := by decide
  have hdescent : baseEnd_2682934 < baseStart_2682934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682944 : List Nat := [2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 3]
def baseStart_2682944 : Nat := 118140960795 + 2682944 * 2 ^ 59
def prefixEnd_2682944 : Nat := 4983230072969 + 3 ^ 40 * 2682944 * 2
def baseEnd_2682944 : Nat := 1377639841096456202961371

theorem tailTrace_2682944 : CollatzResearch.WordTrace tailWord_2682944 prefixEnd_2682944 1377639841096456202961371 := by
  unfold tailWord_2682944
  simp only [CollatzResearch.WordTrace]
  refine ⟨48927503396079786600159943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65236671194773048800213257 48927503396079786600159943)
  ·
    refine ⟨73391255094119679900239915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48927503396079786600159943 73391255094119679900239915)
    ·
      refine ⟨110086882641179519850359873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73391255094119679900239915 110086882641179519850359873)
      ·
        refine ⟨82565161980884639887769905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110086882641179519850359873 82565161980884639887769905)
        ·
          refine ⟨61923871485663479915827429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82565161980884639887769905 61923871485663479915827429)
          ·
            refine ⟨11610725903561902484217643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61923871485663479915827429 11610725903561902484217643)
            ·
              refine ⟨17416088855342853726326465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11610725903561902484217643 17416088855342853726326465)
              ·
                refine ⟨13062066641507140294744849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17416088855342853726326465 13062066641507140294744849)
                ·
                  refine ⟨9796549981130355221058637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13062066641507140294744849 9796549981130355221058637)
                  ·
                    refine ⟨3673706242923883207896989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9796549981130355221058637 3673706242923883207896989)
                    ·
                      refine ⟨1377639841096456202961371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3673706242923883207896989 1377639841096456202961371)
                      ·
                        rfl

theorem cell23_2682944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 3].length) (baseStart_2682944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2682944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2682944 prefixEnd_2682944 := by exact prefixLift 2682944
  have htrace : WordTrace (prefixWord ++ tailWord_2682944) baseStart_2682944 baseEnd_2682944 := by
    simpa [prefixWord, tailWord_2682944, baseEnd_2682944] using wordTrace_append hprefix tailTrace_2682944
  have hstable : (prefixWord ++ tailWord_2682944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682944).length < 2 ^ (prefixWord ++ tailWord_2682944).sum := by decide
  have hdescent : baseEnd_2682944 < baseStart_2682944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682945 : List Nat := [1, 2, 5, 1, 2, 1, 3, 2, 2, 2, 2]
def baseStart_2682945 : Nat := 118140960795 + 2682945 * 2 ^ 59
def prefixEnd_2682945 : Nat := 4983230072969 + 3 ^ 40 * 2682945 * 2
def baseEnd_2682945 : Nat := 1377640354577110699048867

theorem tailTrace_2682945 : CollatzResearch.WordTrace tailWord_2682945 prefixEnd_2682945 1377640354577110699048867 := by
  unfold tailWord_2682945
  simp only [CollatzResearch.WordTrace]
  refine ⟨97855043265155950371106289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65236695510103966914070859 97855043265155950371106289)
  ·
    refine ⟨73391282448866962778329717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97855043265155950371106289 73391282448866962778329717)
    ·
      refine ⟨6880432729581277760468411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73391282448866962778329717 6880432729581277760468411)
      ·
        refine ⟨10320649094371916640702617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6880432729581277760468411 10320649094371916640702617)
        ·
          refine ⟨7740486820778937480526963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10320649094371916640702617 7740486820778937480526963)
          ·
            refine ⟨11610730231168406220790445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7740486820778937480526963 11610730231168406220790445)
            ·
              refine ⟨4354023836688152332796417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11610730231168406220790445 4354023836688152332796417)
              ·
                refine ⟨3265517877516114249597313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4354023836688152332796417 3265517877516114249597313)
                ·
                  refine ⟨2449138408137085687197985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3265517877516114249597313 2449138408137085687197985)
                  ·
                    refine ⟨1836853806102814265398489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2449138408137085687197985 1836853806102814265398489)
                    ·
                      refine ⟨1377640354577110699048867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1836853806102814265398489 1377640354577110699048867)
                      ·
                        rfl

theorem cell23_2682945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_2682945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2682945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2682945 prefixEnd_2682945 := by exact prefixLift 2682945
  have htrace : WordTrace (prefixWord ++ tailWord_2682945) baseStart_2682945 baseEnd_2682945 := by
    simpa [prefixWord, tailWord_2682945, baseEnd_2682945] using wordTrace_append hprefix tailTrace_2682945
  have hstable : (prefixWord ++ tailWord_2682945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682945).length < 2 ^ (prefixWord ++ tailWord_2682945).sum := by decide
  have hdescent : baseEnd_2682945 < baseStart_2682945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682962 : List Nat := [3, 2, 2, 1, 4, 1, 3, 1, 2, 2, 2]
def baseStart_2682962 : Nat := 118140960795 + 2682962 * 2 ^ 59
def prefixEnd_2682962 : Nat := 4983230072969 + 3 ^ 40 * 2682962 * 2
def baseEnd_2682962 : Nat := 1377649083748237132536289

theorem tailTrace_2682962 : CollatzResearch.WordTrace tailWord_2682962 prefixEnd_2682962 1377649083748237132536289 := by
  unfold tailWord_2682962
  simp only [CollatzResearch.WordTrace]
  refine ⟨24463915826523590568618785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65237108870729574849650093 24463915826523590568618785)
  ·
    refine ⟨18347936869892692926464089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24463915826523590568618785 18347936869892692926464089)
    ·
      refine ⟨13760952652419519694848067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18347936869892692926464089 13760952652419519694848067)
      ·
        refine ⟨20641428978629279542272101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13760952652419519694848067 20641428978629279542272101)
        ·
          refine ⟨3870267933492989914176019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20641428978629279542272101 3870267933492989914176019)
          ·
            refine ⟨5805401900239484871264029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3870267933492989914176019 5805401900239484871264029)
            ·
              refine ⟨2177025712589806826724011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5805401900239484871264029 2177025712589806826724011)
              ·
                refine ⟨3265538568884710240086017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2177025712589806826724011 3265538568884710240086017)
                ·
                  refine ⟨2449153926663532680064513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3265538568884710240086017 2449153926663532680064513)
                  ·
                    refine ⟨1836865444997649510048385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2449153926663532680064513 1836865444997649510048385)
                    ·
                      refine ⟨1377649083748237132536289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1836865444997649510048385 1377649083748237132536289)
                      ·
                        rfl

theorem cell23_2682962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 1, 2, 2, 2].length) (baseStart_2682962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2682962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2682962 prefixEnd_2682962 := by exact prefixLift 2682962
  have htrace : WordTrace (prefixWord ++ tailWord_2682962) baseStart_2682962 baseEnd_2682962 := by
    simpa [prefixWord, tailWord_2682962, baseEnd_2682962] using wordTrace_append hprefix tailTrace_2682962
  have hstable : (prefixWord ++ tailWord_2682962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682962).length < 2 ^ (prefixWord ++ tailWord_2682962).sum := by decide
  have hdescent : baseEnd_2682962 < baseStart_2682962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2682977 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 1, 10]
def baseStart_2682977 : Nat := 118140960795 + 2682977 * 2 ^ 59
def prefixEnd_2682977 : Nat := 4983230072969 + 3 ^ 40 * 2682977 * 2
def baseEnd_2682977 : Nat := 459218928652684857949573

theorem tailTrace_2682977 : CollatzResearch.WordTrace tailWord_2682977 prefixEnd_2682977 459218928652684857949573 := by
  unfold tailWord_2682977
  simp only [CollatzResearch.WordTrace]
  refine ⟨97856210401040019836271185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65237473600693346557514123 97856210401040019836271185)
  ·
    refine ⟨73392157800780014877203389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97856210401040019836271185 73392157800780014877203389)
    ·
      refine ⟨27522059175292505578951271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73392157800780014877203389 27522059175292505578951271)
      ·
        refine ⟨41283088762938758368426907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27522059175292505578951271 41283088762938758368426907)
        ·
          refine ⟨61924633144408137552640361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41283088762938758368426907 61924633144408137552640361)
          ·
            refine ⟨46443474858306103164480271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61924633144408137552640361 46443474858306103164480271)
            ·
              refine ⟨69665212287459154746720407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46443474858306103164480271 69665212287459154746720407)
              ·
                refine ⟨104497818431188732120080611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69665212287459154746720407 104497818431188732120080611)
                ·
                  refine ⟨156746727646783098180120917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104497818431188732120080611 156746727646783098180120917)
                  ·
                    refine ⟨459218928652684857949573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 156746727646783098180120917 459218928652684857949573)
                    ·
                      rfl

theorem cell23_2682977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 10].length) (baseStart_2682977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2682977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2682977 prefixEnd_2682977 := by exact prefixLift 2682977
  have htrace : WordTrace (prefixWord ++ tailWord_2682977) baseStart_2682977 baseEnd_2682977 := by
    simpa [prefixWord, tailWord_2682977, baseEnd_2682977] using wordTrace_append hprefix tailTrace_2682977
  have hstable : (prefixWord ++ tailWord_2682977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2682977).length < 2 ^ (prefixWord ++ tailWord_2682977).sum := by decide
  have hdescent : baseEnd_2682977 < baseStart_2682977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2682977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683001 : List Nat := [1, 2, 1, 3, 4, 2, 1, 2, 2, 1, 4]
def baseStart_2683001 : Nat := 118140960795 + 2683001 * 2 ^ 59
def prefixEnd_2683001 : Nat := 4983230072969 + 3 ^ 40 * 2683001 * 2
def baseEnd_2683001 : Nat := 1377669109493762479948609

theorem tailTrace_2683001 : CollatzResearch.WordTrace tailWord_2683001 prefixEnd_2683001 1377669109493762479948609 := by
  unfold tailWord_2683001
  simp only [CollatzResearch.WordTrace]
  refine ⟨97857085752953071935144857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65238057168635381290096571 97857085752953071935144857)
  ·
    refine ⟨73392814314714803951358643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97857085752953071935144857 73392814314714803951358643)
    ·
      refine ⟨110089221472072205927037965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73392814314714803951358643 110089221472072205927037965)
      ·
        refine ⟨41283458052027077222639237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110089221472072205927037965 41283458052027077222639237)
        ·
          refine ⟨7740648384755076979244857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41283458052027077222639237 7740648384755076979244857)
          ·
            refine ⟨5805486288566307734433643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7740648384755076979244857 5805486288566307734433643)
            ·
              refine ⟨8708229432849461601650465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5805486288566307734433643 8708229432849461601650465)
              ·
                refine ⟨6531172074637096201237849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8708229432849461601650465 6531172074637096201237849)
                ·
                  refine ⟨4898379055977822150928387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6531172074637096201237849 4898379055977822150928387)
                  ·
                    refine ⟨7347568583966733226392581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4898379055977822150928387 7347568583966733226392581)
                    ·
                      refine ⟨1377669109493762479948609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7347568583966733226392581 1377669109493762479948609)
                      ·
                        rfl

theorem cell23_2683001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_2683001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2683001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2683001 prefixEnd_2683001 := by exact prefixLift 2683001
  have htrace : WordTrace (prefixWord ++ tailWord_2683001) baseStart_2683001 baseEnd_2683001 := by
    simpa [prefixWord, tailWord_2683001, baseEnd_2683001] using wordTrace_append hprefix tailTrace_2683001
  have hstable : (prefixWord ++ tailWord_2683001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683001).length < 2 ^ (prefixWord ++ tailWord_2683001).sum := by decide
  have hdescent : baseEnd_2683001 < baseStart_2683001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683011 : List Nat := [1, 1, 1, 3, 3, 3, 3, 1, 3, 4]
def baseStart_2683011 : Nat := 118140960795 + 2683011 * 2 ^ 59
def prefixEnd_2683011 : Nat := 4983230072969 + 3 ^ 40 * 2683011 * 2
def baseEnd_2683011 : Nat := 459224748100102480274521

theorem tailTrace_2683011 : CollatzResearch.WordTrace tailWord_2683011 prefixEnd_2683011 459224748100102480274521 := by
  unfold tailWord_2683011
  simp only [CollatzResearch.WordTrace]
  refine ⟨97857450482916843643008887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65238300321944562428672591 97857450482916843643008887)
  ·
    refine ⟨146786175724375265464513331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97857450482916843643008887 146786175724375265464513331)
    ·
      refine ⟨220179263586562898196769997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146786175724375265464513331 220179263586562898196769997)
      ·
        refine ⟨82567223844961086823788749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 220179263586562898196769997 82567223844961086823788749)
        ·
          refine ⟨30962708941860407558920781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82567223844961086823788749 30962708941860407558920781)
          ·
            refine ⟨11611015853197652834595293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30962708941860407558920781 11611015853197652834595293)
            ·
              refine ⟨4354130944949119812973235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11611015853197652834595293 4354130944949119812973235)
              ·
                refine ⟨6531196417423679719459853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4354130944949119812973235 6531196417423679719459853)
                ·
                  refine ⟨2449198656533879894797445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6531196417423679719459853 2449198656533879894797445)
                  ·
                    refine ⟨459224748100102480274521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2449198656533879894797445 459224748100102480274521)
                    ·
                      rfl

theorem cell23_2683011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 3, 4].length) (baseStart_2683011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2683011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2683011 prefixEnd_2683011 := by exact prefixLift 2683011
  have htrace : WordTrace (prefixWord ++ tailWord_2683011) baseStart_2683011 baseEnd_2683011 := by
    simpa [prefixWord, tailWord_2683011, baseEnd_2683011] using wordTrace_append hprefix tailTrace_2683011
  have hstable : (prefixWord ++ tailWord_2683011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683011).length < 2 ^ (prefixWord ++ tailWord_2683011).sum := by decide
  have hdescent : baseEnd_2683011 < baseStart_2683011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683024 : List Nat := [2, 1, 1, 1, 1, 1, 7, 3, 6]
def baseStart_2683024 : Nat := 118140960795 + 2683024 * 2 ^ 59
def prefixEnd_2683024 : Nat := 4983230072969 + 3 ^ 40 * 2683024 * 2
def baseEnd_2683024 : Nat := 153075657727646209995667

theorem tailTrace_2683024 : CollatzResearch.WordTrace tailWord_2683024 prefixEnd_2683024 153075657727646209995667 := by
  unfold tailWord_2683024
  simp only [CollatzResearch.WordTrace]
  refine ⟨48928962315934873431616063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65238616421246497908821417 48928962315934873431616063)
  ·
    refine ⟨73393443473902310147424095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48928962315934873431616063 73393443473902310147424095)
    ·
      refine ⟨110090165210853465221136143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73393443473902310147424095 110090165210853465221136143)
      ·
        refine ⟨165135247816280197831704215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110090165210853465221136143 165135247816280197831704215)
        ·
          refine ⟨247702871724420296747556323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165135247816280197831704215 247702871724420296747556323)
          ·
            refine ⟨371554307586630445121334485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247702871724420296747556323 371554307586630445121334485)
            ·
              refine ⟨8708304084061651057531277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 371554307586630445121334485 8708304084061651057531277)
              ·
                refine ⟨3265614031523119146574229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8708304084061651057531277 3265614031523119146574229)
                ·
                  refine ⟨153075657727646209995667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3265614031523119146574229 153075657727646209995667)
                  ·
                    rfl

theorem cell23_2683024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 3, 6].length) (baseStart_2683024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2683024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2683024 prefixEnd_2683024 := by exact prefixLift 2683024
  have htrace : WordTrace (prefixWord ++ tailWord_2683024) baseStart_2683024 baseEnd_2683024 := by
    simpa [prefixWord, tailWord_2683024, baseEnd_2683024] using wordTrace_append hprefix tailTrace_2683024
  have hstable : (prefixWord ++ tailWord_2683024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683024).length < 2 ^ (prefixWord ++ tailWord_2683024).sum := by decide
  have hdescent : baseEnd_2683024 < baseStart_2683024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683108 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 7, 2, 2]
def baseStart_2683108 : Nat := 118140960795 + 2683108 * 2 ^ 59
def prefixEnd_2683108 : Nat := 4983230072969 + 3 ^ 40 * 2683108 * 2
def baseEnd_2683108 : Nat := 1377724051923793561310617

theorem tailTrace_2683108 : CollatzResearch.WordTrace tailWord_2683108 prefixEnd_2683108 1377724051923793561310617 := by
  unfold tailWord_2683108
  simp only [CollatzResearch.WordTrace]
  refine ⟨48930494181782714604644989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65240658909043619472859985 48930494181782714604644989)
  ·
    refine ⟨18348935318168517976741871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48930494181782714604644989 18348935318168517976741871)
    ·
      refine ⟨27523402977252776965112807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18348935318168517976741871 27523402977252776965112807)
      ·
        refine ⟨41285104465879165447669211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27523402977252776965112807 41285104465879165447669211)
        ·
          refine ⟨61927656698818748171503817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41285104465879165447669211 61927656698818748171503817)
          ·
            refine ⟨46445742524114061128627863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61927656698818748171503817 46445742524114061128627863)
            ·
              refine ⟨69668613786171091692941795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46445742524114061128627863 69668613786171091692941795)
              ·
                refine ⟨104502920679256637539412693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69668613786171091692941795 104502920679256637539412693)
                ·
                  refine ⟨2449287203420077442329985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 104502920679256637539412693 2449287203420077442329985)
                  ·
                    refine ⟨1836965402565058081747489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2449287203420077442329985 1836965402565058081747489)
                    ·
                      refine ⟨1377724051923793561310617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1836965402565058081747489 1377724051923793561310617)
                      ·
                        rfl

theorem cell23_2683108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 7, 2, 2].length) (baseStart_2683108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2683108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2683108 prefixEnd_2683108 := by exact prefixLift 2683108
  have htrace : WordTrace (prefixWord ++ tailWord_2683108) baseStart_2683108 baseEnd_2683108 := by
    simpa [prefixWord, tailWord_2683108, baseEnd_2683108] using wordTrace_append hprefix tailTrace_2683108
  have hstable : (prefixWord ++ tailWord_2683108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683108).length < 2 ^ (prefixWord ++ tailWord_2683108).sum := by decide
  have hdescent : baseEnd_2683108 < baseStart_2683108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683114 : List Nat := [3, 1, 3, 1, 1, 2, 12]
def baseStart_2683114 : Nat := 118140960795 + 2683114 * 2 ^ 59
def prefixEnd_2683114 : Nat := 4983230072969 + 3 ^ 40 * 2683114 * 2
def baseEnd_2683114 : Nat := 17008976948243463430069

theorem tailTrace_2683114 : CollatzResearch.WordTrace tailWord_2683114 prefixEnd_2683114 17008976948243463430069 := by
  unfold tailWord_2683114
  simp only [CollatzResearch.WordTrace]
  refine ⟨24465301800385923058502099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65240804801029128156005597 24465301800385923058502099)
  ·
    refine ⟨36697952700578884587753149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24465301800385923058502099 36697952700578884587753149)
    ·
      refine ⟨13761732262717081720407431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36697952700578884587753149 13761732262717081720407431)
      ·
        refine ⟨20642598394075622580611147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13761732262717081720407431 20642598394075622580611147)
        ·
          refine ⟨30963897591113433870916721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20642598394075622580611147 30963897591113433870916721)
          ·
            refine ⟨23222923193335075403187541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30963897591113433870916721 23222923193335075403187541)
            ·
              refine ⟨17008976948243463430069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 23222923193335075403187541 17008976948243463430069)
              ·
                rfl

theorem cell23_2683114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 12].length) (baseStart_2683114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2683114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2683114 prefixEnd_2683114 := by exact prefixLift 2683114
  have htrace : WordTrace (prefixWord ++ tailWord_2683114) baseStart_2683114 baseEnd_2683114 := by
    simpa [prefixWord, tailWord_2683114, baseEnd_2683114] using wordTrace_append hprefix tailTrace_2683114
  have hstable : (prefixWord ++ tailWord_2683114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683114).length < 2 ^ (prefixWord ++ tailWord_2683114).sum := by decide
  have hdescent : baseEnd_2683114 < baseStart_2683114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683138 : List Nat := [3, 4, 1, 1, 2, 2, 1, 1, 1, 1, 6]
def baseStart_2683138 : Nat := 118140960795 + 2683138 * 2 ^ 59
def prefixEnd_2683138 : Nat := 4983230072969 + 3 ^ 40 * 2683138 * 2
def baseEnd_2683138 : Nat := 1377739456343428443935479

theorem tailTrace_2683138 : CollatzResearch.WordTrace tailWord_2683138 prefixEnd_2683138 1377739456343428443935479 := by
  unfold tailWord_2683138
  simp only [CollatzResearch.WordTrace]
  refine ⟨24465520638364186083220517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65241388368971162888588045 24465520638364186083220517)
  ·
    refine ⟨4587285119693284890603847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24465520638364186083220517 4587285119693284890603847)
    ·
      refine ⟨6880927679539927335905771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4587285119693284890603847 6880927679539927335905771)
      ·
        refine ⟨10321391519309891003858657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6880927679539927335905771 10321391519309891003858657)
        ·
          refine ⟨7741043639482418252893993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10321391519309891003858657 7741043639482418252893993)
          ·
            refine ⟨5805782729611813689670495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7741043639482418252893993 5805782729611813689670495)
            ·
              refine ⟨8708674094417720534505743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5805782729611813689670495 8708674094417720534505743)
              ·
                refine ⟨13063011141626580801758615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8708674094417720534505743 13063011141626580801758615)
                ·
                  refine ⟨19594516712439871202637923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13063011141626580801758615 19594516712439871202637923)
                  ·
                    refine ⟨29391775068659806803956885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19594516712439871202637923 29391775068659806803956885)
                    ·
                      refine ⟨1377739456343428443935479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29391775068659806803956885 1377739456343428443935479)
                      ·
                        rfl

theorem cell23_2683138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_2683138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2683138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2683138 prefixEnd_2683138 := by exact prefixLift 2683138
  have htrace : WordTrace (prefixWord ++ tailWord_2683138) baseStart_2683138 baseEnd_2683138 := by
    simpa [prefixWord, tailWord_2683138, baseEnd_2683138] using wordTrace_append hprefix tailTrace_2683138
  have hstable : (prefixWord ++ tailWord_2683138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683138).length < 2 ^ (prefixWord ++ tailWord_2683138).sum := by decide
  have hdescent : baseEnd_2683138 < baseStart_2683138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683141 : List Nat := [1, 3, 1, 1, 2, 1, 2, 5, 1, 3, 3]
def baseStart_2683141 : Nat := 118140960795 + 2683141 * 2 ^ 59
def prefixEnd_2683141 : Nat := 4983230072969 + 3 ^ 40 * 2683141 * 2
def baseEnd_2683141 : Nat := 1377740996785391932197965

theorem tailTrace_2683141 : CollatzResearch.WordTrace tailWord_2683141 prefixEnd_2683141 1377740996785391932197965 := by
  unfold tailWord_2683141
  simp only [CollatzResearch.WordTrace]
  refine ⟨97862191972445875845241277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65241461314963917230160851 97862191972445875845241277)
  ·
    refine ⟨36698321989667203441965479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97862191972445875845241277 36698321989667203441965479)
    ·
      refine ⟨55047482984500805162948219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36698321989667203441965479 55047482984500805162948219)
      ·
        refine ⟨82571224476751207744422329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55047482984500805162948219 82571224476751207744422329)
        ·
          refine ⟨61928418357563405808316747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82571224476751207744422329 61928418357563405808316747)
          ·
            refine ⟨92892627536345108712475121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61928418357563405808316747 92892627536345108712475121)
            ·
              refine ⟨69669470652258831534356341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92892627536345108712475121 69669470652258831534356341)
              ·
                refine ⟨6531512873649265456345907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69669470652258831534356341 6531512873649265456345907)
                ·
                  refine ⟨9797269310473898184518861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6531512873649265456345907 9797269310473898184518861)
                  ·
                    refine ⟨3673975991427711819194573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9797269310473898184518861 3673975991427711819194573)
                    ·
                      refine ⟨1377740996785391932197965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3673975991427711819194573 1377740996785391932197965)
                      ·
                        rfl

theorem cell23_2683141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 3, 3].length) (baseStart_2683141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2683141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2683141 prefixEnd_2683141 := by exact prefixLift 2683141
  have htrace : WordTrace (prefixWord ++ tailWord_2683141) baseStart_2683141 baseEnd_2683141 := by
    simpa [prefixWord, tailWord_2683141, baseEnd_2683141] using wordTrace_append hprefix tailTrace_2683141
  have hstable : (prefixWord ++ tailWord_2683141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683141).length < 2 ^ (prefixWord ++ tailWord_2683141).sum := by decide
  have hdescent : baseEnd_2683141 < baseStart_2683141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683151 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 2, 7, 2]
def baseStart_2683151 : Nat := 118140960795 + 2683151 * 2 ^ 59
def prefixEnd_2683151 : Nat := 4983230072969 + 3 ^ 40 * 2683151 * 2
def baseEnd_2683151 : Nat := 1377746131591936893072919

theorem tailTrace_2683151 : CollatzResearch.WordTrace tailWord_2683151 prefixEnd_2683151 1377746131591936893072919 := by
  unfold tailWord_2683151
  simp only [CollatzResearch.WordTrace]
  refine ⟨97862556702409647553105307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65241704468273098368736871 97862556702409647553105307)
  ·
    refine ⟨146793835053614471329657961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97862556702409647553105307 146793835053614471329657961)
    ·
      refine ⟨110095376290210853497243471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146793835053614471329657961 110095376290210853497243471)
      ·
        refine ⟨165143064435316280245865207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110095376290210853497243471 165143064435316280245865207)
        ·
          refine ⟨247714596652974420368797811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165143064435316280245865207 247714596652974420368797811)
          ·
            refine ⟨371571894979461630553196717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247714596652974420368797811 371571894979461630553196717)
            ·
              refine ⟨139339460617298111457448769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 371571894979461630553196717 139339460617298111457448769)
              ·
                refine ⟨104504595462973583593086577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139339460617298111457448769 104504595462973583593086577)
                ·
                  refine ⟨78378446597230187694814933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104504595462973583593086577 78378446597230187694814933)
                  ·
                    refine ⟨1836994842122582524097225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 78378446597230187694814933 1836994842122582524097225)
                    ·
                      refine ⟨1377746131591936893072919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1836994842122582524097225 1377746131591936893072919)
                      ·
                        rfl

theorem cell23_2683151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 7, 2].length) (baseStart_2683151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2683151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2683151 prefixEnd_2683151 := by exact prefixLift 2683151
  have htrace : WordTrace (prefixWord ++ tailWord_2683151) baseStart_2683151 baseEnd_2683151 := by
    simpa [prefixWord, tailWord_2683151, baseEnd_2683151] using wordTrace_append hprefix tailTrace_2683151
  have hstable : (prefixWord ++ tailWord_2683151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683151).length < 2 ^ (prefixWord ++ tailWord_2683151).sum := by decide
  have hdescent : baseEnd_2683151 < baseStart_2683151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683159 : List Nat := [1, 1, 3, 4, 1, 4, 1, 3, 1, 2, 2]
def baseStart_2683159 : Nat := 118140960795 + 2683159 * 2 ^ 59
def prefixEnd_2683159 : Nat := 4983230072969 + 3 ^ 40 * 2683159 * 2
def baseEnd_2683159 : Nat := 1377750239437172861772883

theorem tailTrace_2683159 : CollatzResearch.WordTrace tailWord_2683159 prefixEnd_2683159 1377750239437172861772883 := by
  unfold tailWord_2683159
  simp only [CollatzResearch.WordTrace]
  refine ⟨97862848486380664919396531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65241898990920443279597687 97862848486380664919396531)
  ·
    refine ⟨146794272729570997379094797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97862848486380664919396531 146794272729570997379094797)
    ·
      refine ⟨55047852273589124017160549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146794272729570997379094797 55047852273589124017160549)
      ·
        refine ⟨10321472301297960753217603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55047852273589124017160549 10321472301297960753217603)
        ·
          refine ⟨15482208451946941129826405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10321472301297960753217603 15482208451946941129826405)
          ·
            refine ⟨2902914084740051461842451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15482208451946941129826405 2902914084740051461842451)
            ·
              refine ⟨4354371127110077192763677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2902914084740051461842451 4354371127110077192763677)
              ·
                refine ⟨1632889172666278947286379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4354371127110077192763677 1632889172666278947286379)
                ·
                  refine ⟨2449333758999418420929569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1632889172666278947286379 2449333758999418420929569)
                  ·
                    refine ⟨1837000319249563815697177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2449333758999418420929569 1837000319249563815697177)
                    ·
                      refine ⟨1377750239437172861772883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1837000319249563815697177 1377750239437172861772883)
                      ·
                        rfl

theorem cell23_2683159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_2683159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2683159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2683159 prefixEnd_2683159 := by exact prefixLift 2683159
  have htrace : WordTrace (prefixWord ++ tailWord_2683159) baseStart_2683159 baseEnd_2683159 := by
    simpa [prefixWord, tailWord_2683159, baseEnd_2683159] using wordTrace_append hprefix tailTrace_2683159
  have hstable : (prefixWord ++ tailWord_2683159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683159).length < 2 ^ (prefixWord ++ tailWord_2683159).sum := by decide
  have hdescent : baseEnd_2683159 < baseStart_2683159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683176 : List Nat := [2, 1, 5, 1, 3, 1, 3, 2, 1, 2, 2]
def baseStart_2683176 : Nat := 118140960795 + 2683176 * 2 ^ 59
def prefixEnd_2683176 : Nat := 4983230072969 + 3 ^ 40 * 2683176 * 2
def baseEnd_2683176 : Nat := 1377758968608299295260305

theorem tailTrace_2683176 : CollatzResearch.WordTrace tailWord_2683176 prefixEnd_2683176 1377758968608299295260305 := by
  unfold tailWord_2683176
  simp only [CollatzResearch.WordTrace]
  refine ⟨48931734263659538411382691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65242312351546051215176921 48931734263659538411382691)
  ·
    refine ⟨73397601395489307617074037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48931734263659538411382691 73397601395489307617074037)
    ·
      refine ⟨6881025130827122589100691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73397601395489307617074037 6881025130827122589100691)
      ·
        refine ⟨10321537696240683883651037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6881025130827122589100691 10321537696240683883651037)
        ·
          refine ⟨3870576636090256456369139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10321537696240683883651037 3870576636090256456369139)
          ·
            refine ⟨5805864954135384684553709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3870576636090256456369139 5805864954135384684553709)
            ·
              refine ⟨2177199357800769256707641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5805864954135384684553709 2177199357800769256707641)
              ·
                refine ⟨1632899518350576942530731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2177199357800769256707641 1632899518350576942530731)
                ·
                  refine ⟨2449349277525865413796097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1632899518350576942530731 2449349277525865413796097)
                  ·
                    refine ⟨1837011958144399060347073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2449349277525865413796097 1837011958144399060347073)
                    ·
                      refine ⟨1377758968608299295260305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1837011958144399060347073 1377758968608299295260305)
                      ·
                        rfl

theorem cell23_2683176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_2683176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2683176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2683176 prefixEnd_2683176 := by exact prefixLift 2683176
  have htrace : WordTrace (prefixWord ++ tailWord_2683176) baseStart_2683176 baseEnd_2683176 := by
    simpa [prefixWord, tailWord_2683176, baseEnd_2683176] using wordTrace_append hprefix tailTrace_2683176
  have hstable : (prefixWord ++ tailWord_2683176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683176).length < 2 ^ (prefixWord ++ tailWord_2683176).sum := by decide
  have hdescent : baseEnd_2683176 < baseStart_2683176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683248 : List Nat := [2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 3]
def baseStart_2683248 : Nat := 118140960795 + 2683248 * 2 ^ 59
def prefixEnd_2683248 : Nat := 4983230072969 + 3 ^ 40 * 2683248 * 2
def baseEnd_2683248 : Nat := 1377795939215423013559973

theorem tailTrace_2683248 : CollatzResearch.WordTrace tailWord_2683248 prefixEnd_2683248 1377795939215423013559973 := by
  unfold tailWord_2683248
  simp only [CollatzResearch.WordTrace]
  refine ⟨48933047291529116559693199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65244063055372155412924265 48933047291529116559693199)
  ·
    refine ⟨73399570937293674839539799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48933047291529116559693199 73399570937293674839539799)
    ·
      refine ⟨110099356405940512259309699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73399570937293674839539799 110099356405940512259309699)
      ·
        refine ⟨165149034608910768388964549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110099356405940512259309699 165149034608910768388964549)
        ·
          refine ⟨30965443989170769072930853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165149034608910768388964549 30965443989170769072930853)
          ·
            refine ⟨5806020747969519201174535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30965443989170769072930853 5806020747969519201174535)
            ·
              refine ⟨8709031121954278801761803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5806020747969519201174535 8709031121954278801761803)
              ·
                refine ⟨13063546682931418202642705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8709031121954278801761803 13063546682931418202642705)
                ·
                  refine ⟨9797660012198563651982029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13063546682931418202642705 9797660012198563651982029)
                  ·
                    refine ⟨3674122504574461369493261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9797660012198563651982029 3674122504574461369493261)
                    ·
                      refine ⟨1377795939215423013559973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3674122504574461369493261 1377795939215423013559973)
                      ·
                        rfl

theorem cell23_2683248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 3].length) (baseStart_2683248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2683248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2683248 prefixEnd_2683248 := by exact prefixLift 2683248
  have htrace : WordTrace (prefixWord ++ tailWord_2683248) baseStart_2683248 baseEnd_2683248 := by
    simpa [prefixWord, tailWord_2683248, baseEnd_2683248] using wordTrace_append hprefix tailTrace_2683248
  have hstable : (prefixWord ++ tailWord_2683248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683248).length < 2 ^ (prefixWord ++ tailWord_2683248).sum := by decide
  have hdescent : baseEnd_2683248 < baseStart_2683248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683301 : List Nat := [1, 3, 1, 2, 1, 1, 3, 2, 2, 1, 6]
def baseStart_2683301 : Nat := 118140960795 + 2683301 * 2 ^ 59
def prefixEnd_2683301 : Nat := 4983230072969 + 3 ^ 40 * 2683301 * 2
def baseEnd_2683301 : Nat := 1377823153690111306197229

theorem tailTrace_2683301 : CollatzResearch.WordTrace tailWord_2683301 prefixEnd_2683301 1377823153690111306197229 := by
  unfold tailWord_2683301
  simp only [CollatzResearch.WordTrace]
  refine ⟨97868027651866223171065757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65245351767910815447377171 97868027651866223171065757)
  ·
    refine ⟨36700510369449833689149659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97868027651866223171065757 36700510369449833689149659)
    ·
      refine ⟨55050765554174750533724489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36700510369449833689149659 55050765554174750533724489)
      ·
        refine ⟨41288074165631062900293367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55050765554174750533724489 41288074165631062900293367)
        ·
          refine ⟨61932111248446594350440051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41288074165631062900293367 61932111248446594350440051)
          ·
            refine ⟨92898166872669891525660077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61932111248446594350440051 92898166872669891525660077)
            ·
              refine ⟨34836812577251209322122529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92898166872669891525660077 34836812577251209322122529)
              ·
                refine ⟨26127609432938406991591897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34836812577251209322122529 26127609432938406991591897)
                ·
                  refine ⟨19595707074703805243693923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26127609432938406991591897 19595707074703805243693923)
                  ·
                    refine ⟨29393560612055707865540885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19595707074703805243693923 29393560612055707865540885)
                    ·
                      refine ⟨1377823153690111306197229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29393560612055707865540885 1377823153690111306197229)
                      ·
                        rfl

theorem cell23_2683301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_2683301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2683301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2683301 prefixEnd_2683301 := by exact prefixLift 2683301
  have htrace : WordTrace (prefixWord ++ tailWord_2683301) baseStart_2683301 baseEnd_2683301 := by
    simpa [prefixWord, tailWord_2683301, baseEnd_2683301] using wordTrace_append hprefix tailTrace_2683301
  have hstable : (prefixWord ++ tailWord_2683301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683301).length < 2 ^ (prefixWord ++ tailWord_2683301).sum := by decide
  have hdescent : baseEnd_2683301 < baseStart_2683301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683349 : List Nat := [1, 3, 2, 3, 1, 3, 3, 2, 1, 4]
def baseStart_2683349 : Nat := 118140960795 + 2683349 * 2 ^ 59
def prefixEnd_2683349 : Nat := 4983230072969 + 3 ^ 40 * 2683349 * 2
def baseEnd_2683349 : Nat := 459282600253842372799003

theorem tailTrace_2683349 : CollatzResearch.WordTrace tailWord_2683349 prefixEnd_2683349 459282600253842372799003 := by
  unfold tailWord_2683349
  simp only [CollatzResearch.WordTrace]
  refine ⟨97869778355692327368813101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65246518903794884912542067 97869778355692327368813101)
  ·
    refine ⟨36701166883384622763304913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97869778355692327368813101 36701166883384622763304913)
    ·
      refine ⟨27525875162538467072478685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36701166883384622763304913 27525875162538467072478685)
      ·
        refine ⟨10322203185951925152179507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27525875162538467072478685 10322203185951925152179507)
        ·
          refine ⟨15483304778927887728269261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10322203185951925152179507 15483304778927887728269261)
          ·
            refine ⟨5806239292097957898100973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15483304778927887728269261 5806239292097957898100973)
            ·
              refine ⟨2177339734536734211787865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5806239292097957898100973 2177339734536734211787865)
              ·
                refine ⟨1633004800902550658840899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2177339734536734211787865 1633004800902550658840899)
                ·
                  refine ⟨2449507201353825988261349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1633004800902550658840899 2449507201353825988261349)
                  ·
                    refine ⟨459282600253842372799003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2449507201353825988261349 459282600253842372799003)
                    ·
                      rfl

theorem cell23_2683349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 2, 1, 4].length) (baseStart_2683349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2683349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2683349 prefixEnd_2683349 := by exact prefixLift 2683349
  have htrace : WordTrace (prefixWord ++ tailWord_2683349) baseStart_2683349 baseEnd_2683349 := by
    simpa [prefixWord, tailWord_2683349, baseEnd_2683349] using wordTrace_append hprefix tailTrace_2683349
  have hstable : (prefixWord ++ tailWord_2683349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683349).length < 2 ^ (prefixWord ++ tailWord_2683349).sum := by decide
  have hdescent : baseEnd_2683349 < baseStart_2683349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683351 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 7]
def baseStart_2683351 : Nat := 118140960795 + 2683351 * 2 ^ 59
def prefixEnd_2683351 : Nat := 4983230072969 + 3 ^ 40 * 2683351 * 2
def baseEnd_2683351 : Nat := 1377848827722836110571999

theorem tailTrace_2683351 : CollatzResearch.WordTrace tailWord_2683351 prefixEnd_2683351 1377848827722836110571999 := by
  unfold tailWord_2683351
  simp only [CollatzResearch.WordTrace]
  refine ⟨97869851301685081710385907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65246567534456721140257271 97869851301685081710385907)
  ·
    refine ⟨146804776952527622565578861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97869851301685081710385907 146804776952527622565578861)
    ·
      refine ⟨55051791357197858462092073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146804776952527622565578861 55051791357197858462092073)
      ·
        refine ⟨41288843517898393846569055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55051791357197858462092073 41288843517898393846569055)
        ·
          refine ⟨61933265276847590769853583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41288843517898393846569055 61933265276847590769853583)
          ·
            refine ⟨92899897915271386154780375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61933265276847590769853583 92899897915271386154780375)
            ·
              refine ⟨139349846872907079232170563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92899897915271386154780375 139349846872907079232170563)
              ·
                refine ⟨209024770309360618848255845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139349846872907079232170563 209024770309360618848255845)
                ·
                  refine ⟨39192144433005116034047971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 209024770309360618848255845 39192144433005116034047971)
                  ·
                    refine ⟨58788216649507674051071957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39192144433005116034047971 58788216649507674051071957)
                    ·
                      refine ⟨1377848827722836110571999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 58788216649507674051071957 1377848827722836110571999)
                      ·
                        rfl

theorem cell23_2683351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_2683351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2683351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2683351 prefixEnd_2683351 := by exact prefixLift 2683351
  have htrace : WordTrace (prefixWord ++ tailWord_2683351) baseStart_2683351 baseEnd_2683351 := by
    simpa [prefixWord, tailWord_2683351, baseEnd_2683351] using wordTrace_append hprefix tailTrace_2683351
  have hstable : (prefixWord ++ tailWord_2683351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683351).length < 2 ^ (prefixWord ++ tailWord_2683351).sum := by decide
  have hdescent : baseEnd_2683351 < baseStart_2683351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683406 : List Nat := [4, 1, 1, 2, 3, 1, 4, 2, 1, 1, 3]
def baseStart_2683406 : Nat := 118140960795 + 2683406 * 2 ^ 59
def prefixEnd_2683406 : Nat := 4983230072969 + 3 ^ 40 * 2683406 * 2
def baseEnd_2683406 : Nat := 1377877069158833395384247

theorem tailTrace_2683406 : CollatzResearch.WordTrace tailWord_2683406 prefixEnd_2683406 1377877069158833395384247 := by
  unfold tailWord_2683406
  simp only [CollatzResearch.WordTrace]
  refine ⟨12233982164560728262954759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65247904877657217402425381 12233982164560728262954759)
  ·
    refine ⟨18350973246841092394432139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12233982164560728262954759 18350973246841092394432139)
    ·
      refine ⟨27526459870261638591648209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18350973246841092394432139 27526459870261638591648209)
      ·
        refine ⟨20644844902696228943736157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27526459870261638591648209 20644844902696228943736157)
        ·
          refine ⟨7741816838511085853901059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20644844902696228943736157 7741816838511085853901059)
          ·
            refine ⟨11612725257766628780851589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7741816838511085853901059 11612725257766628780851589)
            ·
              refine ⟨2177385985831242896409673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11612725257766628780851589 2177385985831242896409673)
              ·
                refine ⟨1633039489373432172307255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2177385985831242896409673 1633039489373432172307255)
                ·
                  refine ⟨2449559234060148258460883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1633039489373432172307255 2449559234060148258460883)
                  ·
                    refine ⟨3674338851090222387691325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2449559234060148258460883 3674338851090222387691325)
                    ·
                      refine ⟨1377877069158833395384247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3674338851090222387691325 1377877069158833395384247)
                      ·
                        rfl

theorem cell23_2683406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 2, 1, 1, 3].length) (baseStart_2683406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2683406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2683406 prefixEnd_2683406 := by exact prefixLift 2683406
  have htrace : WordTrace (prefixWord ++ tailWord_2683406) baseStart_2683406 baseEnd_2683406 := by
    simpa [prefixWord, tailWord_2683406, baseEnd_2683406] using wordTrace_append hprefix tailTrace_2683406
  have hstable : (prefixWord ++ tailWord_2683406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683406).length < 2 ^ (prefixWord ++ tailWord_2683406).sum := by decide
  have hdescent : baseEnd_2683406 < baseStart_2683406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683412 : List Nat := [2, 4, 3, 1, 1, 1, 1, 2, 3, 1, 4]
def baseStart_2683412 : Nat := 118140960795 + 2683412 * 2 ^ 59
def prefixEnd_2683412 : Nat := 4983230072969 + 3 ^ 40 * 2683412 * 2
def baseEnd_2683412 : Nat := 1377880150042760371909219

theorem tailTrace_2683412 : CollatzResearch.WordTrace tailWord_2683412 prefixEnd_2683412 1377880150042760371909219 := by
  unfold tailWord_2683412
  simp only [CollatzResearch.WordTrace]
  refine ⟨48936038077232044564178245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65248050769642726085570993 48936038077232044564178245)
  ·
    refine ⟨9175507139481008355783421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48936038077232044564178245 9175507139481008355783421)
    ·
      refine ⟨3440815177305378133418783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9175507139481008355783421 3440815177305378133418783)
      ·
        refine ⟨5161222765958067200128175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3440815177305378133418783 5161222765958067200128175)
        ·
          refine ⟨7741834148937100800192263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5161222765958067200128175 7741834148937100800192263)
          ·
            refine ⟨11612751223405651200288395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7741834148937100800192263 11612751223405651200288395)
            ·
              refine ⟨17419126835108476800432593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11612751223405651200288395 17419126835108476800432593)
              ·
                refine ⟨13064345126331357600324445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17419126835108476800432593 13064345126331357600324445)
                ·
                  refine ⟨4899129422374259100121667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13064345126331357600324445 4899129422374259100121667)
                  ·
                    refine ⟨7348694133561388650182501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4899129422374259100121667 7348694133561388650182501)
                    ·
                      refine ⟨1377880150042760371909219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7348694133561388650182501 1377880150042760371909219)
                      ·
                        rfl

theorem cell23_2683412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_2683412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2683412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2683412 prefixEnd_2683412 := by exact prefixLift 2683412
  have htrace : WordTrace (prefixWord ++ tailWord_2683412) baseStart_2683412 baseEnd_2683412 := by
    simpa [prefixWord, tailWord_2683412, baseEnd_2683412] using wordTrace_append hprefix tailTrace_2683412
  have hstable : (prefixWord ++ tailWord_2683412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683412).length < 2 ^ (prefixWord ++ tailWord_2683412).sum := by decide
  have hdescent : baseEnd_2683412 < baseStart_2683412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683418 : List Nat := [3, 1, 1, 3, 1, 1, 5, 8]
def baseStart_2683418 : Nat := 118140960795 + 2683418 * 2 ^ 59
def prefixEnd_2683418 : Nat := 4983230072969 + 3 ^ 40 * 2683418 * 2
def baseEnd_2683418 : Nat := 51032712256543975867933

theorem tailTrace_2683418 : CollatzResearch.WordTrace tailWord_2683418 prefixEnd_2683418 51032712256543975867933 := by
  unfold tailWord_2683418
  simp only [CollatzResearch.WordTrace]
  refine ⟨24468073748110588038268727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65248196661628234768716605 24468073748110588038268727)
  ·
    refine ⟨36702110622165882057403091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24468073748110588038268727 36702110622165882057403091)
    ·
      refine ⟨55053165933248823086104637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36702110622165882057403091 55053165933248823086104637)
      ·
        refine ⟨20644937224968308657289239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55053165933248823086104637 20644937224968308657289239)
        ·
          refine ⟨30967405837452462985933859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20644937224968308657289239 30967405837452462985933859)
          ·
            refine ⟨46451108756178694478900789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30967405837452462985933859 46451108756178694478900789)
            ·
              refine ⟨4354791445891752607396949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46451108756178694478900789 4354791445891752607396949)
              ·
                refine ⟨51032712256543975867933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4354791445891752607396949 51032712256543975867933)
                ·
                  rfl

theorem cell23_2683418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 8].length) (baseStart_2683418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2683418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2683418 prefixEnd_2683418 := by exact prefixLift 2683418
  have htrace : WordTrace (prefixWord ++ tailWord_2683418) baseStart_2683418 baseEnd_2683418 := by
    simpa [prefixWord, tailWord_2683418, baseEnd_2683418] using wordTrace_append hprefix tailTrace_2683418
  have hstable : (prefixWord ++ tailWord_2683418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683418).length < 2 ^ (prefixWord ++ tailWord_2683418).sum := by decide
  have hdescent : baseEnd_2683418 < baseStart_2683418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683425 : List Nat := [1, 2, 3, 2, 2, 1, 4, 1, 1, 2, 4]
def baseStart_2683425 : Nat := 118140960795 + 2683425 * 2 ^ 59
def prefixEnd_2683425 : Nat := 4983230072969 + 3 ^ 40 * 2683425 * 2
def baseEnd_2683425 : Nat := 1377886825291268821046659

theorem tailTrace_2683425 : CollatzResearch.WordTrace tailWord_2683425 prefixEnd_2683425 1377886825291268821046659 := by
  unfold tailWord_2683425
  simp only [CollatzResearch.WordTrace]
  refine ⟨97872550303416992348579729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65248366868944661565719819 97872550303416992348579729)
  ·
    refine ⟨73404412727562744261434797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97872550303416992348579729 73404412727562744261434797)
    ·
      refine ⟨27526654772836029098038049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73404412727562744261434797 27526654772836029098038049)
      ·
        refine ⟨20644991079627021823528537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27526654772836029098038049 20644991079627021823528537)
        ·
          refine ⟨15483743309720266367646403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20644991079627021823528537 15483743309720266367646403)
          ·
            refine ⟨23225614964580399551469605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15483743309720266367646403 23225614964580399551469605)
            ·
              refine ⟨4354802805858824915900551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23225614964580399551469605 4354802805858824915900551)
              ·
                refine ⟨6532204208788237373850827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4354802805858824915900551 6532204208788237373850827)
                ·
                  refine ⟨9798306313182356060776241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6532204208788237373850827 9798306313182356060776241)
                  ·
                    refine ⟨7348729734886767045582181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9798306313182356060776241 7348729734886767045582181)
                    ·
                      refine ⟨1377886825291268821046659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7348729734886767045582181 1377886825291268821046659)
                      ·
                        rfl

theorem cell23_2683425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_2683425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2683425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2683425 prefixEnd_2683425 := by exact prefixLift 2683425
  have htrace : WordTrace (prefixWord ++ tailWord_2683425) baseStart_2683425 baseEnd_2683425 := by
    simpa [prefixWord, tailWord_2683425, baseEnd_2683425] using wordTrace_append hprefix tailTrace_2683425
  have hstable : (prefixWord ++ tailWord_2683425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683425).length < 2 ^ (prefixWord ++ tailWord_2683425).sum := by decide
  have hdescent : baseEnd_2683425 < baseStart_2683425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683432 : List Nat := [2, 1, 5, 2, 1, 1, 2, 1, 3, 2, 3]
def baseStart_2683432 : Nat := 118140960795 + 2683432 * 2 ^ 59
def prefixEnd_2683432 : Nat := 4983230072969 + 3 ^ 40 * 2683432 * 2
def baseEnd_2683432 : Nat := 1377890419655850293659127

theorem tailTrace_2683432 : CollatzResearch.WordTrace tailWord_2683432 prefixEnd_2683432 1377890419655850293659127 := by
  unfold tailWord_2683432
  simp only [CollatzResearch.WordTrace]
  refine ⟨48936402807195816272042275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65248537076261088362723033 48936402807195816272042275)
  ·
    refine ⟨73404604210793724408063413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48936402807195816272042275 73404604210793724408063413)
    ·
      refine ⟨6881681644761911663255945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73404604210793724408063413 6881681644761911663255945)
      ·
        refine ⟨5161261233571433747441959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6881681644761911663255945 5161261233571433747441959)
        ·
          refine ⟨7741891850357150621162939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5161261233571433747441959 7741891850357150621162939)
          ·
            refine ⟨11612837775535725931744409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7741891850357150621162939 11612837775535725931744409)
            ·
              refine ⟨8709628331651794448808307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11612837775535725931744409 8709628331651794448808307)
              ·
                refine ⟨13064442497477691673212461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8709628331651794448808307 13064442497477691673212461)
                ·
                  refine ⟨4899165936554134377454673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13064442497477691673212461 4899165936554134377454673)
                  ·
                    refine ⟨3674374452415600783091005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4899165936554134377454673 3674374452415600783091005)
                    ·
                      refine ⟨1377890419655850293659127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3674374452415600783091005 1377890419655850293659127)
                      ·
                        rfl

theorem cell23_2683432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_2683432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2683432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2683432 prefixEnd_2683432 := by exact prefixLift 2683432
  have htrace : WordTrace (prefixWord ++ tailWord_2683432) baseStart_2683432 baseEnd_2683432 := by
    simpa [prefixWord, tailWord_2683432, baseEnd_2683432] using wordTrace_append hprefix tailTrace_2683432
  have hstable : (prefixWord ++ tailWord_2683432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683432).length < 2 ^ (prefixWord ++ tailWord_2683432).sum := by decide
  have hdescent : baseEnd_2683432 < baseStart_2683432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683445 : List Nat := [1, 3, 3, 1, 1, 2, 1, 4, 1, 3, 3]
def baseStart_2683445 : Nat := 118140960795 + 2683445 * 2 ^ 59
def prefixEnd_2683445 : Nat := 4983230072969 + 3 ^ 40 * 2683445 * 2
def baseEnd_2683445 : Nat := 1377897094904358742796567

theorem tailTrace_2683445 : CollatzResearch.WordTrace tailWord_2683445 prefixEnd_2683445 1377897094904358742796567 := by
  unfold tailWord_2683445
  simp only [CollatzResearch.WordTrace]
  refine ⟨97873279763344535764307789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65248853175563023842871859 97873279763344535764307789)
  ·
    refine ⟨36702479911254200911615421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97873279763344535764307789 36702479911254200911615421)
    ·
      refine ⟨13763429966720325341855783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36702479911254200911615421 13763429966720325341855783)
      ·
        refine ⟨20645144950080488012783675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13763429966720325341855783 20645144950080488012783675)
        ·
          refine ⟨30967717425120732019175513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20645144950080488012783675 30967717425120732019175513)
          ·
            refine ⟨23225788068840549014381635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30967717425120732019175513 23225788068840549014381635)
            ·
              refine ⟨34838682103260823521572453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23225788068840549014381635 34838682103260823521572453)
              ·
                refine ⟨6532252894361404410294835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34838682103260823521572453 6532252894361404410294835)
                ·
                  refine ⟨9798379341542106615442253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6532252894361404410294835 9798379341542106615442253)
                  ·
                    refine ⟨3674392253078289980790845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9798379341542106615442253 3674392253078289980790845)
                    ·
                      refine ⟨1377897094904358742796567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3674392253078289980790845 1377897094904358742796567)
                      ·
                        rfl

theorem cell23_2683445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_2683445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2683445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2683445 prefixEnd_2683445 := by exact prefixLift 2683445
  have htrace : WordTrace (prefixWord ++ tailWord_2683445) baseStart_2683445 baseEnd_2683445 := by
    simpa [prefixWord, tailWord_2683445, baseEnd_2683445] using wordTrace_append hprefix tailTrace_2683445
  have hstable : (prefixWord ++ tailWord_2683445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683445).length < 2 ^ (prefixWord ++ tailWord_2683445).sum := by decide
  have hdescent : baseEnd_2683445 < baseStart_2683445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683446 : List Nat := [5, 1, 2, 1, 2, 3, 2, 1, 1, 1, 4]
def baseStart_2683446 : Nat := 118140960795 + 2683446 * 2 ^ 59
def prefixEnd_2683446 : Nat := 4983230072969 + 3 ^ 40 * 2683446 * 2
def baseEnd_2683446 : Nat := 1377897608385013238884063

theorem tailTrace_2683446 : CollatzResearch.WordTrace tailWord_2683446 prefixEnd_2683446 1377897608385013238884063 := by
  unfold tailWord_2683446
  simp only [CollatzResearch.WordTrace]
  refine ⟨6117082264771307058443387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65248877490893941956729461 6117082264771307058443387)
  ·
    refine ⟨9175623397156960587665081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6117082264771307058443387 9175623397156960587665081)
    ·
      refine ⟨6881717547867720440748811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9175623397156960587665081 6881717547867720440748811)
      ·
        refine ⟨10322576321801580661123217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6881717547867720440748811 10322576321801580661123217)
        ·
          refine ⟨7741932241351185495842413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10322576321801580661123217 7741932241351185495842413)
          ·
            refine ⟨2903224590506694560940905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7741932241351185495842413 2903224590506694560940905)
            ·
              refine ⟨2177418442880020920705679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2903224590506694560940905 2177418442880020920705679)
              ·
                refine ⟨3266127664320031381058519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2177418442880020920705679 3266127664320031381058519)
                ·
                  refine ⟨4899191496480047071587779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3266127664320031381058519 4899191496480047071587779)
                  ·
                    refine ⟨7348787244720070607381669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4899191496480047071587779 7348787244720070607381669)
                    ·
                      refine ⟨1377897608385013238884063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7348787244720070607381669 1377897608385013238884063)
                      ·
                        rfl

theorem cell23_2683446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_2683446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2683446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2683446 prefixEnd_2683446 := by exact prefixLift 2683446
  have htrace : WordTrace (prefixWord ++ tailWord_2683446) baseStart_2683446 baseEnd_2683446 := by
    simpa [prefixWord, tailWord_2683446, baseEnd_2683446] using wordTrace_append hprefix tailTrace_2683446
  have hstable : (prefixWord ++ tailWord_2683446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683446).length < 2 ^ (prefixWord ++ tailWord_2683446).sum := by decide
  have hdescent : baseEnd_2683446 < baseStart_2683446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683479 : List Nat := [1, 1, 3, 2, 2, 2, 5, 1, 2, 1, 3]
def baseStart_2683479 : Nat := 118140960795 + 2683479 * 2 ^ 59
def prefixEnd_2683479 : Nat := 4983230072969 + 3 ^ 40 * 2683479 * 2
def baseEnd_2683479 : Nat := 1377914553246611609771411

theorem tailTrace_2683479 : CollatzResearch.WordTrace tailWord_2683479 prefixEnd_2683479 1377914553246611609771411 := by
  unfold tailWord_2683479
  simp only [CollatzResearch.WordTrace]
  refine ⟨97874519845221359571045491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65249679896814239714030327 97874519845221359571045491)
  ·
    refine ⟨146811779767832039356568237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97874519845221359571045491 146811779767832039356568237)
    ·
      refine ⟨55054417412937014758713089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146811779767832039356568237 55054417412937014758713089)
      ·
        refine ⟨41290813059702761069034817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55054417412937014758713089 41290813059702761069034817)
        ·
          refine ⟨30968109794777070801776113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41290813059702761069034817 30968109794777070801776113)
          ·
            refine ⟨23226082346082803101332085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30968109794777070801776113 23226082346082803101332085)
            ·
              refine ⟨2177445219945262790749883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23226082346082803101332085 2177445219945262790749883)
              ·
                refine ⟨3266167829917894186124825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2177445219945262790749883 3266167829917894186124825)
                ·
                  refine ⟨2449625872438420639593619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3266167829917894186124825 2449625872438420639593619)
                  ·
                    refine ⟨3674438808657630959390429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2449625872438420639593619 3674438808657630959390429)
                    ·
                      refine ⟨1377914553246611609771411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3674438808657630959390429 1377914553246611609771411)
                      ·
                        rfl

theorem cell23_2683479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 1, 2, 1, 3].length) (baseStart_2683479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2683479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2683479 prefixEnd_2683479 := by exact prefixLift 2683479
  have htrace : WordTrace (prefixWord ++ tailWord_2683479) baseStart_2683479 baseEnd_2683479 := by
    simpa [prefixWord, tailWord_2683479, baseEnd_2683479] using wordTrace_append hprefix tailTrace_2683479
  have hstable : (prefixWord ++ tailWord_2683479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683479).length < 2 ^ (prefixWord ++ tailWord_2683479).sum := by decide
  have hdescent : baseEnd_2683479 < baseStart_2683479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683489 : List Nat := [1, 2, 3, 1, 1, 5, 2, 2, 1, 3, 2]
def baseStart_2683489 : Nat := 118140960795 + 2683489 * 2 ^ 59
def prefixEnd_2683489 : Nat := 4983230072969 + 3 ^ 40 * 2683489 * 2
def baseEnd_2683489 : Nat := 1377919688053156570646365

theorem tailTrace_2683489 : CollatzResearch.WordTrace tailWord_2683489 prefixEnd_2683489 1377919688053156570646365 := by
  unfold tailWord_2683489
  simp only [CollatzResearch.WordTrace]
  refine ⟨97874884575185131278909521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65249923050123420852606347 97874884575185131278909521)
  ·
    refine ⟨73406163431388848459182141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97874884575185131278909521 73406163431388848459182141)
    ·
      refine ⟨27527311286770818172193303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73406163431388848459182141 27527311286770818172193303)
      ·
        refine ⟨41290966930156227258289955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27527311286770818172193303 41290966930156227258289955)
        ·
          refine ⟨61936450395234340887434933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41290966930156227258289955 61936450395234340887434933)
          ·
            refine ⟨5806542224553219458197025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61936450395234340887434933 5806542224553219458197025)
            ·
              refine ⟨4354906668414914593647769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5806542224553219458197025 4354906668414914593647769)
              ·
                refine ⟨3266180001311185945235827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4354906668414914593647769 3266180001311185945235827)
                ·
                  refine ⟨4899270001966778917853741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3266180001311185945235827 4899270001966778917853741)
                  ·
                    refine ⟨1837226250737542094195153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4899270001966778917853741 1837226250737542094195153)
                    ·
                      refine ⟨1377919688053156570646365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1837226250737542094195153 1377919688053156570646365)
                      ·
                        rfl

theorem cell23_2683489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 2, 1, 3, 2].length) (baseStart_2683489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2683489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2683489 prefixEnd_2683489 := by exact prefixLift 2683489
  have htrace : WordTrace (prefixWord ++ tailWord_2683489) baseStart_2683489 baseEnd_2683489 := by
    simpa [prefixWord, tailWord_2683489, baseEnd_2683489] using wordTrace_append hprefix tailTrace_2683489
  have hstable : (prefixWord ++ tailWord_2683489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683489).length < 2 ^ (prefixWord ++ tailWord_2683489).sum := by decide
  have hdescent : baseEnd_2683489 < baseStart_2683489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683525 : List Nat := [1, 3, 1, 1, 4, 2, 3, 1, 7]
def baseStart_2683525 : Nat := 118140960795 + 2683525 * 2 ^ 59
def prefixEnd_2683525 : Nat := 4983230072969 + 3 ^ 40 * 2683525 * 2
def baseEnd_2683525 : Nat := 153104241484079825532911

theorem tailTrace_2683525 : CollatzResearch.WordTrace tailWord_2683525 prefixEnd_2683525 153104241484079825532911 := by
  unfold tailWord_2683525
  simp only [CollatzResearch.WordTrace]
  refine ⟨97876197603054709427220029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65250798402036472951480019 97876197603054709427220029)
  ·
    refine ⟨36703574101145516035207511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97876197603054709427220029 36703574101145516035207511)
    ·
      refine ⟨55055361151718274052811267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36703574101145516035207511 55055361151718274052811267)
      ·
        refine ⟨82583041727577411079216901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55055361151718274052811267 82583041727577411079216901)
        ·
          refine ⟨15484320323920764577353169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82583041727577411079216901 15484320323920764577353169)
          ·
            refine ⟨11613240242940573433014877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15484320323920764577353169 11613240242940573433014877)
            ·
              refine ⟨4354965091102715037380579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11613240242940573433014877 4354965091102715037380579)
              ·
                refine ⟨6532447636654072556070869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4354965091102715037380579 6532447636654072556070869)
                ·
                  refine ⟨153104241484079825532911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6532447636654072556070869 153104241484079825532911)
                  ·
                    rfl

theorem cell23_2683525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 7].length) (baseStart_2683525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2683525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2683525 prefixEnd_2683525 := by exact prefixLift 2683525
  have htrace : WordTrace (prefixWord ++ tailWord_2683525) baseStart_2683525 baseEnd_2683525 := by
    simpa [prefixWord, tailWord_2683525, baseEnd_2683525] using wordTrace_append hprefix tailTrace_2683525
  have hstable : (prefixWord ++ tailWord_2683525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683525).length < 2 ^ (prefixWord ++ tailWord_2683525).sum := by decide
  have hdescent : baseEnd_2683525 < baseStart_2683525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683592 : List Nat := [2, 1, 3, 1, 2, 3, 1, 1, 1, 6, 2]
def baseStart_2683592 : Nat := 118140960795 + 2683592 * 2 ^ 59
def prefixEnd_2683592 : Nat := 4983230072969 + 3 ^ 40 * 2683592 * 2
def baseEnd_2683592 : Nat := 1377972576560569667658391

theorem tailTrace_2683592 : CollatzResearch.WordTrace tailWord_2683592 prefixEnd_2683592 1377972576560569667658391 := by
  unfold tailWord_2683592
  simp only [CollatzResearch.WordTrace]
  refine ⟨48939320646905989934954515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65252427529207986579939353 48939320646905989934954515)
  ·
    refine ⟨73408980970358984902431773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48939320646905989934954515 73408980970358984902431773)
    ·
      refine ⟨27528367863884619338411915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73408980970358984902431773 27528367863884619338411915)
      ·
        refine ⟨41292551795826929007617873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27528367863884619338411915 41292551795826929007617873)
        ·
          refine ⟨30969413846870196755713405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41292551795826929007617873 30969413846870196755713405)
          ·
            refine ⟨11613530192576323783392527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30969413846870196755713405 11613530192576323783392527)
            ·
              refine ⟨17420295288864485675088791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11613530192576323783392527 17420295288864485675088791)
              ·
                refine ⟨26130442933296728512633187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17420295288864485675088791 26130442933296728512633187)
                ·
                  refine ⟨39195664399945092768949781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26130442933296728512633187 39195664399945092768949781)
                  ·
                    refine ⟨1837296768747426223544521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 39195664399945092768949781 1837296768747426223544521)
                    ·
                      refine ⟨1377972576560569667658391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1837296768747426223544521 1377972576560569667658391)
                      ·
                        rfl

theorem cell23_2683592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 1, 6, 2].length) (baseStart_2683592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2683592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2683592 prefixEnd_2683592 := by exact prefixLift 2683592
  have htrace : WordTrace (prefixWord ++ tailWord_2683592) baseStart_2683592 baseEnd_2683592 := by
    simpa [prefixWord, tailWord_2683592, baseEnd_2683592] using wordTrace_append hprefix tailTrace_2683592
  have hstable : (prefixWord ++ tailWord_2683592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683592).length < 2 ^ (prefixWord ++ tailWord_2683592).sum := by decide
  have hdescent : baseEnd_2683592 < baseStart_2683592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683669 : List Nat := [1, 3, 2, 1, 2, 2, 2, 3, 2, 3, 2]
def baseStart_2683669 : Nat := 118140960795 + 2683669 * 2 ^ 59
def prefixEnd_2683669 : Nat := 4983230072969 + 3 ^ 40 * 2683669 * 2
def baseEnd_2683669 : Nat := 1378012114570965866395537

theorem tailTrace_2683669 : CollatzResearch.WordTrace tailWord_2683669 prefixEnd_2683669 1378012114570965866395537 := by
  unfold tailWord_2683669
  simp only [CollatzResearch.WordTrace]
  refine ⟨97881449714533022020462061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65254299809688681346974707 97881449714533022020462061)
  ·
    refine ⟨36705543642949883257673273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97881449714533022020462061 36705543642949883257673273)
    ·
      refine ⟨27529157732212412443254955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36705543642949883257673273 27529157732212412443254955)
      ·
        refine ⟨41293736598318618664882433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27529157732212412443254955 41293736598318618664882433)
        ·
          refine ⟨30970302448738963998661825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41293736598318618664882433 30970302448738963998661825)
          ·
            refine ⟨23227726836554222998996369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30970302448738963998661825 23227726836554222998996369)
            ·
              refine ⟨17420795127415667249247277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23227726836554222998996369 17420795127415667249247277)
              ·
                refine ⟨6532798172780875218467729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17420795127415667249247277 6532798172780875218467729)
                ·
                  refine ⟨4899598629585656413850797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6532798172780875218467729 4899598629585656413850797)
                  ·
                    refine ⟨1837349486094621155194049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4899598629585656413850797 1837349486094621155194049)
                    ·
                      refine ⟨1378012114570965866395537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1837349486094621155194049 1378012114570965866395537)
                      ·
                        rfl

theorem cell23_2683669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 2, 3, 2].length) (baseStart_2683669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2683669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2683669 prefixEnd_2683669 := by exact prefixLift 2683669
  have htrace : WordTrace (prefixWord ++ tailWord_2683669) baseStart_2683669 baseEnd_2683669 := by
    simpa [prefixWord, tailWord_2683669, baseEnd_2683669] using wordTrace_append hprefix tailTrace_2683669
  have hstable : (prefixWord ++ tailWord_2683669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683669).length < 2 ^ (prefixWord ++ tailWord_2683669).sum := by decide
  have hdescent : baseEnd_2683669 < baseStart_2683669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683692 : List Nat := [2, 2, 1, 1, 1, 4, 1, 3, 4, 4]
def baseStart_2683692 : Nat := 118140960795 + 2683692 * 2 ^ 59
def prefixEnd_2683692 : Nat := 4983230072969 + 3 ^ 40 * 2683692 * 2
def baseEnd_2683692 : Nat := 459341308208673092135977

theorem tailTrace_2683692 : CollatzResearch.WordTrace tailWord_2683692 prefixEnd_2683692 459341308208673092135977 := by
  unfold tailWord_2683692
  simp only [CollatzResearch.WordTrace]
  refine ⟨48941144296724848474274665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65254859062299797965699553 48941144296724848474274665)
  ·
    refine ⟨36705858222543636355705999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48941144296724848474274665 36705858222543636355705999)
    ·
      refine ⟨55058787333815454533558999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36705858222543636355705999 55058787333815454533558999)
      ·
        refine ⟨82588181000723181800338499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55058787333815454533558999 82588181000723181800338499)
        ·
          refine ⟨123882271501084772700507749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82588181000723181800338499 123882271501084772700507749)
          ·
            refine ⟨23227925906453394881345203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123882271501084772700507749 23227925906453394881345203)
            ·
              refine ⟨34841888859680092322017805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23227925906453394881345203 34841888859680092322017805)
              ·
                refine ⟨13065708322380034620756677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34841888859680092322017805 13065708322380034620756677)
                ·
                  refine ⟨2449820310446256491391877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13065708322380034620756677 2449820310446256491391877)
                  ·
                    refine ⟨459341308208673092135977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2449820310446256491391877 459341308208673092135977)
                    ·
                      rfl

theorem cell23_2683692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 4].length) (baseStart_2683692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2683692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2683692 prefixEnd_2683692 := by exact prefixLift 2683692
  have htrace : WordTrace (prefixWord ++ tailWord_2683692) baseStart_2683692 baseEnd_2683692 := by
    simpa [prefixWord, tailWord_2683692, baseEnd_2683692] using wordTrace_append hprefix tailTrace_2683692
  have hstable : (prefixWord ++ tailWord_2683692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683692).length < 2 ^ (prefixWord ++ tailWord_2683692).sum := by decide
  have hdescent : baseEnd_2683692 < baseStart_2683692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683695 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 2, 6, 4]
def baseStart_2683695 : Nat := 118140960795 + 2683695 * 2 ^ 59
def prefixEnd_2683695 : Nat := 4983230072969 + 3 ^ 40 * 2683695 * 2
def baseEnd_2683695 : Nat := 1378025465067982764670417

theorem tailTrace_2683695 : CollatzResearch.WordTrace tailWord_2683695 prefixEnd_2683695 1378025465067982764670417 := by
  unfold tailWord_2683695
  simp only [CollatzResearch.WordTrace]
  refine ⟨97882398012438828460908539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65254932008292552307272359 97882398012438828460908539)
  ·
    refine ⟨146823597018658242691362809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97882398012438828460908539 146823597018658242691362809)
    ·
      refine ⟨110117697763993682018522107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146823597018658242691362809 110117697763993682018522107)
      ·
        refine ⟨165176546645990523027783161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110117697763993682018522107 165176546645990523027783161)
        ·
          refine ⟨123882409984492892270837371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165176546645990523027783161 123882409984492892270837371)
          ·
            refine ⟨185823614976739338406256057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123882409984492892270837371 185823614976739338406256057)
            ·
              refine ⟨139367711232554503804692043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185823614976739338406256057 139367711232554503804692043)
              ·
                refine ⟨209051566848831755707038065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139367711232554503804692043 209051566848831755707038065)
                ·
                  refine ⟨156788675136623816780278549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 209051566848831755707038065 156788675136623816780278549)
                  ·
                    refine ⟨7349469147029241411575557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 156788675136623816780278549 7349469147029241411575557)
                    ·
                      refine ⟨1378025465067982764670417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7349469147029241411575557 1378025465067982764670417)
                      ·
                        rfl

theorem cell23_2683695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 6, 4].length) (baseStart_2683695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2683695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2683695 prefixEnd_2683695 := by exact prefixLift 2683695
  have htrace : WordTrace (prefixWord ++ tailWord_2683695) baseStart_2683695 baseEnd_2683695 := by
    simpa [prefixWord, tailWord_2683695, baseEnd_2683695] using wordTrace_append hprefix tailTrace_2683695
  have hstable : (prefixWord ++ tailWord_2683695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683695).length < 2 ^ (prefixWord ++ tailWord_2683695).sum := by decide
  have hdescent : baseEnd_2683695 < baseStart_2683695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683713 : List Nat := [1, 2, 5, 3, 1, 2, 1, 2, 1, 5]
def baseStart_2683713 : Nat := 118140960795 + 2683713 * 2 ^ 59
def prefixEnd_2683713 : Nat := 4983230072969 + 3 ^ 40 * 2683713 * 2
def baseEnd_2683713 : Nat := 459344902573254564748445

theorem tailTrace_2683713 : CollatzResearch.WordTrace tailWord_2683713 prefixEnd_2683713 459344902573254564748445 := by
  unfold tailWord_2683713
  simp only [CollatzResearch.WordTrace]
  refine ⟨97883054526373617535063793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65255369684249078356709195 97883054526373617535063793)
  ·
    refine ⟨73412290894780213151297845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97883054526373617535063793 73412290894780213151297845)
    ·
      refine ⟨6882402271385644982934173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73412290894780213151297845 6882402271385644982934173)
      ·
        refine ⟨2580900851769616868600315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6882402271385644982934173 2580900851769616868600315)
        ·
          refine ⟨3871351277654425302900473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2580900851769616868600315 3871351277654425302900473)
          ·
            refine ⟨2903513458240818977175355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3871351277654425302900473 2903513458240818977175355)
            ·
              refine ⟨4355270187361228465763033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2903513458240818977175355 4355270187361228465763033)
              ·
                refine ⟨3266452640520921349322275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4355270187361228465763033 3266452640520921349322275)
                ·
                  refine ⟨4899678960781382023983413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3266452640520921349322275 4899678960781382023983413)
                  ·
                    refine ⟨459344902573254564748445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4899678960781382023983413 459344902573254564748445)
                    ·
                      rfl

theorem cell23_2683713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_2683713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2683713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2683713 prefixEnd_2683713 := by exact prefixLift 2683713
  have htrace : WordTrace (prefixWord ++ tailWord_2683713) baseStart_2683713 baseEnd_2683713 := by
    simpa [prefixWord, tailWord_2683713, baseEnd_2683713] using wordTrace_append hprefix tailTrace_2683713
  have hstable : (prefixWord ++ tailWord_2683713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683713).length < 2 ^ (prefixWord ++ tailWord_2683713).sum := by decide
  have hdescent : baseEnd_2683713 < baseStart_2683713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683729 : List Nat := [1, 2, 2, 1, 6, 1, 1, 2, 1, 2, 4]
def baseStart_2683729 : Nat := 118140960795 + 2683729 * 2 ^ 59
def prefixEnd_2683729 : Nat := 4983230072969 + 3 ^ 40 * 2683729 * 2
def baseEnd_2683729 : Nat := 1378042923410235631645261

theorem tailTrace_2683729 : CollatzResearch.WordTrace tailWord_2683729 prefixEnd_2683729 1378042923410235631645261 := by
  unfold tailWord_2683729
  simp only [CollatzResearch.WordTrace]
  refine ⟨97883638094315652267646241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65255758729543768178430827 97883638094315652267646241)
  ·
    refine ⟨73412728570736739200734681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97883638094315652267646241 73412728570736739200734681)
    ·
      refine ⟨55059546428052554400551011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73412728570736739200734681 55059546428052554400551011)
      ·
        refine ⟨82589319642078831600826517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55059546428052554400551011 82589319642078831600826517)
        ·
          refine ⟨3871374358222445231288743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 82589319642078831600826517 3871374358222445231288743)
          ·
            refine ⟨5807061537333667846933115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3871374358222445231288743 5807061537333667846933115)
            ·
              refine ⟨8710592306000501770399673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5807061537333667846933115 8710592306000501770399673)
              ·
                refine ⟨6532944229500376327799755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8710592306000501770399673 6532944229500376327799755)
                ·
                  refine ⟨9799416344250564491699633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6532944229500376327799755 9799416344250564491699633)
                  ·
                    refine ⟨7349562258187923368774725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9799416344250564491699633 7349562258187923368774725)
                    ·
                      refine ⟨1378042923410235631645261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7349562258187923368774725 1378042923410235631645261)
                      ·
                        rfl

theorem cell23_2683729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 2, 4].length) (baseStart_2683729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2683729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2683729 prefixEnd_2683729 := by exact prefixLift 2683729
  have htrace : WordTrace (prefixWord ++ tailWord_2683729) baseStart_2683729 baseEnd_2683729 := by
    simpa [prefixWord, tailWord_2683729, baseEnd_2683729] using wordTrace_append hprefix tailTrace_2683729
  have hstable : (prefixWord ++ tailWord_2683729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683729).length < 2 ^ (prefixWord ++ tailWord_2683729).sum := by decide
  have hdescent : baseEnd_2683729 < baseStart_2683729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683733 : List Nat := [1, 3, 2, 2, 2, 1, 2, 5, 1, 2, 2]
def baseStart_2683733 : Nat := 118140960795 + 2683733 * 2 ^ 59
def prefixEnd_2683733 : Nat := 4983230072969 + 3 ^ 40 * 2683733 * 2
def baseEnd_2683733 : Nat := 1378044977332853615995243

theorem tailTrace_2683733 : CollatzResearch.WordTrace tailWord_2683733 prefixEnd_2683733 1378044977332853615995243 := by
  unfold tailWord_2683733
  simp only [CollatzResearch.WordTrace]
  refine ⟨97883783986301160950791853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65255855990867440633861235 97883783986301160950791853)
  ·
    refine ⟨36706418994862935356546945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97883783986301160950791853 36706418994862935356546945)
    ·
      refine ⟨27529814246147201517410209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36706418994862935356546945 27529814246147201517410209)
      ·
        refine ⟨20647360684610401138057657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27529814246147201517410209 20647360684610401138057657)
        ·
          refine ⟨15485520513457800853543243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20647360684610401138057657 15485520513457800853543243)
          ·
            refine ⟨23228280770186701280314865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15485520513457800853543243 23228280770186701280314865)
            ·
              refine ⟨17421210577640025960236149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23228280770186701280314865 17421210577640025960236149)
              ·
                refine ⟨1633238491653752433772139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17421210577640025960236149 1633238491653752433772139)
                ·
                  refine ⟨2449857737480628650658209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1633238491653752433772139 2449857737480628650658209)
                  ·
                    refine ⟨1837393303110471487993657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2449857737480628650658209 1837393303110471487993657)
                    ·
                      refine ⟨1378044977332853615995243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1837393303110471487993657 1378044977332853615995243)
                      ·
                        rfl

theorem cell23_2683733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 5, 1, 2, 2].length) (baseStart_2683733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2683733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2683733 prefixEnd_2683733 := by exact prefixLift 2683733
  have htrace : WordTrace (prefixWord ++ tailWord_2683733) baseStart_2683733 baseEnd_2683733 := by
    simpa [prefixWord, tailWord_2683733, baseEnd_2683733] using wordTrace_append hprefix tailTrace_2683733
  have hstable : (prefixWord ++ tailWord_2683733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683733).length < 2 ^ (prefixWord ++ tailWord_2683733).sum := by decide
  have hdescent : baseEnd_2683733 < baseStart_2683733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683749 : List Nat := [1, 3, 1, 3, 1, 1, 2, 3, 4, 1, 3]
def baseStart_2683749 : Nat := 118140960795 + 2683749 * 2 ^ 59
def prefixEnd_2683749 : Nat := 4983230072969 + 3 ^ 40 * 2683749 * 2
def baseEnd_2683749 : Nat := 1378053193023325553395169

theorem tailTrace_2683749 : CollatzResearch.WordTrace tailWord_2683749 prefixEnd_2683749 1378053193023325553395169 := by
  unfold tailWord_2683749
  simp only [CollatzResearch.WordTrace]
  refine ⟨97884367554243195683374301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65256245036162130455582867 97884367554243195683374301)
  ·
    refine ⟨36706637832841198381265363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97884367554243195683374301 36706637832841198381265363)
    ·
      refine ⟨55059956749261797571898045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36706637832841198381265363 55059956749261797571898045)
      ·
        refine ⟨20647483780973174089461767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55059956749261797571898045 20647483780973174089461767)
        ·
          refine ⟨30971225671459761134192651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20647483780973174089461767 30971225671459761134192651)
          ·
            refine ⟨46456838507189641701288977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30971225671459761134192651 46456838507189641701288977)
            ·
              refine ⟨34842628880392231275966733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46456838507189641701288977 34842628880392231275966733)
              ·
                refine ⟨13065985830147086728487525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34842628880392231275966733 13065985830147086728487525)
                ·
                  refine ⟨2449872343152578761591411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13065985830147086728487525 2449872343152578761591411)
                  ·
                    refine ⟨3674808514728868142387117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2449872343152578761591411 3674808514728868142387117)
                    ·
                      refine ⟨1378053193023325553395169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3674808514728868142387117 1378053193023325553395169)
                      ·
                        rfl

theorem cell23_2683749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_2683749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2683749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2683749 prefixEnd_2683749 := by exact prefixLift 2683749
  have htrace : WordTrace (prefixWord ++ tailWord_2683749) baseStart_2683749 baseEnd_2683749 := by
    simpa [prefixWord, tailWord_2683749, baseEnd_2683749] using wordTrace_append hprefix tailTrace_2683749
  have hstable : (prefixWord ++ tailWord_2683749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683749).length < 2 ^ (prefixWord ++ tailWord_2683749).sum := by decide
  have hdescent : baseEnd_2683749 < baseStart_2683749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683752 : List Nat := [2, 1, 4, 2, 1, 2, 1, 1, 2, 7]
def baseStart_2683752 : Nat := 118140960795 + 2683752 * 2 ^ 59
def prefixEnd_2683752 : Nat := 4983230072969 + 3 ^ 40 * 2683752 * 2
def baseEnd_2683752 : Nat := 459351577821763013885885

theorem tailTrace_2683752 : CollatzResearch.WordTrace tailWord_2683752 prefixEnd_2683752 459351577821763013885885 := by
  unfold tailWord_2683752
  simp only [CollatzResearch.WordTrace]
  refine ⟨48942238486616163597866755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65256317982154884797155673 48942238486616163597866755)
  ·
    refine ⟨73413357729924245396800133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48942238486616163597866755 73413357729924245396800133)
    ·
      refine ⟨13765004574360796011900025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73413357729924245396800133 13765004574360796011900025)
      ·
        refine ⟨10323753430770597008925019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13765004574360796011900025 10323753430770597008925019)
        ·
          refine ⟨15485630146155895513387529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10323753430770597008925019 15485630146155895513387529)
          ·
            refine ⟨11614222609616921635040647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15485630146155895513387529 11614222609616921635040647)
            ·
              refine ⟨17421333914425382452560971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11614222609616921635040647 17421333914425382452560971)
              ·
                refine ⟨26132000871638073678841457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17421333914425382452560971 26132000871638073678841457)
                ·
                  refine ⟨19599000653728555259131093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26132000871638073678841457 19599000653728555259131093)
                  ·
                    refine ⟨459351577821763013885885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19599000653728555259131093 459351577821763013885885)
                    ·
                      rfl

theorem cell23_2683752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_2683752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2683752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2683752 prefixEnd_2683752 := by exact prefixLift 2683752
  have htrace : WordTrace (prefixWord ++ tailWord_2683752) baseStart_2683752 baseEnd_2683752 := by
    simpa [prefixWord, tailWord_2683752, baseEnd_2683752] using wordTrace_append hprefix tailTrace_2683752
  have hstable : (prefixWord ++ tailWord_2683752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683752).length < 2 ^ (prefixWord ++ tailWord_2683752).sum := by decide
  have hdescent : baseEnd_2683752 < baseStart_2683752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683766 : List Nat := [5, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3]
def baseStart_2683766 : Nat := 118140960795 + 2683766 * 2 ^ 59
def prefixEnd_2683766 : Nat := 4983230072969 + 3 ^ 40 * 2683766 * 2
def baseEnd_2683766 : Nat := 1378061922194451986882591

theorem tailTrace_2683766 : CollatzResearch.WordTrace tailWord_2683766 prefixEnd_2683766 1378061922194451986882591 := by
  unfold tailWord_2683766
  simp only [CollatzResearch.WordTrace]
  refine ⟨6117811724698850474171447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65256658396787738391162101 6117811724698850474171447)
  ·
    refine ⟨9176717587048275711257171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6117811724698850474171447 9176717587048275711257171)
    ·
      refine ⟨13765076380572413566885757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9176717587048275711257171 13765076380572413566885757)
      ·
        refine ⟨5161903642714655087582159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13765076380572413566885757 5161903642714655087582159)
        ·
          refine ⟨7742855464071982631373239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5161903642714655087582159 7742855464071982631373239)
          ·
            refine ⟨11614283196107973947059859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7742855464071982631373239 11614283196107973947059859)
            ·
              refine ⟨17421424794161960920589789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11614283196107973947059859 17421424794161960920589789)
              ·
                refine ⟨6533034297810735345221171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17421424794161960920589789 6533034297810735345221171)
                ·
                  refine ⟨9799551446716103017831757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6533034297810735345221171 9799551446716103017831757)
                  ·
                    refine ⟨3674831792518538631686909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9799551446716103017831757 3674831792518538631686909)
                    ·
                      refine ⟨1378061922194451986882591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3674831792518538631686909 1378061922194451986882591)
                      ·
                        rfl

theorem cell23_2683766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_2683766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2683766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2683766 prefixEnd_2683766 := by exact prefixLift 2683766
  have htrace : WordTrace (prefixWord ++ tailWord_2683766) baseStart_2683766 baseEnd_2683766 := by
    simpa [prefixWord, tailWord_2683766, baseEnd_2683766] using wordTrace_append hprefix tailTrace_2683766
  have hstable : (prefixWord ++ tailWord_2683766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683766).length < 2 ^ (prefixWord ++ tailWord_2683766).sum := by decide
  have hdescent : baseEnd_2683766 < baseStart_2683766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683869 : List Nat := [1, 4, 3, 1, 2, 1, 1, 1, 1, 1, 7]
def baseStart_2683869 : Nat := 118140960795 + 2683869 * 2 ^ 59
def prefixEnd_2683869 : Nat := 4983230072969 + 3 ^ 40 * 2683869 * 2
def baseEnd_2683869 : Nat := 1378114810701865083894617

theorem tailTrace_2683869 : CollatzResearch.WordTrace tailWord_2683869 prefixEnd_2683869 1378114810701865083894617 := by
  unfold tailWord_2683869
  simp only [CollatzResearch.WordTrace]
  refine ⟨97888744313808456177742661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65259162875872304118495107 97888744313808456177742661)
  ·
    refine ⟨18354139558839085533326749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97888744313808456177742661 18354139558839085533326749)
    ·
      refine ⟨6882802334564657074997531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18354139558839085533326749 6882802334564657074997531)
      ·
        refine ⟨10324203501846985612496297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6882802334564657074997531 10324203501846985612496297)
        ·
          refine ⟨7743152626385239209372223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10324203501846985612496297 7743152626385239209372223)
          ·
            refine ⟨11614728939577858814058335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7743152626385239209372223 11614728939577858814058335)
            ·
              refine ⟨17422093409366788221087503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11614728939577858814058335 17422093409366788221087503)
              ·
                refine ⟨26133140114050182331631255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17422093409366788221087503 26133140114050182331631255)
                ·
                  refine ⟨39199710171075273497446883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26133140114050182331631255 39199710171075273497446883)
                  ·
                    refine ⟨58799565256612910246170325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39199710171075273497446883 58799565256612910246170325)
                    ·
                      refine ⟨1378114810701865083894617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 58799565256612910246170325 1378114810701865083894617)
                      ·
                        rfl

theorem cell23_2683869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_2683869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2683869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2683869 prefixEnd_2683869 := by exact prefixLift 2683869
  have htrace : WordTrace (prefixWord ++ tailWord_2683869) baseStart_2683869 baseEnd_2683869 := by
    simpa [prefixWord, tailWord_2683869, baseEnd_2683869] using wordTrace_append hprefix tailTrace_2683869
  have hstable : (prefixWord ++ tailWord_2683869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683869).length < 2 ^ (prefixWord ++ tailWord_2683869).sum := by decide
  have hdescent : baseEnd_2683869 < baseStart_2683869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683874 : List Nat := [3, 3, 3, 1, 1, 3, 2, 1, 2, 2, 2]
def baseStart_2683874 : Nat := 118140960795 + 2683874 * 2 ^ 59
def prefixEnd_2683874 : Nat := 4983230072969 + 3 ^ 40 * 2683874 * 2
def baseEnd_2683874 : Nat := 1378117378105137564332095

theorem tailTrace_2683874 : CollatzResearch.WordTrace tailWord_2683874 prefixEnd_2683874 1378117378105137564332095 := by
  unfold tailWord_2683874
  simp only [CollatzResearch.WordTrace]
  refine ⟨24472231669697585507918669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65259284452526894687783117 24472231669697585507918669)
  ·
    refine ⟨9177086876136594565469501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24472231669697585507918669 9177086876136594565469501)
    ·
      refine ⟨3441407578551222962051063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9177086876136594565469501 3441407578551222962051063)
      ·
        refine ⟨5162111367826834443076595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3441407578551222962051063 5162111367826834443076595)
        ·
          refine ⟨7743167051740251664614893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5162111367826834443076595 7743167051740251664614893)
          ·
            refine ⟨2903687644402594374230585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7743167051740251664614893 2903687644402594374230585)
            ·
              refine ⟨2177765733301945780672939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2903687644402594374230585 2177765733301945780672939)
              ·
                refine ⟨3266648599952918671009409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2177765733301945780672939 3266648599952918671009409)
                ·
                  refine ⟨2449986449964689003257057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3266648599952918671009409 2449986449964689003257057)
                  ·
                    refine ⟨1837489837473516752442793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2449986449964689003257057 1837489837473516752442793)
                    ·
                      refine ⟨1378117378105137564332095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1837489837473516752442793 1378117378105137564332095)
                      ·
                        rfl

theorem cell23_2683874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_2683874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2683874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2683874 prefixEnd_2683874 := by exact prefixLift 2683874
  have htrace : WordTrace (prefixWord ++ tailWord_2683874) baseStart_2683874 baseEnd_2683874 := by
    simpa [prefixWord, tailWord_2683874, baseEnd_2683874] using wordTrace_append hprefix tailTrace_2683874
  have hstable : (prefixWord ++ tailWord_2683874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683874).length < 2 ^ (prefixWord ++ tailWord_2683874).sum := by decide
  have hdescent : baseEnd_2683874 < baseStart_2683874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683916 : List Nat := [2, 2, 1, 2, 3, 2, 2, 2, 2, 2, 3]
def baseStart_2683916 : Nat := 118140960795 + 2683916 * 2 ^ 59
def prefixEnd_2683916 : Nat := 4983230072969 + 3 ^ 40 * 2683916 * 2
def baseEnd_2683916 : Nat := 1378138944292626400006901

theorem tailTrace_2683916 : CollatzResearch.WordTrace tailWord_2683916 prefixEnd_2683916 1378138944292626400006901 := by
  unfold tailWord_2683916
  simp only [CollatzResearch.WordTrace]
  refine ⟨48945229272319091602351801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65260305696425455469802401 48945229272319091602351801)
  ·
    refine ⟨36708921954239318701763851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48945229272319091602351801 36708921954239318701763851)
    ·
      refine ⟨55063382931358978052645777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36708921954239318701763851 55063382931358978052645777)
      ·
        refine ⟨41297537198519233539484333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55063382931358978052645777 41297537198519233539484333)
        ·
          refine ⟨15486576449444712577306625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41297537198519233539484333 15486576449444712577306625)
          ·
            refine ⟨11614932337083534432979969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15486576449444712577306625 11614932337083534432979969)
            ·
              refine ⟨8711199252812650824734977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11614932337083534432979969 8711199252812650824734977)
              ·
                refine ⟨6533399439609488118551233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8711199252812650824734977 6533399439609488118551233)
                ·
                  refine ⟨4900049579707116088913425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6533399439609488118551233 4900049579707116088913425)
                  ·
                    refine ⟨3675037184780337066685069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4900049579707116088913425 3675037184780337066685069)
                    ·
                      refine ⟨1378138944292626400006901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3675037184780337066685069 1378138944292626400006901)
                      ·
                        rfl

theorem cell23_2683916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 2, 2, 3].length) (baseStart_2683916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2683916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2683916 prefixEnd_2683916 := by exact prefixLift 2683916
  have htrace : WordTrace (prefixWord ++ tailWord_2683916) baseStart_2683916 baseEnd_2683916 := by
    simpa [prefixWord, tailWord_2683916, baseEnd_2683916] using wordTrace_append hprefix tailTrace_2683916
  have hstable : (prefixWord ++ tailWord_2683916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683916).length < 2 ^ (prefixWord ++ tailWord_2683916).sum := by decide
  have hdescent : baseEnd_2683916 < baseStart_2683916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2683999 : List Nat := [1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 6]
def baseStart_2683999 : Nat := 118140960795 + 2683999 * 2 ^ 59
def prefixEnd_2683999 : Nat := 4983230072969 + 3 ^ 40 * 2683999 * 2
def baseEnd_2683999 : Nat := 1378181563186949575269019

theorem tailTrace_2683999 : CollatzResearch.WordTrace tailWord_2683999 prefixEnd_2683999 1378181563186949575269019 := by
  unfold tailWord_2683999
  simp only [CollatzResearch.WordTrace]
  refine ⟨97893485803337488379975051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65262323868891658919983367 97893485803337488379975051)
  ·
    refine ⟨146840228705006232569962577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97893485803337488379975051 146840228705006232569962577)
    ·
      refine ⟨110130171528754674427471933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146840228705006232569962577 110130171528754674427471933)
      ·
        refine ⟨41298814323283002910301975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110130171528754674427471933 41298814323283002910301975)
        ·
          refine ⟨61948221484924504365452963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41298814323283002910301975 61948221484924504365452963)
          ·
            refine ⟨92922332227386756548179445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61948221484924504365452963 92922332227386756548179445)
            ·
              refine ⟨8711468646317508426391823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 92922332227386756548179445 8711468646317508426391823)
              ·
                refine ⟨13067202969476262639587735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8711468646317508426391823 13067202969476262639587735)
                ·
                  refine ⟨19600804454214393959381603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13067202969476262639587735 19600804454214393959381603)
                  ·
                    refine ⟨29401206681321590939072405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19600804454214393959381603 29401206681321590939072405)
                    ·
                      refine ⟨1378181563186949575269019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29401206681321590939072405 1378181563186949575269019)
                      ·
                        rfl

theorem cell23_2683999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_2683999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2683999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2683999 prefixEnd_2683999 := by exact prefixLift 2683999
  have htrace : WordTrace (prefixWord ++ tailWord_2683999) baseStart_2683999 baseEnd_2683999 := by
    simpa [prefixWord, tailWord_2683999, baseEnd_2683999] using wordTrace_append hprefix tailTrace_2683999
  have hstable : (prefixWord ++ tailWord_2683999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2683999).length < 2 ^ (prefixWord ++ tailWord_2683999).sum := by decide
  have hdescent : baseEnd_2683999 < baseStart_2683999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2683999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684009 : List Nat := [1, 2, 1, 1, 1, 7, 1, 9]
def baseStart_2684009 : Nat := 118140960795 + 2684009 * 2 ^ 59
def prefixEnd_2684009 : Nat := 4983230072969 + 3 ^ 40 * 2684009 * 2
def baseEnd_2684009 : Nat := 51043951777536834671999

theorem tailTrace_2684009 : CollatzResearch.WordTrace tailWord_2684009 prefixEnd_2684009 51043951777536834671999 := by
  unfold tailWord_2684009
  simp only [CollatzResearch.WordTrace]
  refine ⟨97893850533301260087839081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65262567022200840058559387 97893850533301260087839081)
  ·
    refine ⟨73420387899975945065879311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97893850533301260087839081 73420387899975945065879311)
    ·
      refine ⟨110130581849963917598818967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73420387899975945065879311 110130581849963917598818967)
      ·
        refine ⟨165195872774945876398228451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110130581849963917598818967 165195872774945876398228451)
        ·
          refine ⟨247793809162418814597342677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165195872774945876398228451 247793809162418814597342677)
          ·
            refine ⟨5807667402244190967125219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 247793809162418814597342677 5807667402244190967125219)
            ·
              refine ⟨8711501103366286450687829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5807667402244190967125219 8711501103366286450687829)
              ·
                refine ⟨51043951777536834671999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8711501103366286450687829 51043951777536834671999)
                ·
                  rfl

theorem cell23_2684009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 9].length) (baseStart_2684009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2684009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2684009 prefixEnd_2684009 := by exact prefixLift 2684009
  have htrace : WordTrace (prefixWord ++ tailWord_2684009) baseStart_2684009 baseEnd_2684009 := by
    simpa [prefixWord, tailWord_2684009, baseEnd_2684009] using wordTrace_append hprefix tailTrace_2684009
  have hstable : (prefixWord ++ tailWord_2684009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684009).length < 2 ^ (prefixWord ++ tailWord_2684009).sum := by decide
  have hdescent : baseEnd_2684009 < baseStart_2684009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684037 : List Nat := [1, 3, 1, 1, 6, 2, 1, 1, 3, 2, 2]
def baseStart_2684037 : Nat := 118140960795 + 2684037 * 2 ^ 59
def prefixEnd_2684037 : Nat := 4983230072969 + 3 ^ 40 * 2684037 * 2
def baseEnd_2684037 : Nat := 1378201075451820426593845

theorem tailTrace_2684037 : CollatzResearch.WordTrace tailWord_2684037 prefixEnd_2684037 1378201075451820426593845 := by
  unfold tailWord_2684037
  simp only [CollatzResearch.WordTrace]
  refine ⟨97894871777199820869858365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65263247851466547246572243 97894871777199820869858365)
  ·
    refine ⟨36710576916449932826196887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97894871777199820869858365 36710576916449932826196887)
    ·
      refine ⟨55065865374674899239295331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36710576916449932826196887 55065865374674899239295331)
      ·
        refine ⟨82598798062012348858942997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55065865374674899239295331 82598798062012348858942997)
        ·
          refine ⟨3871818659156828852762953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 82598798062012348858942997 3871818659156828852762953)
          ·
            refine ⟨2903863994367621639572215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3871818659156828852762953 2903863994367621639572215)
            ·
              refine ⟨4355795991551432459358323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2903863994367621639572215 4355795991551432459358323)
              ·
                refine ⟨6533693987327148689037485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4355795991551432459358323 6533693987327148689037485)
                ·
                  refine ⟨2450135245247680758389057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6533693987327148689037485 2450135245247680758389057)
                  ·
                    refine ⟨1837601433935760568791793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2450135245247680758389057 1837601433935760568791793)
                    ·
                      refine ⟨1378201075451820426593845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1837601433935760568791793 1378201075451820426593845)
                      ·
                        rfl

theorem cell23_2684037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 3, 2, 2].length) (baseStart_2684037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2684037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2684037 prefixEnd_2684037 := by exact prefixLift 2684037
  have htrace : WordTrace (prefixWord ++ tailWord_2684037) baseStart_2684037 baseEnd_2684037 := by
    simpa [prefixWord, tailWord_2684037, baseEnd_2684037] using wordTrace_append hprefix tailTrace_2684037
  have hstable : (prefixWord ++ tailWord_2684037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684037).length < 2 ^ (prefixWord ++ tailWord_2684037).sum := by decide
  have hdescent : baseEnd_2684037 < baseStart_2684037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684039 : List Nat := [1, 1, 4, 2, 1, 1, 1, 3, 2, 7]
def baseStart_2684039 : Nat := 118140960795 + 2684039 * 2 ^ 59
def prefixEnd_2684039 : Nat := 4983230072969 + 3 ^ 40 * 2684039 * 2
def baseEnd_2684039 : Nat := 459400700804376472922945

theorem tailTrace_2684039 : CollatzResearch.WordTrace tailWord_2684039 prefixEnd_2684039 459400700804376472922945 := by
  unfold tailWord_2684039
  simp only [CollatzResearch.WordTrace]
  refine ⟨97894944723192575211431171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65263296482128383474287447 97894944723192575211431171)
  ·
    refine ⟨146842417084788862817146757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97894944723192575211431171 146842417084788862817146757)
    ·
      refine ⟨27532953203397911778215017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146842417084788862817146757 27532953203397911778215017)
      ·
        refine ⟨20649714902548433833661263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27532953203397911778215017 20649714902548433833661263)
        ·
          refine ⟨30974572353822650750491895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20649714902548433833661263 30974572353822650750491895)
          ·
            refine ⟨46461858530733976125737843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30974572353822650750491895 46461858530733976125737843)
            ·
              refine ⟨69692787796100964188606765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46461858530733976125737843 69692787796100964188606765)
              ·
                refine ⟨26134795423537861570727537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69692787796100964188606765 26134795423537861570727537)
                ·
                  refine ⟨19601096567653396178045653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26134795423537861570727537 19601096567653396178045653)
                  ·
                    refine ⟨459400700804376472922945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19601096567653396178045653 459400700804376472922945)
                    ·
                      rfl

theorem cell23_2684039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 7].length) (baseStart_2684039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2684039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2684039 prefixEnd_2684039 := by exact prefixLift 2684039
  have htrace : WordTrace (prefixWord ++ tailWord_2684039) baseStart_2684039 baseEnd_2684039 := by
    simpa [prefixWord, tailWord_2684039, baseEnd_2684039] using wordTrace_append hprefix tailTrace_2684039
  have hstable : (prefixWord ++ tailWord_2684039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684039).length < 2 ^ (prefixWord ++ tailWord_2684039).sum := by decide
  have hdescent : baseEnd_2684039 < baseStart_2684039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684106 : List Nat := [3, 1, 2, 1, 3, 2, 1, 1, 1, 4, 4]
def baseStart_2684106 : Nat := 118140960795 + 2684106 * 2 ^ 59
def prefixEnd_2684106 : Nat := 4983230072969 + 3 ^ 40 * 2684106 * 2
def baseEnd_2684106 : Nat := 1378236505616980656631027

theorem tailTrace_2684106 : CollatzResearch.WordTrace tailWord_2684106 prefixEnd_2684106 1378236505616980656631027 := by
  unfold tailWord_2684106
  simp only [CollatzResearch.WordTrace]
  refine ⟨24474347103487461413530043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65264925609299897102746781 24474347103487461413530043)
  ·
    refine ⟨36711520655231192120295065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24474347103487461413530043 36711520655231192120295065)
    ·
      refine ⟨27533640491423394090221299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36711520655231192120295065 27533640491423394090221299)
      ·
        refine ⟨41300460737135091135331949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27533640491423394090221299 41300460737135091135331949)
        ·
          refine ⟨15487672776425659175749481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41300460737135091135331949 15487672776425659175749481)
          ·
            refine ⟨11615754582319244381812111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15487672776425659175749481 11615754582319244381812111)
            ·
              refine ⟨17423631873478866572718167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11615754582319244381812111 17423631873478866572718167)
              ·
                refine ⟨26135447810218299859077251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17423631873478866572718167 26135447810218299859077251)
                ·
                  refine ⟨39203171715327449788615877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26135447810218299859077251 39203171715327449788615877)
                  ·
                    refine ⟨7350594696623896835365477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39203171715327449788615877 7350594696623896835365477)
                    ·
                      refine ⟨1378236505616980656631027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7350594696623896835365477 1378236505616980656631027)
                      ·
                        rfl

theorem cell23_2684106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_2684106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2684106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2684106 prefixEnd_2684106 := by exact prefixLift 2684106
  have htrace : WordTrace (prefixWord ++ tailWord_2684106) baseStart_2684106 baseEnd_2684106 := by
    simpa [prefixWord, tailWord_2684106, baseEnd_2684106] using wordTrace_append hprefix tailTrace_2684106
  have hstable : (prefixWord ++ tailWord_2684106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684106).length < 2 ^ (prefixWord ++ tailWord_2684106).sum := by decide
  have hdescent : baseEnd_2684106 < baseStart_2684106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684183 : List Nat := [1, 1, 3, 4, 1, 1, 2, 3, 2, 1, 4]
def baseStart_2684183 : Nat := 118140960795 + 2684183 * 2 ^ 59
def prefixEnd_2684183 : Nat := 4983230072969 + 3 ^ 40 * 2684183 * 2
def baseEnd_2684183 : Nat := 1378276043627376855368173

theorem tailTrace_2684183 : CollatzResearch.WordTrace tailWord_2684183 prefixEnd_2684183 1378276043627376855368173 := by
  unfold tailWord_2684183
  simp only [CollatzResearch.WordTrace]
  refine ⟨97900196834670887804673203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65266797889780591869782135 97900196834670887804673203)
  ·
    refine ⟨146850295252006331707009805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97900196834670887804673203 146850295252006331707009805)
    ·
      refine ⟨55068860719502374390128677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146850295252006331707009805 55068860719502374390128677)
      ·
        refine ⟨10325411384906695198149127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55068860719502374390128677 10325411384906695198149127)
        ·
          refine ⟨15488117077360042797223691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10325411384906695198149127 15488117077360042797223691)
          ·
            refine ⟨23232175616040064195835537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15488117077360042797223691 23232175616040064195835537)
            ·
              refine ⟨17424131712030048146876653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23232175616040064195835537 17424131712030048146876653)
              ·
                refine ⟨6534049392011268055078745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17424131712030048146876653 6534049392011268055078745)
                ·
                  refine ⟨4900537044008451041309059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6534049392011268055078745 4900537044008451041309059)
                  ·
                    refine ⟨7350805566012676561963589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4900537044008451041309059 7350805566012676561963589)
                    ·
                      refine ⟨1378276043627376855368173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7350805566012676561963589 1378276043627376855368173)
                      ·
                        rfl

theorem cell23_2684183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_2684183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2684183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2684183 prefixEnd_2684183 := by exact prefixLift 2684183
  have htrace : WordTrace (prefixWord ++ tailWord_2684183) baseStart_2684183 baseEnd_2684183 := by
    simpa [prefixWord, tailWord_2684183, baseEnd_2684183] using wordTrace_append hprefix tailTrace_2684183
  have hstable : (prefixWord ++ tailWord_2684183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684183).length < 2 ^ (prefixWord ++ tailWord_2684183).sum := by decide
  have hdescent : baseEnd_2684183 < baseStart_2684183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684200 : List Nat := [2, 1, 5, 1, 2, 2, 1, 2, 2, 1, 4]
def baseStart_2684200 : Nat := 118140960795 + 2684200 * 2 ^ 59
def prefixEnd_2684200 : Nat := 4983230072969 + 3 ^ 40 * 2684200 * 2
def baseEnd_2684200 : Nat := 1378284772798503288855595

theorem tailTrace_2684200 : CollatzResearch.WordTrace tailWord_2684200 prefixEnd_2684200 1378284772798503288855595 := by
  unfold tailWord_2684200
  simp only [CollatzResearch.WordTrace]
  refine ⟨48950408437804649854021027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65267211250406199805361369 48950408437804649854021027)
  ·
    refine ⟨73425612656706974781031541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48950408437804649854021027 73425612656706974781031541)
    ·
      refine ⟨6883651186566278885721707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73425612656706974781031541 6883651186566278885721707)
      ·
        refine ⟨10325476779849418328582561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6883651186566278885721707 10325476779849418328582561)
        ·
          refine ⟨7744107584887063746436921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10325476779849418328582561 7744107584887063746436921)
          ·
            refine ⟨5808080688665297809827691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7744107584887063746436921 5808080688665297809827691)
            ·
              refine ⟨8712121032997946714741537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5808080688665297809827691 8712121032997946714741537)
              ·
                refine ⟨6534090774748460036056153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8712121032997946714741537 6534090774748460036056153)
                ·
                  refine ⟨4900568081061345027042115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6534090774748460036056153 4900568081061345027042115)
                  ·
                    refine ⟨7350852121592017540563173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4900568081061345027042115 7350852121592017540563173)
                    ·
                      refine ⟨1378284772798503288855595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7350852121592017540563173 1378284772798503288855595)
                      ·
                        rfl

theorem cell23_2684200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_2684200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2684200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2684200 prefixEnd_2684200 := by exact prefixLift 2684200
  have htrace : WordTrace (prefixWord ++ tailWord_2684200) baseStart_2684200 baseEnd_2684200 := by
    simpa [prefixWord, tailWord_2684200, baseEnd_2684200] using wordTrace_append hprefix tailTrace_2684200
  have hstable : (prefixWord ++ tailWord_2684200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684200).length < 2 ^ (prefixWord ++ tailWord_2684200).sum := by decide
  have hdescent : baseEnd_2684200 < baseStart_2684200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684210 : List Nat := [3, 2, 1, 1, 4, 1, 3, 1, 3, 4]
def baseStart_2684210 : Nat := 118140960795 + 2684210 * 2 ^ 59
def prefixEnd_2684210 : Nat := 4983230072969 + 3 ^ 40 * 2684210 * 2
def baseEnd_2684210 : Nat := 459429969201682749910183

theorem tailTrace_2684210 : CollatzResearch.WordTrace tailWord_2684210 prefixEnd_2684210 459429969201682749910183 := by
  unfold tailWord_2684210
  simp only [CollatzResearch.WordTrace]
  refine ⟨24475295401393267853976521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65267454403715380943937389 24475295401393267853976521)
  ·
    refine ⟨18356471551044950890482391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24475295401393267853976521 18356471551044950890482391)
    ·
      refine ⟨27534707326567426335723587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18356471551044950890482391 27534707326567426335723587)
      ·
        refine ⟨41302060989851139503585381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27534707326567426335723587 41302060989851139503585381)
        ·
          refine ⟨7744136435597088656922259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41302060989851139503585381 7744136435597088656922259)
          ·
            refine ⟨11616204653395632985383389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7744136435597088656922259 11616204653395632985383389)
            ·
              refine ⟨4356076745023362369518771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11616204653395632985383389 4356076745023362369518771)
              ·
                refine ⟨6534115117535043554278157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4356076745023362369518771 6534115117535043554278157)
                ·
                  refine ⟨2450293169075641332854309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6534115117535043554278157 2450293169075641332854309)
                  ·
                    refine ⟨459429969201682749910183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2450293169075641332854309 459429969201682749910183)
                    ·
                      rfl

theorem cell23_2684210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 3, 4].length) (baseStart_2684210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2684210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2684210 prefixEnd_2684210 := by exact prefixLift 2684210
  have htrace : WordTrace (prefixWord ++ tailWord_2684210) baseStart_2684210 baseEnd_2684210 := by
    simpa [prefixWord, tailWord_2684210, baseEnd_2684210] using wordTrace_append hprefix tailTrace_2684210
  have hstable : (prefixWord ++ tailWord_2684210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684210).length < 2 ^ (prefixWord ++ tailWord_2684210).sum := by decide
  have hdescent : baseEnd_2684210 < baseStart_2684210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684223 : List Nat := [1, 1, 2, 2, 4, 3, 1, 3, 6]
def baseStart_2684223 : Nat := 118140960795 + 2684223 * 2 ^ 59
def prefixEnd_2684223 : Nat := 4983230072969 + 3 ^ 40 * 2684223 * 2
def baseEnd_2684223 : Nat := 153144064761506299874221

theorem tailTrace_2684223 : CollatzResearch.WordTrace tailWord_2684223 prefixEnd_2684223 153144064761506299874221 := by
  unfold tailWord_2684223
  simp only [CollatzResearch.WordTrace]
  refine ⟨97901655754525974636129323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65267770503017316424086215 97901655754525974636129323)
  ·
    refine ⟨146852483631788961954193985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97901655754525974636129323 146852483631788961954193985)
    ·
      refine ⟨110139362723841721465645489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146852483631788961954193985 110139362723841721465645489)
      ·
        refine ⟨82604522042881291099234117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110139362723841721465645489 82604522042881291099234117)
        ·
          refine ⟨15488347883040242081106397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82604522042881291099234117 15488347883040242081106397)
          ·
            refine ⟨5808130456140090780414899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15488347883040242081106397 5808130456140090780414899)
            ·
              refine ⟨8712195684210136170622349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5808130456140090780414899 8712195684210136170622349)
              ·
                refine ⟨3267073381578801063983381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8712195684210136170622349 3267073381578801063983381)
                ·
                  refine ⟨153144064761506299874221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3267073381578801063983381 153144064761506299874221)
                  ·
                    rfl

theorem cell23_2684223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 3, 6].length) (baseStart_2684223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2684223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2684223 prefixEnd_2684223 := by exact prefixLift 2684223
  have htrace : WordTrace (prefixWord ++ tailWord_2684223) baseStart_2684223 baseEnd_2684223 := by
    simpa [prefixWord, tailWord_2684223, baseEnd_2684223] using wordTrace_append hprefix tailTrace_2684223
  have hstable : (prefixWord ++ tailWord_2684223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684223).length < 2 ^ (prefixWord ++ tailWord_2684223).sum := by decide
  have hdescent : baseEnd_2684223 < baseStart_2684223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684273 : List Nat := [1, 2, 2, 2, 1, 2, 3, 2, 3, 1, 4]
def baseStart_2684273 : Nat := 118140960795 + 2684273 * 2 ^ 59
def prefixEnd_2684273 : Nat := 4983230072969 + 3 ^ 40 * 2684273 * 2
def baseEnd_2684273 : Nat := 1378322256886281503242759

theorem tailTrace_2684273 : CollatzResearch.WordTrace tailWord_2684273 prefixEnd_2684273 1378322256886281503242759 := by
  unfold tailWord_2684273
  simp only [CollatzResearch.WordTrace]
  refine ⟨97903479404344833175449473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65268986269563222116966315 97903479404344833175449473)
  ·
    refine ⟨73427609553258624881587105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97903479404344833175449473 73427609553258624881587105)
    ·
      refine ⟨55070707164943968661190329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73427609553258624881587105 55070707164943968661190329)
      ·
        refine ⟨41303030373707976495892747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55070707164943968661190329 41303030373707976495892747)
        ·
          refine ⟨61954545560561964743839121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41303030373707976495892747 61954545560561964743839121)
          ·
            refine ⟨46465909170421473557879341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61954545560561964743839121 46465909170421473557879341)
            ·
              refine ⟨17424715938908052584204753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46465909170421473557879341 17424715938908052584204753)
              ·
                refine ⟨13068536954181039438153565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17424715938908052584204753 13068536954181039438153565)
                ·
                  refine ⟨4900701357817889789307587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13068536954181039438153565 4900701357817889789307587)
                  ·
                    refine ⟨7351052036726834683961381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4900701357817889789307587 7351052036726834683961381)
                    ·
                      refine ⟨1378322256886281503242759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7351052036726834683961381 1378322256886281503242759)
                      ·
                        rfl

theorem cell23_2684273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_2684273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2684273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2684273 prefixEnd_2684273 := by exact prefixLift 2684273
  have htrace : WordTrace (prefixWord ++ tailWord_2684273) baseStart_2684273 baseEnd_2684273 := by
    simpa [prefixWord, tailWord_2684273, baseEnd_2684273] using wordTrace_append hprefix tailTrace_2684273
  have hstable : (prefixWord ++ tailWord_2684273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684273).length < 2 ^ (prefixWord ++ tailWord_2684273).sum := by decide
  have hdescent : baseEnd_2684273 < baseStart_2684273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684283 : List Nat := [1, 1, 1, 1, 1, 6, 4, 1, 1, 6]
def baseStart_2684283 : Nat := 118140960795 + 2684283 * 2 ^ 59
def prefixEnd_2684283 : Nat := 4983230072969 + 3 ^ 40 * 2684283 * 2
def baseEnd_2684283 : Nat := 459442463897608821372571

theorem tailTrace_2684283 : CollatzResearch.WordTrace tailWord_2684283 prefixEnd_2684283 459442463897608821372571 := by
  unfold tailWord_2684283
  simp only [CollatzResearch.WordTrace]
  refine ⟨97903844134308604883313503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65269229422872403255542335 97903844134308604883313503)
  ·
    refine ⟨146855766201462907324970255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97903844134308604883313503 146855766201462907324970255)
    ·
      refine ⟨220283649302194360987455383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146855766201462907324970255 220283649302194360987455383)
      ·
        refine ⟨330425473953291541481183075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220283649302194360987455383 330425473953291541481183075)
        ·
          refine ⟨495638210929937312221774613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330425473953291541481183075 495638210929937312221774613)
          ·
            refine ⟨23233041137340811510395685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 495638210929937312221774613 23233041137340811510395685)
            ·
              refine ⟨4356195213251402158199191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23233041137340811510395685 4356195213251402158199191)
              ·
                refine ⟨6534292819877103237298787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4356195213251402158199191 6534292819877103237298787)
                ·
                  refine ⟨9801439229815654855948181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6534292819877103237298787 9801439229815654855948181)
                  ·
                    refine ⟨459442463897608821372571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9801439229815654855948181 459442463897608821372571)
                    ·
                      rfl

theorem cell23_2684283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 6].length) (baseStart_2684283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2684283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2684283 prefixEnd_2684283 := by exact prefixLift 2684283
  have htrace : WordTrace (prefixWord ++ tailWord_2684283) baseStart_2684283 baseEnd_2684283 := by
    simpa [prefixWord, tailWord_2684283, baseEnd_2684283] using wordTrace_append hprefix tailTrace_2684283
  have hstable : (prefixWord ++ tailWord_2684283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684283).length < 2 ^ (prefixWord ++ tailWord_2684283).sum := by decide
  have hdescent : baseEnd_2684283 < baseStart_2684283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684317 : List Nat := [1, 4, 2, 1, 3, 1, 3, 2, 2, 4]
def baseStart_2684317 : Nat := 118140960795 + 2684317 * 2 ^ 59
def prefixEnd_2684317 : Nat := 4983230072969 + 3 ^ 40 * 2684317 * 2
def baseEnd_2684317 : Nat := 459448283345026443697519

theorem tailTrace_2684317 : CollatzResearch.WordTrace tailWord_2684317 prefixEnd_2684317 459448283345026443697519 := by
  unfold tailWord_2684317
  simp only [CollatzResearch.WordTrace]
  refine ⟨97905084216185428690051205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65270056144123619126700803 97905084216185428690051205)
  ·
    refine ⟨18357203290534767879384601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97905084216185428690051205 18357203290534767879384601)
    ·
      refine ⟨13767902467901075909538451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18357203290534767879384601 13767902467901075909538451)
      ·
        refine ⟨20651853701851613864307677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13767902467901075909538451 20651853701851613864307677)
        ·
          refine ⟨7744445138194355199115379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20651853701851613864307677 7744445138194355199115379)
          ·
            refine ⟨11616667707291532798673069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7744445138194355199115379 11616667707291532798673069)
            ·
              refine ⟨4356250390234324799502401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11616667707291532798673069 4356250390234324799502401)
              ·
                refine ⟨3267187792675743599626801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4356250390234324799502401 3267187792675743599626801)
                ·
                  refine ⟨2450390844506807699720101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3267187792675743599626801 2450390844506807699720101)
                  ·
                    refine ⟨459448283345026443697519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2450390844506807699720101 459448283345026443697519)
                    ·
                      rfl

theorem cell23_2684317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_2684317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2684317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2684317 prefixEnd_2684317 := by exact prefixLift 2684317
  have htrace : WordTrace (prefixWord ++ tailWord_2684317) baseStart_2684317 baseEnd_2684317 := by
    simpa [prefixWord, tailWord_2684317, baseEnd_2684317] using wordTrace_append hprefix tailTrace_2684317
  have hstable : (prefixWord ++ tailWord_2684317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684317).length < 2 ^ (prefixWord ++ tailWord_2684317).sum := by decide
  have hdescent : baseEnd_2684317 < baseStart_2684317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684367 : List Nat := [1, 1, 2, 1, 1, 4, 4, 3, 1, 3, 2]
def baseStart_2684367 : Nat := 118140960795 + 2684367 * 2 ^ 59
def prefixEnd_2684367 : Nat := 4983230072969 + 3 ^ 40 * 2684367 * 2
def baseEnd_2684367 : Nat := 1378370524067804135467327

theorem tailTrace_2684367 : CollatzResearch.WordTrace tailWord_2684367 prefixEnd_2684367 1378370524067804135467327 := by
  unfold tailWord_2684367
  simp only [CollatzResearch.WordTrace]
  refine ⟨97906907866004287229371355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65271271910669524819580903 97906907866004287229371355)
  ·
    refine ⟨146860361799006430844057033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97906907866004287229371355 146860361799006430844057033)
    ·
      refine ⟨110145271349254823133042775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146860361799006430844057033 110145271349254823133042775)
      ·
        refine ⟨165217907023882234699564163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110145271349254823133042775 165217907023882234699564163)
        ·
          refine ⟨247826860535823352049346245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165217907023882234699564163 247826860535823352049346245)
          ·
            refine ⟨46467536350466878509252421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 247826860535823352049346245 46467536350466878509252421)
            ·
              refine ⟨8712663065712539720484829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46467536350466878509252421 8712663065712539720484829)
              ·
                refine ⟨3267248649642202395181811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8712663065712539720484829 3267248649642202395181811)
                ·
                  refine ⟨4900872974463303592772717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3267248649642202395181811 4900872974463303592772717)
                  ·
                    refine ⟨1837827365423738847289769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4900872974463303592772717 1837827365423738847289769)
                    ·
                      refine ⟨1378370524067804135467327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1837827365423738847289769 1378370524067804135467327)
                      ·
                        rfl

theorem cell23_2684367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 3, 1, 3, 2].length) (baseStart_2684367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2684367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2684367 prefixEnd_2684367 := by exact prefixLift 2684367
  have htrace : WordTrace (prefixWord ++ tailWord_2684367) baseStart_2684367 baseEnd_2684367 := by
    simpa [prefixWord, tailWord_2684367, baseEnd_2684367] using wordTrace_append hprefix tailTrace_2684367
  have hstable : (prefixWord ++ tailWord_2684367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684367).length < 2 ^ (prefixWord ++ tailWord_2684367).sum := by decide
  have hdescent : baseEnd_2684367 < baseStart_2684367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684374 : List Nat := [5, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3]
def baseStart_2684374 : Nat := 118140960795 + 2684374 * 2 ^ 59
def prefixEnd_2684374 : Nat := 4983230072969 + 3 ^ 40 * 2684374 * 2
def baseEnd_2684374 : Nat := 1378374118432385608079795

theorem tailTrace_2684374 : CollatzResearch.WordTrace tailWord_2684374 prefixEnd_2684374 1378374118432385608079795 := by
  unfold tailWord_2684374
  simp only [CollatzResearch.WordTrace]
  refine ⟨6119197698561182964054761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65271442117985951616584117 6119197698561182964054761)
  ·
    refine ⟨4589398273920887223041071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6119197698561182964054761 4589398273920887223041071)
    ·
      refine ⟨6884097410881330834561607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4589398273920887223041071 6884097410881330834561607)
      ·
        refine ⟨10326146116321996251842411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6884097410881330834561607 10326146116321996251842411)
        ·
          refine ⟨15489219174482994377763617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10326146116321996251842411 15489219174482994377763617)
          ·
            refine ⟨11616914380862245783322713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15489219174482994377763617 11616914380862245783322713)
            ·
              refine ⟨8712685785646684337492035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11616914380862245783322713 8712685785646684337492035)
              ·
                refine ⟨13069028678470026506238053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8712685785646684337492035 13069028678470026506238053)
                ·
                  refine ⟨2450442877213129969919635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13069028678470026506238053 2450442877213129969919635)
                  ·
                    refine ⟨3675664315819694954879453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2450442877213129969919635 3675664315819694954879453)
                    ·
                      refine ⟨1378374118432385608079795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3675664315819694954879453 1378374118432385608079795)
                      ·
                        rfl

theorem cell23_2684374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_2684374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2684374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2684374 prefixEnd_2684374 := by exact prefixLift 2684374
  have htrace : WordTrace (prefixWord ++ tailWord_2684374) baseStart_2684374 baseEnd_2684374 := by
    simpa [prefixWord, tailWord_2684374, baseEnd_2684374] using wordTrace_append hprefix tailTrace_2684374
  have hstable : (prefixWord ++ tailWord_2684374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684374).length < 2 ^ (prefixWord ++ tailWord_2684374).sum := by decide
  have hdescent : baseEnd_2684374 < baseStart_2684374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684383 : List Nat := [1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 5]
def baseStart_2684383 : Nat := 118140960795 + 2684383 * 2 ^ 59
def prefixEnd_2684383 : Nat := 4983230072969 + 3 ^ 40 * 2684383 * 2
def baseEnd_2684383 : Nat := 1378378739758276072867253

theorem tailTrace_2684383 : CollatzResearch.WordTrace tailWord_2684383 prefixEnd_2684383 1378378739758276072867253 := by
  unfold tailWord_2684383
  simp only [CollatzResearch.WordTrace]
  refine ⟨97907491433946321961953803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65271660955964214641302535 97907491433946321961953803)
  ·
    refine ⟨146861237150919482942930705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97907491433946321961953803 146861237150919482942930705)
    ·
      refine ⟨110145927863189612207198029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146861237150919482942930705 110145927863189612207198029)
      ·
        refine ⟨41304722948696104577699261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110145927863189612207198029 41304722948696104577699261)
        ·
          refine ⟨15489271105761039216637223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41304722948696104577699261 15489271105761039216637223)
          ·
            refine ⟨23233906658641558824955835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15489271105761039216637223 23233906658641558824955835)
            ·
              refine ⟨34850859987962338237433753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23233906658641558824955835 34850859987962338237433753)
              ·
                refine ⟨26138144990971753678075315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34850859987962338237433753 26138144990971753678075315)
                ·
                  refine ⟨39207217486457630517112973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26138144990971753678075315 39207217486457630517112973)
                  ·
                    refine ⟨14702706557421611443917365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39207217486457630517112973 14702706557421611443917365)
                    ·
                      refine ⟨1378378739758276072867253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14702706557421611443917365 1378378739758276072867253)
                      ·
                        rfl

theorem cell23_2684383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_2684383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2684383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2684383 prefixEnd_2684383 := by exact prefixLift 2684383
  have htrace : WordTrace (prefixWord ++ tailWord_2684383) baseStart_2684383 baseEnd_2684383 := by
    simpa [prefixWord, tailWord_2684383, baseEnd_2684383] using wordTrace_append hprefix tailTrace_2684383
  have hstable : (prefixWord ++ tailWord_2684383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684383).length < 2 ^ (prefixWord ++ tailWord_2684383).sum := by decide
  have hdescent : baseEnd_2684383 < baseStart_2684383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684391 : List Nat := [1, 1, 5, 2, 1, 4, 2, 1, 2, 1, 3]
def baseStart_2684391 : Nat := 118140960795 + 2684391 * 2 ^ 59
def prefixEnd_2684391 : Nat := 4983230072969 + 3 ^ 40 * 2684391 * 2
def baseEnd_2684391 : Nat := 1378382847603512041567217

theorem tailTrace_2684391 : CollatzResearch.WordTrace tailWord_2684391 prefixEnd_2684391 1378382847603512041567217 := by
  unfold tailWord_2684391
  simp only [CollatzResearch.WordTrace]
  refine ⟨97907783217917339328245027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65271855478611559552163351 97907783217917339328245027)
  ·
    refine ⟨146861674826876008992367541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97907783217917339328245027 146861674826876008992367541)
    ·
      refine ⟨13768282015019625843034457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 146861674826876008992367541 13768282015019625843034457)
      ·
        refine ⟨10326211511264719382275843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13768282015019625843034457 10326211511264719382275843)
        ·
          refine ⟨15489317266897079073413765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10326211511264719382275843 15489317266897079073413765)
          ·
            refine ⟨2904246987543202326265081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15489317266897079073413765 2904246987543202326265081)
            ·
              refine ⟨2178185240657401744698811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2904246987543202326265081 2178185240657401744698811)
              ·
                refine ⟨3267277860986102617048217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2178185240657401744698811 3267277860986102617048217)
                ·
                  refine ⟨2450458395739576962786163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3267277860986102617048217 2450458395739576962786163)
                  ·
                    refine ⟨3675687593609365444179245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2450458395739576962786163 3675687593609365444179245)
                    ·
                      refine ⟨1378382847603512041567217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3675687593609365444179245 1378382847603512041567217)
                      ·
                        rfl

theorem cell23_2684391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_2684391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2684391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2684391 prefixEnd_2684391 := by exact prefixLift 2684391
  have htrace : WordTrace (prefixWord ++ tailWord_2684391) baseStart_2684391 baseEnd_2684391 := by
    simpa [prefixWord, tailWord_2684391, baseEnd_2684391] using wordTrace_append hprefix tailTrace_2684391
  have hstable : (prefixWord ++ tailWord_2684391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684391).length < 2 ^ (prefixWord ++ tailWord_2684391).sum := by decide
  have hdescent : baseEnd_2684391 < baseStart_2684391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684393 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 6, 2, 4]
def baseStart_2684393 : Nat := 118140960795 + 2684393 * 2 ^ 59
def prefixEnd_2684393 : Nat := 4983230072969 + 3 ^ 40 * 2684393 * 2
def baseEnd_2684393 : Nat := 1378383874564821033742207

theorem tailTrace_2684393 : CollatzResearch.WordTrace tailWord_2684393 prefixEnd_2684393 1378383874564821033742207 := by
  unfold tailWord_2684393
  simp only [CollatzResearch.WordTrace]
  refine ⟨97907856163910093669817833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65271904109273395779878555 97907856163910093669817833)
  ·
    refine ⟨73430892122932570252363375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97907856163910093669817833 73430892122932570252363375)
    ·
      refine ⟨110146338184398855378545063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73430892122932570252363375 110146338184398855378545063)
      ·
        refine ⟨165219507276598283067817595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110146338184398855378545063 165219507276598283067817595)
        ·
          refine ⟨247829260914897424601726393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165219507276598283067817595 247829260914897424601726393)
          ·
            refine ⟨185871945686173068451294795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 247829260914897424601726393 185871945686173068451294795)
            ·
              refine ⟨278807918529259602676942193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185871945686173068451294795 278807918529259602676942193)
              ·
                refine ⟨209105938896944702007706645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 278807918529259602676942193 209105938896944702007706645)
                ·
                  refine ⟨9801840885794282906611249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 209105938896944702007706645 9801840885794282906611249)
                  ·
                    refine ⟨7351380664345712179958437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9801840885794282906611249 7351380664345712179958437)
                    ·
                      refine ⟨1378383874564821033742207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7351380664345712179958437 1378383874564821033742207)
                      ·
                        rfl

theorem cell23_2684393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 2, 4].length) (baseStart_2684393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2684393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2684393 prefixEnd_2684393 := by exact prefixLift 2684393
  have htrace : WordTrace (prefixWord ++ tailWord_2684393) baseStart_2684393 baseEnd_2684393 := by
    simpa [prefixWord, tailWord_2684393, baseEnd_2684393] using wordTrace_append hprefix tailTrace_2684393
  have hstable : (prefixWord ++ tailWord_2684393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684393).length < 2 ^ (prefixWord ++ tailWord_2684393).sum := by decide
  have hdescent : baseEnd_2684393 < baseStart_2684393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684418 : List Nat := [3, 4, 1, 2, 1, 2, 3, 1, 1, 3, 2]
def baseStart_2684418 : Nat := 118140960795 + 2684418 * 2 ^ 59
def prefixEnd_2684418 : Nat := 4983230072969 + 3 ^ 40 * 2684418 * 2
def baseEnd_2684418 : Nat := 1378396711581183435929593

theorem tailTrace_2684418 : CollatzResearch.WordTrace tailWord_2684418 prefixEnd_2684418 1378396711581183435929593 := by
  unfold tailWord_2684418
  simp only [CollatzResearch.WordTrace]
  refine ⟨24477191997204880734869477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65272511992546348626318605 24477191997204880734869477)
  ·
    refine ⟨4589473499475915137788027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24477191997204880734869477 4589473499475915137788027)
    ·
      refine ⟨6884210249213872706682041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4589473499475915137788027 6884210249213872706682041)
      ·
        refine ⟨5163157686910404530011531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6884210249213872706682041 5163157686910404530011531)
        ·
          refine ⟨7744736530365606795017297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5163157686910404530011531 7744736530365606795017297)
          ·
            refine ⟨5808552397774205096262973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7744736530365606795017297 5808552397774205096262973)
            ·
              refine ⟨2178207149165326911098615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5808552397774205096262973 2178207149165326911098615)
              ·
                refine ⟨3267310723747990366647923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2178207149165326911098615 3267310723747990366647923)
                ·
                  refine ⟨4900966085621985549971885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3267310723747990366647923 4900966085621985549971885)
                  ·
                    refine ⟨1837862282108244581239457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4900966085621985549971885 1837862282108244581239457)
                    ·
                      refine ⟨1378396711581183435929593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1837862282108244581239457 1378396711581183435929593)
                      ·
                        rfl

theorem cell23_2684418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_2684418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2684418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2684418 prefixEnd_2684418 := by exact prefixLift 2684418
  have htrace : WordTrace (prefixWord ++ tailWord_2684418) baseStart_2684418 baseEnd_2684418 := by
    simpa [prefixWord, tailWord_2684418, baseEnd_2684418] using wordTrace_append hprefix tailTrace_2684418
  have hstable : (prefixWord ++ tailWord_2684418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684418).length < 2 ^ (prefixWord ++ tailWord_2684418).sum := by decide
  have hdescent : baseEnd_2684418 < baseStart_2684418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684437 : List Nat := [1, 3, 2, 1, 3, 3, 1, 4, 5]
def baseStart_2684437 : Nat := 118140960795 + 2684437 * 2 ^ 59
def prefixEnd_2684437 : Nat := 4983230072969 + 3 ^ 40 * 2684437 * 2
def baseEnd_2684437 : Nat := 153156274190402095732445

theorem tailTrace_2684437 : CollatzResearch.WordTrace tailWord_2684437 prefixEnd_2684437 153156274190402095732445 := by
  unfold tailWord_2684437
  simp only [CollatzResearch.WordTrace]
  refine ⟨97909460975750689184419565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65272973983833792789613043 97909460975750689184419565)
  ·
    refine ⟨36716047865906508444157337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97909460975750689184419565 36716047865906508444157337)
    ·
      refine ⟨27537035899429881333118003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36716047865906508444157337 27537035899429881333118003)
      ·
        refine ⟨41305553849144821999677005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27537035899429881333118003 41305553849144821999677005)
        ·
          refine ⟨15489582693429308249878877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41305553849144821999677005 15489582693429308249878877)
          ·
            refine ⟨5808593510035990593704579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15489582693429308249878877 5808593510035990593704579)
            ·
              refine ⟨8712890265053985890556869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5808593510035990593704579 8712890265053985890556869)
              ·
                refine ⟨1633666924697622354479413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8712890265053985890556869 1633666924697622354479413)
                ·
                  refine ⟨153156274190402095732445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1633666924697622354479413 153156274190402095732445)
                  ·
                    rfl

theorem cell23_2684437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 4, 5].length) (baseStart_2684437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2684437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2684437 prefixEnd_2684437 := by exact prefixLift 2684437
  have htrace : WordTrace (prefixWord ++ tailWord_2684437) baseStart_2684437 baseEnd_2684437 := by
    simpa [prefixWord, tailWord_2684437, baseEnd_2684437] using wordTrace_append hprefix tailTrace_2684437
  have hstable : (prefixWord ++ tailWord_2684437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684437).length < 2 ^ (prefixWord ++ tailWord_2684437).sum := by decide
  have hdescent : baseEnd_2684437 < baseStart_2684437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684450 : List Nat := [3, 3, 1, 1, 1, 1, 2, 2, 4, 5]
def baseStart_2684450 : Nat := 118140960795 + 2684450 * 2 ^ 59
def prefixEnd_2684450 : Nat := 4983230072969 + 3 ^ 40 * 2684450 * 2
def baseEnd_2684450 : Nat := 459471047654042436909815

theorem tailTrace_2684450 : CollatzResearch.WordTrace tailWord_2684450 prefixEnd_2684450 459471047654042436909815 := by
  unfold tailWord_2684450
  simp only [CollatzResearch.WordTrace]
  refine ⟨24477483781175898101160701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65273290083135728269761869 24477483781175898101160701)
  ·
    refine ⟨9179056417940961787935263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24477483781175898101160701 9179056417940961787935263)
    ·
      refine ⟨13768584626911442681902895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9179056417940961787935263 13768584626911442681902895)
      ·
        refine ⟨20652876940367164022854343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13768584626911442681902895 20652876940367164022854343)
        ·
          refine ⟨30979315410550746034281515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20652876940367164022854343 30979315410550746034281515)
          ·
            refine ⟨46468973115826119051422273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30979315410550746034281515 46468973115826119051422273)
            ·
              refine ⟨34851729836869589288566705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46468973115826119051422273 34851729836869589288566705)
              ·
                refine ⟨26138797377652191966425029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34851729836869589288566705 26138797377652191966425029)
                ·
                  refine ⟨4901024508309785993704693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26138797377652191966425029 4901024508309785993704693)
                  ·
                    refine ⟨459471047654042436909815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4901024508309785993704693 459471047654042436909815)
                    ·
                      rfl

theorem cell23_2684450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_2684450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2684450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2684450 prefixEnd_2684450 := by exact prefixLift 2684450
  have htrace : WordTrace (prefixWord ++ tailWord_2684450) baseStart_2684450 baseEnd_2684450 := by
    simpa [prefixWord, tailWord_2684450, baseEnd_2684450] using wordTrace_append hprefix tailTrace_2684450
  have hstable : (prefixWord ++ tailWord_2684450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684450).length < 2 ^ (prefixWord ++ tailWord_2684450).sum := by decide
  have hdescent : baseEnd_2684450 < baseStart_2684450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684467 : List Nat := [1, 1, 1, 2, 4, 5, 1, 1, 2, 5]
def baseStart_2684467 : Nat := 118140960795 + 2684467 * 2 ^ 59
def prefixEnd_2684467 : Nat := 4983230072969 + 3 ^ 40 * 2684467 * 2
def baseEnd_2684467 : Nat := 459473957377751248072289

theorem tailTrace_2684467 : CollatzResearch.WordTrace tailWord_2684467 prefixEnd_2684467 459473957377751248072289 := by
  unfold tailWord_2684467
  simp only [CollatzResearch.WordTrace]
  refine ⟨97910555165642004308011655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65273703443761336205341103 97910555165642004308011655)
  ·
    refine ⟨146865832748463006462017483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97910555165642004308011655 146865832748463006462017483)
    ·
      refine ⟨220298749122694509693026225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146865832748463006462017483 220298749122694509693026225)
      ·
        refine ⟨165224061842020882269769669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220298749122694509693026225 165224061842020882269769669)
        ·
          refine ⟨30979511595378915425581813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165224061842020882269769669 30979511595378915425581813)
          ·
            refine ⟨2904329212066773321148295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30979511595378915425581813 2904329212066773321148295)
            ·
              refine ⟨4356493818100159981722443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2904329212066773321148295 4356493818100159981722443)
              ·
                refine ⟨6534740727150239972583665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4356493818100159981722443 6534740727150239972583665)
                ·
                  refine ⟨4901055545362679979437749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6534740727150239972583665 4901055545362679979437749)
                  ·
                    refine ⟨459473957377751248072289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4901055545362679979437749 459473957377751248072289)
                    ·
                      rfl

theorem cell23_2684467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 2, 5].length) (baseStart_2684467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2684467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2684467 prefixEnd_2684467 := by exact prefixLift 2684467
  have htrace : WordTrace (prefixWord ++ tailWord_2684467) baseStart_2684467 baseEnd_2684467 := by
    simpa [prefixWord, tailWord_2684467, baseEnd_2684467] using wordTrace_append hprefix tailTrace_2684467
  have hstable : (prefixWord ++ tailWord_2684467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684467).length < 2 ^ (prefixWord ++ tailWord_2684467).sum := by decide
  have hdescent : baseEnd_2684467 < baseStart_2684467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684480 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 7, 4]
def baseStart_2684480 : Nat := 118140960795 + 2684480 * 2 ^ 59
def prefixEnd_2684480 : Nat := 4983230072969 + 3 ^ 40 * 2684480 * 2
def baseEnd_2684480 : Nat := 459476182460587397784769

theorem tailTrace_2684480 : CollatzResearch.WordTrace tailWord_2684480 prefixEnd_2684480 459476182460587397784769 := by
  unfold tailWord_2684480
  simp only [CollatzResearch.WordTrace]
  refine ⟨48955514657297453764117447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65274019543063271685489929 48955514657297453764117447)
  ·
    refine ⟨73433271985946180646176171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48955514657297453764117447 73433271985946180646176171)
    ·
      refine ⟨110149907978919270969264257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73433271985946180646176171 110149907978919270969264257)
      ·
        refine ⟨82612430984189453226948193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110149907978919270969264257 82612430984189453226948193)
        ·
          refine ⟨61959323238142089920211145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82612430984189453226948193 61959323238142089920211145)
          ·
            refine ⟨46469492428606567440158359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61959323238142089920211145 46469492428606567440158359)
            ·
              refine ⟨69704238642909851160237539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46469492428606567440158359 69704238642909851160237539)
              ·
                refine ⟨104556357964364776740356309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69704238642909851160237539 104556357964364776740356309)
                ·
                  refine ⟨2450539639789799454852101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 104556357964364776740356309 2450539639789799454852101)
                  ·
                    refine ⟨459476182460587397784769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2450539639789799454852101 459476182460587397784769)
                    ·
                      rfl

theorem cell23_2684480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 7, 4].length) (baseStart_2684480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2684480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2684480 prefixEnd_2684480 := by exact prefixLift 2684480
  have htrace : WordTrace (prefixWord ++ tailWord_2684480) baseStart_2684480 baseEnd_2684480 := by
    simpa [prefixWord, tailWord_2684480, baseEnd_2684480] using wordTrace_append hprefix tailTrace_2684480
  have hstable : (prefixWord ++ tailWord_2684480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684480).length < 2 ^ (prefixWord ++ tailWord_2684480).sum := by decide
  have hdescent : baseEnd_2684480 < baseStart_2684480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684497 : List Nat := [1, 2, 2, 1, 3, 2, 4, 1, 3, 4]
def baseStart_2684497 : Nat := 118140960795 + 2684497 * 2 ^ 59
def prefixEnd_2684497 : Nat := 4983230072969 + 3 ^ 40 * 2684497 * 2
def baseEnd_2684497 : Nat := 459479092184296208947243

theorem tailTrace_2684497 : CollatzResearch.WordTrace tailWord_2684497 prefixEnd_2684497 459479092184296208947243 := by
  unfold tailWord_2684497
  simp only [CollatzResearch.WordTrace]
  refine ⟨97911649355533319431603745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65274432903688879621069163 97911649355533319431603745)
  ·
    refine ⟨73433737016649989573702809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97911649355533319431603745 73433737016649989573702809)
    ·
      refine ⟨55075302762487492180277107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73433737016649989573702809 55075302762487492180277107)
      ·
        refine ⟨82612954143731238270415661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55075302762487492180277107 82612954143731238270415661)
        ·
          refine ⟨30979857803899214351405873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82612954143731238270415661 30979857803899214351405873)
          ·
            refine ⟨23234893352924410763554405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30979857803899214351405873 23234893352924410763554405)
            ·
              refine ⟨4356542503673327018166451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23234893352924410763554405 4356542503673327018166451)
              ·
                refine ⟨6534813755509990527249677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4356542503673327018166451 6534813755509990527249677)
                ·
                  refine ⟨2450555158316246447718629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6534813755509990527249677 2450555158316246447718629)
                  ·
                    refine ⟨459479092184296208947243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2450555158316246447718629 459479092184296208947243)
                    ·
                      rfl

theorem cell23_2684497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 3, 4].length) (baseStart_2684497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2684497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2684497 prefixEnd_2684497 := by exact prefixLift 2684497
  have htrace : WordTrace (prefixWord ++ tailWord_2684497) baseStart_2684497 baseEnd_2684497 := by
    simpa [prefixWord, tailWord_2684497, baseEnd_2684497] using wordTrace_append hprefix tailTrace_2684497
  have hstable : (prefixWord ++ tailWord_2684497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684497).length < 2 ^ (prefixWord ++ tailWord_2684497).sum := by decide
  have hdescent : baseEnd_2684497 < baseStart_2684497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684500 : List Nat := [2, 4, 1, 1, 1, 2, 1, 2, 2, 1, 6]
def baseStart_2684500 : Nat := 118140960795 + 2684500 * 2 ^ 59
def prefixEnd_2684500 : Nat := 4983230072969 + 3 ^ 40 * 2684500 * 2
def baseEnd_2684500 : Nat := 1378438816994852115104215

theorem tailTrace_2684500 : CollatzResearch.WordTrace tailWord_2684500 prefixEnd_2684500 1378438816994852115104215 := by
  unfold tailWord_2684500
  simp only [CollatzResearch.WordTrace]
  refine ⟨48955879387261225471981477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65274505849681633962641969 48955879387261225471981477)
  ·
    refine ⟨9179227385111479775996527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48955879387261225471981477 9179227385111479775996527)
    ·
      refine ⟨13768841077667219663994791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9179227385111479775996527 13768841077667219663994791)
      ·
        refine ⟨20653261616500829495992187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13768841077667219663994791 20653261616500829495992187)
        ·
          refine ⟨30979892424751244243988281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20653261616500829495992187 30979892424751244243988281)
          ·
            refine ⟨23234919318563433182991211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30979892424751244243988281 23234919318563433182991211)
            ·
              refine ⟨34852378977845149774486817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23234919318563433182991211 34852378977845149774486817)
              ·
                refine ⟨26139284233383862330865113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34852378977845149774486817 26139284233383862330865113)
                ·
                  refine ⟨19604463175037896748148835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26139284233383862330865113 19604463175037896748148835)
                  ·
                    refine ⟨29406694762556845122223253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19604463175037896748148835 29406694762556845122223253)
                    ·
                      refine ⟨1378438816994852115104215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29406694762556845122223253 1378438816994852115104215)
                      ·
                        rfl

theorem cell23_2684500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_2684500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2684500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2684500 prefixEnd_2684500 := by exact prefixLift 2684500
  have htrace : WordTrace (prefixWord ++ tailWord_2684500) baseStart_2684500 baseEnd_2684500 := by
    simpa [prefixWord, tailWord_2684500, baseEnd_2684500] using wordTrace_append hprefix tailTrace_2684500
  have hstable : (prefixWord ++ tailWord_2684500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684500).length < 2 ^ (prefixWord ++ tailWord_2684500).sum := by decide
  have hdescent : baseEnd_2684500 < baseStart_2684500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684540 : List Nat := [2, 2, 2, 1, 1, 2, 1, 2, 5, 5]
def baseStart_2684540 : Nat := 118140960795 + 2684540 * 2 ^ 59
def prefixEnd_2684540 : Nat := 4983230072969 + 3 ^ 40 * 2684540 * 2
def baseEnd_2684540 : Nat := 459486452073677319534677

theorem tailTrace_2684540 : CollatzResearch.WordTrace tailWord_2684540 prefixEnd_2684540 459486452073677319534677 := by
  unfold tailWord_2684540
  simp only [CollatzResearch.WordTrace]
  refine ⟨48956608847188768887709537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65275478462918358516946049 48956608847188768887709537)
  ·
    refine ⟨36717456635391576665782153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48956608847188768887709537 36717456635391576665782153)
    ·
      refine ⟨27538092476543682499336615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36717456635391576665782153 27538092476543682499336615)
      ·
        refine ⟨41307138714815523749004923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27538092476543682499336615 41307138714815523749004923)
        ·
          refine ⟨61960708072223285623507385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41307138714815523749004923 61960708072223285623507385)
          ·
            refine ⟨46470531054167464217630539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61960708072223285623507385 46470531054167464217630539)
            ·
              refine ⟨69705796581251196326445809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46470531054167464217630539 69705796581251196326445809)
              ·
                refine ⟨52279347435938397244834357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69705796581251196326445809 52279347435938397244834357)
                ·
                  refine ⟨4901188822119224741703221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52279347435938397244834357 4901188822119224741703221)
                  ·
                    refine ⟨459486452073677319534677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4901188822119224741703221 459486452073677319534677)
                    ·
                      rfl

theorem cell23_2684540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 5, 5].length) (baseStart_2684540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2684540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2684540 prefixEnd_2684540 := by exact prefixLift 2684540
  have htrace : WordTrace (prefixWord ++ tailWord_2684540) baseStart_2684540 baseEnd_2684540 := by
    simpa [prefixWord, tailWord_2684540, baseEnd_2684540] using wordTrace_append hprefix tailTrace_2684540
  have hstable : (prefixWord ++ tailWord_2684540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684540).length < 2 ^ (prefixWord ++ tailWord_2684540).sum := by decide
  have hdescent : baseEnd_2684540 < baseStart_2684540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684548 : List Nat := [2, 3, 2, 1, 4, 1, 3, 2, 1, 4]
def baseStart_2684548 : Nat := 118140960795 + 2684548 * 2 ^ 59
def prefixEnd_2684548 : Nat := 4983230072969 + 3 ^ 40 * 2684548 * 2
def baseEnd_2684548 : Nat := 459487821355422642434665

theorem tailTrace_2684548 : CollatzResearch.WordTrace tailWord_2684548 prefixEnd_2684548 459487821355422642434665 := by
  unfold tailWord_2684548
  simp only [CollatzResearch.WordTrace]
  refine ⟨48956754739174277570855149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65275672985565703427806865 48956754739174277570855149)
  ·
    refine ⟨18358783027190354089070681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48956754739174277570855149 18358783027190354089070681)
    ·
      refine ⟨13769087270392765566803011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18358783027190354089070681 13769087270392765566803011)
      ·
        refine ⟨20653630905589148350204517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13769087270392765566803011 20653630905589148350204517)
        ·
          refine ⟨3872555794797965315663347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20653630905589148350204517 3872555794797965315663347)
          ·
            refine ⟨5808833692196947973495021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3872555794797965315663347 5808833692196947973495021)
            ·
              refine ⟨2178312634573855490060633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5808833692196947973495021 2178312634573855490060633)
              ·
                refine ⟨1633734475930391617545475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2178312634573855490060633 1633734475930391617545475)
                ·
                  refine ⟨2450601713895587426318213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1633734475930391617545475 2450601713895587426318213)
                  ·
                    refine ⟨459487821355422642434665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2450601713895587426318213 459487821355422642434665)
                    ·
                      rfl

theorem cell23_2684548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_2684548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2684548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2684548 prefixEnd_2684548 := by exact prefixLift 2684548
  have htrace : WordTrace (prefixWord ++ tailWord_2684548) baseStart_2684548 baseEnd_2684548 := by
    simpa [prefixWord, tailWord_2684548, baseEnd_2684548] using wordTrace_append hprefix tailTrace_2684548
  have hstable : (prefixWord ++ tailWord_2684548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684548).length < 2 ^ (prefixWord ++ tailWord_2684548).sum := by decide
  have hdescent : baseEnd_2684548 < baseStart_2684548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684574 : List Nat := [4, 3, 1, 1, 1, 3, 1, 1, 3, 5]
def baseStart_2684574 : Nat := 118140960795 + 2684574 * 2 ^ 59
def prefixEnd_2684574 : Nat := 4983230072969 + 3 ^ 40 * 2684574 * 2
def baseEnd_2684574 : Nat := 459492271521094941859625

theorem tailTrace_2684574 : CollatzResearch.WordTrace tailWord_2684574 prefixEnd_2684574 459492271521094941859625 := by
  unfold tailWord_2684574
  simp only [CollatzResearch.WordTrace]
  refine ⟨12239307222031795197769597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65276305184169574388104517 12239307222031795197769597)
  ·
    refine ⟨4589740208261923199163599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12239307222031795197769597 4589740208261923199163599)
    ·
      refine ⟨6884610312392884798745399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4589740208261923199163599 6884610312392884798745399)
      ·
        refine ⟨10326915468589327198118099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6884610312392884798745399 10326915468589327198118099)
        ·
          refine ⟨15490373202883990797177149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10326915468589327198118099 15490373202883990797177149)
          ·
            refine ⟨5808889951081496548941431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15490373202883990797177149 5808889951081496548941431)
            ·
              refine ⟨8713334926622244823412147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5808889951081496548941431 8713334926622244823412147)
              ·
                refine ⟨13070002389933367235118221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8713334926622244823412147 13070002389933367235118221)
                ·
                  refine ⟨4901250896225012713169333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13070002389933367235118221 4901250896225012713169333)
                  ·
                    refine ⟨459492271521094941859625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4901250896225012713169333 459492271521094941859625)
                    ·
                      rfl

theorem cell23_2684574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_2684574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2684574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2684574 prefixEnd_2684574 := by exact prefixLift 2684574
  have htrace : WordTrace (prefixWord ++ tailWord_2684574) baseStart_2684574 baseEnd_2684574 := by
    simpa [prefixWord, tailWord_2684574, baseEnd_2684574] using wordTrace_append hprefix tailTrace_2684574
  have hstable : (prefixWord ++ tailWord_2684574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684574).length < 2 ^ (prefixWord ++ tailWord_2684574).sum := by decide
  have hdescent : baseEnd_2684574 < baseStart_2684574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684598 : List Nat := [5, 1, 3, 1, 1, 1, 2, 2, 2, 3, 2]
def baseStart_2684598 : Nat := 118140960795 + 2684598 * 2 ^ 59
def prefixEnd_2684598 : Nat := 4983230072969 + 3 ^ 40 * 2684598 * 2
def baseEnd_2684598 : Nat := 1378489138098992731678765

theorem tailTrace_2684598 : CollatzResearch.WordTrace tailWord_2684598 prefixEnd_2684598 1378489138098992731678765 := by
  unfold tailWord_2684598
  simp only [CollatzResearch.WordTrace]
  refine ⟨6119708320510463355064403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65276888752111609120686965 6119708320510463355064403)
  ·
    refine ⟨9179562480765695032596605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6119708320510463355064403 9179562480765695032596605)
    ·
      refine ⟨3442335930287135637223727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9179562480765695032596605 3442335930287135637223727)
      ·
        refine ⟨5163503895430703455835591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3442335930287135637223727 5163503895430703455835591)
        ·
          refine ⟨7745255843146055183753387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5163503895430703455835591 7745255843146055183753387)
          ·
            refine ⟨11617883764719082775630081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7745255843146055183753387 11617883764719082775630081)
            ·
              refine ⟨8713412823539312081722561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11617883764719082775630081 8713412823539312081722561)
              ·
                refine ⟨6535059617654484061291921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8713412823539312081722561 6535059617654484061291921)
                ·
                  refine ⟨4901294713240863045968941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6535059617654484061291921 4901294713240863045968941)
                  ·
                    refine ⟨1837985517465323642238353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4901294713240863045968941 1837985517465323642238353)
                    ·
                      refine ⟨1378489138098992731678765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1837985517465323642238353 1378489138098992731678765)
                      ·
                        rfl

theorem cell23_2684598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_2684598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2684598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2684598 prefixEnd_2684598 := by exact prefixLift 2684598
  have htrace : WordTrace (prefixWord ++ tailWord_2684598) baseStart_2684598 baseEnd_2684598 := by
    simpa [prefixWord, tailWord_2684598, baseEnd_2684598] using wordTrace_append hprefix tailTrace_2684598
  have hstable : (prefixWord ++ tailWord_2684598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684598).length < 2 ^ (prefixWord ++ tailWord_2684598).sum := by decide
  have hdescent : baseEnd_2684598 < baseStart_2684598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684604 : List Nat := [2, 2, 2, 3, 1, 2, 1, 4, 2, 4]
def baseStart_2684604 : Nat := 118140960795 + 2684604 * 2 ^ 59
def prefixEnd_2684604 : Nat := 4983230072969 + 3 ^ 40 * 2684604 * 2
def baseEnd_2684604 : Nat := 459497406327639902734579

theorem tailTrace_2684604 : CollatzResearch.WordTrace tailWord_2684604 prefixEnd_2684604 459497406327639902734579 := by
  unfold tailWord_2684604
  simp only [CollatzResearch.WordTrace]
  refine ⟨48957775983072838352874433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65277034644097117803832577 48957775983072838352874433)
  ·
    refine ⟨36718331987304628764655825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48957775983072838352874433 36718331987304628764655825)
    ·
      refine ⟨27538748990478471573491869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36718331987304628764655825 27538748990478471573491869)
      ·
        refine ⟨10327030871429426840059451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27538748990478471573491869 10327030871429426840059451)
        ·
          refine ⟨15490546307144140260089177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10327030871429426840059451 15490546307144140260089177)
          ·
            refine ⟨11617909730358105195066883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15490546307144140260089177 11617909730358105195066883)
            ·
              refine ⟨17426864595537157792600325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11617909730358105195066883 17426864595537157792600325)
              ·
                refine ⟨3267537111663217086112561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17426864595537157792600325 3267537111663217086112561)
                ·
                  refine ⟨2450652833747412814584421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3267537111663217086112561 2450652833747412814584421)
                  ·
                    refine ⟨459497406327639902734579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2450652833747412814584421 459497406327639902734579)
                    ·
                      rfl

theorem cell23_2684604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 4, 2, 4].length) (baseStart_2684604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2684604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2684604 prefixEnd_2684604 := by exact prefixLift 2684604
  have htrace : WordTrace (prefixWord ++ tailWord_2684604) baseStart_2684604 baseEnd_2684604 := by
    simpa [prefixWord, tailWord_2684604, baseEnd_2684604] using wordTrace_append hprefix tailTrace_2684604
  have hstable : (prefixWord ++ tailWord_2684604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684604).length < 2 ^ (prefixWord ++ tailWord_2684604).sum := by decide
  have hdescent : baseEnd_2684604 < baseStart_2684604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684621 : List Nat := [1, 6, 2, 1, 1, 2, 2, 1, 1, 6]
def baseStart_2684621 : Nat := 118140960795 + 2684621 * 2 ^ 59
def prefixEnd_2684621 : Nat := 4983230072969 + 3 ^ 40 * 2684621 * 2
def baseEnd_2684621 : Nat := 459500316051348713897053

theorem tailTrace_2684621 : CollatzResearch.WordTrace tailWord_2684621 prefixEnd_2684621 459500316051348713897053 := by
  unfold tailWord_2684621
  simp only [CollatzResearch.WordTrace]
  refine ⟨97916172007084088609117717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65277448004722725739411811 97916172007084088609117717)
  ·
    refine ⟨4589820562832066653552393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 97916172007084088609117717 4589820562832066653552393)
    ·
      refine ⟨3442365422124049990164295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4589820562832066653552393 3442365422124049990164295)
      ·
        refine ⟨5163548133186074985246443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3442365422124049990164295 5163548133186074985246443)
        ·
          refine ⟨7745322199779112477869665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5163548133186074985246443 7745322199779112477869665)
          ·
            refine ⟨5808991649834334358402249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7745322199779112477869665 5808991649834334358402249)
            ·
              refine ⟨4356743737375750768801687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5808991649834334358402249 4356743737375750768801687)
              ·
                refine ⟨6535115606063626153202531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4356743737375750768801687 6535115606063626153202531)
                ·
                  refine ⟨9802673409095439229803797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6535115606063626153202531 9802673409095439229803797)
                  ·
                    refine ⟨459500316051348713897053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9802673409095439229803797 459500316051348713897053)
                    ·
                      rfl

theorem cell23_2684621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_2684621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2684621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2684621 prefixEnd_2684621 := by exact prefixLift 2684621
  have htrace : WordTrace (prefixWord ++ tailWord_2684621) baseStart_2684621 baseEnd_2684621 := by
    simpa [prefixWord, tailWord_2684621, baseEnd_2684621] using wordTrace_append hprefix tailTrace_2684621
  have hstable : (prefixWord ++ tailWord_2684621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684621).length < 2 ^ (prefixWord ++ tailWord_2684621).sum := by decide
  have hdescent : baseEnd_2684621 < baseStart_2684621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684628 : List Nat := [2, 4, 1, 3, 1, 2, 1, 2, 3, 2, 2]
def baseStart_2684628 : Nat := 118140960795 + 2684628 * 2 ^ 59
def prefixEnd_2684628 : Nat := 4983230072969 + 3 ^ 40 * 2684628 * 2
def baseEnd_2684628 : Nat := 1378504542518627614303627

theorem tailTrace_2684628 : CollatzResearch.WordTrace tailWord_2684628 prefixEnd_2684628 1378504542518627614303627 := by
  unfold tailWord_2684628
  simp only [CollatzResearch.WordTrace]
  refine ⟨48958213659029364402311269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65277618212039152536415025 48958213659029364402311269)
  ·
    refine ⟨9179665061068005825433363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48958213659029364402311269 9179665061068005825433363)
    ·
      refine ⟨13769497591602008738150045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9179665061068005825433363 13769497591602008738150045)
      ·
        refine ⟨5163561596850753276806267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13769497591602008738150045 5163561596850753276806267)
        ·
          refine ⟨7745342395276129915209401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5163561596850753276806267 7745342395276129915209401)
          ·
            refine ⟨5809006796457097436407051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7745342395276129915209401 5809006796457097436407051)
            ·
              refine ⟨8713510194685646154610577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5809006796457097436407051 8713510194685646154610577)
              ·
                refine ⟨6535132646014234615957933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8713510194685646154610577 6535132646014234615957933)
                ·
                  refine ⟨2450674742255337980984225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6535132646014234615957933 2450674742255337980984225)
                  ·
                    refine ⟨1838006056691503485738169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2450674742255337980984225 1838006056691503485738169)
                    ·
                      refine ⟨1378504542518627614303627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1838006056691503485738169 1378504542518627614303627)
                      ·
                        rfl

theorem cell23_2684628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_2684628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2684628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2684628 prefixEnd_2684628 := by exact prefixLift 2684628
  have htrace : WordTrace (prefixWord ++ tailWord_2684628) baseStart_2684628 baseEnd_2684628 := by
    simpa [prefixWord, tailWord_2684628, baseEnd_2684628] using wordTrace_append hprefix tailTrace_2684628
  have hstable : (prefixWord ++ tailWord_2684628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684628).length < 2 ^ (prefixWord ++ tailWord_2684628).sum := by decide
  have hdescent : baseEnd_2684628 < baseStart_2684628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684644 : List Nat := [2, 3, 1, 1, 1, 3, 2, 2, 4, 1, 3]
def baseStart_2684644 : Nat := 118140960795 + 2684644 * 2 ^ 59
def prefixEnd_2684644 : Nat := 4983230072969 + 3 ^ 40 * 2684644 * 2
def baseEnd_2684644 : Nat := 1378512758209099551703553

theorem tailTrace_2684644 : CollatzResearch.WordTrace tailWord_2684644 prefixEnd_2684644 1378512758209099551703553 := by
  unfold tailWord_2684644
  simp only [CollatzResearch.WordTrace]
  refine ⟨48958505443000381768602493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65278007257333842358136657 48958505443000381768602493)
  ·
    refine ⟨18359439541125143163225935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48958505443000381768602493 18359439541125143163225935)
    ·
      refine ⟨27539159311687714744838903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18359439541125143163225935 27539159311687714744838903)
      ·
        refine ⟨41308738967531572117258355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27539159311687714744838903 41308738967531572117258355)
        ·
          refine ⟨61963108451297358175887533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41308738967531572117258355 61963108451297358175887533)
          ·
            refine ⟨23236165669236509315957825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61963108451297358175887533 23236165669236509315957825)
            ·
              refine ⟨17427124251927381986968369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23236165669236509315957825 17427124251927381986968369)
              ·
                refine ⟨13070343188945536490226277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17427124251927381986968369 13070343188945536490226277)
                ·
                  refine ⟨2450689347927288091917427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13070343188945536490226277 2450689347927288091917427)
                  ·
                    refine ⟨3676034021890932137876141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2450689347927288091917427 3676034021890932137876141)
                    ·
                      refine ⟨1378512758209099551703553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3676034021890932137876141 1378512758209099551703553)
                      ·
                        rfl

theorem cell23_2684644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 4, 1, 3].length) (baseStart_2684644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2684644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2684644 prefixEnd_2684644 := by exact prefixLift 2684644
  have htrace : WordTrace (prefixWord ++ tailWord_2684644) baseStart_2684644 baseEnd_2684644 := by
    simpa [prefixWord, tailWord_2684644, baseEnd_2684644] using wordTrace_append hprefix tailTrace_2684644
  have hstable : (prefixWord ++ tailWord_2684644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684644).length < 2 ^ (prefixWord ++ tailWord_2684644).sum := by decide
  have hdescent : baseEnd_2684644 < baseStart_2684644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684648 : List Nat := [2, 1, 4, 1, 3, 3, 2, 1, 1, 2, 3]
def baseStart_2684648 : Nat := 118140960795 + 2684648 * 2 ^ 59
def prefixEnd_2684648 : Nat := 4983230072969 + 3 ^ 40 * 2684648 * 2
def baseEnd_2684648 : Nat := 1378514812131717536053535

theorem tailTrace_2684648 : CollatzResearch.WordTrace tailWord_2684648 prefixEnd_2684648 1378514812131717536053535 := by
  unfold tailWord_2684648
  simp only [CollatzResearch.WordTrace]
  refine ⟨48958578388993136110175299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65278104518657514813567065 48958578388993136110175299)
  ·
    refine ⟨73437867583489704165262949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48958578388993136110175299 73437867583489704165262949)
    ·
      refine ⟨13769600171904319530986803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73437867583489704165262949 13769600171904319530986803)
      ·
        refine ⟨20654400257856479296480205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13769600171904319530986803 20654400257856479296480205)
        ·
          refine ⟨7745400096696179736180077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20654400257856479296480205 7745400096696179736180077)
          ·
            refine ⟨2904525036261067401067529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7745400096696179736180077 2904525036261067401067529)
            ·
              refine ⟨2178393777195800550800647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2904525036261067401067529 2178393777195800550800647)
              ·
                refine ⟨3267590665793700826200971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2178393777195800550800647 3267590665793700826200971)
                ·
                  refine ⟨4901385998690551239301457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3267590665793700826200971 4901385998690551239301457)
                  ·
                    refine ⟨3676039499017913429476093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4901385998690551239301457 3676039499017913429476093)
                    ·
                      refine ⟨1378514812131717536053535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3676039499017913429476093 1378514812131717536053535)
                      ·
                        rfl

theorem cell23_2684648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 1, 1, 2, 3].length) (baseStart_2684648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2684648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2684648 prefixEnd_2684648 := by exact prefixLift 2684648
  have htrace : WordTrace (prefixWord ++ tailWord_2684648) baseStart_2684648 baseEnd_2684648 := by
    simpa [prefixWord, tailWord_2684648, baseEnd_2684648] using wordTrace_append hprefix tailTrace_2684648
  have hstable : (prefixWord ++ tailWord_2684648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684648).length < 2 ^ (prefixWord ++ tailWord_2684648).sum := by decide
  have hdescent : baseEnd_2684648 < baseStart_2684648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684754 : List Nat := [3, 2, 2, 1, 1, 3, 1, 3, 2, 5]
def baseStart_2684754 : Nat := 118140960795 + 2684754 * 2 ^ 59
def prefixEnd_2684754 : Nat := 4983230072969 + 3 ^ 40 * 2684754 * 2
def baseEnd_2684754 : Nat := 459523080360364707109349

theorem tailTrace_2684754 : CollatzResearch.WordTrace tailWord_2684754 prefixEnd_2684754 459523080360364707109349 := by
  unfold tailWord_2684754
  simp only [CollatzResearch.WordTrace]
  refine ⟨24480255728900563080927329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65280681943734834882472877 24480255728900563080927329)
  ·
    refine ⟨18360191796675422310695497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24480255728900563080927329 18360191796675422310695497)
    ·
      refine ⟨13770143847506566733021623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18360191796675422310695497 13770143847506566733021623)
      ·
        refine ⟨20655215771259850099532435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13770143847506566733021623 20655215771259850099532435)
        ·
          refine ⟨30982823656889775149298653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20655215771259850099532435 30982823656889775149298653)
          ·
            refine ⟨11618558871333665680986995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30982823656889775149298653 11618558871333665680986995)
            ·
              refine ⟨17427838307000498521480493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11618558871333665680986995 17427838307000498521480493)
              ·
                refine ⟨6535439365125186945555185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17427838307000498521480493 6535439365125186945555185)
                ·
                  refine ⟨4901579523843890209166389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6535439365125186945555185 4901579523843890209166389)
                  ·
                    refine ⟨459523080360364707109349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4901579523843890209166389 459523080360364707109349)
                    ·
                      rfl

theorem cell23_2684754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_2684754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2684754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2684754 prefixEnd_2684754 := by exact prefixLift 2684754
  have htrace : WordTrace (prefixWord ++ tailWord_2684754) baseStart_2684754 baseEnd_2684754 := by
    simpa [prefixWord, tailWord_2684754, baseEnd_2684754] using wordTrace_append hprefix tailTrace_2684754
  have hstable : (prefixWord ++ tailWord_2684754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684754).length < 2 ^ (prefixWord ++ tailWord_2684754).sum := by decide
  have hdescent : baseEnd_2684754 < baseStart_2684754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684784 : List Nat := [2, 1, 1, 1, 4, 1, 1, 5, 3, 4]
def baseStart_2684784 : Nat := 118140960795 + 2684784 * 2 ^ 59
def prefixEnd_2684784 : Nat := 4983230072969 + 3 ^ 40 * 2684784 * 2
def baseEnd_2684784 : Nat := 459528215166909667984303

theorem tailTrace_2684784 : CollatzResearch.WordTrace tailWord_2684784 prefixEnd_2684784 459528215166909667984303 := by
  unfold tailWord_2684784
  simp only [CollatzResearch.WordTrace]
  refine ⟨48961058552746783723650703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65281411403662378298200937 48961058552746783723650703)
  ·
    refine ⟨73441587829120175585476055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48961058552746783723650703 73441587829120175585476055)
    ·
      refine ⟨110162381743680263378214083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73441587829120175585476055 110162381743680263378214083)
      ·
        refine ⟨165243572615520395067321125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110162381743680263378214083 165243572615520395067321125)
        ·
          refine ⟨30983169865410074075122711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165243572615520395067321125 30983169865410074075122711)
          ·
            refine ⟨46474754798115111112684067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30983169865410074075122711 46474754798115111112684067)
            ·
              refine ⟨69712132197172666669026101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46474754798115111112684067 69712132197172666669026101)
              ·
                refine ⟨6535512393484937500221197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69712132197172666669026101 6535512393484937500221197)
                ·
                  refine ⟨2450817147556851562582949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6535512393484937500221197 2450817147556851562582949)
                  ·
                    refine ⟨459528215166909667984303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2450817147556851562582949 459528215166909667984303)
                    ·
                      rfl

theorem cell23_2684784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 3, 4].length) (baseStart_2684784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2684784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2684784 prefixEnd_2684784 := by exact prefixLift 2684784
  have htrace : WordTrace (prefixWord ++ tailWord_2684784) baseStart_2684784 baseEnd_2684784 := by
    simpa [prefixWord, tailWord_2684784, baseEnd_2684784] using wordTrace_append hprefix tailTrace_2684784
  have hstable : (prefixWord ++ tailWord_2684784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684784).length < 2 ^ (prefixWord ++ tailWord_2684784).sum := by decide
  have hdescent : baseEnd_2684784 < baseStart_2684784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684787 : List Nat := [1, 1, 1, 2, 2, 1, 3, 2, 2, 4, 4]
def baseStart_2684787 : Nat := 118140960795 + 2684787 * 2 ^ 59
def prefixEnd_2684787 : Nat := 4983230072969 + 3 ^ 40 * 2684787 * 2
def baseEnd_2684787 : Nat := 1378586185942692492215395

theorem tailTrace_2684787 : CollatzResearch.WordTrace tailWord_2684787 prefixEnd_2684787 1378586185942692492215395 := by
  unfold tailWord_2684787
  simp only [CollatzResearch.WordTrace]
  refine ⟨97922226524482698959660615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65281484349655132639773743 97922226524482698959660615)
  ·
    refine ⟨146883339786724048439490923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97922226524482698959660615 146883339786724048439490923)
    ·
      refine ⟨220325009680086072659236385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146883339786724048439490923 220325009680086072659236385)
      ·
        refine ⟨165243757260064554494427289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220325009680086072659236385 165243757260064554494427289)
        ·
          refine ⟨123932817945048415870820467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165243757260064554494427289 123932817945048415870820467)
          ·
            refine ⟨185899226917572623806230701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123932817945048415870820467 185899226917572623806230701)
            ·
              refine ⟨69712210094089733927336513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 185899226917572623806230701 69712210094089733927336513)
              ·
                refine ⟨52284157570567300445502385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69712210094089733927336513 52284157570567300445502385)
                ·
                  refine ⟨39213118177925475334126789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52284157570567300445502385 39213118177925475334126789)
                  ·
                    refine ⟨7352459658361026625148773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39213118177925475334126789 7352459658361026625148773)
                    ·
                      refine ⟨1378586185942692492215395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7352459658361026625148773 1378586185942692492215395)
                      ·
                        rfl

theorem cell23_2684787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 4, 4].length) (baseStart_2684787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2684787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2684787 prefixEnd_2684787 := by exact prefixLift 2684787
  have htrace : WordTrace (prefixWord ++ tailWord_2684787) baseStart_2684787 baseEnd_2684787 := by
    simpa [prefixWord, tailWord_2684787, baseEnd_2684787] using wordTrace_append hprefix tailTrace_2684787
  have hstable : (prefixWord ++ tailWord_2684787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684787).length < 2 ^ (prefixWord ++ tailWord_2684787).sum := by decide
  have hdescent : baseEnd_2684787 < baseStart_2684787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684794 : List Nat := [3, 1, 1, 1, 1, 1, 4, 2, 4, 2, 3]
def baseStart_2684794 : Nat := 118140960795 + 2684794 * 2 ^ 59
def prefixEnd_2684794 : Nat := 4983230072969 + 3 ^ 40 * 2684794 * 2
def baseEnd_2684794 : Nat := 1378589780307273964827863

theorem tailTrace_2684794 : CollatzResearch.WordTrace tailWord_2684794 prefixEnd_2684794 1378589780307273964827863 := by
  unfold tailWord_2684794
  simp only [CollatzResearch.WordTrace]
  refine ⟨24480620458864334788791359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65281654556971559436776957 24480620458864334788791359)
  ·
    refine ⟨36720930688296502183187039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24480620458864334788791359 36720930688296502183187039)
    ·
      refine ⟨55081396032444753274780559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36720930688296502183187039 55081396032444753274780559)
      ·
        refine ⟨82622094048667129912170839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55081396032444753274780559 82622094048667129912170839)
        ·
          refine ⟨123933141073000694868256259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82622094048667129912170839 123933141073000694868256259)
          ·
            refine ⟨185899711609501042302384389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123933141073000694868256259 185899711609501042302384389)
            ·
              refine ⟨34856195926781445431697073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 185899711609501042302384389 34856195926781445431697073)
              ·
                refine ⟨26142146945086084073772805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34856195926781445431697073 26142146945086084073772805)
                ·
                  refine ⟨4901652552203640763832401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26142146945086084073772805 4901652552203640763832401)
                  ·
                    refine ⟨3676239414152730572874301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4901652552203640763832401 3676239414152730572874301)
                    ·
                      refine ⟨1378589780307273964827863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3676239414152730572874301 1378589780307273964827863)
                      ·
                        rfl

theorem cell23_2684794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 4, 2, 3].length) (baseStart_2684794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2684794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2684794 prefixEnd_2684794 := by exact prefixLift 2684794
  have htrace : WordTrace (prefixWord ++ tailWord_2684794) baseStart_2684794 baseEnd_2684794 := by
    simpa [prefixWord, tailWord_2684794, baseEnd_2684794] using wordTrace_append hprefix tailTrace_2684794
  have hstable : (prefixWord ++ tailWord_2684794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684794).length < 2 ^ (prefixWord ++ tailWord_2684794).sum := by decide
  have hdescent : baseEnd_2684794 < baseStart_2684794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684797 : List Nat := [1, 4, 1, 1, 2, 1, 1, 2, 10]
def baseStart_2684797 : Nat := 118140960795 + 2684797 * 2 ^ 59
def prefixEnd_2684797 : Nat := 4983230072969 + 3 ^ 40 * 2684797 * 2
def baseEnd_2684797 : Nat := 153176813416581939232261

theorem tailTrace_2684797 : CollatzResearch.WordTrace tailWord_2684797 prefixEnd_2684797 153176813416581939232261 := by
  unfold tailWord_2684797
  simp only [CollatzResearch.WordTrace]
  refine ⟨97922591254446470667524645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65281727502964313778349763 97922591254446470667524645)
  ·
    refine ⟨18360485860208713250160871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97922591254446470667524645 18360485860208713250160871)
    ·
      refine ⟨27540728790313069875241307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18360485860208713250160871 27540728790313069875241307)
      ·
        refine ⟨41311093185469604812861961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27540728790313069875241307 41311093185469604812861961)
        ·
          refine ⟨30983319889102203609646471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41311093185469604812861961 30983319889102203609646471)
          ·
            refine ⟨46474979833653305414469707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30983319889102203609646471 46474979833653305414469707)
            ·
              refine ⟨69712469750479958121704561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46474979833653305414469707 69712469750479958121704561)
              ·
                refine ⟨52284352312859968591278421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69712469750479958121704561 52284352312859968591278421)
                ·
                  refine ⟨153176813416581939232261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 52284352312859968591278421 153176813416581939232261)
                  ·
                    rfl

theorem cell23_2684797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 10].length) (baseStart_2684797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2684797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2684797 prefixEnd_2684797 := by exact prefixLift 2684797
  have htrace : WordTrace (prefixWord ++ tailWord_2684797) baseStart_2684797 baseEnd_2684797 := by
    simpa [prefixWord, tailWord_2684797, baseEnd_2684797] using wordTrace_append hprefix tailTrace_2684797
  have hstable : (prefixWord ++ tailWord_2684797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684797).length < 2 ^ (prefixWord ++ tailWord_2684797).sum := by decide
  have hdescent : baseEnd_2684797 < baseStart_2684797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684808 : List Nat := [2, 1, 3, 3, 3, 2, 1, 1, 2, 1, 4]
def baseStart_2684808 : Nat := 118140960795 + 2684808 * 2 ^ 59
def prefixEnd_2684808 : Nat := 4983230072969 + 3 ^ 40 * 2684808 * 2
def baseEnd_2684808 : Nat := 1378596969036436910052799

theorem tailTrace_2684808 : CollatzResearch.WordTrace tailWord_2684808 prefixEnd_2684808 1378596969036436910052799 := by
  unfold tailWord_2684808
  simp only [CollatzResearch.WordTrace]
  refine ⟨48961496228703309773087539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65281994971604413030783385 48961496228703309773087539)
  ·
    refine ⟨73442244343054964659631309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48961496228703309773087539 73442244343054964659631309)
    ·
      refine ⟨27540841628645611747361741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73442244343054964659631309 27540841628645611747361741)
      ·
        refine ⟨10327815610742104405260653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27540841628645611747361741 10327815610742104405260653)
        ·
          refine ⟨3872930854028289151972745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10327815610742104405260653 3872930854028289151972745)
          ·
            refine ⟨2904698140521216863979559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3872930854028289151972745 2904698140521216863979559)
            ·
              refine ⟨4357047210781825295969339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2904698140521216863979559 4357047210781825295969339)
              ·
                refine ⟨6535570816172737943954009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4357047210781825295969339 6535570816172737943954009)
                ·
                  refine ⟨4901678112129553457965507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6535570816172737943954009 4901678112129553457965507)
                  ·
                    refine ⟨7352517168194330186948261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4901678112129553457965507 7352517168194330186948261)
                    ·
                      refine ⟨1378596969036436910052799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7352517168194330186948261 1378596969036436910052799)
                      ·
                        rfl

theorem cell23_2684808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_2684808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2684808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2684808 prefixEnd_2684808 := by exact prefixLift 2684808
  have htrace : WordTrace (prefixWord ++ tailWord_2684808) baseStart_2684808 baseEnd_2684808 := by
    simpa [prefixWord, tailWord_2684808, baseEnd_2684808] using wordTrace_append hprefix tailTrace_2684808
  have hstable : (prefixWord ++ tailWord_2684808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684808).length < 2 ^ (prefixWord ++ tailWord_2684808).sum := by decide
  have hdescent : baseEnd_2684808 < baseStart_2684808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684861 : List Nat := [1, 4, 1, 2, 3, 1, 1, 4, 1, 5]
def baseStart_2684861 : Nat := 118140960795 + 2684861 * 2 ^ 59
def prefixEnd_2684861 : Nat := 4983230072969 + 3 ^ 40 * 2684861 * 2
def baseEnd_2684861 : Nat := 459541394503708400896685

theorem tailTrace_2684861 : CollatzResearch.WordTrace tailWord_2684861 prefixEnd_2684861 459541394503708400896685 := by
  unfold tailWord_2684861
  simp only [CollatzResearch.WordTrace]
  refine ⟨97924925526214609597854437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65283283684143073065236291 97924925526214609597854437)
  ·
    refine ⟨18360923536165239299597707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97924925526214609597854437 18360923536165239299597707)
    ·
      refine ⟨27541385304247858949396561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18360923536165239299597707 27541385304247858949396561)
      ·
        refine ⟨20656038978185894212047421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27541385304247858949396561 20656038978185894212047421)
        ·
          refine ⟨7746014616819710329517783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20656038978185894212047421 7746014616819710329517783)
          ·
            refine ⟨11619021925229565494276675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7746014616819710329517783 11619021925229565494276675)
            ·
              refine ⟨17428532887844348241415013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11619021925229565494276675 17428532887844348241415013)
              ·
                refine ⟨3267849916470815295265315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17428532887844348241415013 3267849916470815295265315)
                ·
                  refine ⟨4901774874706222942897973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3267849916470815295265315 4901774874706222942897973)
                  ·
                    refine ⟨459541394503708400896685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4901774874706222942897973 459541394503708400896685)
                    ·
                      rfl

theorem cell23_2684861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 4, 1, 5].length) (baseStart_2684861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2684861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2684861 prefixEnd_2684861 := by exact prefixLift 2684861
  have htrace : WordTrace (prefixWord ++ tailWord_2684861) baseStart_2684861 baseEnd_2684861 := by
    simpa [prefixWord, tailWord_2684861, baseEnd_2684861] using wordTrace_append hprefix tailTrace_2684861
  have hstable : (prefixWord ++ tailWord_2684861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684861).length < 2 ^ (prefixWord ++ tailWord_2684861).sum := by decide
  have hdescent : baseEnd_2684861 < baseStart_2684861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684874 : List Nat := [3, 1, 2, 1, 2, 1, 2, 4, 1, 6]
def baseStart_2684874 : Nat := 118140960795 + 2684874 * 2 ^ 59
def prefixEnd_2684874 : Nat := 4983230072969 + 3 ^ 40 * 2684874 * 2
def baseEnd_2684874 : Nat := 459543619586544550609165

theorem tailTrace_2684874 : CollatzResearch.WordTrace tailWord_2684874 prefixEnd_2684874 459543619586544550609165 := by
  unfold tailWord_2684874
  simp only [CollatzResearch.WordTrace]
  refine ⟨24481349918791878204519419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65283599783445008545385117 24481349918791878204519419)
  ·
    refine ⟨36722024878187817306779129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24481349918791878204519419 36722024878187817306779129)
    ·
      refine ⟨27541518658640862980084347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36722024878187817306779129 27541518658640862980084347)
      ·
        refine ⟨41312277987961294470126521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27541518658640862980084347 41312277987961294470126521)
        ·
          refine ⟨30984208490970970852594891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41312277987961294470126521 30984208490970970852594891)
          ·
            refine ⟨46476312736456456278892337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30984208490970970852594891 46476312736456456278892337)
            ·
              refine ⟨34857234552342342209169253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46476312736456456278892337 34857234552342342209169253)
              ·
                refine ⟨6535731478564189164219235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34857234552342342209169253 6535731478564189164219235)
                ·
                  refine ⟨9803597217846283746328853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6535731478564189164219235 9803597217846283746328853)
                  ·
                    refine ⟨459543619586544550609165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9803597217846283746328853 459543619586544550609165)
                    ·
                      rfl

theorem cell23_2684874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 1, 6].length) (baseStart_2684874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2684874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2684874 prefixEnd_2684874 := by exact prefixLift 2684874
  have htrace : WordTrace (prefixWord ++ tailWord_2684874) baseStart_2684874 baseEnd_2684874 := by
    simpa [prefixWord, tailWord_2684874, baseEnd_2684874] using wordTrace_append hprefix tailTrace_2684874
  have hstable : (prefixWord ++ tailWord_2684874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684874).length < 2 ^ (prefixWord ++ tailWord_2684874).sum := by decide
  have hdescent : baseEnd_2684874 < baseStart_2684874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684931 : List Nat := [1, 1, 1, 3, 2, 1, 1, 3, 6, 1, 3]
def baseStart_2684931 : Nat := 118140960795 + 2684931 * 2 ^ 59
def prefixEnd_2684931 : Nat := 4983230072969 + 3 ^ 40 * 2684931 * 2
def baseEnd_2684931 : Nat := 1378660127156939928814733

theorem tailTrace_2684931 : CollatzResearch.WordTrace tailWord_2684931 prefixEnd_2684931 1378660127156939928814733 := by
  unfold tailWord_2684931
  simp only [CollatzResearch.WordTrace]
  refine ⟨97927478635961011552902647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65284985757307341035268431 97927478635961011552902647)
  ·
    refine ⟨146891217953941517329353971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97927478635961011552902647 146891217953941517329353971)
    ·
      refine ⟨220336826930912275994030957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146891217953941517329353971 220336826930912275994030957)
      ·
        refine ⟨82626310099092103497761609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 220336826930912275994030957 82626310099092103497761609)
        ·
          refine ⟨61969732574319077623321207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82626310099092103497761609 61969732574319077623321207)
          ·
            refine ⟨92954598861478616434981811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61969732574319077623321207 92954598861478616434981811)
            ·
              refine ⟨139431898292217924652472717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92954598861478616434981811 139431898292217924652472717)
              ·
                refine ⟨52286961859581721744677269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139431898292217924652472717 52286961859581721744677269)
                ·
                  refine ⟨2450951337167893206781747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 52286961859581721744677269 2450951337167893206781747)
                  ·
                    refine ⟨3676427005751839810172621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2450951337167893206781747 3676427005751839810172621)
                    ·
                      refine ⟨1378660127156939928814733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3676427005751839810172621 1378660127156939928814733)
                      ·
                        rfl

theorem cell23_2684931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 6, 1, 3].length) (baseStart_2684931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2684931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2684931 prefixEnd_2684931 := by exact prefixLift 2684931
  have htrace : WordTrace (prefixWord ++ tailWord_2684931) baseStart_2684931 baseEnd_2684931 := by
    simpa [prefixWord, tailWord_2684931, baseEnd_2684931] using wordTrace_append hprefix tailTrace_2684931
  have hstable : (prefixWord ++ tailWord_2684931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684931).length < 2 ^ (prefixWord ++ tailWord_2684931).sum := by decide
  have hdescent : baseEnd_2684931 < baseStart_2684931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684932 : List Nat := [2, 3, 2, 4, 1, 1, 3, 1, 1, 1, 4]
def baseStart_2684932 : Nat := 118140960795 + 2684932 * 2 ^ 59
def prefixEnd_2684932 : Nat := 4983230072969 + 3 ^ 40 * 2684932 * 2
def baseEnd_2684932 : Nat := 1378660640637594424902229

theorem tailTrace_2684932 : CollatzResearch.WordTrace tailWord_2684932 prefixEnd_2684932 1378660640637594424902229 := by
  unfold tailWord_2684932
  simp only [CollatzResearch.WordTrace]
  refine ⟨48963757554478694361844525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65285010072638259149126033 48963757554478694361844525)
  ·
    refine ⟨18361409082929510385691697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48963757554478694361844525 18361409082929510385691697)
    ·
      refine ⟨13771056812197132789268773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18361409082929510385691697 13771056812197132789268773)
      ·
        refine ⟨2582073152286962397987895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13771056812197132789268773 2582073152286962397987895)
        ·
          refine ⟨3873109728430443596981843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2582073152286962397987895 3873109728430443596981843)
          ·
            refine ⟨5809664592645665395472765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3873109728430443596981843 5809664592645665395472765)
            ·
              refine ⟨2178624222242124523302287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5809664592645665395472765 2178624222242124523302287)
              ·
                refine ⟨3267936333363186784953431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2178624222242124523302287 3267936333363186784953431)
                ·
                  refine ⟨4901904500044780177430147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3267936333363186784953431 4901904500044780177430147)
                  ·
                    refine ⟨7352856750067170266145221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4901904500044780177430147 7352856750067170266145221)
                    ·
                      refine ⟨1378660640637594424902229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7352856750067170266145221 1378660640637594424902229)
                      ·
                        rfl

theorem cell23_2684932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_2684932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2684932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2684932 prefixEnd_2684932 := by exact prefixLift 2684932
  have htrace : WordTrace (prefixWord ++ tailWord_2684932) baseStart_2684932 baseEnd_2684932 := by
    simpa [prefixWord, tailWord_2684932, baseEnd_2684932] using wordTrace_append hprefix tailTrace_2684932
  have hstable : (prefixWord ++ tailWord_2684932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684932).length < 2 ^ (prefixWord ++ tailWord_2684932).sum := by decide
  have hdescent : baseEnd_2684932 < baseStart_2684932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684935 : List Nat := [1, 1, 4, 3, 1, 3, 3, 1, 1, 2, 3]
def baseStart_2684935 : Nat := 118140960795 + 2684935 * 2 ^ 59
def prefixEnd_2684935 : Nat := 4983230072969 + 3 ^ 40 * 2684935 * 2
def baseEnd_2684935 : Nat := 1378662181079557913164715

theorem tailTrace_2684935 : CollatzResearch.WordTrace tailWord_2684935 prefixEnd_2684935 1378662181079557913164715 := by
  unfold tailWord_2684935
  simp only [CollatzResearch.WordTrace]
  refine ⟨97927624527946520236048259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65285083018631013490698839 97927624527946520236048259)
  ·
    refine ⟨146891436791919780354072389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97927624527946520236048259 146891436791919780354072389)
    ·
      refine ⟨27542144398484958816388573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146891436791919780354072389 27542144398484958816388573)
      ·
        refine ⟨10328304149431859556145715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27542144398484958816388573 10328304149431859556145715)
        ·
          refine ⟨15492456224147789334218573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10328304149431859556145715 15492456224147789334218573)
          ·
            refine ⟨5809671084055421000331965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15492456224147789334218573 5809671084055421000331965)
            ·
              refine ⟨2178626656520782875124487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5809671084055421000331965 2178626656520782875124487)
              ·
                refine ⟨3267939984781174312686731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2178626656520782875124487 3267939984781174312686731)
                ·
                  refine ⟨4901909977171761469030097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3267939984781174312686731 4901909977171761469030097)
                  ·
                    refine ⟨3676432482878821101772573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4901909977171761469030097 3676432482878821101772573)
                    ·
                      refine ⟨1378662181079557913164715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3676432482878821101772573 1378662181079557913164715)
                      ·
                        rfl

theorem cell23_2684935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_2684935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2684935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2684935 prefixEnd_2684935 := by exact prefixLift 2684935
  have htrace : WordTrace (prefixWord ++ tailWord_2684935) baseStart_2684935 baseEnd_2684935 := by
    simpa [prefixWord, tailWord_2684935, baseEnd_2684935] using wordTrace_append hprefix tailTrace_2684935
  have hstable : (prefixWord ++ tailWord_2684935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684935).length < 2 ^ (prefixWord ++ tailWord_2684935).sum := by decide
  have hdescent : baseEnd_2684935 < baseStart_2684935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684988 : List Nat := [2, 2, 2, 2, 2, 1, 1, 4, 1, 4, 2]
def baseStart_2684988 : Nat := 118140960795 + 2684988 * 2 ^ 59
def prefixEnd_2684988 : Nat := 4983230072969 + 3 ^ 40 * 2684988 * 2
def baseEnd_2684988 : Nat := 1378689395554246205801971

theorem tailTrace_2684988 : CollatzResearch.WordTrace tailWord_2684988 prefixEnd_2684988 1378689395554246205801971 := by
  unfold tailWord_2684988
  simp only [CollatzResearch.WordTrace]
  refine ⟨48964778798377255143863809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65286371731169673525151745 48964778798377255143863809)
  ·
    refine ⟨36723584098782941357897857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48964778798377255143863809 36723584098782941357897857)
    ·
      refine ⟨27542688074087206018423393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36723584098782941357897857 27542688074087206018423393)
      ·
        refine ⟨20657016055565404513817545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27542688074087206018423393 20657016055565404513817545)
        ·
          refine ⟨15492762041674053385363159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20657016055565404513817545 15492762041674053385363159)
          ·
            refine ⟨23239143062511080078044739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15492762041674053385363159 23239143062511080078044739)
            ·
              refine ⟨34858714593766620117067109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23239143062511080078044739 34858714593766620117067109)
              ·
                refine ⟨6536008986331241271950083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34858714593766620117067109 6536008986331241271950083)
                ·
                  refine ⟨9804013479496861907925125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6536008986331241271950083 9804013479496861907925125)
                  ·
                    refine ⟨1838252527405661607735961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9804013479496861907925125 1838252527405661607735961)
                    ·
                      refine ⟨1378689395554246205801971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1838252527405661607735961 1378689395554246205801971)
                      ·
                        rfl

theorem cell23_2684988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 1, 4, 2].length) (baseStart_2684988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2684988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2684988 prefixEnd_2684988 := by exact prefixLift 2684988
  have htrace : WordTrace (prefixWord ++ tailWord_2684988) baseStart_2684988 baseEnd_2684988 := by
    simpa [prefixWord, tailWord_2684988, baseEnd_2684988] using wordTrace_append hprefix tailTrace_2684988
  have hstable : (prefixWord ++ tailWord_2684988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684988).length < 2 ^ (prefixWord ++ tailWord_2684988).sum := by decide
  have hdescent : baseEnd_2684988 < baseStart_2684988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684992 : List Nat := [2, 1, 1, 2, 2, 6, 2, 1, 1, 3, 2]
def baseStart_2684992 : Nat := 118140960795 + 2684992 * 2 ^ 59
def prefixEnd_2684992 : Nat := 4983230072969 + 3 ^ 40 * 2684992 * 2
def baseEnd_2684992 : Nat := 1378691449476864190151953

theorem tailTrace_2684992 : CollatzResearch.WordTrace tailWord_2684992 prefixEnd_2684992 1378691449476864190151953 := by
  unfold tailWord_2684992
  simp only [CollatzResearch.WordTrace]
  refine ⟨48964851744370009485436615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65286468992493345980582153 48964851744370009485436615)
  ·
    refine ⟨73447277616555014228154923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48964851744370009485436615 73447277616555014228154923)
    ·
      refine ⟨110170916424832521342232385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73447277616555014228154923 110170916424832521342232385)
      ·
        refine ⟨82628187318624391006674289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110170916424832521342232385 82628187318624391006674289)
        ·
          refine ⟨61971140488968293255005717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82628187318624391006674289 61971140488968293255005717)
          ·
            refine ⟨2904897210420388746328393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 61971140488968293255005717 2904897210420388746328393)
            ·
              refine ⟨2178672907815291559746295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2904897210420388746328393 2178672907815291559746295)
              ·
                refine ⟨3268009361722937339619443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2178672907815291559746295 3268009361722937339619443)
                ·
                  refine ⟨4902014042584406009429165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3268009361722937339619443 4902014042584406009429165)
                  ·
                    refine ⟨1838255265969152253535937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4902014042584406009429165 1838255265969152253535937)
                    ·
                      refine ⟨1378691449476864190151953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1838255265969152253535937 1378691449476864190151953)
                      ·
                        rfl

theorem cell23_2684992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 1, 1, 3, 2].length) (baseStart_2684992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2684992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2684992 prefixEnd_2684992 := by exact prefixLift 2684992
  have htrace : WordTrace (prefixWord ++ tailWord_2684992) baseStart_2684992 baseEnd_2684992 := by
    simpa [prefixWord, tailWord_2684992, baseEnd_2684992] using wordTrace_append hprefix tailTrace_2684992
  have hstable : (prefixWord ++ tailWord_2684992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684992).length < 2 ^ (prefixWord ++ tailWord_2684992).sum := by decide
  have hdescent : baseEnd_2684992 < baseStart_2684992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2684998 : List Nat := [6, 1, 1, 1, 1, 1, 1, 1, 4, 6]
def baseStart_2684998 : Nat := 118140960795 + 2684998 * 2 ^ 59
def prefixEnd_2684998 : Nat := 4983230072969 + 3 ^ 40 * 2684998 * 2
def baseEnd_2684998 : Nat := 459564843453597055558975

theorem tailTrace_2684998 : CollatzResearch.WordTrace tailWord_2684998 prefixEnd_2684998 459564843453597055558975 := by
  unfold tailWord_2684998
  simp only [CollatzResearch.WordTrace]
  refine ⟨3060310072709946312362239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 65286614884478854663727765 3060310072709946312362239)
  ·
    refine ⟨4590465109064919468543359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3060310072709946312362239 4590465109064919468543359)
    ·
      refine ⟨6885697663597379202815039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4590465109064919468543359 6885697663597379202815039)
      ·
        refine ⟨10328546495396068804222559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6885697663597379202815039 10328546495396068804222559)
        ·
          refine ⟨15492819743094103206333839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10328546495396068804222559 15492819743094103206333839)
          ·
            refine ⟨23239229614641154809500759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15492819743094103206333839 23239229614641154809500759)
            ·
              refine ⟨34858844421961732214251139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23239229614641154809500759 34858844421961732214251139)
              ·
                refine ⟨52288266632942598321376709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34858844421961732214251139 52288266632942598321376709)
                ·
                  refine ⟨9804049993676737185258133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52288266632942598321376709 9804049993676737185258133)
                  ·
                    refine ⟨459564843453597055558975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9804049993676737185258133 459564843453597055558975)
                    ·
                      rfl

theorem cell23_2684998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_2684998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2684998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2684998 prefixEnd_2684998 := by exact prefixLift 2684998
  have htrace : WordTrace (prefixWord ++ tailWord_2684998) baseStart_2684998 baseEnd_2684998 := by
    simpa [prefixWord, tailWord_2684998, baseEnd_2684998] using wordTrace_append hprefix tailTrace_2684998
  have hstable : (prefixWord ++ tailWord_2684998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2684998).length < 2 ^ (prefixWord ++ tailWord_2684998).sum := by decide
  have hdescent : baseEnd_2684998 < baseStart_2684998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2684998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685041 : List Nat := [1, 2, 2, 2, 1, 1, 4, 3, 2, 5]
def baseStart_2685041 : Nat := 118140960795 + 2685041 * 2 ^ 59
def prefixEnd_2685041 : Nat := 4983230072969 + 3 ^ 40 * 2685041 * 2
def baseEnd_2685041 : Nat := 459572203342978166146409

theorem tailTrace_2685041 : CollatzResearch.WordTrace tailWord_2685041 prefixEnd_2685041 459572203342978166146409 := by
  unfold tailWord_2685041
  simp only [CollatzResearch.WordTrace]
  refine ⟨97931490665562500339406977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65287660443708333559604651 97931490665562500339406977)
  ·
    refine ⟨73448617999171875254555233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97931490665562500339406977 73448617999171875254555233)
    ·
      refine ⟨55086463499378906440916425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73448617999171875254555233 55086463499378906440916425)
      ·
        refine ⟨41314847624534179830687319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55086463499378906440916425 41314847624534179830687319)
        ·
          refine ⟨61972271436801269746030979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41314847624534179830687319 61972271436801269746030979)
          ·
            refine ⟨92958407155201904619046469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61972271436801269746030979 92958407155201904619046469)
            ·
              refine ⟨17429701341600357116071213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92958407155201904619046469 17429701341600357116071213)
              ·
                refine ⟨6536138003100133918526705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17429701341600357116071213 6536138003100133918526705)
                ·
                  refine ⟨4902103502325100438895029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6536138003100133918526705 4902103502325100438895029)
                  ·
                    refine ⟨459572203342978166146409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4902103502325100438895029 459572203342978166146409)
                    ·
                      rfl

theorem cell23_2685041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 2, 5].length) (baseStart_2685041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2685041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2685041 prefixEnd_2685041 := by exact prefixLift 2685041
  have htrace : WordTrace (prefixWord ++ tailWord_2685041) baseStart_2685041 baseEnd_2685041 := by
    simpa [prefixWord, tailWord_2685041, baseEnd_2685041] using wordTrace_append hprefix tailTrace_2685041
  have hstable : (prefixWord ++ tailWord_2685041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685041).length < 2 ^ (prefixWord ++ tailWord_2685041).sum := by decide
  have hdescent : baseEnd_2685041 < baseStart_2685041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685081 : List Nat := [1, 2, 1, 2, 1, 2, 1, 3, 3, 4, 3]
def baseStart_2685081 : Nat := 118140960795 + 2685081 * 2 ^ 59
def prefixEnd_2685081 : Nat := 4983230072969 + 3 ^ 40 * 2685081 * 2
def baseEnd_2685081 : Nat := 1378737149255114341939043

theorem tailTrace_2685081 : CollatzResearch.WordTrace tailWord_2685081 prefixEnd_2685081 1378737149255114341939043 := by
  unfold tailWord_2685081
  simp only [CollatzResearch.WordTrace]
  refine ⟨97932949585417587170863097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65288633056945058113908731 97932949585417587170863097)
  ·
    refine ⟨73449712189063190378147323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97932949585417587170863097 73449712189063190378147323)
    ·
      refine ⟨110174568283594785567220985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73449712189063190378147323 110174568283594785567220985)
      ·
        refine ⟨82630926212696089175415739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110174568283594785567220985 82630926212696089175415739)
        ·
          refine ⟨123946389319044133763123609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82630926212696089175415739 123946389319044133763123609)
          ·
            refine ⟨92959791989283100322342707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123946389319044133763123609 92959791989283100322342707)
            ·
              refine ⟨139439687983924650483514061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92959791989283100322342707 139439687983924650483514061)
              ·
                refine ⟨52289882993971743931317773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139439687983924650483514061 52289882993971743931317773)
                ·
                  refine ⟨19608706122739403974244165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52289882993971743931317773 19608706122739403974244165)
                  ·
                    refine ⟨3676632398013638245170781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19608706122739403974244165 3676632398013638245170781)
                    ·
                      refine ⟨1378737149255114341939043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3676632398013638245170781 1378737149255114341939043)
                      ·
                        rfl

theorem cell23_2685081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 4, 3].length) (baseStart_2685081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2685081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2685081 prefixEnd_2685081 := by exact prefixLift 2685081
  have htrace : WordTrace (prefixWord ++ tailWord_2685081) baseStart_2685081 baseEnd_2685081 := by
    simpa [prefixWord, tailWord_2685081, baseEnd_2685081] using wordTrace_append hprefix tailTrace_2685081
  have hstable : (prefixWord ++ tailWord_2685081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685081).length < 2 ^ (prefixWord ++ tailWord_2685081).sum := by decide
  have hdescent : baseEnd_2685081 < baseStart_2685081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685131 : List Nat := [1, 1, 1, 1, 3, 2, 3, 1, 5, 5]
def baseStart_2685131 : Nat := 118140960795 + 2685131 * 2 ^ 59
def prefixEnd_2685131 : Nat := 4983230072969 + 3 ^ 40 * 2685131 * 2
def baseEnd_2685131 : Nat := 459587607762613048771271

theorem tailTrace_2685131 : CollatzResearch.WordTrace tailWord_2685131 prefixEnd_2685131 459587607762613048771271 := by
  unfold tailWord_2685131
  simp only [CollatzResearch.WordTrace]
  refine ⟨97934773235236445710183247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65289848823490963806788831 97934773235236445710183247)
  ·
    refine ⟨146902159852854668565274871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97934773235236445710183247 146902159852854668565274871)
    ·
      refine ⟨220353239779282002847912307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146902159852854668565274871 220353239779282002847912307)
      ·
        refine ⟨330529859668923004271868461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220353239779282002847912307 330529859668923004271868461)
        ·
          refine ⟨123948697375846126601950673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 330529859668923004271868461 123948697375846126601950673)
          ·
            refine ⟨92961523031884594951463005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123948697375846126601950673 92961523031884594951463005)
            ·
              refine ⟨34860571136956723106798627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92961523031884594951463005 34860571136956723106798627)
              ·
                refine ⟨52290856705435084660197941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34860571136956723106798627 52290856705435084660197941)
                ·
                  refine ⟨4902267816134539186893557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52290856705435084660197941 4902267816134539186893557)
                  ·
                    refine ⟨459587607762613048771271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4902267816134539186893557 459587607762613048771271)
                    ·
                      rfl

theorem cell23_2685131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 5, 5].length) (baseStart_2685131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2685131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2685131 prefixEnd_2685131 := by exact prefixLift 2685131
  have htrace : WordTrace (prefixWord ++ tailWord_2685131) baseStart_2685131 baseEnd_2685131 := by
    simpa [prefixWord, tailWord_2685131, baseEnd_2685131] using wordTrace_append hprefix tailTrace_2685131
  have hstable : (prefixWord ++ tailWord_2685131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685131).length < 2 ^ (prefixWord ++ tailWord_2685131).sum := by decide
  have hdescent : baseEnd_2685131 < baseStart_2685131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685168 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 1, 8, 2]
def baseStart_2685168 : Nat := 118140960795 + 2685168 * 2 ^ 59
def prefixEnd_2685168 : Nat := 4983230072969 + 3 ^ 40 * 2685168 * 2
def baseEnd_2685168 : Nat := 1378781822072055501551143

theorem tailTrace_2685168 : CollatzResearch.WordTrace tailWord_2685168 prefixEnd_2685168 1378781822072055501551143 := by
  unfold tailWord_2685168
  simp only [CollatzResearch.WordTrace]
  refine ⟨48968061368051200514640079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65290748490734934019520105 48968061368051200514640079)
  ·
    refine ⟨73452092052076800771960119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48968061368051200514640079 73452092052076800771960119)
    ·
      refine ⟨110178138078115201157940179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73452092052076800771960119 110178138078115201157940179)
      ·
        refine ⟨165267207117172801736910269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110178138078115201157940179 165267207117172801736910269)
        ·
          refine ⟨61975202668939800651341351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165267207117172801736910269 61975202668939800651341351)
          ·
            refine ⟨92962804003409700977012027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61975202668939800651341351 92962804003409700977012027)
            ·
              refine ⟨139444206005114551465518041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92962804003409700977012027 139444206005114551465518041)
              ·
                refine ⟨104583154503835913599138531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139444206005114551465518041 104583154503835913599138531)
                ·
                  refine ⟨156874731755753870398707797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104583154503835913599138531 156874731755753870398707797)
                  ·
                    refine ⟨1838375762762740668734857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 156874731755753870398707797 1838375762762740668734857)
                    ·
                      refine ⟨1378781822072055501551143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1838375762762740668734857 1378781822072055501551143)
                      ·
                        rfl

theorem cell23_2685168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 1, 8, 2].length) (baseStart_2685168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2685168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2685168 prefixEnd_2685168 := by exact prefixLift 2685168
  have htrace : WordTrace (prefixWord ++ tailWord_2685168) baseStart_2685168 baseEnd_2685168 := by
    simpa [prefixWord, tailWord_2685168, baseEnd_2685168] using wordTrace_append hprefix tailTrace_2685168
  have hstable : (prefixWord ++ tailWord_2685168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685168).length < 2 ^ (prefixWord ++ tailWord_2685168).sum := by decide
  have hdescent : baseEnd_2685168 < baseStart_2685168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685198 : List Nat := [4, 1, 1, 2, 1, 2, 3, 1, 1, 1, 6]
def baseStart_2685198 : Nat := 118140960795 + 2685198 * 2 ^ 59
def prefixEnd_2685198 : Nat := 4983230072969 + 3 ^ 40 * 2685198 * 2
def baseEnd_2685198 : Nat := 1378797226491690384176005

theorem tailTrace_2685198 : CollatzResearch.WordTrace tailWord_2685198 prefixEnd_2685198 1378797226491690384176005 := by
  unfold tailWord_2685198
  simp only [CollatzResearch.WordTrace]
  refine ⟨12242152115749214519109031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65291477950662477435248165 12242152115749214519109031)
  ·
    refine ⟨18363228173623821778663547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12242152115749214519109031 18363228173623821778663547)
    ·
      refine ⟨27544842260435732667995321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18363228173623821778663547 27544842260435732667995321)
      ·
        refine ⟨20658631695326799500996491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27544842260435732667995321 20658631695326799500996491)
        ·
          refine ⟨30987947542990199251494737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20658631695326799500996491 30987947542990199251494737)
          ·
            refine ⟨23240960657242649438621053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30987947542990199251494737 23240960657242649438621053)
            ·
              refine ⟨8715360246465993539482895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23240960657242649438621053 8715360246465993539482895)
              ·
                refine ⟨13073040369698990309224343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8715360246465993539482895 13073040369698990309224343)
                ·
                  refine ⟨19609560554548485463836515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13073040369698990309224343 19609560554548485463836515)
                  ·
                    refine ⟨29414340831822728195754773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19609560554548485463836515 29414340831822728195754773)
                    ·
                      refine ⟨1378797226491690384176005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29414340831822728195754773 1378797226491690384176005)
                      ·
                        rfl

theorem cell23_2685198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_2685198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2685198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2685198 prefixEnd_2685198 := by exact prefixLift 2685198
  have htrace : WordTrace (prefixWord ++ tailWord_2685198) baseStart_2685198 baseEnd_2685198 := by
    simpa [prefixWord, tailWord_2685198, baseEnd_2685198] using wordTrace_append hprefix tailTrace_2685198
  have hstable : (prefixWord ++ tailWord_2685198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685198).length < 2 ^ (prefixWord ++ tailWord_2685198).sum := by decide
  have hdescent : baseEnd_2685198 < baseStart_2685198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685205 : List Nat := [1, 3, 2, 1, 2, 1, 3, 4, 1, 2, 3]
def baseStart_2685205 : Nat := 118140960795 + 2685205 * 2 ^ 59
def prefixEnd_2685205 : Nat := 4983230072969 + 3 ^ 40 * 2685205 * 2
def baseEnd_2685205 : Nat := 1378800820856271856788473

theorem tailTrace_2685205 : CollatzResearch.WordTrace tailWord_2685205 prefixEnd_2685205 1378800820856271856788473 := by
  unfold tailWord_2685205
  simp only [CollatzResearch.WordTrace]
  refine ⟨97937472236968356348377069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65291648157978904232251379 97937472236968356348377069)
  ·
    refine ⟨36726552088863133630641401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97937472236968356348377069 36726552088863133630641401)
    ·
      refine ⟨27544914066647350222981051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36726552088863133630641401 27544914066647350222981051)
      ·
        refine ⟨41317371099971025334471577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27544914066647350222981051 41317371099971025334471577)
        ·
          refine ⟨30988028324978269000853683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41317371099971025334471577 30988028324978269000853683)
          ·
            refine ⟨46482042487467403501280525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30988028324978269000853683 46482042487467403501280525)
            ·
              refine ⟨17430765932800276312980197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46482042487467403501280525 17430765932800276312980197)
              ·
                refine ⟨3268268612400051808683787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17430765932800276312980197 3268268612400051808683787)
                ·
                  refine ⟨4902402918600077713025681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3268268612400051808683787 4902402918600077713025681)
                  ·
                    refine ⟨3676802188950058284769261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4902402918600077713025681 3676802188950058284769261)
                    ·
                      refine ⟨1378800820856271856788473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3676802188950058284769261 1378800820856271856788473)
                      ·
                        rfl

theorem cell23_2685205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 4, 1, 2, 3].length) (baseStart_2685205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2685205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2685205 prefixEnd_2685205 := by exact prefixLift 2685205
  have htrace : WordTrace (prefixWord ++ tailWord_2685205) baseStart_2685205 baseEnd_2685205 := by
    simpa [prefixWord, tailWord_2685205, baseEnd_2685205] using wordTrace_append hprefix tailTrace_2685205
  have hstable : (prefixWord ++ tailWord_2685205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685205).length < 2 ^ (prefixWord ++ tailWord_2685205).sum := by decide
  have hdescent : baseEnd_2685205 < baseStart_2685205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685213 : List Nat := [1, 4, 2, 3, 3, 1, 1, 3, 1, 1, 3]
def baseStart_2685213 : Nat := 118140960795 + 2685213 * 2 ^ 59
def prefixEnd_2685213 : Nat := 4983230072969 + 3 ^ 40 * 2685213 * 2
def baseEnd_2685213 : Nat := 1378804928701507825488437

theorem tailTrace_2685213 : CollatzResearch.WordTrace tailWord_2685213 prefixEnd_2685213 1378804928701507825488437 := by
  unfold tailWord_2685213
  simp only [CollatzResearch.WordTrace]
  refine ⟨97937764020939373714668293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65291842680626249143112195 97937764020939373714668293)
  ·
    refine ⟨18363330753926132571500305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97937764020939373714668293 18363330753926132571500305)
    ·
      refine ⟨13772498065444599428625229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18363330753926132571500305 13772498065444599428625229)
      ·
        refine ⟨5164686774541724785734461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13772498065444599428625229 5164686774541724785734461)
        ·
          refine ⟨1936757540453146794650423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5164686774541724785734461 1936757540453146794650423)
          ·
            refine ⟨2905136310679720191975635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1936757540453146794650423 2905136310679720191975635)
            ·
              refine ⟨4357704466019580287963453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2905136310679720191975635 4357704466019580287963453)
              ·
                refine ⟨1634139174757342607986295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4357704466019580287963453 1634139174757342607986295)
                ·
                  refine ⟨2451208762136013911979443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1634139174757342607986295 2451208762136013911979443)
                  ·
                    refine ⟨3676813143204020867969165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2451208762136013911979443 3676813143204020867969165)
                    ·
                      refine ⟨1378804928701507825488437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3676813143204020867969165 1378804928701507825488437)
                      ·
                        rfl

theorem cell23_2685213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_2685213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2685213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2685213 prefixEnd_2685213 := by exact prefixLift 2685213
  have htrace : WordTrace (prefixWord ++ tailWord_2685213) baseStart_2685213 baseEnd_2685213 := by
    simpa [prefixWord, tailWord_2685213, baseEnd_2685213] using wordTrace_append hprefix tailTrace_2685213
  have hstable : (prefixWord ++ tailWord_2685213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685213).length < 2 ^ (prefixWord ++ tailWord_2685213).sum := by decide
  have hdescent : baseEnd_2685213 < baseStart_2685213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685235 : List Nat := [1, 1, 1, 2, 5, 1, 1, 3, 4, 1, 3]
def baseStart_2685235 : Nat := 118140960795 + 2685235 * 2 ^ 59
def prefixEnd_2685235 : Nat := 4983230072969 + 3 ^ 40 * 2685235 * 2
def baseEnd_2685235 : Nat := 1378816225275906739413335

theorem tailTrace_2685235 : CollatzResearch.WordTrace tailWord_2685235 prefixEnd_2685235 1378816225275906739413335 := by
  unfold tailWord_2685235
  simp only [CollatzResearch.WordTrace]
  refine ⟨97938566426859671471969159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65292377617906447647979439 97938566426859671471969159)
  ·
    refine ⟨146907849640289507207953739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97938566426859671471969159 146907849640289507207953739)
    ·
      refine ⟨220361774460434260811930609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146907849640289507207953739 220361774460434260811930609)
      ·
        refine ⟨165271330845325695608947957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220361774460434260811930609 165271330845325695608947957)
        ·
          refine ⟨15494187266749283963338871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 165271330845325695608947957 15494187266749283963338871)
          ·
            refine ⟨23241280900123925945008307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15494187266749283963338871 23241280900123925945008307)
            ·
              refine ⟨34861921350185888917512461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23241280900123925945008307 34861921350185888917512461)
              ·
                refine ⟨13073220506319708344067173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34861921350185888917512461 13073220506319708344067173)
                ·
                  refine ⟨2451228844934945314512595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13073220506319708344067173 2451228844934945314512595)
                  ·
                    refine ⟨3676843267402417971768893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2451228844934945314512595 3676843267402417971768893)
                    ·
                      refine ⟨1378816225275906739413335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3676843267402417971768893 1378816225275906739413335)
                      ·
                        rfl

theorem cell23_2685235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 4, 1, 3].length) (baseStart_2685235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2685235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2685235 prefixEnd_2685235 := by exact prefixLift 2685235
  have htrace : WordTrace (prefixWord ++ tailWord_2685235) baseStart_2685235 baseEnd_2685235 := by
    simpa [prefixWord, tailWord_2685235, baseEnd_2685235] using wordTrace_append hprefix tailTrace_2685235
  have hstable : (prefixWord ++ tailWord_2685235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685235).length < 2 ^ (prefixWord ++ tailWord_2685235).sum := by decide
  have hdescent : baseEnd_2685235 < baseStart_2685235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685236 : List Nat := [2, 5, 1, 1, 1, 4, 1, 1, 3, 2, 2]
def baseStart_2685236 : Nat := 118140960795 + 2685236 * 2 ^ 59
def prefixEnd_2685236 : Nat := 4983230072969 + 3 ^ 40 * 2685236 * 2
def baseEnd_2685236 : Nat := 1378816738756561235500831

theorem tailTrace_2685236 : CollatzResearch.WordTrace tailWord_2685236 prefixEnd_2685236 1378816738756561235500831 := by
  unfold tailWord_2685236
  simp only [CollatzResearch.WordTrace]
  refine ⟨48969301449928024321377781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65292401933237365761837041 48969301449928024321377781)
  ·
    refine ⟨4590872010930752280129167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48969301449928024321377781 4590872010930752280129167)
    ·
      refine ⟨6886308016396128420193751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4590872010930752280129167 6886308016396128420193751)
      ·
        refine ⟨10329462024594192630290627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6886308016396128420193751 10329462024594192630290627)
        ·
          refine ⟨15494193036891288945435941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10329462024594192630290627 15494193036891288945435941)
          ·
            refine ⟨2905161194417116677269239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15494193036891288945435941 2905161194417116677269239)
            ·
              refine ⟨4357741791625675015903859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2905161194417116677269239 4357741791625675015903859)
              ·
                refine ⟨6536612687438512523855789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4357741791625675015903859 6536612687438512523855789)
                ·
                  refine ⟨2451229757789442196445921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6536612687438512523855789 2451229757789442196445921)
                  ·
                    refine ⟨1838422318342081647334441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2451229757789442196445921 1838422318342081647334441)
                    ·
                      refine ⟨1378816738756561235500831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1838422318342081647334441 1378816738756561235500831)
                      ·
                        rfl

theorem cell23_2685236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_2685236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2685236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2685236 prefixEnd_2685236 := by exact prefixLift 2685236
  have htrace : WordTrace (prefixWord ++ tailWord_2685236) baseStart_2685236 baseEnd_2685236 := by
    simpa [prefixWord, tailWord_2685236, baseEnd_2685236] using wordTrace_append hprefix tailTrace_2685236
  have hstable : (prefixWord ++ tailWord_2685236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685236).length < 2 ^ (prefixWord ++ tailWord_2685236).sum := by decide
  have hdescent : baseEnd_2685236 < baseStart_2685236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685262 : List Nat := [4, 1, 1, 1, 1, 1, 2, 6, 1, 3, 2]
def baseStart_2685262 : Nat := 118140960795 + 2685262 * 2 ^ 59
def prefixEnd_2685262 : Nat := 4983230072969 + 3 ^ 40 * 2685262 * 2
def baseEnd_2685262 : Nat := 1378830089253578133775711

theorem tailTrace_2685262 : CollatzResearch.WordTrace tailWord_2685262 prefixEnd_2685262 1378830089253578133775711 := by
  unfold tailWord_2685262
  simp only [CollatzResearch.WordTrace]
  refine ⟨12242443899720231885400255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65293034131841236722134693 12242443899720231885400255)
  ·
    refine ⟨18363665849580347828100383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12242443899720231885400255 18363665849580347828100383)
    ·
      refine ⟨27545498774370521742150575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18363665849580347828100383 27545498774370521742150575)
      ·
        refine ⟨41318248161555782613225863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27545498774370521742150575 41318248161555782613225863)
        ·
          refine ⟨61977372242333673919838795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41318248161555782613225863 61977372242333673919838795)
          ·
            refine ⟨92966058363500510879758193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61977372242333673919838795 92966058363500510879758193)
            ·
              refine ⟨69724543772625383159818645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92966058363500510879758193 69724543772625383159818645)
              ·
                refine ⟨3268337989341814835616499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 69724543772625383159818645 3268337989341814835616499)
                ·
                  refine ⟨4902506984012722253424749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3268337989341814835616499 4902506984012722253424749)
                  ·
                    refine ⟨1838440119004770845034281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4902506984012722253424749 1838440119004770845034281)
                    ·
                      refine ⟨1378830089253578133775711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1838440119004770845034281 1378830089253578133775711)
                      ·
                        rfl

theorem cell23_2685262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 6, 1, 3, 2].length) (baseStart_2685262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2685262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2685262 prefixEnd_2685262 := by exact prefixLift 2685262
  have htrace : WordTrace (prefixWord ++ tailWord_2685262) baseStart_2685262 baseEnd_2685262 := by
    simpa [prefixWord, tailWord_2685262, baseEnd_2685262] using wordTrace_append hprefix tailTrace_2685262
  have hstable : (prefixWord ++ tailWord_2685262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685262).length < 2 ^ (prefixWord ++ tailWord_2685262).sum := by decide
  have hdescent : baseEnd_2685262 < baseStart_2685262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685309 : List Nat := [1, 4, 1, 1, 2, 3, 2, 3, 2, 2, 2]
def baseStart_2685309 : Nat := 118140960795 + 2685309 * 2 ^ 59
def prefixEnd_2685309 : Nat := 4983230072969 + 3 ^ 40 * 2685309 * 2
def baseEnd_2685309 : Nat := 1378854222844339449887995

theorem tailTrace_2685309 : CollatzResearch.WordTrace tailWord_2685309 prefixEnd_2685309 1378854222844339449887995 := by
  unfold tailWord_2685309
  simp only [CollatzResearch.WordTrace]
  refine ⟨97941265428591582110162981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65294176952394388073441987 97941265428591582110162981)
  ·
    refine ⟨18363987267860921645655559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97941265428591582110162981 18363987267860921645655559)
    ·
      refine ⟨27545980901791382468483339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18363987267860921645655559 27545980901791382468483339)
      ·
        refine ⟨41318971352687073702725009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27545980901791382468483339 41318971352687073702725009)
        ·
          refine ⟨30989228514515305277043757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41318971352687073702725009 30989228514515305277043757)
          ·
            refine ⟨11620960692943239478891409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30989228514515305277043757 11620960692943239478891409)
            ·
              refine ⟨8715720519707429609168557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11620960692943239478891409 8715720519707429609168557)
              ·
                refine ⟨3268395194890286103438209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8715720519707429609168557 3268395194890286103438209)
                ·
                  refine ⟨2451296396167714577578657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3268395194890286103438209 2451296396167714577578657)
                  ·
                    refine ⟨1838472297125785933183993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2451296396167714577578657 1838472297125785933183993)
                    ·
                      refine ⟨1378854222844339449887995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1838472297125785933183993 1378854222844339449887995)
                      ·
                        rfl

theorem cell23_2685309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 3, 2, 2, 2].length) (baseStart_2685309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2685309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2685309 prefixEnd_2685309 := by exact prefixLift 2685309
  have htrace : WordTrace (prefixWord ++ tailWord_2685309) baseStart_2685309 baseEnd_2685309 := by
    simpa [prefixWord, tailWord_2685309, baseEnd_2685309] using wordTrace_append hprefix tailTrace_2685309
  have hstable : (prefixWord ++ tailWord_2685309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685309).length < 2 ^ (prefixWord ++ tailWord_2685309).sum := by decide
  have hdescent : baseEnd_2685309 < baseStart_2685309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685315 : List Nat := [1, 1, 1, 3, 6, 1, 1, 2, 7]
def baseStart_2685315 : Nat := 118140960795 + 2685315 * 2 ^ 59
def prefixEnd_2685315 : Nat := 4983230072969 + 3 ^ 40 * 2685315 * 2
def baseEnd_2685315 : Nat := 153206367080918491823663

theorem tailTrace_2685315 : CollatzResearch.WordTrace tailWord_2685315 prefixEnd_2685315 153206367080918491823663 := by
  unfold tailWord_2685315
  simp only [CollatzResearch.WordTrace]
  refine ⟨97941484266569845134881399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65294322844379896756587599 97941484266569845134881399)
  ·
    refine ⟨146912226399854767702322099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97941484266569845134881399 146912226399854767702322099)
    ·
      refine ⟨220368339599782151553483149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146912226399854767702322099 220368339599782151553483149)
      ·
        refine ⟨82638127349918306832556181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 220368339599782151553483149 82638127349918306832556181)
        ·
          refine ⟨3873662219527420632776071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 82638127349918306832556181 3873662219527420632776071)
          ·
            refine ⟨5810493329291130949164107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3873662219527420632776071 5810493329291130949164107)
            ·
              refine ⟨8715739993936696423746161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5810493329291130949164107 8715739993936696423746161)
              ·
                refine ⟨6536804995452522317809621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8715739993936696423746161 6536804995452522317809621)
                ·
                  refine ⟨153206367080918491823663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6536804995452522317809621 153206367080918491823663)
                  ·
                    rfl

theorem cell23_2685315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 7].length) (baseStart_2685315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2685315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2685315 prefixEnd_2685315 := by exact prefixLift 2685315
  have htrace : WordTrace (prefixWord ++ tailWord_2685315) baseStart_2685315 baseEnd_2685315 := by
    simpa [prefixWord, tailWord_2685315, baseEnd_2685315] using wordTrace_append hprefix tailTrace_2685315
  have hstable : (prefixWord ++ tailWord_2685315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685315).length < 2 ^ (prefixWord ++ tailWord_2685315).sum := by decide
  have hdescent : baseEnd_2685315 < baseStart_2685315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685328 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 8, 5]
def baseStart_2685328 : Nat := 118140960795 + 2685328 * 2 ^ 59
def prefixEnd_2685328 : Nat := 4983230072969 + 3 ^ 40 * 2685328 * 2
def baseEnd_2685328 : Nat := 459621326325591625183469

theorem tailTrace_2685328 : CollatzResearch.WordTrace tailWord_2685328 prefixEnd_2685328 459621326325591625183469 := by
  unfold tailWord_2685328
  simp only [CollatzResearch.WordTrace]
  refine ⟨48970979207761374177552319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65294638943681832236736425 48970979207761374177552319)
  ·
    refine ⟨73456468811642061266328479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48970979207761374177552319 73456468811642061266328479)
    ·
      refine ⟨110184703217463091899492719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73456468811642061266328479 110184703217463091899492719)
      ·
        refine ⟨165277054826194637849239079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110184703217463091899492719 165277054826194637849239079)
        ·
          refine ⟨247915582239291956773858619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165277054826194637849239079 247915582239291956773858619)
          ·
            refine ⟨371873373358937935160787929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247915582239291956773858619 371873373358937935160787929)
            ·
              refine ⟨278905030019203451370590947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 371873373358937935160787929 278905030019203451370590947)
              ·
                refine ⟨418357545028805177055886421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 278905030019203451370590947 418357545028805177055886421)
                ·
                  refine ⟨4902627480806310668623669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 418357545028805177055886421 4902627480806310668623669)
                  ·
                    refine ⟨459621326325591625183469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4902627480806310668623669 459621326325591625183469)
                    ·
                      rfl

theorem cell23_2685328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 8, 5].length) (baseStart_2685328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2685328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2685328 prefixEnd_2685328 := by exact prefixLift 2685328
  have htrace : WordTrace (prefixWord ++ tailWord_2685328) baseStart_2685328 baseEnd_2685328 := by
    simpa [prefixWord, tailWord_2685328, baseEnd_2685328] using wordTrace_append hprefix tailTrace_2685328
  have hstable : (prefixWord ++ tailWord_2685328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685328).length < 2 ^ (prefixWord ++ tailWord_2685328).sum := by decide
  have hdescent : baseEnd_2685328 < baseStart_2685328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685385 : List Nat := [1, 2, 1, 1, 2, 1, 6, 1, 1, 4, 3]
def baseStart_2685385 : Nat := 118140960795 + 2685385 * 2 ^ 59
def prefixEnd_2685385 : Nat := 4983230072969 + 3 ^ 40 * 2685385 * 2
def baseEnd_2685385 : Nat := 1378893247374081152537645

theorem tailTrace_2685385 : CollatzResearch.WordTrace tailWord_2685385 prefixEnd_2685385 1378893247374081152537645 := by
  unfold tailWord_2685385
  simp only [CollatzResearch.WordTrace]
  refine ⟨97944037376316247089929609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65296024917544164726619739 97944037376316247089929609)
  ·
    refine ⟨73458028032237185317447207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97944037376316247089929609 73458028032237185317447207)
    ·
      refine ⟨110187042048355777976170811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73458028032237185317447207 110187042048355777976170811)
      ·
        refine ⟨165280563072533666964256217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110187042048355777976170811 165280563072533666964256217)
        ·
          refine ⟨123960422304400250223192163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165280563072533666964256217 123960422304400250223192163)
          ·
            refine ⟨185940633456600375334788245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123960422304400250223192163 185940633456600375334788245)
            ·
              refine ⟨8715967193278142593818199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 185940633456600375334788245 8715967193278142593818199)
              ·
                refine ⟨13073950789917213890727299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8715967193278142593818199 13073950789917213890727299)
                ·
                  refine ⟨19610926184875820836090949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13073950789917213890727299 19610926184875820836090949)
                  ·
                    refine ⟨3677048659664216406767053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19610926184875820836090949 3677048659664216406767053)
                    ·
                      refine ⟨1378893247374081152537645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3677048659664216406767053 1378893247374081152537645)
                      ·
                        rfl

theorem cell23_2685385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 4, 3].length) (baseStart_2685385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2685385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2685385 prefixEnd_2685385 := by exact prefixLift 2685385
  have htrace : WordTrace (prefixWord ++ tailWord_2685385) baseStart_2685385 baseEnd_2685385 := by
    simpa [prefixWord, tailWord_2685385, baseEnd_2685385] using wordTrace_append hprefix tailTrace_2685385
  have hstable : (prefixWord ++ tailWord_2685385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685385).length < 2 ^ (prefixWord ++ tailWord_2685385).sum := by decide
  have hdescent : baseEnd_2685385 < baseStart_2685385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685402 : List Nat := [3, 1, 1, 2, 3, 1, 3, 2, 2, 2, 3]
def baseStart_2685402 : Nat := 118140960795 + 2685402 * 2 ^ 59
def prefixEnd_2685402 : Nat := 4983230072969 + 3 ^ 40 * 2685402 * 2
def baseEnd_2685402 : Nat := 1378901976545207586025067

theorem tailTrace_2685402 : CollatzResearch.WordTrace tailWord_2685402 prefixEnd_2685402 1378901976545207586025067 := by
  unfold tailWord_2685402
  simp only [CollatzResearch.WordTrace]
  refine ⟨24486164354313664748324615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65296438278169772662198973 24486164354313664748324615)
  ·
    refine ⟨36729246531470497122486923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24486164354313664748324615 36729246531470497122486923)
    ·
      refine ⟨55093869797205745683730385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36729246531470497122486923 55093869797205745683730385)
      ·
        refine ⟨41320402347904309262797789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55093869797205745683730385 41320402347904309262797789)
        ·
          refine ⟨15495150880464115973549171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41320402347904309262797789 15495150880464115973549171)
          ·
            refine ⟨23242726320696173960323757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15495150880464115973549171 23242726320696173960323757)
            ·
              refine ⟨8716022370261065235121409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23242726320696173960323757 8716022370261065235121409)
              ·
                refine ⟨6537016777695798926341057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8716022370261065235121409 6537016777695798926341057)
                ·
                  refine ⟨4902762583271849194755793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6537016777695798926341057 4902762583271849194755793)
                  ·
                    refine ⟨3677071937453886896066845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4902762583271849194755793 3677071937453886896066845)
                    ·
                      refine ⟨1378901976545207586025067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3677071937453886896066845 1378901976545207586025067)
                      ·
                        rfl

theorem cell23_2685402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 2, 2, 3].length) (baseStart_2685402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2685402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2685402 prefixEnd_2685402 := by exact prefixLift 2685402
  have htrace : WordTrace (prefixWord ++ tailWord_2685402) baseStart_2685402 baseEnd_2685402 := by
    simpa [prefixWord, tailWord_2685402, baseEnd_2685402] using wordTrace_append hprefix tailTrace_2685402
  have hstable : (prefixWord ++ tailWord_2685402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685402).length < 2 ^ (prefixWord ++ tailWord_2685402).sum := by decide
  have hdescent : baseEnd_2685402 < baseStart_2685402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685405 : List Nat := [1, 4, 3, 1, 1, 1, 1, 3, 8]
def baseStart_2685405 : Nat := 118140960795 + 2685405 * 2 ^ 59
def prefixEnd_2685405 : Nat := 4983230072969 + 3 ^ 40 * 2685405 * 2
def baseEnd_2685405 : Nat := 153211501887463452698617

theorem tailTrace_2685405 : CollatzResearch.WordTrace tailWord_2685405 prefixEnd_2685405 153211501887463452698617 := by
  unfold tailWord_2685405
  simp only [CollatzResearch.WordTrace]
  refine ⟨97944766836243790505657669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65296511224162527003771779 97944766836243790505657669)
  ·
    refine ⟨18364643781795710719810813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97944766836243790505657669 18364643781795710719810813)
    ·
      refine ⟨6886741418173391519929055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18364643781795710719810813 6886741418173391519929055)
      ·
        refine ⟨10330112127260087279893583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6886741418173391519929055 10330112127260087279893583)
        ·
          refine ⟨15495168190890130919840375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10330112127260087279893583 15495168190890130919840375)
          ·
            refine ⟨23242752286335196379760563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15495168190890130919840375 23242752286335196379760563)
            ·
              refine ⟨34864128429502794569640845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23242752286335196379760563 34864128429502794569640845)
              ·
                refine ⟨13074048161063547963615317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34864128429502794569640845 13074048161063547963615317)
                ·
                  refine ⟨153211501887463452698617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13074048161063547963615317 153211501887463452698617)
                  ·
                    rfl

theorem cell23_2685405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 8].length) (baseStart_2685405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2685405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2685405 prefixEnd_2685405 := by exact prefixLift 2685405
  have htrace : WordTrace (prefixWord ++ tailWord_2685405) baseStart_2685405 baseEnd_2685405 := by
    simpa [prefixWord, tailWord_2685405, baseEnd_2685405] using wordTrace_append hprefix tailTrace_2685405
  have hstable : (prefixWord ++ tailWord_2685405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685405).length < 2 ^ (prefixWord ++ tailWord_2685405).sum := by decide
  have hdescent : baseEnd_2685405 < baseStart_2685405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685422 : List Nat := [4, 1, 2, 1, 2, 3, 1, 3, 6]
def baseStart_2685422 : Nat := 118140960795 + 2685422 * 2 ^ 59
def prefixEnd_2685422 : Nat := 4983230072969 + 3 ^ 40 * 2685422 * 2
def baseEnd_2685422 : Nat := 153212471795366389752775

theorem tailTrace_2685422 : CollatzResearch.WordTrace tailWord_2685422 prefixEnd_2685422 153212471795366389752775 := by
  unfold tailWord_2685422
  simp only [CollatzResearch.WordTrace]
  refine ⟨12243173359647775301128315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65296924584788134939351013 12243173359647775301128315)
  ·
    refine ⟨18364760039471662951692473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12243173359647775301128315 18364760039471662951692473)
    ·
      refine ⟨13773570029603747213769355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18364760039471662951692473 13773570029603747213769355)
      ·
        refine ⟨20660355044405620820654033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13773570029603747213769355 20660355044405620820654033)
        ·
          refine ⟨15495266283304215615490525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20660355044405620820654033 15495266283304215615490525)
          ·
            refine ⟨5810724856239080855808947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15495266283304215615490525 5810724856239080855808947)
            ·
              refine ⟨8716087284358621283713421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5810724856239080855808947 8716087284358621283713421)
              ·
                refine ⟨3268532731634482981392533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8716087284358621283713421 3268532731634482981392533)
                ·
                  refine ⟨153212471795366389752775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3268532731634482981392533 153212471795366389752775)
                  ·
                    rfl

theorem cell23_2685422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 3, 6].length) (baseStart_2685422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2685422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2685422 prefixEnd_2685422 := by exact prefixLift 2685422
  have htrace : WordTrace (prefixWord ++ tailWord_2685422) baseStart_2685422 baseEnd_2685422 := by
    simpa [prefixWord, tailWord_2685422, baseEnd_2685422] using wordTrace_append hprefix tailTrace_2685422
  have hstable : (prefixWord ++ tailWord_2685422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685422).length < 2 ^ (prefixWord ++ tailWord_2685422).sum := by decide
  have hdescent : baseEnd_2685422 < baseStart_2685422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685432 : List Nat := [2, 1, 2, 1, 1, 4, 2, 1, 5, 1, 3]
def baseStart_2685432 : Nat := 118140960795 + 2685432 * 2 ^ 59
def prefixEnd_2685432 : Nat := 4983230072969 + 3 ^ 40 * 2685432 * 2
def baseEnd_2685432 : Nat := 1378917380964842468649929

theorem tailTrace_2685432 : CollatzResearch.WordTrace tailWord_2685432 prefixEnd_2685432 1378917380964842468649929 := by
  unfold tailWord_2685432
  simp only [CollatzResearch.WordTrace]
  refine ⟨48972875803572987058445275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65297167738097316077927033 48972875803572987058445275)
  ·
    refine ⟨73459313705359480587667913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48972875803572987058445275 73459313705359480587667913)
    ·
      refine ⟨55094485279019610440750935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73459313705359480587667913 55094485279019610440750935)
      ·
        refine ⟨82641727918529415661126403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55094485279019610440750935 82641727918529415661126403)
        ·
          refine ⟨123962591877794123491689605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82641727918529415661126403 123962591877794123491689605)
          ·
            refine ⟨23242985977086398154691801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123962591877794123491689605 23242985977086398154691801)
            ·
              refine ⟨17432239482814798616018851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23242985977086398154691801 17432239482814798616018851)
              ·
                refine ⟨26148359224222197924028277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17432239482814798616018851 26148359224222197924028277)
                ·
                  refine ⟨2451408677270831055377651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26148359224222197924028277 2451408677270831055377651)
                  ·
                    refine ⟨3677113015906246583066477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2451408677270831055377651 3677113015906246583066477)
                    ·
                      refine ⟨1378917380964842468649929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3677113015906246583066477 1378917380964842468649929)
                      ·
                        rfl

theorem cell23_2685432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 5, 1, 3].length) (baseStart_2685432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2685432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2685432 prefixEnd_2685432 := by exact prefixLift 2685432
  have htrace : WordTrace (prefixWord ++ tailWord_2685432) baseStart_2685432 baseEnd_2685432 := by
    simpa [prefixWord, tailWord_2685432, baseEnd_2685432] using wordTrace_append hprefix tailTrace_2685432
  have hstable : (prefixWord ++ tailWord_2685432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685432).length < 2 ^ (prefixWord ++ tailWord_2685432).sum := by decide
  have hdescent : baseEnd_2685432 < baseStart_2685432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685455 : List Nat := [1, 1, 2, 1, 1, 1, 2, 4, 5, 1, 4]
def baseStart_2685455 : Nat := 118140960795 + 2685455 * 2 ^ 59
def prefixEnd_2685455 : Nat := 4983230072969 + 3 ^ 40 * 2685455 * 2
def baseEnd_2685455 : Nat := 1378929191019895878662323

theorem tailTrace_2685455 : CollatzResearch.WordTrace tailWord_2685455 prefixEnd_2685455 1378929191019895878662323 := by
  unfold tailWord_2685455
  simp only [CollatzResearch.WordTrace]
  refine ⟨97946590486062649044977819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65297726990708432696651879 97946590486062649044977819)
  ·
    refine ⟨146919885729093973567466729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97946590486062649044977819 146919885729093973567466729)
    ·
      refine ⟨110189914296820480175600047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146919885729093973567466729 110189914296820480175600047)
      ·
        refine ⟨165284871445230720263400071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110189914296820480175600047 165284871445230720263400071)
        ·
          refine ⟨247927307167846080395100107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165284871445230720263400071 247927307167846080395100107)
          ·
            refine ⟨371890960751769120592650161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247927307167846080395100107 371890960751769120592650161)
            ·
              refine ⟨278918220563826840444487621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 371890960751769120592650161 278918220563826840444487621)
              ·
                refine ⟨52297166355717532583341429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 278918220563826840444487621 52297166355717532583341429)
                ·
                  refine ⟨4902859345848518679688259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52297166355717532583341429 4902859345848518679688259)
                  ·
                    refine ⟨7354289018772778019532389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4902859345848518679688259 7354289018772778019532389)
                    ·
                      refine ⟨1378929191019895878662323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7354289018772778019532389 1378929191019895878662323)
                      ·
                        rfl

theorem cell23_2685455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 5, 1, 4].length) (baseStart_2685455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2685455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2685455 prefixEnd_2685455 := by exact prefixLift 2685455
  have htrace : WordTrace (prefixWord ++ tailWord_2685455) baseStart_2685455 baseEnd_2685455 := by
    simpa [prefixWord, tailWord_2685455, baseEnd_2685455] using wordTrace_append hprefix tailTrace_2685455
  have hstable : (prefixWord ++ tailWord_2685455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685455).length < 2 ^ (prefixWord ++ tailWord_2685455).sum := by decide
  have hdescent : baseEnd_2685455 < baseStart_2685455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685460 : List Nat := [2, 4, 3, 1, 1, 3, 2, 2, 1, 4]
def baseStart_2685460 : Nat := 118140960795 + 2685460 * 2 ^ 59
def prefixEnd_2685460 : Nat := 4983230072969 + 3 ^ 40 * 2685460 * 2
def baseEnd_2685460 : Nat := 459643919474389453033267

theorem tailTrace_2685460 : CollatzResearch.WordTrace tailWord_2685460 prefixEnd_2685460 459643919474389453033267 := by
  unfold tailWord_2685460
  simp only [CollatzResearch.WordTrace]
  refine ⟨48973386425522267449454917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65297848567363023265939889 48973386425522267449454917)
  ·
    refine ⟨9182509954785425146772797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48973386425522267449454917 9182509954785425146772797)
    ·
      refine ⟨3443441233044534430039799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9182509954785425146772797 3443441233044534430039799)
      ·
        refine ⟨5165161849566801645059699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3443441233044534430039799 5165161849566801645059699)
        ·
          refine ⟨7747742774350202467589549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5165161849566801645059699 7747742774350202467589549)
          ·
            refine ⟨2905403540381325925346081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7747742774350202467589549 2905403540381325925346081)
            ·
              refine ⟨2179052655285994444009561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2905403540381325925346081 2179052655285994444009561)
              ·
                refine ⟨1634289491464495833007171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2179052655285994444009561 1634289491464495833007171)
                ·
                  refine ⟨2451434237196743749510757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1634289491464495833007171 2451434237196743749510757)
                  ·
                    refine ⟨459643919474389453033267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2451434237196743749510757 459643919474389453033267)
                    ·
                      rfl

theorem cell23_2685460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_2685460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2685460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2685460 prefixEnd_2685460 := by exact prefixLift 2685460
  have htrace : WordTrace (prefixWord ++ tailWord_2685460) baseStart_2685460 baseEnd_2685460 := by
    simpa [prefixWord, tailWord_2685460, baseEnd_2685460] using wordTrace_append hprefix tailTrace_2685460
  have hstable : (prefixWord ++ tailWord_2685460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685460).length < 2 ^ (prefixWord ++ tailWord_2685460).sum := by decide
  have hdescent : baseEnd_2685460 < baseStart_2685460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685482 : List Nat := [3, 1, 4, 1, 1, 2, 1, 3, 1, 6]
def baseStart_2685482 : Nat := 118140960795 + 2685482 * 2 ^ 59
def prefixEnd_2685482 : Nat := 4983230072969 + 3 ^ 40 * 2685482 * 2
def baseEnd_2685482 : Nat := 459647684999189091008233

theorem tailTrace_2685482 : CollatzResearch.WordTrace tailWord_2685482 prefixEnd_2685482 459647684999189091008233 := by
  unfold tailWord_2685482
  simp only [CollatzResearch.WordTrace]
  refine ⟨24486893814241208164052675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65298383504643221770807133 24486893814241208164052675)
  ·
    refine ⟨36730340721361812246079013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24486893814241208164052675 36730340721361812246079013)
    ·
      refine ⟨6886938885255339796139815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36730340721361812246079013 6886938885255339796139815)
      ·
        refine ⟨10330408327883009694209723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6886938885255339796139815 10330408327883009694209723)
        ·
          refine ⟨15495612491824514541314585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10330408327883009694209723 15495612491824514541314585)
          ·
            refine ⟨11621709368868385905985939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15495612491824514541314585 11621709368868385905985939)
            ·
              refine ⟨17432564053302578858978909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11621709368868385905985939 17432564053302578858978909)
              ·
                refine ⟨6537211519988467072117091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17432564053302578858978909 6537211519988467072117091)
                ·
                  refine ⟨9805817279982700608175637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6537211519988467072117091 9805817279982700608175637)
                  ·
                    refine ⟨459647684999189091008233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9805817279982700608175637 459647684999189091008233)
                    ·
                      rfl

theorem cell23_2685482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_2685482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2685482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2685482 prefixEnd_2685482 := by exact prefixLift 2685482
  have htrace : WordTrace (prefixWord ++ tailWord_2685482) baseStart_2685482 baseEnd_2685482 := by
    simpa [prefixWord, tailWord_2685482, baseEnd_2685482] using wordTrace_append hprefix tailTrace_2685482
  have hstable : (prefixWord ++ tailWord_2685482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685482).length < 2 ^ (prefixWord ++ tailWord_2685482).sum := by decide
  have hdescent : baseEnd_2685482 < baseStart_2685482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685489 : List Nat := [1, 2, 2, 3, 1, 1, 3, 1, 5, 2, 2]
def baseStart_2685489 : Nat := 118140960795 + 2685489 * 2 ^ 59
def prefixEnd_2685489 : Nat := 4983230072969 + 3 ^ 40 * 2685489 * 2
def baseEnd_2685489 : Nat := 1378946649362148745637167

theorem tailTrace_2685489 : CollatzResearch.WordTrace tailWord_2685489 prefixEnd_2685489 1378946649362148745637167 := by
  unfold tailWord_2685489
  simp only [CollatzResearch.WordTrace]
  refine ⟨97947830567939472851715521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65298553711959648567810347 97947830567939472851715521)
  ·
    refine ⟨73460872925954604638786641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97947830567939472851715521 73460872925954604638786641)
    ·
      refine ⟨55095654694465953479089981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73460872925954604638786641 55095654694465953479089981)
      ·
        refine ⟨20660870510424732554658743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55095654694465953479089981 20660870510424732554658743)
        ·
          refine ⟨30991305765637098831988115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20660870510424732554658743 30991305765637098831988115)
          ·
            refine ⟨46486958648455648247982173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30991305765637098831988115 46486958648455648247982173)
            ·
              refine ⟨17432609493170868092993315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46486958648455648247982173 17432609493170868092993315)
              ·
                refine ⟨26148914239756302139489973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17432609493170868092993315 26148914239756302139489973)
                ·
                  refine ⟨2451460709977153325577185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26148914239756302139489973 2451460709977153325577185)
                  ·
                    refine ⟨1838595532482864994182889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2451460709977153325577185 1838595532482864994182889)
                    ·
                      refine ⟨1378946649362148745637167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1838595532482864994182889 1378946649362148745637167)
                      ·
                        rfl

theorem cell23_2685489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 5, 2, 2].length) (baseStart_2685489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2685489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2685489 prefixEnd_2685489 := by exact prefixLift 2685489
  have htrace : WordTrace (prefixWord ++ tailWord_2685489) baseStart_2685489 baseEnd_2685489 := by
    simpa [prefixWord, tailWord_2685489, baseEnd_2685489] using wordTrace_append hprefix tailTrace_2685489
  have hstable : (prefixWord ++ tailWord_2685489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685489).length < 2 ^ (prefixWord ++ tailWord_2685489).sum := by decide
  have hdescent : baseEnd_2685489 < baseStart_2685489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685509 : List Nat := [1, 3, 1, 1, 1, 6, 1, 3, 1, 2, 3]
def baseStart_2685509 : Nat := 118140960795 + 2685509 * 2 ^ 59
def prefixEnd_2685509 : Nat := 4983230072969 + 3 ^ 40 * 2685509 * 2
def baseEnd_2685509 : Nat := 1378956918975238667387075

theorem tailTrace_2685509 : CollatzResearch.WordTrace tailWord_2685509 prefixEnd_2685509 1378956918975238667387075 := by
  unfold tailWord_2685509
  simp only [CollatzResearch.WordTrace]
  refine ⟨97948560027867016267443581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65299040018578010844962387 97948560027867016267443581)
  ·
    refine ⟨36730710010450131100291343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97948560027867016267443581 36730710010450131100291343)
    ·
      refine ⟨55096065015675196650437015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36730710010450131100291343 55096065015675196650437015)
      ·
        refine ⟨82644097523512794975655523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55096065015675196650437015 82644097523512794975655523)
        ·
          refine ⟨123966146285269192463483285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82644097523512794975655523 123966146285269192463483285)
          ·
            refine ⟨5810913107121993396725779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 123966146285269192463483285 5810913107121993396725779)
            ·
              refine ⟨8716369660682990095088669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5810913107121993396725779 8716369660682990095088669)
              ·
                refine ⟨3268638622756121285658251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8716369660682990095088669 3268638622756121285658251)
                ·
                  refine ⟨4902957934134181928487377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3268638622756121285658251 4902957934134181928487377)
                  ·
                    refine ⟨3677218450600636446365533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4902957934134181928487377 3677218450600636446365533)
                    ·
                      refine ⟨1378956918975238667387075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3677218450600636446365533 1378956918975238667387075)
                      ·
                        rfl

theorem cell23_2685509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 3, 1, 2, 3].length) (baseStart_2685509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2685509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2685509 prefixEnd_2685509 := by exact prefixLift 2685509
  have htrace : WordTrace (prefixWord ++ tailWord_2685509) baseStart_2685509 baseEnd_2685509 := by
    simpa [prefixWord, tailWord_2685509, baseEnd_2685509] using wordTrace_append hprefix tailTrace_2685509
  have hstable : (prefixWord ++ tailWord_2685509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685509).length < 2 ^ (prefixWord ++ tailWord_2685509).sum := by decide
  have hdescent : baseEnd_2685509 < baseStart_2685509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685525 : List Nat := [1, 3, 2, 2, 1, 1, 2, 1, 1, 9]
def baseStart_2685525 : Nat := 118140960795 + 2685525 * 2 ^ 59
def prefixEnd_2685525 : Nat := 4983230072969 + 3 ^ 40 * 2685525 * 2
def baseEnd_2685525 : Nat := 459655044888570201595667

theorem tailTrace_2685525 : CollatzResearch.WordTrace tailWord_2685525 prefixEnd_2685525 459655044888570201595667 := by
  unfold tailWord_2685525
  simp only [CollatzResearch.WordTrace]
  refine ⟨97949143595809051000026029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65299429063872700666684019 97949143595809051000026029)
  ·
    refine ⟨36730928848428394125009761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97949143595809051000026029 36730928848428394125009761)
    ·
      refine ⟨27548196636321295593757321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36730928848428394125009761 27548196636321295593757321)
      ·
        refine ⟨20661147477240971695317991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27548196636321295593757321 20661147477240971695317991)
        ·
          refine ⟨30991721215861457542976987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20661147477240971695317991 30991721215861457542976987)
          ·
            refine ⟨46487581823792186314465481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30991721215861457542976987 46487581823792186314465481)
            ·
              refine ⟨34865686367844139735849111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46487581823792186314465481 34865686367844139735849111)
              ·
                refine ⟨52298529551766209603773667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34865686367844139735849111 52298529551766209603773667)
                ·
                  refine ⟨78447794327649314405660501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52298529551766209603773667 78447794327649314405660501)
                  ·
                    refine ⟨459655044888570201595667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 78447794327649314405660501 459655044888570201595667)
                    ·
                      rfl

theorem cell23_2685525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 9].length) (baseStart_2685525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2685525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2685525 prefixEnd_2685525 := by exact prefixLift 2685525
  have htrace : WordTrace (prefixWord ++ tailWord_2685525) baseStart_2685525 baseEnd_2685525 := by
    simpa [prefixWord, tailWord_2685525, baseEnd_2685525] using wordTrace_append hprefix tailTrace_2685525
  have hstable : (prefixWord ++ tailWord_2685525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685525).length < 2 ^ (prefixWord ++ tailWord_2685525).sum := by decide
  have hdescent : baseEnd_2685525 < baseStart_2685525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685535 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 5]
def baseStart_2685535 : Nat := 118140960795 + 2685535 * 2 ^ 59
def prefixEnd_2685535 : Nat := 4983230072969 + 3 ^ 40 * 2685535 * 2
def baseEnd_2685535 : Nat := 1378970269472255565661955

theorem tailTrace_2685535 : CollatzResearch.WordTrace tailWord_2685535 prefixEnd_2685535 1378970269472255565661955 := by
  unfold tailWord_2685535
  simp only [CollatzResearch.WordTrace]
  refine ⟨97949508325772822707890059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65299672217181881805260039 97949508325772822707890059)
  ·
    refine ⟨146924262488659234061835089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97949508325772822707890059 146924262488659234061835089)
    ·
      refine ⟨110193196866494425546376317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146924262488659234061835089 110193196866494425546376317)
      ·
        refine ⟨41322448824935409579891119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110193196866494425546376317 41322448824935409579891119)
        ·
          refine ⟨61983673237403114369836679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41322448824935409579891119 61983673237403114369836679)
          ·
            refine ⟨92975509856104671554755019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61983673237403114369836679 92975509856104671554755019)
            ·
              refine ⟨139463264784157007332132529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92975509856104671554755019 139463264784157007332132529)
              ·
                refine ⟨104597448588117755499099397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139463264784157007332132529 104597448588117755499099397)
                ·
                  refine ⟨19612021610272079156081137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 104597448588117755499099397 19612021610272079156081137)
                  ·
                    refine ⟨14709016207704059367060853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19612021610272079156081137 14709016207704059367060853)
                    ·
                      refine ⟨1378970269472255565661955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14709016207704059367060853 1378970269472255565661955)
                      ·
                        rfl

theorem cell23_2685535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_2685535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2685535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2685535 prefixEnd_2685535 := by exact prefixLift 2685535
  have htrace : WordTrace (prefixWord ++ tailWord_2685535) baseStart_2685535 baseEnd_2685535 := by
    simpa [prefixWord, tailWord_2685535, baseEnd_2685535] using wordTrace_append hprefix tailTrace_2685535
  have hstable : (prefixWord ++ tailWord_2685535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685535).length < 2 ^ (prefixWord ++ tailWord_2685535).sum := by decide
  have hdescent : baseEnd_2685535 < baseStart_2685535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685555 : List Nat := [1, 1, 1, 2, 2, 1, 1, 4, 4, 6]
def baseStart_2685555 : Nat := 118140960795 + 2685555 * 2 ^ 59
def prefixEnd_2685555 : Nat := 4983230072969 + 3 ^ 40 * 2685555 * 2
def baseEnd_2685555 : Nat := 459660179695115162470621

theorem tailTrace_2685555 : CollatzResearch.WordTrace tailWord_2685555 prefixEnd_2685555 459660179695115162470621 := by
  unfold tailWord_2685555
  simp only [CollatzResearch.WordTrace]
  refine ⟨97950237785700366123618119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65300158523800244082412079 97950237785700366123618119)
  ·
    refine ⟨146925356678550549185427179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97950237785700366123618119 146925356678550549185427179)
    ·
      refine ⟨220388035017825823778140769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146925356678550549185427179 220388035017825823778140769)
      ·
        refine ⟨165291026263369367833605577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220388035017825823778140769 165291026263369367833605577)
        ·
          refine ⟨123968269697527025875204183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165291026263369367833605577 123968269697527025875204183)
          ·
            refine ⟨185952404546290538812806275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123968269697527025875204183 185952404546290538812806275)
            ·
              refine ⟨278928606819435808219209413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185952404546290538812806275 278928606819435808219209413)
              ·
                refine ⟨52299113778644214041101765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 278928606819435808219209413 52299113778644214041101765)
                ·
                  refine ⟨9806083833495790132706581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52299113778644214041101765 9806083833495790132706581)
                  ·
                    refine ⟨459660179695115162470621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9806083833495790132706581 459660179695115162470621)
                    ·
                      rfl

theorem cell23_2685555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 6].length) (baseStart_2685555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2685555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2685555 prefixEnd_2685555 := by exact prefixLift 2685555
  have htrace : WordTrace (prefixWord ++ tailWord_2685555) baseStart_2685555 baseEnd_2685555 := by
    simpa [prefixWord, tailWord_2685555, baseEnd_2685555] using wordTrace_append hprefix tailTrace_2685555
  have hstable : (prefixWord ++ tailWord_2685555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685555).length < 2 ^ (prefixWord ++ tailWord_2685555).sum := by decide
  have hdescent : baseEnd_2685555 < baseStart_2685555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685557 : List Nat := [1, 3, 4, 2, 2, 2, 1, 3, 1, 2, 2]
def baseStart_2685557 : Nat := 118140960795 + 2685557 * 2 ^ 59
def prefixEnd_2685557 : Nat := 4983230072969 + 3 ^ 40 * 2685557 * 2
def baseEnd_2685557 : Nat := 1378981566046654479586855

theorem tailTrace_2685557 : CollatzResearch.WordTrace tailWord_2685557 prefixEnd_2685557 1378981566046654479586855 := by
  unfold tailWord_2685557
  simp only [CollatzResearch.WordTrace]
  refine ⟨97950310731693120465190925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65300207154462080310127283 97950310731693120465190925)
  ·
    refine ⟨36731366524384920174446597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97950310731693120465190925 36731366524384920174446597)
    ·
      refine ⟨6887131223322172532708737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36731366524384920174446597 6887131223322172532708737)
      ·
        refine ⟨5165348417491629399531553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6887131223322172532708737 5165348417491629399531553)
        ·
          refine ⟨3874011313118722049648665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5165348417491629399531553 3874011313118722049648665)
          ·
            refine ⟨2905508484839041537236499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3874011313118722049648665 2905508484839041537236499)
            ·
              refine ⟨4358262727258562305854749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2905508484839041537236499 4358262727258562305854749)
              ·
                refine ⟨1634348522721960864695531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4358262727258562305854749 1634348522721960864695531)
                ·
                  refine ⟨2451522784082941297043297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1634348522721960864695531 2451522784082941297043297)
                  ·
                    refine ⟨1838642088062205972782473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2451522784082941297043297 1838642088062205972782473)
                    ·
                      refine ⟨1378981566046654479586855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1838642088062205972782473 1378981566046654479586855)
                      ·
                        rfl

theorem cell23_2685557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_2685557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2685557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2685557 prefixEnd_2685557 := by exact prefixLift 2685557
  have htrace : WordTrace (prefixWord ++ tailWord_2685557) baseStart_2685557 baseEnd_2685557 := by
    simpa [prefixWord, tailWord_2685557, baseEnd_2685557] using wordTrace_append hprefix tailTrace_2685557
  have hstable : (prefixWord ++ tailWord_2685557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685557).length < 2 ^ (prefixWord ++ tailWord_2685557).sum := by decide
  have hdescent : baseEnd_2685557 < baseStart_2685557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685582 : List Nat := [4, 1, 1, 3, 1, 1, 1, 2, 1, 3, 5]
def baseStart_2685582 : Nat := 118140960795 + 2685582 * 2 ^ 59
def prefixEnd_2685582 : Nat := 4983230072969 + 3 ^ 40 * 2685582 * 2
def baseEnd_2685582 : Nat := 1378994403063016881774239

theorem tailTrace_2685582 : CollatzResearch.WordTrace tailWord_2685582 prefixEnd_2685582 1378994403063016881774239 := by
  unfold tailWord_2685582
  simp only [CollatzResearch.WordTrace]
  refine ⟨12243902819575318716856375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65300815037735033156567333 12243902819575318716856375)
  ·
    refine ⟨18365854229362978075284563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12243902819575318716856375 18365854229362978075284563)
    ·
      refine ⟨27548781344044467112926845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18365854229362978075284563 27548781344044467112926845)
      ·
        refine ⟨10330793004016675167347567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27548781344044467112926845 10330793004016675167347567)
        ·
          refine ⟨15496189506025012751021351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10330793004016675167347567 15496189506025012751021351)
          ·
            refine ⟨23244284259037519126532027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15496189506025012751021351 23244284259037519126532027)
            ·
              refine ⟨34866426388556278689798041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23244284259037519126532027 34866426388556278689798041)
              ·
                refine ⟨26149819791417209017348531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34866426388556278689798041 26149819791417209017348531)
                ·
                  refine ⟨39224729687125813526022797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26149819791417209017348531 39224729687125813526022797)
                  ·
                    refine ⟨14709273632672180072258549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39224729687125813526022797 14709273632672180072258549)
                    ·
                      refine ⟨1378994403063016881774239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14709273632672180072258549 1378994403063016881774239)
                      ·
                        rfl

theorem cell23_2685582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_2685582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2685582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2685582 prefixEnd_2685582 := by exact prefixLift 2685582
  have htrace : WordTrace (prefixWord ++ tailWord_2685582) baseStart_2685582 baseEnd_2685582 := by
    simpa [prefixWord, tailWord_2685582, baseEnd_2685582] using wordTrace_append hprefix tailTrace_2685582
  have hstable : (prefixWord ++ tailWord_2685582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685582).length < 2 ^ (prefixWord ++ tailWord_2685582).sum := by decide
  have hdescent : baseEnd_2685582 < baseStart_2685582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685592 : List Nat := [2, 1, 2, 4, 1, 1, 2, 1, 1, 4, 4]
def baseStart_2685592 : Nat := 118140960795 + 2685592 * 2 ^ 59
def prefixEnd_2685592 : Nat := 4983230072969 + 3 ^ 40 * 2685592 * 2
def baseEnd_2685592 : Nat := 1378999537869561842649193

theorem tailTrace_2685592 : CollatzResearch.WordTrace tailWord_2685592 prefixEnd_2685592 1378999537869561842649193 := by
  unfold tailWord_2685592
  simp only [CollatzResearch.WordTrace]
  refine ⟨48975793643283160721357515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65301058191044214295143353 48975793643283160721357515)
  ·
    refine ⟨73463690464924741082036273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48975793643283160721357515 73463690464924741082036273)
    ·
      refine ⟨55097767848693555811527205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73463690464924741082036273 55097767848693555811527205)
      ·
        refine ⟨10330831471630041714661351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55097767848693555811527205 10330831471630041714661351)
        ·
          refine ⟨15496247207445062571992027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10330831471630041714661351 15496247207445062571992027)
          ·
            refine ⟨23244370811167593857988041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15496247207445062571992027 23244370811167593857988041)
            ·
              refine ⟨17433278108375695393491031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23244370811167593857988041 17433278108375695393491031)
              ·
                refine ⟨26149917162563543090236547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17433278108375695393491031 26149917162563543090236547)
                ·
                  refine ⟨39224875743845314635354821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26149917162563543090236547 39224875743845314635354821)
                  ·
                    refine ⟨7354664201970996494129029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39224875743845314635354821 7354664201970996494129029)
                    ·
                      refine ⟨1378999537869561842649193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7354664201970996494129029 1378999537869561842649193)
                      ·
                        rfl

theorem cell23_2685592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_2685592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2685592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2685592 prefixEnd_2685592 := by exact prefixLift 2685592
  have htrace : WordTrace (prefixWord ++ tailWord_2685592) baseStart_2685592 baseEnd_2685592 := by
    simpa [prefixWord, tailWord_2685592, baseEnd_2685592] using wordTrace_append hprefix tailTrace_2685592
  have hstable : (prefixWord ++ tailWord_2685592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685592).length < 2 ^ (prefixWord ++ tailWord_2685592).sum := by decide
  have hdescent : baseEnd_2685592 < baseStart_2685592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685600 : List Nat := [2, 1, 1, 4, 5, 1, 1, 2, 1, 3, 2]
def baseStart_2685600 : Nat := 118140960795 + 2685600 * 2 ^ 59
def prefixEnd_2685600 : Nat := 4983230072969 + 3 ^ 40 * 2685600 * 2
def baseEnd_2685600 : Nat := 1379003645714797811349157

theorem tailTrace_2685600 : CollatzResearch.WordTrace tailWord_2685600 prefixEnd_2685600 1379003645714797811349157 := by
  unfold tailWord_2685600
  simp only [CollatzResearch.WordTrace]
  refine ⟨48975939535268669404503127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65301252713691559206004169 48975939535268669404503127)
  ·
    refine ⟨73463909302903004106754691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48975939535268669404503127 73463909302903004106754691)
    ·
      refine ⟨110195863954354506160132037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73463909302903004106754691 110195863954354506160132037)
      ·
        refine ⟨20661724491441469905024757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110195863954354506160132037 20661724491441469905024757)
        ·
          refine ⟨1937036671072637803596071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20661724491441469905024757 1937036671072637803596071)
          ·
            refine ⟨2905555006608956705394107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1937036671072637803596071 2905555006608956705394107)
            ·
              refine ⟨4358332509913435058091161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2905555006608956705394107 4358332509913435058091161)
              ·
                refine ⟨3268749382435076293568371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4358332509913435058091161 3268749382435076293568371)
                ·
                  refine ⟨4903124073652614440352557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3268749382435076293568371 4903124073652614440352557)
                  ·
                    refine ⟨1838671527619730415132209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4903124073652614440352557 1838671527619730415132209)
                    ·
                      refine ⟨1379003645714797811349157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1838671527619730415132209 1379003645714797811349157)
                      ·
                        rfl

theorem cell23_2685600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 2, 1, 3, 2].length) (baseStart_2685600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2685600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2685600 prefixEnd_2685600 := by exact prefixLift 2685600
  have htrace : WordTrace (prefixWord ++ tailWord_2685600) baseStart_2685600 baseEnd_2685600 := by
    simpa [prefixWord, tailWord_2685600, baseEnd_2685600] using wordTrace_append hprefix tailTrace_2685600
  have hstable : (prefixWord ++ tailWord_2685600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685600).length < 2 ^ (prefixWord ++ tailWord_2685600).sum := by decide
  have hdescent : baseEnd_2685600 < baseStart_2685600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685636 : List Nat := [2, 3, 3, 1, 1, 3, 1, 4, 5]
def baseStart_2685636 : Nat := 118140960795 + 2685636 * 2 ^ 59
def prefixEnd_2685636 : Nat := 4983230072969 + 3 ^ 40 * 2685636 * 2
def baseEnd_2685636 : Nat := 153224681224262185610999

theorem tailTrace_2685636 : CollatzResearch.WordTrace tailWord_2685636 prefixEnd_2685636 153224681224262185610999 := by
  unfold tailWord_2685636
  simp only [CollatzResearch.WordTrace]
  refine ⟨48976596049203458478658381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65302128065604611304877841 48976596049203458478658381)
  ·
    refine ⟨18366223518451296929496893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48976596049203458478658381 18366223518451296929496893)
    ·
      refine ⟨6887333819419236348561335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18366223518451296929496893 6887333819419236348561335)
      ·
        refine ⟨10331000729128854522842003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6887333819419236348561335 10331000729128854522842003)
        ·
          refine ⟨15496501093693281784263005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10331000729128854522842003 15496501093693281784263005)
          ·
            refine ⟨5811187910134980669098627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15496501093693281784263005 5811187910134980669098627)
            ·
              refine ⟨8716781865202471003647941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5811187910134980669098627 8716781865202471003647941)
              ·
                refine ⟨1634396599725463313183989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8716781865202471003647941 1634396599725463313183989)
                ·
                  refine ⟨153224681224262185610999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1634396599725463313183989 153224681224262185610999)
                  ·
                    rfl

theorem cell23_2685636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 4, 5].length) (baseStart_2685636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2685636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2685636 prefixEnd_2685636 := by exact prefixLift 2685636
  have htrace : WordTrace (prefixWord ++ tailWord_2685636) baseStart_2685636 baseEnd_2685636 := by
    simpa [prefixWord, tailWord_2685636, baseEnd_2685636] using wordTrace_append hprefix tailTrace_2685636
  have hstable : (prefixWord ++ tailWord_2685636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685636).length < 2 ^ (prefixWord ++ tailWord_2685636).sum := by decide
  have hdescent : baseEnd_2685636 < baseStart_2685636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685669 : List Nat := [1, 3, 1, 4, 1, 3, 1, 1, 1, 3, 4]
def baseStart_2685669 : Nat := 118140960795 + 2685669 * 2 ^ 59
def prefixEnd_2685669 : Nat := 4983230072969 + 3 ^ 40 * 2685669 * 2
def baseEnd_2685669 : Nat := 1379039075879958041386339

theorem tailTrace_2685669 : CollatzResearch.WordTrace tailWord_2685669 prefixEnd_2685669 1379039075879958041386339 := by
  unfold tailWord_2685669
  simp only [CollatzResearch.WordTrace]
  refine ⟨97954395707287363593268061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65302930471524909062178707 97954395707287363593268061)
  ·
    refine ⟨36732898390232761347475523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97954395707287363593268061 36732898390232761347475523)
    ·
      refine ⟨55099347585349142021213285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36732898390232761347475523 55099347585349142021213285)
      ·
        refine ⟨10331127672252964128977491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55099347585349142021213285 10331127672252964128977491)
        ·
          refine ⟨15496691508379446193466237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10331127672252964128977491 15496691508379446193466237)
          ·
            refine ⟨5811259315642292322549839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15496691508379446193466237 5811259315642292322549839)
            ·
              refine ⟨8716888973463438483824759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5811259315642292322549839 8716888973463438483824759)
              ·
                refine ⟨13075333460195157725737139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8716888973463438483824759 13075333460195157725737139)
                ·
                  refine ⟨19613000190292736588605709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13075333460195157725737139 19613000190292736588605709)
                  ·
                    refine ⟨7354875071359776220727141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19613000190292736588605709 7354875071359776220727141)
                    ·
                      refine ⟨1379039075879958041386339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7354875071359776220727141 1379039075879958041386339)
                      ·
                        rfl

theorem cell23_2685669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_2685669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2685669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2685669 prefixEnd_2685669 := by exact prefixLift 2685669
  have htrace : WordTrace (prefixWord ++ tailWord_2685669) baseStart_2685669 baseEnd_2685669 := by
    simpa [prefixWord, tailWord_2685669, baseEnd_2685669] using wordTrace_append hprefix tailTrace_2685669
  have hstable : (prefixWord ++ tailWord_2685669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685669).length < 2 ^ (prefixWord ++ tailWord_2685669).sum := by decide
  have hdescent : baseEnd_2685669 < baseStart_2685669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685686 : List Nat := [5, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2]
def baseStart_2685686 : Nat := 118140960795 + 2685686 * 2 ^ 59
def prefixEnd_2685686 : Nat := 4983230072969 + 3 ^ 40 * 2685686 * 2
def baseEnd_2685686 : Nat := 1379047805051084474873761

theorem tailTrace_2685686 : CollatzResearch.WordTrace tailWord_2685686 prefixEnd_2685686 1379047805051084474873761 := by
  unfold tailWord_2685686
  simp only [CollatzResearch.WordTrace]
  refine ⟨6122188484264110968539807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65303343832150516997757941 6122188484264110968539807)
  ·
    refine ⟨9183282726396166452809711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6122188484264110968539807 9183282726396166452809711)
    ·
      refine ⟨13774924089594249679214567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9183282726396166452809711 13774924089594249679214567)
      ·
        refine ⟨20662386134391374518821851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13774924089594249679214567 20662386134391374518821851)
        ·
          refine ⟨30993579201587061778232777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20662386134391374518821851 30993579201587061778232777)
          ·
            refine ⟨23245184401190296333674583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30993579201587061778232777 23245184401190296333674583)
            ·
              refine ⟨34867776601785444500511875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23245184401190296333674583 34867776601785444500511875)
              ·
                refine ⟨52301664902678166750767813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34867776601785444500511875 52301664902678166750767813)
                ·
                  refine ⟨9806562169252156265768965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52301664902678166750767813 9806562169252156265768965)
                  ·
                    refine ⟨1838730406734779299831681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9806562169252156265768965 1838730406734779299831681)
                    ·
                      refine ⟨1379047805051084474873761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1838730406734779299831681 1379047805051084474873761)
                      ·
                        rfl

theorem cell23_2685686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2].length) (baseStart_2685686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2685686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2685686 prefixEnd_2685686 := by exact prefixLift 2685686
  have htrace : WordTrace (prefixWord ++ tailWord_2685686) baseStart_2685686 baseEnd_2685686 := by
    simpa [prefixWord, tailWord_2685686, baseEnd_2685686] using wordTrace_append hprefix tailTrace_2685686
  have hstable : (prefixWord ++ tailWord_2685686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685686).length < 2 ^ (prefixWord ++ tailWord_2685686).sum := by decide
  have hdescent : baseEnd_2685686 < baseStart_2685686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685689 : List Nat := [1, 2, 1, 3, 1, 1, 1, 6, 2, 2, 3]
def baseStart_2685689 : Nat := 118140960795 + 2685689 * 2 ^ 59
def prefixEnd_2685689 : Nat := 4983230072969 + 3 ^ 40 * 2685689 * 2
def baseEnd_2685689 : Nat := 1379049345493047963136247

theorem tailTrace_2685689 : CollatzResearch.WordTrace tailWord_2685689 prefixEnd_2685689 1379049345493047963136247 := by
  unfold tailWord_2685689
  simp only [CollatzResearch.WordTrace]
  refine ⟨97955125167214907008996121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65303416778143271339330747 97955125167214907008996121)
  ·
    refine ⟨73466343875411180256747091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97955125167214907008996121 73466343875411180256747091)
    ·
      refine ⟨110199515813116770385120637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73466343875411180256747091 110199515813116770385120637)
      ·
        refine ⟨41324818429918788894420239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110199515813116770385120637 41324818429918788894420239)
        ·
          refine ⟨61987227644878183341630359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41324818429918788894420239 61987227644878183341630359)
          ·
            refine ⟨92980841467317275012445539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61987227644878183341630359 92980841467317275012445539)
            ·
              refine ⟨139471262200975912518668309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92980841467317275012445539 139471262200975912518668309)
              ·
                refine ⟨6537715415670745899312577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 139471262200975912518668309 6537715415670745899312577)
                ·
                  refine ⟨4903286561753059424484433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6537715415670745899312577 4903286561753059424484433)
                  ·
                    refine ⟨3677464921314794568363325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4903286561753059424484433 3677464921314794568363325)
                    ·
                      refine ⟨1379049345493047963136247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3677464921314794568363325 1379049345493047963136247)
                      ·
                        rfl

theorem cell23_2685689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 2, 2, 3].length) (baseStart_2685689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2685689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2685689 prefixEnd_2685689 := by exact prefixLift 2685689
  have htrace : WordTrace (prefixWord ++ tailWord_2685689) baseStart_2685689 baseEnd_2685689 := by
    simpa [prefixWord, tailWord_2685689, baseEnd_2685689] using wordTrace_append hprefix tailTrace_2685689
  have hstable : (prefixWord ++ tailWord_2685689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685689).length < 2 ^ (prefixWord ++ tailWord_2685689).sum := by decide
  have hdescent : baseEnd_2685689 < baseStart_2685689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685730 : List Nat := [3, 3, 1, 1, 2, 4, 1, 3, 1, 4]
def baseStart_2685730 : Nat := 118140960795 + 2685730 * 2 ^ 59
def prefixEnd_2685730 : Nat := 4983230072969 + 3 ^ 40 * 2685730 * 2
def baseEnd_2685730 : Nat := 459690132733294100907853

theorem tailTrace_2685730 : CollatzResearch.WordTrace tailWord_2685730 prefixEnd_2685730 459690132733294100907853 := by
  unfold tailWord_2685730
  simp only [CollatzResearch.WordTrace]
  refine ⟨24489155140016592752809661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65304413706710914007492429 24489155140016592752809661)
  ·
    refine ⟨9183433177506222282303623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24489155140016592752809661 9183433177506222282303623)
    ·
      refine ⟨13775149766259333423455435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9183433177506222282303623 13775149766259333423455435)
      ·
        refine ⟨20662724649389000135183153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13775149766259333423455435 20662724649389000135183153)
        ·
          refine ⟨15497043487041750101387365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20662724649389000135183153 15497043487041750101387365)
          ·
            refine ⟨2905695653820328144010131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15497043487041750101387365 2905695653820328144010131)
            ·
              refine ⟨4358543480730492216015197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2905695653820328144010131 4358543480730492216015197)
              ·
                refine ⟨1634453805273934581005699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4358543480730492216015197 1634453805273934581005699)
                ·
                  refine ⟨2451680707910901871508549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1634453805273934581005699 2451680707910901871508549)
                  ·
                    refine ⟨459690132733294100907853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2451680707910901871508549 459690132733294100907853)
                    ·
                      rfl

theorem cell23_2685730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_2685730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2685730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2685730 prefixEnd_2685730 := by exact prefixLift 2685730
  have htrace : WordTrace (prefixWord ++ tailWord_2685730) baseStart_2685730 baseEnd_2685730 := by
    simpa [prefixWord, tailWord_2685730, baseEnd_2685730] using wordTrace_append hprefix tailTrace_2685730
  have hstable : (prefixWord ++ tailWord_2685730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685730).length < 2 ^ (prefixWord ++ tailWord_2685730).sum := by decide
  have hdescent : baseEnd_2685730 < baseStart_2685730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685773 : List Nat := [1, 6, 1, 2, 2, 1, 1, 1, 3, 5]
def baseStart_2685773 : Nat := 118140960795 + 2685773 * 2 ^ 59
def prefixEnd_2685773 : Nat := 4983230072969 + 3 ^ 40 * 2685773 * 2
def baseEnd_2685773 : Nat := 459697492622675211495287

theorem tailTrace_2685773 : CollatzResearch.WordTrace tailWord_2685773 prefixEnd_2685773 459697492622675211495287 := by
  unfold tailWord_2685773
  simp only [CollatzResearch.WordTrace]
  refine ⟨97958188898910589355053973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65305459265940392903369315 97958188898910589355053973)
  ·
    refine ⟨4591790104636433876018155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 97958188898910589355053973 4591790104636433876018155)
    ·
      refine ⟨6887685156954650814027233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4591790104636433876018155 6887685156954650814027233)
      ·
        refine ⟨5165763867715988110520425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6887685156954650814027233 5165763867715988110520425)
        ·
          refine ⟨3874322900786991082890319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5165763867715988110520425 3874322900786991082890319)
          ·
            refine ⟨5811484351180486624335479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3874322900786991082890319 5811484351180486624335479)
            ·
              refine ⟨8717226526770729936503219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5811484351180486624335479 8717226526770729936503219)
              ·
                refine ⟨13075839790156094904754829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8717226526770729936503219 13075839790156094904754829)
                ·
                  refine ⟨4903439921308535589283061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13075839790156094904754829 4903439921308535589283061)
                  ·
                    refine ⟨459697492622675211495287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4903439921308535589283061 459697492622675211495287)
                    ·
                      rfl

theorem cell23_2685773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_2685773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2685773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2685773 prefixEnd_2685773 := by exact prefixLift 2685773
  have htrace : WordTrace (prefixWord ++ tailWord_2685773) baseStart_2685773 baseEnd_2685773 := by
    simpa [prefixWord, tailWord_2685773, baseEnd_2685773] using wordTrace_append hprefix tailTrace_2685773
  have hstable : (prefixWord ++ tailWord_2685773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685773).length < 2 ^ (prefixWord ++ tailWord_2685773).sum := by decide
  have hdescent : baseEnd_2685773 < baseStart_2685773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685776 : List Nat := [2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 4]
def baseStart_2685776 : Nat := 118140960795 + 2685776 * 2 ^ 59
def prefixEnd_2685776 : Nat := 4983230072969 + 3 ^ 40 * 2685776 * 2
def baseEnd_2685776 : Nat := 1379094018309989122748347

theorem tailTrace_2685776 : CollatzResearch.WordTrace tailWord_2685776 prefixEnd_2685776 1379094018309989122748347 := by
  unfold tailWord_2685776
  simp only [CollatzResearch.WordTrace]
  refine ⟨48979149158949860433706591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65305532211933147244942121 48979149158949860433706591)
  ·
    refine ⟨73468723738424790650559887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48979149158949860433706591 73468723738424790650559887)
    ·
      refine ⟨110203085607637185975839831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73468723738424790650559887 110203085607637185975839831)
      ·
        refine ⟨165304628411455778963759747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110203085607637185975839831 165304628411455778963759747)
        ·
          refine ⟨247956942617183668445639621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165304628411455778963759747 247956942617183668445639621)
          ·
            refine ⟨46491926740721937833557429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 247956942617183668445639621 46491926740721937833557429)
            ·
              refine ⟨4358618131942681671896009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46491926740721937833557429 4358618131942681671896009)
              ·
                refine ⟨3268963598957011253922007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4358618131942681671896009 3268963598957011253922007)
                ·
                  refine ⟨4903445398435516880883011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3268963598957011253922007 4903445398435516880883011)
                  ·
                    refine ⟨7355168097653275321324517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4903445398435516880883011 7355168097653275321324517)
                    ·
                      refine ⟨1379094018309989122748347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7355168097653275321324517 1379094018309989122748347)
                      ·
                        rfl

theorem cell23_2685776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 4].length) (baseStart_2685776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2685776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2685776 prefixEnd_2685776 := by exact prefixLift 2685776
  have htrace : WordTrace (prefixWord ++ tailWord_2685776) baseStart_2685776 baseEnd_2685776 := by
    simpa [prefixWord, tailWord_2685776, baseEnd_2685776] using wordTrace_append hprefix tailTrace_2685776
  have hstable : (prefixWord ++ tailWord_2685776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685776).length < 2 ^ (prefixWord ++ tailWord_2685776).sum := by decide
  have hdescent : baseEnd_2685776 < baseStart_2685776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685780 : List Nat := [2, 4, 1, 1, 4, 1, 2, 1, 2, 3, 2]
def baseStart_2685780 : Nat := 118140960795 + 2685780 * 2 ^ 59
def prefixEnd_2685780 : Nat := 4983230072969 + 3 ^ 40 * 2685780 * 2
def baseEnd_2685780 : Nat := 1379096072232607107098329

theorem tailTrace_2685780 : CollatzResearch.WordTrace tailWord_2685780 prefixEnd_2685780 1379096072232607107098329 := by
  unfold tailWord_2685780
  simp only [CollatzResearch.WordTrace]
  refine ⟨48979222104942614775279397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65305629473256819700372529 48979222104942614775279397)
  ·
    refine ⟨9183604144676740270364887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48979222104942614775279397 9183604144676740270364887)
    ·
      refine ⟨13775406217015110405547331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9183604144676740270364887 13775406217015110405547331)
      ·
        refine ⟨20663109325522665608320997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13775406217015110405547331 20663109325522665608320997)
        ·
          refine ⟨3874332998535499801560187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20663109325522665608320997 3874332998535499801560187)
          ·
            refine ⟨5811499497803249702340281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3874332998535499801560187 5811499497803249702340281)
            ·
              refine ⟨4358624623352437276755211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5811499497803249702340281 4358624623352437276755211)
              ·
                refine ⟨6537936935028655915132817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4358624623352437276755211 6537936935028655915132817)
                ·
                  refine ⟨4903452701271491936349613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6537936935028655915132817 4903452701271491936349613)
                  ·
                    refine ⟨1838794762976809476131105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4903452701271491936349613 1838794762976809476131105)
                    ·
                      refine ⟨1379096072232607107098329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1838794762976809476131105 1379096072232607107098329)
                      ·
                        rfl

theorem cell23_2685780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 2, 3, 2].length) (baseStart_2685780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2685780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2685780 prefixEnd_2685780 := by exact prefixLift 2685780
  have htrace : WordTrace (prefixWord ++ tailWord_2685780) baseStart_2685780 baseEnd_2685780 := by
    simpa [prefixWord, tailWord_2685780, baseEnd_2685780] using wordTrace_append hprefix tailTrace_2685780
  have hstable : (prefixWord ++ tailWord_2685780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685780).length < 2 ^ (prefixWord ++ tailWord_2685780).sum := by decide
  have hdescent : baseEnd_2685780 < baseStart_2685780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685796 : List Nat := [2, 3, 1, 1, 4, 1, 3, 1, 1, 1, 5]
def baseStart_2685796 : Nat := 118140960795 + 2685796 * 2 ^ 59
def prefixEnd_2685796 : Nat := 4983230072969 + 3 ^ 40 * 2685796 * 2
def baseEnd_2685796 : Nat := 1379104287923079044498255

theorem tailTrace_2685796 : CollatzResearch.WordTrace tailWord_2685796 prefixEnd_2685796 1379104287923079044498255 := by
  unfold tailWord_2685796
  simp only [CollatzResearch.WordTrace]
  refine ⟨48979513888913632141570621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65306018518551509522094161 48979513888913632141570621)
  ·
    refine ⟨18367317708342612053088983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48979513888913632141570621 18367317708342612053088983)
    ·
      refine ⟨27550976562513918079633475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18367317708342612053088983 27550976562513918079633475)
      ·
        refine ⟨41326464843770877119450213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27550976562513918079633475 41326464843770877119450213)
        ·
          refine ⟨7748712158207039459896915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41326464843770877119450213 7748712158207039459896915)
          ·
            refine ⟨11623068237310559189845373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7748712158207039459896915 11623068237310559189845373)
            ·
              refine ⟨4358650588991459696192015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11623068237310559189845373 4358650588991459696192015)
              ·
                refine ⟨6537975883487189544288023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4358650588991459696192015 6537975883487189544288023)
                ·
                  refine ⟨9806963825230784316432035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6537975883487189544288023 9806963825230784316432035)
                  ·
                    refine ⟨14710445737846176474648053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9806963825230784316432035 14710445737846176474648053)
                    ·
                      refine ⟨1379104287923079044498255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14710445737846176474648053 1379104287923079044498255)
                      ·
                        rfl

theorem cell23_2685796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 1, 1, 5].length) (baseStart_2685796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2685796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2685796 prefixEnd_2685796 := by exact prefixLift 2685796
  have htrace : WordTrace (prefixWord ++ tailWord_2685796) baseStart_2685796 baseEnd_2685796 := by
    simpa [prefixWord, tailWord_2685796, baseEnd_2685796] using wordTrace_append hprefix tailTrace_2685796
  have hstable : (prefixWord ++ tailWord_2685796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685796).length < 2 ^ (prefixWord ++ tailWord_2685796).sum := by decide
  have hdescent : baseEnd_2685796 < baseStart_2685796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685859 : List Nat := [1, 1, 1, 4, 1, 2, 3, 2, 2, 6]
def baseStart_2685859 : Nat := 118140960795 + 2685859 * 2 ^ 59
def prefixEnd_2685859 : Nat := 4983230072969 + 3 ^ 40 * 2685859 * 2
def baseEnd_2685859 : Nat := 459712212401437432670155

theorem tailTrace_2685859 : CollatzResearch.WordTrace tailWord_2685859 prefixEnd_2685859 459712212401437432670155 := by
  unfold tailWord_2685859
  simp only [CollatzResearch.WordTrace]
  refine ⟨97961325576599026042684631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65307550384399350695123087 97961325576599026042684631)
  ·
    refine ⟨146941988364898539064026947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97961325576599026042684631 146941988364898539064026947)
    ·
      refine ⟨220412982547347808596040421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146941988364898539064026947 220412982547347808596040421)
      ·
        refine ⟨41327434227627714111757579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 220412982547347808596040421 41327434227627714111757579)
        ·
          refine ⟨61991151341441571167636369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41327434227627714111757579 61991151341441571167636369)
          ·
            refine ⟨46493363506081178375727277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61991151341441571167636369 46493363506081178375727277)
            ·
              refine ⟨17435011314780441890897729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46493363506081178375727277 17435011314780441890897729)
              ·
                refine ⟨13076258486085331418173297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17435011314780441890897729 13076258486085331418173297)
                ·
                  refine ⟨9807193864563998563629973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13076258486085331418173297 9807193864563998563629973)
                  ·
                    refine ⟨459712212401437432670155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9807193864563998563629973 459712212401437432670155)
                    ·
                      rfl

theorem cell23_2685859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 6].length) (baseStart_2685859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2685859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2685859 prefixEnd_2685859 := by exact prefixLift 2685859
  have htrace : WordTrace (prefixWord ++ tailWord_2685859) baseStart_2685859 baseEnd_2685859 := by
    simpa [prefixWord, tailWord_2685859, baseEnd_2685859] using wordTrace_append hprefix tailTrace_2685859
  have hstable : (prefixWord ++ tailWord_2685859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685859).length < 2 ^ (prefixWord ++ tailWord_2685859).sum := by decide
  have hdescent : baseEnd_2685859 < baseStart_2685859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685886 : List Nat := [4, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5]
def baseStart_2685886 : Nat := 118140960795 + 2685886 * 2 ^ 59
def prefixEnd_2685886 : Nat := 4983230072969 + 3 ^ 40 * 2685886 * 2
def baseEnd_2685886 : Nat := 1379150501181983692372841

theorem tailTrace_2685886 : CollatzResearch.WordTrace tailWord_2685886 prefixEnd_2685886 1379150501181983692372841 := by
  unfold tailWord_2685886
  simp only [CollatzResearch.WordTrace]
  refine ⟨12245288793437651206739689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65308206898334139769278341 12245288793437651206739689)
  ·
    refine ⟨9183966595078238405054767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12245288793437651206739689 9183966595078238405054767)
    ·
      refine ⟨13775949892617357607582151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9183966595078238405054767 13775949892617357607582151)
      ·
        refine ⟨20663924838926036411373227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13775949892617357607582151 20663924838926036411373227)
        ·
          refine ⟨30995887258389054617059841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20663924838926036411373227 30995887258389054617059841)
          ·
            refine ⟨23246915443791790962794881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30995887258389054617059841 23246915443791790962794881)
            ·
              refine ⟨17435186582843843222096161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23246915443791790962794881 17435186582843843222096161)
              ·
                refine ⟨13076389937132882416572121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17435186582843843222096161 13076389937132882416572121)
                ·
                  refine ⟨9807292452849661812429091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13076389937132882416572121 9807292452849661812429091)
                  ·
                    refine ⟨14710938679274492718643637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9807292452849661812429091 14710938679274492718643637)
                    ·
                      refine ⟨1379150501181983692372841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14710938679274492718643637 1379150501181983692372841)
                      ·
                        rfl

theorem cell23_2685886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_2685886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2685886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2685886 prefixEnd_2685886 := by exact prefixLift 2685886
  have htrace : WordTrace (prefixWord ++ tailWord_2685886) baseStart_2685886 baseEnd_2685886 := by
    simpa [prefixWord, tailWord_2685886, baseEnd_2685886] using wordTrace_append hprefix tailTrace_2685886
  have hstable : (prefixWord ++ tailWord_2685886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685886).length < 2 ^ (prefixWord ++ tailWord_2685886).sum := by decide
  have hdescent : baseEnd_2685886 < baseStart_2685886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685953 : List Nat := [1, 2, 4, 1, 2, 3, 2, 1, 2, 5]
def baseStart_2685953 : Nat := 118140960795 + 2685953 * 2 ^ 59
def prefixEnd_2685953 : Nat := 4983230072969 + 3 ^ 40 * 2685953 * 2
def baseEnd_2685953 : Nat := 459728301461944976745011

theorem tailTrace_2685953 : CollatzResearch.WordTrace tailWord_2685953 prefixEnd_2685953 459728301461944976745011 := by
  unfold tailWord_2685953
  simp only [CollatzResearch.WordTrace]
  refine ⟨97964754038258480096606513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65309836025505653397737675 97964754038258480096606513)
  ·
    refine ⟨73473565528693860072454885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97964754038258480096606513 73473565528693860072454885)
    ·
      refine ⟨13776293536630098763585291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73473565528693860072454885 13776293536630098763585291)
      ·
        refine ⟨20664440304945148145377937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13776293536630098763585291 20664440304945148145377937)
        ·
          refine ⟨15498330228708861109033453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20664440304945148145377937 15498330228708861109033453)
          ·
            refine ⟨5811873835765822915887545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15498330228708861109033453 5811873835765822915887545)
            ·
              refine ⟨4358905376824367186915659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5811873835765822915887545 4358905376824367186915659)
              ·
                refine ⟨6538358065236550780373489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4358905376824367186915659 6538358065236550780373489)
                ·
                  refine ⟨4903768548927413085280117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6538358065236550780373489 4903768548927413085280117)
                  ·
                    refine ⟨459728301461944976745011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4903768548927413085280117 459728301461944976745011)
                    ·
                      rfl

theorem cell23_2685953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_2685953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2685953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2685953 prefixEnd_2685953 := by exact prefixLift 2685953
  have htrace : WordTrace (prefixWord ++ tailWord_2685953) baseStart_2685953 baseEnd_2685953 := by
    simpa [prefixWord, tailWord_2685953, baseEnd_2685953] using wordTrace_append hprefix tailTrace_2685953
  have hstable : (prefixWord ++ tailWord_2685953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685953).length < 2 ^ (prefixWord ++ tailWord_2685953).sum := by decide
  have hdescent : baseEnd_2685953 < baseStart_2685953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685973 : List Nat := [1, 3, 2, 1, 4, 1, 2, 2, 2, 1, 4]
def baseStart_2685973 : Nat := 118140960795 + 2685973 * 2 ^ 59
def prefixEnd_2685973 : Nat := 4983230072969 + 3 ^ 40 * 2685973 * 2
def baseEnd_2685973 : Nat := 1379195173998924851984941

theorem tailTrace_2685973 : CollatzResearch.WordTrace tailWord_2685973 prefixEnd_2685973 1379195173998924851984941 := by
  unfold tailWord_2685973
  simp only [CollatzResearch.WordTrace]
  refine ⟨97965483498186023512334573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65310322332124015674889715 97965483498186023512334573)
  ·
    refine ⟨36737056311819758817125465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97965483498186023512334573 36737056311819758817125465)
    ·
      refine ⟨27552792233864819112844099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36737056311819758817125465 27552792233864819112844099)
      ·
        refine ⟨41329188350797228669266149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27552792233864819112844099 41329188350797228669266149)
        ·
          refine ⟨7749222815774480375487403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41329188350797228669266149 7749222815774480375487403)
          ·
            refine ⟨11623834223661720563231105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7749222815774480375487403 11623834223661720563231105)
            ·
              refine ⟨8717875667746290422423329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11623834223661720563231105 8717875667746290422423329)
              ·
                refine ⟨6538406750809717816817497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8717875667746290422423329 6538406750809717816817497)
                ·
                  refine ⟨4903805063107288362613123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6538406750809717816817497 4903805063107288362613123)
                  ·
                    refine ⟨7355707594660932543919685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4903805063107288362613123 7355707594660932543919685)
                    ·
                      refine ⟨1379195173998924851984941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7355707594660932543919685 1379195173998924851984941)
                      ·
                        rfl

theorem cell23_2685973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_2685973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2685973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2685973 prefixEnd_2685973 := by exact prefixLift 2685973
  have htrace : WordTrace (prefixWord ++ tailWord_2685973) baseStart_2685973 baseEnd_2685973 := by
    simpa [prefixWord, tailWord_2685973, baseEnd_2685973] using wordTrace_append hprefix tailTrace_2685973
  have hstable : (prefixWord ++ tailWord_2685973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685973).length < 2 ^ (prefixWord ++ tailWord_2685973).sum := by decide
  have hdescent : baseEnd_2685973 < baseStart_2685973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685979 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 12]
def baseStart_2685979 : Nat := 118140960795 + 2685979 * 2 ^ 59
def prefixEnd_2685979 : Nat := 4983230072969 + 3 ^ 40 * 2685979 * 2
def baseEnd_2685979 : Nat := 153244250542539092056657

theorem tailTrace_2685979 : CollatzResearch.WordTrace tailWord_2685979 prefixEnd_2685979 153244250542539092056657 := by
  unfold tailWord_2685979
  simp only [CollatzResearch.WordTrace]
  refine ⟨97965702336164286537052991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65310468224109524358035327 97965702336164286537052991)
  ·
    refine ⟨146948553504246429805579487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97965702336164286537052991 146948553504246429805579487)
    ·
      refine ⟨220422830256369644708369231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146948553504246429805579487 220422830256369644708369231)
      ·
        refine ⟨330634245384554467062553847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220422830256369644708369231 330634245384554467062553847)
        ·
          refine ⟨495951368076831700593830771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330634245384554467062553847 495951368076831700593830771)
          ·
            refine ⟨743927052115247550890746157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 495951368076831700593830771 743927052115247550890746157)
            ·
              refine ⟨278972644543217831584029809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 743927052115247550890746157 278972644543217831584029809)
              ·
                refine ⟨209229483407413373688022357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 278972644543217831584029809 209229483407413373688022357)
                ·
                  refine ⟨153244250542539092056657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 209229483407413373688022357 153244250542539092056657)
                  ·
                    rfl

theorem cell23_2685979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 12].length) (baseStart_2685979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2685979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2685979 prefixEnd_2685979 := by exact prefixLift 2685979
  have htrace : WordTrace (prefixWord ++ tailWord_2685979) baseStart_2685979 baseEnd_2685979 := by
    simpa [prefixWord, tailWord_2685979, baseEnd_2685979] using wordTrace_append hprefix tailTrace_2685979
  have hstable : (prefixWord ++ tailWord_2685979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685979).length < 2 ^ (prefixWord ++ tailWord_2685979).sum := by decide
  have hdescent : baseEnd_2685979 < baseStart_2685979 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2685996 : List Nat := [2, 2, 1, 1, 1, 2, 3, 5, 6]
def baseStart_2685996 : Nat := 118140960795 + 2685996 * 2 ^ 59
def prefixEnd_2685996 : Nat := 4983230072969 + 3 ^ 40 * 2685996 * 2
def baseEnd_2685996 : Nat := 153245220450442029110815

theorem tailTrace_2685996 : CollatzResearch.WordTrace tailWord_2685996 prefixEnd_2685996 153245220450442029110815 := by
  unfold tailWord_2685996
  simp only [CollatzResearch.WordTrace]
  refine ⟨48983161188551349220210921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65310881584735132293614561 48983161188551349220210921)
  ·
    refine ⟨36737370891413511915158191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48983161188551349220210921 36737370891413511915158191)
    ·
      refine ⟨55106056337120267872737287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36737370891413511915158191 55106056337120267872737287)
      ·
        refine ⟨82659084505680401809105931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55106056337120267872737287 82659084505680401809105931)
        ·
          refine ⟨123988626758520602713658897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82659084505680401809105931 123988626758520602713658897)
          ·
            refine ⟨92991470068890452035244173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123988626758520602713658897 92991470068890452035244173)
            ·
              refine ⟨34871801275833919513216565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92991470068890452035244173 34871801275833919513216565)
              ·
                refine ⟨3269231369609429954364053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34871801275833919513216565 3269231369609429954364053)
                ·
                  refine ⟨153245220450442029110815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3269231369609429954364053 153245220450442029110815)
                  ·
                    rfl

theorem cell23_2685996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 6].length) (baseStart_2685996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2685996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2685996 prefixEnd_2685996 := by exact prefixLift 2685996
  have htrace : WordTrace (prefixWord ++ tailWord_2685996) baseStart_2685996 baseEnd_2685996 := by
    simpa [prefixWord, tailWord_2685996, baseEnd_2685996] using wordTrace_append hprefix tailTrace_2685996
  have hstable : (prefixWord ++ tailWord_2685996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2685996).length < 2 ^ (prefixWord ++ tailWord_2685996).sum := by decide
  have hdescent : baseEnd_2685996 < baseStart_2685996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2685996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686040 : List Nat := [2, 1, 2, 2, 1, 3, 4, 1, 3, 1, 3]
def baseStart_2686040 : Nat := 118140960795 + 2686040 * 2 ^ 59
def prefixEnd_2686040 : Nat := 4983230072969 + 3 ^ 40 * 2686040 * 2
def baseEnd_2686040 : Nat := 1379229577202776089847133

theorem tailTrace_2686040 : CollatzResearch.WordTrace tailWord_2686040 prefixEnd_2686040 1379229577202776089847133 := by
  unfold tailWord_2686040
  simp only [CollatzResearch.WordTrace]
  refine ⟨48983963594471646977511787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65311951459295529303349049 48983963594471646977511787)
  ·
    refine ⟨73475945391707470466267681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48983963594471646977511787 73475945391707470466267681)
    ·
      refine ⟨55106959043780602849700761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73475945391707470466267681 55106959043780602849700761)
      ·
        refine ⟨41330219282835452137275571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55106959043780602849700761 41330219282835452137275571)
        ·
          refine ⟨61995328924253178205913357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41330219282835452137275571 61995328924253178205913357)
          ·
            refine ⟨23248248346594941827217509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61995328924253178205913357 23248248346594941827217509)
            ·
              refine ⟨4359046564986551592603283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23248248346594941827217509 4359046564986551592603283)
              ·
                refine ⟨6538569847479827388904925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4359046564986551592603283 6538569847479827388904925)
                ·
                  refine ⟨2451963692804935270839347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6538569847479827388904925 2451963692804935270839347)
                  ·
                    refine ⟨3677945539207402906259021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2451963692804935270839347 3677945539207402906259021)
                    ·
                      refine ⟨1379229577202776089847133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3677945539207402906259021 1379229577202776089847133)
                      ·
                        rfl

theorem cell23_2686040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 3, 1, 3].length) (baseStart_2686040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2686040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2686040 prefixEnd_2686040 := by exact prefixLift 2686040
  have htrace : WordTrace (prefixWord ++ tailWord_2686040) baseStart_2686040 baseEnd_2686040 := by
    simpa [prefixWord, tailWord_2686040, baseEnd_2686040] using wordTrace_append hprefix tailTrace_2686040
  have hstable : (prefixWord ++ tailWord_2686040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686040).length < 2 ^ (prefixWord ++ tailWord_2686040).sum := by decide
  have hdescent : baseEnd_2686040 < baseStart_2686040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686063 : List Nat := [1, 1, 2, 1, 3, 3, 1, 1, 2, 6, 2]
def baseStart_2686063 : Nat := 118140960795 + 2686063 * 2 ^ 59
def prefixEnd_2686063 : Nat := 4983230072969 + 3 ^ 40 * 2686063 * 2
def baseEnd_2686063 : Nat := 1379241387257829499859527

theorem tailTrace_2686063 : CollatzResearch.WordTrace tailWord_2686063 prefixEnd_2686063 1379241387257829499859527 := by
  unfold tailWord_2686063
  simp only [CollatzResearch.WordTrace]
  refine ⟨97968766067859968883110843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65312510711906645922073895 97968766067859968883110843)
  ·
    refine ⟨146953149101789953324666265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97968766067859968883110843 146953149101789953324666265)
    ·
      refine ⟨110214861826342464993499699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146953149101789953324666265 110214861826342464993499699)
      ·
        refine ⟨165322292739513697490249549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110214861826342464993499699 165322292739513697490249549)
        ·
          refine ⟨61995859777317636558843581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165322292739513697490249549 61995859777317636558843581)
          ·
            refine ⟨23248447416494113709566343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61995859777317636558843581 23248447416494113709566343)
            ·
              refine ⟨34872671124741170564349515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23248447416494113709566343 34872671124741170564349515)
              ·
                refine ⟨52309006687111755846524273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34872671124741170564349515 52309006687111755846524273)
                ·
                  refine ⟨39231755015333816884893205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52309006687111755846524273 39231755015333816884893205)
                  ·
                    refine ⟨1838988516343772666479369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 39231755015333816884893205 1838988516343772666479369)
                    ·
                      refine ⟨1379241387257829499859527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1838988516343772666479369 1379241387257829499859527)
                      ·
                        rfl

theorem cell23_2686063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 6, 2].length) (baseStart_2686063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2686063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2686063 prefixEnd_2686063 := by exact prefixLift 2686063
  have htrace : WordTrace (prefixWord ++ tailWord_2686063) baseStart_2686063 baseEnd_2686063 := by
    simpa [prefixWord, tailWord_2686063, baseEnd_2686063] using wordTrace_append hprefix tailTrace_2686063
  have hstable : (prefixWord ++ tailWord_2686063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686063).length < 2 ^ (prefixWord ++ tailWord_2686063).sum := by decide
  have hdescent : baseEnd_2686063 < baseStart_2686063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686080 : List Nat := [2, 1, 1, 2, 1, 3, 2, 2, 5, 2, 2]
def baseStart_2686080 : Nat := 118140960795 + 2686080 * 2 ^ 59
def prefixEnd_2686080 : Nat := 4983230072969 + 3 ^ 40 * 2686080 * 2
def baseEnd_2686080 : Nat := 1379250116428955933346949

theorem tailTrace_2686080 : CollatzResearch.WordTrace tailWord_2686080 prefixEnd_2686080 1379250116428955933346949 := by
  unfold tailWord_2686080
  simp only [CollatzResearch.WordTrace]
  refine ⟨48984693054399190393239847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65312924072532253857653129 48984693054399190393239847)
  ·
    refine ⟨73477039581598785589859771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48984693054399190393239847 73477039581598785589859771)
    ·
      refine ⟨110215559372398178384789657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73477039581598785589859771 110215559372398178384789657)
      ·
        refine ⟨82661669529298633788592243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110215559372398178384789657 82661669529298633788592243)
        ·
          refine ⟨123992504293947950682888365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82661669529298633788592243 123992504293947950682888365)
          ·
            refine ⟨46497189110230481506083137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123992504293947950682888365 46497189110230481506083137)
            ·
              refine ⟨34872891832672861129562353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46497189110230481506083137 34872891832672861129562353)
              ·
                refine ⟨26154668874504645847171765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34872891832672861129562353 26154668874504645847171765)
                ·
                  refine ⟨2452000206984810548172353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26154668874504645847171765 2452000206984810548172353)
                  ·
                    refine ⟨1839000155238607911129265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2452000206984810548172353 1839000155238607911129265)
                    ·
                      refine ⟨1379250116428955933346949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1839000155238607911129265 1379250116428955933346949)
                      ·
                        rfl

theorem cell23_2686080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 5, 2, 2].length) (baseStart_2686080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2686080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2686080 prefixEnd_2686080 := by exact prefixLift 2686080
  have htrace : WordTrace (prefixWord ++ tailWord_2686080) baseStart_2686080 baseEnd_2686080 := by
    simpa [prefixWord, tailWord_2686080, baseEnd_2686080] using wordTrace_append hprefix tailTrace_2686080
  have hstable : (prefixWord ++ tailWord_2686080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686080).length < 2 ^ (prefixWord ++ tailWord_2686080).sum := by decide
  have hdescent : baseEnd_2686080 < baseStart_2686080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686083 : List Nat := [1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 5]
def baseStart_2686083 : Nat := 118140960795 + 2686083 * 2 ^ 59
def prefixEnd_2686083 : Nat := 4983230072969 + 3 ^ 40 * 2686083 * 2
def baseEnd_2686083 : Nat := 1379251656870919421609435

theorem tailTrace_2686083 : CollatzResearch.WordTrace tailWord_2686083 prefixEnd_2686083 1379251656870919421609435 := by
  unfold tailWord_2686083
  simp only [CollatzResearch.WordTrace]
  refine ⟨97969495527787512298838903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65312997018525008199225935 97969495527787512298838903)
  ·
    refine ⟨146954243291681268448258355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97969495527787512298838903 146954243291681268448258355)
    ·
      refine ⟨220431364937521902672387533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146954243291681268448258355 220431364937521902672387533)
      ·
        refine ⟨82661761851570713502145325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 220431364937521902672387533 82661761851570713502145325)
        ·
          refine ⟨30998160694339017563304497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82661761851570713502145325 30998160694339017563304497)
          ·
            refine ⟨23248620520754263172478373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30998160694339017563304497 23248620520754263172478373)
            ·
              refine ⟨4359116347641424344839695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23248620520754263172478373 4359116347641424344839695)
              ·
                refine ⟨6538674521462136517259543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4359116347641424344839695 6538674521462136517259543)
                ·
                  refine ⟨9808011782193204775889315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6538674521462136517259543 9808011782193204775889315)
                  ·
                    refine ⟨14712017673289807163833973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9808011782193204775889315 14712017673289807163833973)
                    ·
                      refine ⟨1379251656870919421609435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14712017673289807163833973 1379251656870919421609435)
                      ·
                        rfl

theorem cell23_2686083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 5].length) (baseStart_2686083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2686083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2686083 prefixEnd_2686083 := by exact prefixLift 2686083
  have htrace : WordTrace (prefixWord ++ tailWord_2686083) baseStart_2686083 baseEnd_2686083 := by
    simpa [prefixWord, tailWord_2686083, baseEnd_2686083] using wordTrace_append hprefix tailTrace_2686083
  have hstable : (prefixWord ++ tailWord_2686083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686083).length < 2 ^ (prefixWord ++ tailWord_2686083).sum := by decide
  have hdescent : baseEnd_2686083 < baseStart_2686083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686090 : List Nat := [3, 1, 2, 3, 1, 1, 2, 4, 2, 4]
def baseStart_2686090 : Nat := 118140960795 + 2686090 * 2 ^ 59
def prefixEnd_2686090 : Nat := 4983230072969 + 3 ^ 40 * 2686090 * 2
def baseEnd_2686090 : Nat := 459751750411833631407301

theorem tailTrace_2686090 : CollatzResearch.WordTrace tailWord_2686090 prefixEnd_2686090 459751750411833631407301 := by
  unfold tailWord_2686090
  simp only [CollatzResearch.WordTrace]
  refine ⟨24492437709690538123585931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65313167225841434996229149 24492437709690538123585931)
  ·
    refine ⟨36738656564535807185378897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24492437709690538123585931 36738656564535807185378897)
    ·
      refine ⟨27553992423401855389034173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36738656564535807185378897 27553992423401855389034173)
      ·
        refine ⟨10332747158775695770887815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27553992423401855389034173 10332747158775695770887815)
        ·
          refine ⟨15499120738163543656331723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10332747158775695770887815 15499120738163543656331723)
          ·
            refine ⟨23248681107245315484497585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15499120738163543656331723 23248681107245315484497585)
            ·
              refine ⟨17436510830433986613373189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23248681107245315484497585 17436510830433986613373189)
              ·
                refine ⟨3269345780706372490007473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17436510830433986613373189 3269345780706372490007473)
                ·
                  refine ⟨2452009335529779367505605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3269345780706372490007473 2452009335529779367505605)
                  ·
                    refine ⟨459751750411833631407301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2452009335529779367505605 459751750411833631407301)
                    ·
                      rfl

theorem cell23_2686090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 4, 2, 4].length) (baseStart_2686090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2686090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2686090 prefixEnd_2686090 := by exact prefixLift 2686090
  have htrace : WordTrace (prefixWord ++ tailWord_2686090) baseStart_2686090 baseEnd_2686090 := by
    simpa [prefixWord, tailWord_2686090, baseEnd_2686090] using wordTrace_append hprefix tailTrace_2686090
  have hstable : (prefixWord ++ tailWord_2686090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686090).length < 2 ^ (prefixWord ++ tailWord_2686090).sum := by decide
  have hdescent : baseEnd_2686090 < baseStart_2686090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686103 : List Nat := [1, 1, 3, 3, 3, 2, 2, 8]
def baseStart_2686103 : Nat := 118140960795 + 2686103 * 2 ^ 59
def prefixEnd_2686103 : Nat := 4983230072969 + 3 ^ 40 * 2686103 * 2
def baseEnd_2686103 : Nat := 51083775054963309013309

theorem tailTrace_2686103 : CollatzResearch.WordTrace tailWord_2686103 prefixEnd_2686103 51083775054963309013309 := by
  unfold tailWord_2686103
  simp only [CollatzResearch.WordTrace]
  refine ⟨97970224987715055714566963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65313483325143370476377975 97970224987715055714566963)
  ·
    refine ⟨146955337481572583571850445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97970224987715055714566963 146955337481572583571850445)
    ·
      refine ⟨55108251555589718839443917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146955337481572583571850445 55108251555589718839443917)
      ·
        refine ⟨20665594333346144564791469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55108251555589718839443917 20665594333346144564791469)
        ·
          refine ⟨7749597875004804211796801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20665594333346144564791469 7749597875004804211796801)
          ·
            refine ⟨5812198406253603158847601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7749597875004804211796801 5812198406253603158847601)
            ·
              refine ⟨4359148804690202369135701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5812198406253603158847601 4359148804690202369135701)
              ·
                refine ⟨51083775054963309013309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4359148804690202369135701 51083775054963309013309)
                ·
                  rfl

theorem cell23_2686103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 8].length) (baseStart_2686103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2686103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2686103 prefixEnd_2686103 := by exact prefixLift 2686103
  have htrace : WordTrace (prefixWord ++ tailWord_2686103) baseStart_2686103 baseEnd_2686103 := by
    simpa [prefixWord, tailWord_2686103, baseEnd_2686103] using wordTrace_append hprefix tailTrace_2686103
  have hstable : (prefixWord ++ tailWord_2686103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686103).length < 2 ^ (prefixWord ++ tailWord_2686103).sum := by decide
  have hdescent : baseEnd_2686103 < baseStart_2686103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686110 : List Nat := [4, 3, 1, 1, 2, 1, 2, 1, 1, 1, 6]
def baseStart_2686110 : Nat := 118140960795 + 2686110 * 2 ^ 59
def prefixEnd_2686110 : Nat := 4983230072969 + 3 ^ 40 * 2686110 * 2
def baseEnd_2686110 : Nat := 1379265520848590815971811

theorem tailTrace_2686110 : CollatzResearch.WordTrace tailWord_2686110 prefixEnd_2686110 1379265520848590815971811 := by
  unfold tailWord_2686110
  simp only [CollatzResearch.WordTrace]
  refine ⟨12246310037336211988758973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65313653532459797273381189 12246310037336211988758973)
  ·
    refine ⟨4592366264001079495784615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12246310037336211988758973 4592366264001079495784615)
    ·
      refine ⟨6888549396001619243676923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4592366264001079495784615 6888549396001619243676923)
      ·
        refine ⟨10332824094002428865515385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6888549396001619243676923 10332824094002428865515385)
        ·
          refine ⟨7749618070501821649136539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10332824094002428865515385 7749618070501821649136539)
          ·
            refine ⟨11624427105752732473704809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7749618070501821649136539 11624427105752732473704809)
            ·
              refine ⟨8718320329314549355278607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11624427105752732473704809 8718320329314549355278607)
              ·
                refine ⟨13077480493971824032917911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8718320329314549355278607 13077480493971824032917911)
                ·
                  refine ⟨19616220740957736049376867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13077480493971824032917911 19616220740957736049376867)
                  ·
                    refine ⟨29424331111436604074065301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19616220740957736049376867 29424331111436604074065301)
                    ·
                      refine ⟨1379265520848590815971811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29424331111436604074065301 1379265520848590815971811)
                      ·
                        rfl

theorem cell23_2686110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_2686110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2686110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2686110 prefixEnd_2686110 := by exact prefixLift 2686110
  have htrace : WordTrace (prefixWord ++ tailWord_2686110) baseStart_2686110 baseEnd_2686110 := by
    simpa [prefixWord, tailWord_2686110, baseEnd_2686110] using wordTrace_append hprefix tailTrace_2686110
  have hstable : (prefixWord ++ tailWord_2686110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686110).length < 2 ^ (prefixWord ++ tailWord_2686110).sum := by decide
  have hdescent : baseEnd_2686110 < baseStart_2686110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2686114 : List Nat := [3, 3, 1, 3, 2, 2, 1, 2, 1, 1, 4]
def baseStart_2686114 : Nat := 118140960795 + 2686114 * 2 ^ 59
def prefixEnd_2686114 : Nat := 4983230072969 + 3 ^ 40 * 2686114 * 2
def baseEnd_2686114 : Nat := 1379267574771208800321793

theorem tailTrace_2686114 : CollatzResearch.WordTrace tailWord_2686114 prefixEnd_2686114 1379267574771208800321793 := by
  unfold tailWord_2686114
  simp only [CollatzResearch.WordTrace]
  refine ⟨24492656547668801148304349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65313750793783469728811597 24492656547668801148304349)
  ·
    refine ⟨9184746205375800430614131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24492656547668801148304349 9184746205375800430614131)
    ·
      refine ⟨13777119308063700645921197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9184746205375800430614131 13777119308063700645921197)
      ·
        refine ⟨5166419740523887742220449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13777119308063700645921197 5166419740523887742220449)
        ·
          refine ⟨3874814805392915806665337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5166419740523887742220449 3874814805392915806665337)
          ·
            refine ⟨2906111104044686854999003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3874814805392915806665337 2906111104044686854999003)
            ·
              refine ⟨4359166656067030282498505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2906111104044686854999003 4359166656067030282498505)
              ·
                refine ⟨3269374992050272711873879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4359166656067030282498505 3269374992050272711873879)
                ·
                  refine ⟨4904062488075409067810819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3269374992050272711873879 4904062488075409067810819)
                  ·
                    refine ⟨7356093732113113601716229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4904062488075409067810819 7356093732113113601716229)
                    ·
                      refine ⟨1379267574771208800321793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7356093732113113601716229 1379267574771208800321793)
                      ·
                        rfl

theorem cell23_2686114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_2686114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2686114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2686114 prefixEnd_2686114 := by exact prefixLift 2686114
  have htrace : WordTrace (prefixWord ++ tailWord_2686114) baseStart_2686114 baseEnd_2686114 := by
    simpa [prefixWord, tailWord_2686114, baseEnd_2686114] using wordTrace_append hprefix tailTrace_2686114
  have hstable : (prefixWord ++ tailWord_2686114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2686114).length < 2 ^ (prefixWord ++ tailWord_2686114).sum := by decide
  have hdescent : baseEnd_2686114 < baseStart_2686114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2686114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
